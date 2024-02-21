import Lean
import Auto.Lib.ExprExtra
import Auto.Lib.MessageData
import Auto.Lib.MetaExtra
import Auto.Lib.MonadUtils
import Auto.Translation.Reduction
open Lean

initialize
  registerTraceClass `auto.collectInd

namespace Auto

/--
  Test whether a given inductive type is explicitly and inductive family.
  i.e., return `false` iff `numParams` match the number of arguments of
    the type constructor
-/
def isFamily (tyctorname : Name) : CoreM Bool := do
  let .some (.inductInfo val) := (← getEnv).find? tyctorname
    | throwError "isFamily :: {tyctorname} is not a type constructor"
  return (Expr.forallBinders val.type).size != val.numParams

/--
  Test whether a given inductive type is an inductively defined proposition
-/
def isIndProp (tyctorname : Name) : CoreM Bool := do
  let .some (.inductInfo val) := (← getEnv).find? tyctorname
    | throwError "isIndProp :: {tyctorname} is not a type constructor"
  (Meta.withTransparency (n := MetaM) .all <|
    Meta.forallTelescopeReducing val.type fun _ body =>
      Meta.isDefEq body (.sort .zero)).run' {}

/--
  Whether the constructor is monomorphic after all parameters are instantiated.
-/
def isSimpleCtor (ctorname : Name) : CoreM Bool := do
  let .some (.ctorInfo val) := (← getEnv).find? ctorname
    | throwError "isSimpleCtor :: {ctorname} is not a type constructor"
  Meta.MetaM.run' <| Meta.forallBoundedTelescope val.type val.numParams fun _ body =>
    pure ((Expr.depArgs body).size == 0)

/--
  Returns true iff the inductive type is not explicitly an inductive family,
    and all constructors of this inductive type are simple (refer to `isSimpleCtor`)
-/
def isSimpleInductive (tyctorname : Name) : CoreM Bool := do
  let .some (.inductInfo val) := (← getEnv).find? tyctorname
    | throwError "isSimple :: {tyctorname} is not a type constructor"
  return (← val.ctors.allM isSimpleCtor) && !(← isFamily tyctorname)

structure SimpleIndVal where
  /-- Name of type constructor -/
  name : Name
  /-- Instantiated type constructor -/
  type : Expr
  /-- Array of `(instantiated_ctor, type_of_instantiated_constructor)` -/
  ctors : Array (Expr × Expr)
  /-- Instantiated projections -/
  projs : Option (Array Expr)

instance : ToMessageData SimpleIndVal where
  toMessageData siv :=
    m!"SimpleIndVal ⦗⦗ {siv.type}, Ctors : " ++
      MessageData.array siv.ctors (fun (e₁, e₂) => m!"{e₁} : {e₂}") ++
      (match siv.projs with
       | .some arr =>
         ", Projs : " ++ MessageData.array arr (fun e => m!"{e}")
       | .none => m!"") ++
      m!" ⦘⦘"

def SimpleIndVal.zetaReduce (si : SimpleIndVal) : MetaM SimpleIndVal := do
  let ⟨name, type, ctors, projs⟩ := si
  let ctors ← ctors.mapM (fun (val, ty) => do return (← Meta.zetaReduce val, ← Meta.zetaReduce ty))
  let projs ← projs.mapM (fun arr => arr.mapM Meta.zetaReduce)
  return ⟨name, ← Meta.zetaReduce type, ctors, projs⟩

def isComplexStructure (tyctorname : Name) : CoreM Bool := do
  let .some (.inductInfo val) := (← getEnv).find? tyctorname
    | throwError "isComplex :: {tyctorname} is not a type constructor"
  return val.numIndices = 0
  && !val.isRec
  && !val.isUnsafe
  && !val.isNested
  -- is a structure / has only one constructor
  && val.ctors.length = 1
  -- is not mutually inductive
  && val.all.length = 1

/-- A type for structures with axioms. These cannot be
  constructed (or selected from) in FOL, i.e. they are not
  represented as FOL sorts, but individual _instances_ of this
  type can be used in FOL by "flattening". For example, suppose
  we have the type (TotalOrder Nat):

  ```
  structure TotalOrder (t : Type) :=
  le (x y : t) : Bool
  le_refl       (x : t) : le x x
  le_trans  (x y z : t) : le x y → le y z → le x z
  le_antisymm (x y : t) : le x y → le y x → x = y
  le_total    (x y : t) : le x y ∨ le y x
  ```

  We can represent this in FOL as an _uninterpreted_ sort `TotalOrder_Nat`
  without constructors or selectors, but with the following declarations:

  ```
  (declare-sort TotalOrder_Nat 0)
  (declare-fun le (TotalOrder_Nat Nat Nat) Bool)
  (assert (forall ((inst TotalOrder_Nat) (x Nat)) le inst x x))
  [... and so on]
  ```
  -/
structure ComplexStructure where
  /-- Name of type constructor -/
  name : Name
  /-- Instantiated type constructor -/
  type : Expr
  /-- Instantiated fields -/
  fields : Option (Array Expr)
  /-- Instantiated axioms -/
  axioms : Option (Array Expr)

instance : ToMessageData ComplexStructure where
  toMessageData str :=
    m!"ComplexStructure ⦗⦗ {str.type}, Fields : " ++
      (match str.fields with
       | .some arr => MessageData.array arr (fun e => m!"{e}")
       | .none => m!"") ++
      (match str.axioms with
       | .some arr =>
         ", Axioms : " ++ MessageData.array arr (fun e => m!"{e}")
       | .none => m!"") ++
      m!" ⦘⦘"

/--
  For a given type constructor `tyctor`, `CollectIndState[tyctor]`
    is an array of `(instantiated_tyctor, [SimpleIndVal associated to tyctor])`
-/
structure CollectInduct.State where
  recorded : HashMap Name (Array Expr)     := {}
  sis      : Array (Array SimpleIndVal) := #[]
  cis      : Array ComplexStructure := #[]

abbrev IndCollectM := StateRefT CollectInduct.State MetaM

#genMonadState IndCollectM

private def collectSimpleInduct
  (tyctor : Name) (lvls : List Level) (args : Array Expr) : MetaM SimpleIndVal := do
  let .some (.inductInfo val) := (← getEnv).find? tyctor
    | throwError "collectSimpleInduct :: Unexpected error"
  let ctors ← (Array.mk val.ctors).mapM (fun ctorname => do
    let instctor := mkAppN (Expr.const ctorname lvls) args
    let type ← Meta.inferType instctor
    let type ← prepReduceExpr type
    return (instctor, type))
  let env ← getEnv
  let projs ← (getStructureInfo? env tyctor).mapM (fun si => do
    si.fieldNames.mapM (fun fieldName => do
      let .some projFn := getProjFnForField? env tyctor fieldName
        | throwError "collectSimpleInduct :: Unexpected error"
      return mkAppN (Expr.const projFn lvls) args))
  return ⟨tyctor, mkAppN (Expr.const tyctor lvls) args, ctors, projs⟩

private def collectComplexStruct
  (tyctor : Name) (lvls : List Level) (args : Array Expr) : MetaM ComplexStructure := do
  let env ← getEnv
  let .some info := getStructureInfo? env tyctor
    | throwError "collectComplexStruct :: {tyctor} is not a structure"
  let mut fields := Array.empty
  let mut axioms := Array.empty
  trace[auto.collectInd] "structure {info.structName} has fields {info.fieldNames}"
  for field in info.fieldInfo do
    if field.subobject?.isSome then
      continue
    let proj := (env.find? field.projFn).get!
    let instantiated ← Meta.instantiateForall proj.type args
    let isAxiom := (← Meta.isProp proj.type)
    let typeStr := if isAxiom then "[axiom]" else "[function]"
    trace[auto.collectInd] "{typeStr} {field.fieldName} : {instantiated}"
    if isAxiom then
      axioms := axioms.push instantiated
    else
      fields := fields.push instantiated
  return ⟨tyctor, mkAppN (Expr.const tyctor lvls) args, .some fields, .some axioms⟩

mutual

  private partial def collectAppInstInduct (e : Expr) : IndCollectM Unit := do
    let .const tyctor lvls := e.getAppFn
      | return
    let .some (.inductInfo val) := (← getEnv).find? tyctor
      | return
    let isSimpleInductive ← @id (CoreM _) (val.all.allM isSimpleInductive)
    let isComplexStructure := val.all.length = 1 && (← @id (CoreM _) (val.all.anyM isComplexStructure))
    if !(isSimpleInductive || isComplexStructure) then
      trace[auto.collectInd] (m!"Warning : {tyctor} or some type within the " ++
        m!"same mutual block ({val.all}) is neither a simple nor a complex inductive type. Ignoring it...")
      return
    /-
      Do not translate typeclasses as inductive types
      Mathlib has a complex typeclass hierarchy, so translating typeclasses might make a mess
    -/
    if Lean.isClass (← getEnv) tyctor then
      return
    let args := e.getAppArgs
    if args.size != val.numParams then
      trace[auto.collectInd] "Warning : Parameters of {tyctor} in {e} is not fully instantiated. Ignoring it ..."
      return
    if !(← getRecorded).contains tyctor then
      setRecorded ((← getRecorded).insert tyctor #[])
    let .some arr := (← getRecorded).find? tyctor
      | throwError "collectAppInstSimpleInduct :: Unexpected error"
    for e' in arr do
      if ← Meta.isDefEq e e' then
        return
    for tyctor' in val.all do
      setRecorded ((← getRecorded).insert tyctor' (arr.push (mkAppN (.const tyctor' lvls) args)))
    if isSimpleInductive then
      let mutualInductVal ← val.all.mapM (collectSimpleInduct · lvls args)
      for inductval in mutualInductVal do
        for (_, type) in inductval.ctors do
          collectExprInduct type
      setSis ((← getSis).push ⟨mutualInductVal⟩)
    if isComplexStructure then
      trace[auto.collectInd] "Experimental support for structures with axioms: {tyctor}"
      let complexStructures ← val.all.mapM (collectComplexStruct · lvls args)
      for struct in complexStructures do
        setCis ((← getCis).push struct)

  partial def collectExprInduct : Expr → IndCollectM Unit
  | e@(.app ..) => do
    collectAppInstInduct e
    let _ ← e.getAppArgs.mapM collectExprInduct
  | e@(.lam ..) => do trace[auto.collectInd] "Warning : Ignoring lambda expression {e}"
  | e@(.forallE _ ty body _) => do
    if body.hasLooseBVar 0 then
      trace[auto.collectInd] "Warning : Ignoring forall expression {e}"
      return
    collectExprInduct ty
    collectExprInduct body
  | .letE .. => throwError "collectExprSimpleInduct :: Let-expressions should have been reduced"
  | .mdata .. => throwError "collectExprSimpleInduct :: mdata should have been consumed"
  | .proj .. => throwError "collectExprSimpleInduct :: Projections should have been turned into ordinary expressions"
  | e => collectAppInstInduct e

end

def collectExprsInduct (es : Array Expr) : MetaM (Array (Array SimpleIndVal) × Array ComplexStructure) := do
  let (_, st) ← (es.mapM collectExprInduct).run {}
  return (st.sis, st.cis)

end Auto

section Test

  private def skd (e : Expr) : Elab.Term.TermElabM Unit := do
    let (_, st) ← (Auto.collectExprInduct (Auto.Expr.eraseMData e)).run {}
    for siw in st.sis do
      for si in siw do
        logInfo m!"{si}"

  #getExprAndApply[List.cons 2|skd]
  #getExprAndApply[(Array Bool × Array Nat)|skd]

  mutual

    private inductive tree where
      | leaf : Nat → tree
      | node : treelist → tree

    private inductive treelist where
      | nil : treelist
      | cons : tree → treelist → treelist

  end

  #getExprAndApply[tree|skd]

  mutual

    private inductive Tree (α : Type u) where
      | leaf : α → Tree α
      | node : TreeList α → Tree α

    private inductive TreeList (α : Type u) where
      | nil : TreeList α
      | cons : Tree α → TreeList α → TreeList α

  end

  #getExprAndApply[Tree Int|skd]

end Test
