import Auto

set_option trace.auto.lamReif.prep.printResult true
set_option trace.auto.lamReif.printResult true

set_option trace.auto.mono true
set_option trace.auto.mono.match true
set_option trace.auto.mono.printConstInst true
set_option trace.auto.mono.printLemmaInst true
set_option trace.auto.mono.printResult true

set_option trace.auto.collectInd true
set_option trace.auto.lamFOL2SMT true

set_option auto.smt true
set_option auto.smt.trust true
set_option trace.auto.printLemmas true
set_option trace.auto.smt.printCommands true
set_option trace.auto.smt.result true

example : ∃ (t : Fin 5), True := by
  auto

structure TotalOrder (t : Type) :=
  -- relation: total order
  le (x y : t) : Bool
  -- axioms
  le_refl       (x : t) : le x x
  le_trans  (x y z : t) : le x y → le y z → le x z
  le_antisymm (x y : t) : le x y → le y x → x = y
  le_total    (x y : t) : le x y ∨ le y x

example : ∃ (t : TotalOrder Nat), True := by
  auto
