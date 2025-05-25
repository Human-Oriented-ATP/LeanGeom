import LeanGeom.Defs
import LeanGeom.LeanDefs
import Mathlib.Tactic.NormNum.Core

/-!
This file defines how to read the lean goal-state
-/

open Lean Qq Mathlib.Meta
instance : Neg AngleSum := ⟨fun { sum, θ } => { sum := sum.map fun (a, b) => (-a, b), θ := -θ }⟩
instance : SMul Int AngleSum := ⟨fun n { sum, θ } => { sum := sum.map fun (a, b) => (n * a, b), θ := n • θ }⟩
instance : Add AngleSum := ⟨fun a b => { sum := a.sum ++ b.sum, θ := a.θ + b.θ }⟩
instance : Sub AngleSum := ⟨fun a b => a + -b⟩

partial def obtainAngle (x : Q(Real.Angle)) : OptionT MetaM AngleSum := do
  match x with
  | ~q(∠ $A $B) => return { sum := [(1, ⟨⟨A⟩, ⟨B⟩⟩)], θ := 0 }
  | ~q(($n : Int) • $a) =>
    have : Q(Ring Int) := q(inferInstance)
    let ⟨n, _⟩ ← NormNum.deriveInt n
    let a ← obtainAngle a
    return (n.intLit! : Int) • a
  | ~q($a + $b) =>
    let a ← obtainAngle a
    let b ← obtainAngle b
    return a + b
  | ~q($a - $b) =>
    let a ← obtainAngle a
    let b ← obtainAngle b
    return a - b
  | ~q(-$a) =>
    let a ← obtainAngle a
    return -a
  | ~q(0) => return { sum := [], θ := 0}
  | _ => failure

def obtainFact (e : Q(Prop)) (pf : TermProof) : GeomM Unit := do
  match e with
  | ~q(($a : Real.Angle) = $b) =>
    let some a ← (obtainAngle a).run | return
    let some b ← (obtainAngle b).run | return
    let pf ← atomize pf
    modifyFacts fun facts => { facts with angles := facts.angles.push (a - b, pf) }
  | ~q(¬($a : Real.Angle) = $b) =>
    let some a ← (obtainAngle a).run | return
    let some b ← (obtainAngle b).run | return
    let pf ← atomize pf
    modifyFacts fun facts => { facts with nangles := facts.nangles.push (a - b, pf) }
  | _ => return

def obtainFacts (goal : Q(Prop)) : GeomM Unit := do
  for decl in ← getLCtx do
    unless decl.isImplementationDetail do
      obtainFact decl.type (.hypothesis decl.userName)
  match goal with
  | ~q(¬$p) => obtainFact p .negatedGoal
  | p => obtainFact q(¬$p) .negatedGoal
