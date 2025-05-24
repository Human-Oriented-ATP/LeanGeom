import Mathlib.Geometry.Euclidean.Angle.Oriented.Basic
import Lean
import Qq

open Lean Elab Meta Qq

notation "∠" A:max B:max => Complex.orientation.oangle A B
instance : Fact <| Module.finrank ℝ ℂ = 2 := ⟨Complex.finrank_real_complex⟩

simproc raySwap (Orientation.oangle Complex.orientation _ _) := fun e => do
  let ⟨1, ~q(Real.Angle), ~q(Orientation.oangle Complex.orientation $A $B)⟩ ← inferTypeQ e | return .continue
  if Expr.lt A B then
    return .continue
  else
    return .done {
      expr := q(-(Orientation.oangle Complex.orientation $B $A)),
      proof? := some q(Orientation.oangle_rev Complex.orientation $B $A)
    }

-- #check  AddCircle.equivAddCircle

/-
first use simp with `equivAddCircle` to cast into `AddCircle 1`, and push the cast.
then, use a simproc to swap rays to be sorted.
and, use simp to push `equivAddCircle` through casts from `ℝ` involving `π`.
And finally, call `abel`
-/

/-
For distances with multiplication, use `log` to cast it into something additive, and a positivity side goal.
-/

section Angles

elab "abel_angle" : tactic => return

-- example : (↑(Real.pi/2) : Real.Angle) = ↑((5/2) * Real.pi) := by
--   abel_angle

-- example (A B : ℂ) : ∠ A B = ∠ B A + ↑(9 * Real.pi) := by
--   abel_angle

example (A B : ℂ) : ∠ A B + ∠ B A = 0 := by
  simp only [raySwap]
  abel

end Angles


section Distance

-- example (A B : ℂ) (h : A ≠ B) : dist A B ≠ 0 := by
--   positivity

elab "mul_abel" : tactic => return

-- example (x y : ℝ) (h₁ : x ≠ 0) (h₂ : y ≠ 0) : x^2 * y⁻¹ * x⁻¹^2 * y = 1 := by
--   mul_abel

end Distance
