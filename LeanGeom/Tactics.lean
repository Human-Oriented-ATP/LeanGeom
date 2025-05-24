import Mathlib.Geometry.Euclidean.Angle.Oriented.Basic
import Lean
import Qq

open Lean Elab Meta Qq

instance : Fact <| Module.finrank ℝ ℂ = 2 := ⟨Complex.finrank_real_complex⟩

noncomputable def RayAngle (A B : ℂ) : Real.Angle := Complex.orientation.oangle (A - B) 1

notation "∠" A:max B:max => RayAngle A B

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

open Real

open private dischargeUsingAssumption? in Simp.dischargeDefault?

theorem rayAngle_swap (A B : ℂ) (h : A ≠ B) : ∠ B A = ∠ A B + π := by
  unfold RayAngle
  rw [← Orientation.oangle_neg_left _ (sub_ne_zero_of_ne h) (by norm_num), neg_sub]

simproc raySwap (RayAngle _ _) := .ofQ fun
  | 1, ~q(Real.Angle), ~q(∠ $B $A) => do
    if Expr.lt A B then
      let some e ← dischargeUsingAssumption? q($A ≠ $B) | return .continue
      have e : Q($A ≠ $B) := e
      return .done <| .mk q(∠ $A $B + π) (some q(rayAngle_swap $A $B $e))
    else
      return .continue


elab "abel_angle" : tactic => return

-- example : (↑(Real.pi/2) : Real.Angle) = ↑((5/2) * Real.pi) := by
--   abel_angle

-- example (A B : ℂ) : ∠ A B = ∠ B A + ↑(9 * Real.pi) := by
--   abel_angle

example (A B : ℂ) (h : A ≠ B) : ∠ A B = ∠ B A - π := by
  simp [raySwap]


end Angles


section Distance

-- example (A B : ℂ) (h : A ≠ B) : dist A B ≠ 0 := by
--   positivity

elab "mul_abel" : tactic => return

-- example (x y : ℝ) (h₁ : x ≠ 0) (h₂ : y ≠ 0) : x^2 * y⁻¹ * x⁻¹^2 * y = 1 := by
--   mul_abel

end Distance
