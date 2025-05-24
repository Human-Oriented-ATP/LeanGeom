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
      let some e ← checkTypeQ e q($A ≠ $B) | return .continue
      return .done <| .mk q(∠ $A $B + π) (some q(rayAngle_swap $A $B $e))
    else
      return .continue

noncomputable abbrev Angle.equivUnitAddCircle : Angle ≃+ UnitAddCircle :=
  AddCircle.equivAddCircle (2 * π) (1 : ℝ) (by simp [pi_ne_zero]) (zero_ne_one' ℝ).symm

lemma Angle.equivUnitAddCircle_apply_mk (x : ℝ) :
  Angle.equivUnitAddCircle (Angle.coe x) = (x * (2 * π)⁻¹ : UnitAddCircle) := by
  rw [← mul_one (2 * π)⁻¹]
  apply AddCircle.equivAddCircle_apply_mk

macro "angle_to_unit_add_circle" : tactic =>
`(tactic| (
  rw [← Angle.equivUnitAddCircle.apply_eq_iff_eq]
  try (simp only [AddEquiv.map_add, AddEquiv.map_zero, AddEquiv.map_sub, AddEquiv.map_neg, ← Angle.coe_nsmul])
  simp only [Angle.equivUnitAddCircle_apply_mk]
  ring_nf
  try (simp only [mul_inv_cancel₀ pi_ne_zero, inv_mul_cancel₀ pi_ne_zero, mul_one, one_mul])
  ))

macro "abel_angle" : tactic =>
`(tactic| (
    try (simp only [raySwap])
    angle_to_unit_add_circle
    refine sub_eq_zero.mp ?_
    abel_nf
    try (simp only [← QuotientAddGroup.mk_add, ← QuotientAddGroup.mk_zsmul])
    rw [AddCircle.coe_eq_zero_iff]
    use ?n
    norm_num
    norm_cast
    exact rfl))

example : (↑(Real.pi/2) : Real.Angle) = ↑((5/2) * Real.pi) := by
  abel_angle

example (A B : ℂ) (h : A ≠ B) : ∠ A B = ∠ B A + ↑(9 * Real.pi) := by
  abel_angle

example (A B C D : ℂ) (h : A ≠ B) : ∠ A B - π + ∠ C D = (↑(Real.pi/2) : Real.Angle) + ∠ C D + (π : Real.Angle) + ∠ B A + (↑(Real.pi/2) : Real.Angle) := by
  abel_angle

end Angles


section Distance

-- example (A B : ℂ) (h : A ≠ B) : dist A B ≠ 0 := by
--   positivity

elab "mul_abel" : tactic => return

-- example (x y : ℝ) (h₁ : x ≠ 0) (h₂ : y ≠ 0) : x^2 * y⁻¹ * x⁻¹^2 * y = 1 := by
--   mul_abel

end Distance
