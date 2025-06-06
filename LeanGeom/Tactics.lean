import LeanGeom.LeanDefs
import Mathlib.Tactic.Abel

/-!
This file defines the tactics that are used by the `lean_geom` tactic.
-/

namespace Tactic

open Lean Elab Meta Qq

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


theorem rayAngle_swap (A B : ℂ) (h : A ≠ B) : ∠ B A = ∠ A B + π := by
  unfold RayAngle
  rw [← Orientation.oangle_neg_left _ (sub_ne_zero_of_ne h) (by norm_num), neg_sub]

open private dischargeUsingAssumption? in Simp.dischargeDefault?

def proveNe (A B : Q(ℂ)) : SimpM Q($A ≠ $B) := do
  if let some e ← dischargeUsingAssumption? q($A ≠ $B) then
    return e
  else if let some e ← dischargeUsingAssumption? q($B ≠ $A) then
    have e : Q($B ≠ $A) := e
    return q(($e).symm)
  throwError "couldn't find a proof of {q($A ≠ $B)} in the local context"

simproc_decl raySwap (RayAngle _ _) := .ofQ fun
  | 1, ~q(Real.Angle), ~q(∠ $B $A) => do
    if Expr.lt A B then
      let ne ← proveNe A B
      return .done <| .mk q(∠ $A $B + π) (some q(rayAngle_swap $A $B $ne))
    else
      return .continue


private noncomputable def AngleEquiv : Angle ≃+ AddCircle (1 : ℝ) :=
  AddCircle.equivAddCircle (2 * π) 1 (by positivity) (by positivity)

private lemma angleEquiv_inj {x y : Angle} : AngleEquiv x = AngleEquiv y → x = y := by apply AddEquiv.injective

private lemma map_angleEquiv_zero : AngleEquiv 0 = 0 := map_zero AngleEquiv
private lemma map_angleEquiv_neg (x : Angle) : AngleEquiv (-x) = -AngleEquiv x := map_neg AngleEquiv x
private lemma map_angleEquiv_nsmul (n : Nat) (x : Angle) : AngleEquiv (n • x) = n • AngleEquiv x := map_nsmul AngleEquiv n x
private lemma map_angleEquiv_add (x y : Angle) : AngleEquiv (x + y) = AngleEquiv x + AngleEquiv y := map_add AngleEquiv x y
private lemma map_angleEquiv_sub (x y : Angle) : AngleEquiv (x - y) = AngleEquiv x - AngleEquiv y := map_sub AngleEquiv x y

private lemma angleEquiv_pi : AngleEquiv π = ↑(1/2 : Real) := by
  unfold AngleEquiv Angle.coe Angle
  rw [AddCircle.equivAddCircle_apply_mk]
  simp [pi_ne_zero]

private lemma angleEquiv_mul_pi (x : ℝ) : AngleEquiv ↑(x * π) = ↑(x / 2 : Real) := by
  unfold AngleEquiv Angle.coe Angle
  rw [AddCircle.equivAddCircle_apply_mk, mul_assoc]
  simp [pi_ne_zero]
  ring_nf

private lemma angleEquiv_pi_div (x : ℝ) : AngleEquiv ↑(π / x) = ↑((2 * x)⁻¹ : Real) := by
  unfold AngleEquiv Angle.coe Angle
  rw [AddCircle.equivAddCircle_apply_mk, div_mul_eq_mul_div]
  simp [pi_ne_zero]
  ring_nf

private lemma angleEquiv_mul_pi_div (x y : ℝ) : AngleEquiv ↑(x * π / y) = ↑(x / (2 * y) : Real) := by
  unfold AngleEquiv Angle.coe Angle
  rw [AddCircle.equivAddCircle_apply_mk, mul_div_assoc, mul_assoc, div_mul_eq_mul_div]
  simp [pi_ne_zero]
  ring_nf

macro "angle_preprocess" : tactic => `(tactic| (
  refine angleEquiv_inj ?_
  simp only [
    ↓map_angleEquiv_neg, ↓map_angleEquiv_zero, ↓map_angleEquiv_add, ↓map_angleEquiv_sub, ↓map_angleEquiv_nsmul,
    ↓angleEquiv_pi, ↓angleEquiv_mul_pi, ↓angleEquiv_pi_div, ↓angleEquiv_mul_pi_div,
    ↓raySwap]))

private lemma sub_eq_zero {a b : AddCircle (1 : ℝ)} : a - b = 0 → a = b := _root_.sub_eq_zero.mp

private lemma coe_eq_zero {x : ℝ} : (∃ n : ℤ, n = x) → (x : AddCircle (1 : ℝ)) = 0 := by
  rw [AddCircle.coe_eq_zero_iff 1]
  simp

macro "abel_mod_1" : tactic => `(tactic| (
  refine sub_eq_zero ?_
  try abel_nf -recursive
  all_goals
  simp -failIfUnchanged only [← QuotientAddGroup.mk_add, ← QuotientAddGroup.mk_zsmul]
  all_goals
  refine coe_eq_zero ?_
  use ?_
  norm_num
  norm_cast
  try exact rfl))

macro "abel_angle" : tactic => `(tactic| angle_preprocess <;> abel_mod_1)

example : (↑(π/2) : Angle) = ↑((5/2) * π) := by
  abel_angle

example : (↑(π/2) : Angle) = ↑(5 * π / 2) := by
  abel_angle

variable (A B : ℂ) (h : A ≠ B)

example  : ∠ A B = ∠ B A + ↑(9 * π) := by
  abel_angle

example  : ∠ B A = ∠ B A + ↑(10 * π) := by
  abel_angle

example  : (0 : Angle) =  ↑(10 * π) := by
  abel_angle

example  : ∠ A B = ∠ A B := by
  abel_angle

example  : ∠ A B = ∠ B A - π := by
  abel_angle

end Angles


section Distance

-- example (A B : ℂ) (h : A ≠ B) : dist A B ≠ 0 := by
--   positivity

elab "mul_abel" : tactic => return

-- example (x y : ℝ) (h₁ : x ≠ 0) (h₂ : y ≠ 0) : x^2 * y⁻¹ * x⁻¹^2 * y = 1 := by
--   mul_abel

end Distance
