import Mathlib.Geometry.Euclidean.Angle.Sphere

open EuclideanGeometry

/-!
This file builds up the theory that is used by the `lean_geom` tactic.
-/

instance : Fact <| Module.finrank ℝ ℂ = 2 := ⟨Complex.finrank_real_complex⟩

noncomputable def RayAngle (A B : ℂ) : Real.Angle :=
  Complex.orientation.oangle (A - B) 1

noncomputable instance : Module.Oriented ℝ ℂ (Fin 2) where
  positiveOrientation := Complex.orientation

notation "∠" A:max B:max => RayAngle A B

lemma oangle_eq_rayAngle_sub {A B C : ℂ} (h₁ : A ≠ B) (h₂ : C ≠ B) : ∡ A B C = ∠ A B - ∠ C B := by
  simp only [∡ ·, EuclideanGeometry.o, positiveOrientation, RayAngle]
  rw [@Orientation.oangle_sub_right, vsub_eq_sub, vsub_eq_sub]
  · exact sub_ne_zero_of_ne h₁
  · exact sub_ne_zero_of_ne h₂
  · norm_num

variable {A B C D : ℂ} {s : Set ℂ}

private lemma collinear_iff {p₁ p₂ p₃ : ℂ} :
    Collinear ℝ ({p₁, p₂, p₃} : Set ℂ) ↔ (2 : ℤ) • ∡ p₁ p₂ p₃ = 0 := by
  rw [← oangle_eq_zero_or_eq_pi_iff_collinear, Real.Angle.two_zsmul_eq_zero_iff]

section Line

def Collinear₃ (A B C : ℂ) := Collinear ℝ {A, B, C}

lemma collinear_iff_collinear₃ : Collinear ℝ {A, B, C} ↔ Collinear₃ A B C := Iff.rfl

private lemma Collinear₃.cycle : Collinear₃ A B C ↔ Collinear₃ B C A := by
  apply iff_of_eq; unfold Collinear₃; congr 1; ext x; simp; cc

lemma Collinear₃_iff₂ (h₁ : A ≠ B) (h₃ : C ≠ B) :
    Collinear₃ A B C ↔ (2 : ℤ) • ∠ A B = (2 : ℤ) • ∠ C B := by
  rw [← sub_eq_zero, ← zsmul_sub, ← oangle_eq_rayAngle_sub h₁ h₃, ← collinear_iff]
  rfl

lemma Collinear₃_iff₃ (h₁ : B ≠ C) (h₂ : A ≠ C) :
    Collinear₃ A B C ↔ (2 : ℤ) • ∠ B C = (2 : ℤ) • ∠ A C := by
  rw [Collinear₃.cycle]
  exact Collinear₃_iff₂ h₁ h₂

lemma Collinear₃_iff₁ (h₂ : C ≠ A) (h₃ : B ≠ A) :
    Collinear₃ A B C ↔ (2 : ℤ) • ∠ C A = (2 : ℤ) • ∠ B A := by
  rw [Collinear₃.cycle]
  exact Collinear₃_iff₃ h₂ h₃

end Line

def Circline (s : Set ℂ) := EuclideanGeometry.Cospherical s ∨ Collinear ℝ s
def Circline₄ (A B C D : ℂ) := Circline {A, B, C, D}

private lemma Circline₄.cycle : Circline₄ A B C D ↔ Circline₄ A C D B := by
  apply iff_of_eq
  unfold Circline₄
  congr 2
  ext x; simp; cc

lemma concyclic₄_iff₄ (h₁₂ : A ≠ B) (h₁₃ : A ≠ C) (h₄₂ : D ≠ B) (h₄₃ : D ≠ C) :
    Circline₄ A B C D ↔ ((2 : ℤ) • ∠ A B + (2 : ℤ) • ∠ D C = (2 : ℤ) • ∠ A C + (2 : ℤ) • ∠ D B) := by
  rw [← sub_eq_sub_iff_add_eq_add, ← zsmul_sub, ← zsmul_sub,
    ← oangle_eq_rayAngle_sub h₁₂ h₄₂, ← oangle_eq_rayAngle_sub h₁₃ h₄₃]
  unfold Circline₄
  refine ⟨?_, EuclideanGeometry.cospherical_or_collinear_of_two_zsmul_oangle_eq⟩
  rintro (h | h)
  · exact h.two_zsmul_oangle_eq h₁₂.symm h₄₂.symm h₁₃.symm h₄₃.symm
  · rw [collinear_iff.mp, collinear_iff.mp]
    all_goals
      refine Collinear.subset ?_ h
      rintro _ (_ | _ | _) <;> simp [*]

lemma concyclic₄_iff₂ (h₁₃ : A ≠ C) (h₁₄ : A ≠ D) (h₃₄ : B ≠ C) (h₂₄ : B ≠ D) :
    Circline₄ A B C D ↔ ((2 : ℤ) • ∠ A C + (2 : ℤ) • ∠ B D = (2 : ℤ) • ∠ A D + (2 : ℤ) • ∠ B C) := by
  rw [Circline₄.cycle]
  exact concyclic₄_iff₄ h₁₃ h₁₄ h₃₄ h₂₄

lemma concyclic₄_iff₃ (h₁₄ : A ≠ D) (h₁₂ : A ≠ B) (h₃₄ : C ≠ D) (h₃₂ : C ≠ B) :
    Circline₄ A B C D ↔ ((2 : ℤ) • ∠ A D + (2 : ℤ) • ∠ C B = (2 : ℤ) • ∠ A B + (2 : ℤ) • ∠ C D) := by
  rw [Circline₄.cycle]
  exact concyclic₄_iff₂ h₁₄ h₁₂ h₃₄ h₃₂
