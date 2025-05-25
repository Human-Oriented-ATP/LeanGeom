import Mathlib.Geometry.Euclidean.Angle.Oriented.Basic

/-!
This file builds up the theory that is used by the `lean_geom` tactic.
-/

instance : Fact <| Module.finrank ℝ ℂ = 2 := ⟨Complex.finrank_real_complex⟩

noncomputable def RayAngle (A B : ℂ) : Real.Angle :=
  Complex.orientation.oangle (A - B) 1

notation "∠" A:max B:max => RayAngle A B
