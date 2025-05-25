import LeanGeom.Util

namespace LeanGeom

local instance : Ord Lean.Name := ⟨Lean.Name.cmp⟩

inductive Point where
| free (p : Lean.Name)
deriving Inhabited, DecidableEq, Hashable, Ord

-- `Angle` lives in `(ℝ/2πℤ) ∪ ⊥`
inductive Angle where
| ray (A B : Point)
| const (θ : RatAngle)
| smul (n : Int) (a : Angle)
| add (a₁ a₂ : Angle)
| free (θ : Lean.Name)
deriving Inhabited, DecidableEq, Hashable, Ord

instance : Zero Angle := ⟨.const 0⟩
instance : Add Angle := ⟨.add⟩
instance : SMul Int Angle := ⟨.smul⟩
instance : Neg Angle := ⟨fun a => -1 • a⟩
instance : Sub Angle := ⟨fun a₁ a₂ => a₁ + -a₂⟩

scoped notation:max "∠" A:max B:max C:max => (2 : ℤ) • Angle.ray A B - (2 : ℤ) • Angle.ray B C

-- `Length` lives in `ℝ`
inductive Length where
| segment (A B : Point)
-- TODO: improve so that we can have roots of rational numbers directly
| const (q : Rat)
| add (l₁ l₂ : Length)
| mul (l₁ l₂ : Length)
| pow (l : Length) (n : Rat)
| free (l : Lean.Name)
deriving Inhabited, DecidableEq, Hashable, Ord

instance : Zero Length := ⟨.const 0⟩
instance : Add Length := ⟨.add⟩
-- instance : SMul Rat Length := ⟨.smul⟩
-- instance : Neg Length := ⟨fun l => (-1 : Rat) • l⟩
-- instance : Sub Length := ⟨fun l₁ l₂ => l₁ + -l₂⟩

instance : One Length := ⟨.const 1⟩
instance : Mul Length := ⟨.mul⟩
instance : Pow Length Rat := ⟨.pow⟩
instance : Inv Length := ⟨fun l => l ^ (-1 : Rat)⟩
instance : Div Length := ⟨fun l₁ l₂ => l₁ * l₂⁻¹⟩

scoped macro:max atomic("|" noWs) A:term:max B:term:max noWs "|" : term => `(Length.segment $A $B)

-- -- `PosLength` lives in `ℝ>0`
-- inductive PosLength where
-- | pos (l : Length)
-- -- const and segment are obtained via `pos`.
-- -- add is not relevant.
-- | mul (l₁ l₂ : PosLength)
-- | pow (l : PosLength) (n : Rat)
-- deriving Inhabited, DecidableEq, Hashable, Ord

-- instance : Mul PosLength := ⟨.mul⟩
-- instance : Pow PosLength Rat := ⟨.pow⟩
-- instance : Inv PosLength := ⟨fun l => l ^ (-1 : Rat)⟩
-- instance : Div PosLength := ⟨fun l₁ l₂ => l₁ * l₂⁻¹⟩
-- scoped macro:max atomic("|" noWs) A:term:max B:term:max noWs "|₊" : term => `(PosLenght.pos (Length.segment $A $B))


structure Triangle where
  A : Point
  B : Point
  C : Point
deriving Inhabited, DecidableEq, Hashable, Ord

scoped notation:max "△" A:max B:max C:max => Triangle.mk A B C

mutual

inductive PointEq : Point → Point → Type where
| refl (A) : PointEq A A
| symm {A B} : PointEq A B → PointEq B A
| trans {A B C} : PointEq A B → PointEq B C → PointEq A C
| given {A B} : Lean.Name → PointEq A B

inductive PointNe : Point → Point → Type where
| symm {A B} : PointNe A B → PointNe B A
| congr {A B A' B'} : PointEq A A' → PointEq B B' → PointNe A B → PointNe A' B'
| given {A B} : Lean.Name → PointNe A B

-- `AngleEq a b` defaults to `True` in the case that `a` is `⊥`
inductive AngleEq : Angle → Angle → Type where
| refl (a) : AngleEq a a
| symm {a b} : AngleEq a b → AngleEq b a
| trans {a b c} : AngleEq a b → AngleEq b c → AngleEq a c
| add_const {θ₁ θ₂} : AngleEq (.const θ₁ + .const θ₂) (.const (θ₁ + θ₂))
| smul_const {n : Int} {θ} : AngleEq (n • .const θ) (.const (n • θ))
| add_smul {n₁ n₂ : Int} {a} : AngleEq (n₁ • a + n₂ • a) ((n₁ + n₂) • a)
-- | smul_add {n : Int} {a b} : AngleEq (n • (a + b)) (n • a + n • b)
-- | smul_zero {n : Int} : AngleEq (n • 0) 0
| zero_smul {a} : AngleEq ((0 : Int) • a) 0
| zero_add {a} : AngleEq (0 + a) a
| assoc₁ {a as₁ as₂} : AngleEq ((a + as₁) + as₂) (a + (as₁ + as₂))
| assoc₂ {a as₁ as₂} : AngleEq (as₁ + (a + as₂)) (a + (as₁ + as₂))
| smul_congr {a b} {n : Int} : AngleEq a b → AngleEq (n • a) (n • b)
| add_congr {a₁ a₂ b₁ b₂} : AngleEq a₁ b₁ → AngleEq a₂ b₂ → AngleEq (a₁ + a₂) (b₁ + b₂)

| ray {A B} : AngleEq (.ray A B) (.ray B A + .const ⟨1/2, _, _⟩)
| ray' {A B} : AngleEq ((2 : Int) • .ray A B) ((2 : Int) • .ray B A)
| coll {A B C} : Coll [A,B,C] → AngleEq (.ray A B) (.ray B C)
| similar {A B C A₂ B₂ C₂ s} : Similar △A B C △A₂ B₂ C₂ s → AngleEq ∠A B C (s • ∠A₂ B₂ C₂)
| given {a θ} : Lean.Name → AngleEq a θ

inductive AngleNe : Angle → Angle → Type where
| irrefl {θ₁ θ₂} : θ₁ ≠ θ₂ → AngleNe (.const θ₁) (.const θ₂)
| symm {a b} : AngleNe a b → AngleNe b a
| congr {a₁ b₁ a₂ b₂} : AngleNe a₁ b₁ → AngleEq a₁ a₂ → AngleEq b₁ b₂ → AngleNe a₂ b₂

-- | smul_congr {a θ} {n : Int} : AngleNe (n • a) (n • θ) → AngleNe a θ
-- | add_congr {a₁ a₂ b₁ b₂} : AngleEq a₁ b₁ → AngleNe a₂ b₂ → AngleNe (a₁ + a₂) (b₁ + b₂)

| ncoll {A B C} : NColl [A,B,C] → AngleNe (∠A B C) 0
| given {a θ} : Lean.Name → AngleNe a θ


inductive LengthEq : Length → Length → Type where
| refl (l) : LengthEq l l
| symm (k l) : LengthEq k l → LengthEq l k
| trans (k l m) : LengthEq k l → LengthEq l m → LengthEq k m

| add_const {r₁ r₂} : LengthEq (.const r₁ + .const r₂) (.const (r₁ + r₂))
| add_smul {n₁ n₂ : Rat} {l} : LengthEq (.const n₁ * l + .const n₂ * l) ((.const (n₁ + n₂)) * l)
| zero_mul {l} : LengthEq (0 * l) 0
| zero_add {l} : LengthEq (0 + l) l
| add_assoc₁ {l ls₁ ls₂} : LengthEq ((l + ls₁) + ls₂) (l + (ls₁ + ls₂))
| add_assoc₂ {l ls₁ ls₂} : LengthEq (ls₁ + (l + ls₂)) (l + (ls₁ + ls₂))
| add_congr {k₁ k₂ l₁ l₂} : LengthEq k₁ l₁ → LengthEq k₂ l₂ → LengthEq (k₁ + k₂) (l₁ + l₂)

| mul_const {r₁ r₂} : LengthEq (.const r₁ * .const r₂) (.const (r₁ * r₂))
| const_pow {n : Int} {r} : LengthEq (.const r ^ (n : Rat)) (.const (r ^ n)) -- TODO: expand from `Rat` in `.const`.
| mul_pow {n₁ n₂ : Rat} {l} : LengthNe l 0 → LengthEq (l ^ n₁ * l ^ n₂) (l ^ (n₁ + n₂))
| pow_zero {l} : LengthNe l 0 → LengthEq (l ^ (0 : Rat)) 1
| one_mul {l} : LengthEq (1 * l) l
| mul_assoc₁ {l ls₁ ls₂} : LengthEq ((l * ls₁) * ls₂) (l * (ls₁ * ls₂))
| mul_assoc₂ {l ls₁ ls₂} : LengthEq (ls₁ * (l * ls₂)) (l * (ls₁ * ls₂))
| pow_congr {k l} {r : Rat} : LengthEq k l → LengthEq (k ^ r) (l ^ r)
| mul_congr {k₁ k₂ l₁ l₂} : LengthEq k₁ l₁ → LengthEq k₂ l₂ → LengthEq (k₁ * k₂) (l₁ * l₂)

| similar {A B C A₂ B₂ C₂ s} : Similar △A B C △A₂ B₂ C₂ s → LengthEq (|A B|/|B C|) (|A₂ B₂|/|B₂ C₂|)
| given {l r} : Lean.Name → LengthEq l r

inductive LengthNe : Length → Length → Type where
| irrefl {r₁ r₂} : r₁ ≠ r₂ → LengthNe (.const r₁) (.const r₂)
| symm {a b} : LengthNe a b → LengthNe b a
| congr {a₁ b₁ a₂ b₂} : LengthNe a₁ b₁ → LengthEq a₁ a₂ → LengthEq b₁ b₂ → LengthNe a₂ b₂

| segment {A B} : PointNe A B → LengthNe |A B| 0

-- | smul_congr {k l} {r : Rat} : LengthNe (.const r * k) (.const r * l) → LengthNe k l
-- | add_congr {k₁ k₂ l₁ l₂} : LengthEq k₁ l₁ → LengthNe k₂ l₂ → LengthNe (k₁ + k₂) (l₁ + l₂)
-- | pow_congr {k l} {r : Rat} : LengthNe (k ^ r) (l ^ r) → LengthNe k l
-- | mul_congr {k₁ k₂ l₁ l₂} : LengthEq k₁ l₁ → LengthNe k₂ l₂ → LengthNe (k₁ * k₂) (l₁ * l₂)

| given {a θ} : Lean.Name → LengthNe a θ


-- TODO: LengthLe ?

inductive Similar : (T₁ T₂ : Triangle) → SignGroup → Type where
| swap₁ {A B C A₂ B₂ C₂ s} : Similar △A B C △A₂ B₂ C₂ s → Similar △B A C △B₂ A₂ C₂ s
| swap₂ {A B C A₂ B₂ C₂ s} : Similar △A B C △A₂ B₂ C₂ s → Similar △C B A △C₂ B₂ A₂ s
| swap₃ {A B C A₂ B₂ C₂ s} : Similar △A B C △A₂ B₂ C₂ s → Similar △A C B △A₂ C₂ B₂ s
| swap₄ {A B C A₂ B₂ C₂ s} : Similar △A B C △A₂ B₂ C₂ s → Similar △B C A △B₂ C₂ A₂ s
| swap₅ {A B C A₂ B₂ C₂ s} : Similar △A B C △A₂ B₂ C₂ s → Similar △C A B △C₂ A₂ B₂ s
| refl (T) {s} : Similar T T s
| symm {T₁ T₂ s} : Similar T₁ T₂ s → Similar T₂ T₁ s
| trans {T₁ T₂ T₃ s₁ s₂} : Similar T₁ T₂ s₁ → Similar T₂ T₃ s₂ → Similar T₁ T₃ (s₁ * s₂)
| aa  {A B C A₂ B₂ C₂ s} : AngleEq ∠A B C (s • ∠A₂ B₂ C₂) → AngleEq ∠C A B (s • ∠C₂ A₂ B₂) → NColl [A,B,C] → Similar △A B C △A₂ B₂ C₂ s
| sas {A B C A₂ B₂ C₂ s} : AngleEq ∠A B C (s • ∠A₂ B₂ C₂) → LengthEq (|A B|/|B C|) (|A₂ B₂|/|B₂ C₂|) → Similar △A B C △A₂ B₂ C₂ s

inductive Coll : List Point → Type where
-- | two {A B} : Coll [A,B]
| subset {l₁ l₂} : l₂ ⊆ l₁ → Coll l₁ → Coll l₂
| para {A B C} : AngleEq (∠A B C) 0 → Coll [A, B, C]
| given {l} : Lean.Name → Coll l

inductive NColl : List Point → Type where
| para {A B C} : AngleNe (∠A B C) 0 → NColl [A, B, C]
| subset {l₁ l₂} : l₁ ⊆ l₂ → NColl l₁ → NColl l₂
| given {l} : Lean.Name → NColl l


inductive Cyclic : List Point → Type where
-- | three {A B C} : Cyclic [A,B,C]
| subset {l₁ l₂} : l₂ ⊆ l₁ → Cyclic l₁ → Cyclic l₂
| quad {A B C D} : AngleEq (∠A B D - ∠ A C D) 0 → Cyclic [A,B,C,D]

end

inductive Proposition where
| pointEq : Point → Point → Proposition
| pointNe : Point → Point → Proposition
| angleEq : Angle → Angle → Proposition
| angleNe : Angle → Angle → Proposition
| lengthEq : Length → Length → Proposition
| lengthNe : Length → Length → Proposition
| similar : Triangle → Triangle → SignGroup → Proposition
| coll : List Point → Proposition
| ncoll : List Point → Proposition
| cyclic : List Point → Proposition
deriving Inhabited, DecidableEq, Hashable, Ord

inductive Proof : Proposition → Type where
| pointEq {A B} : PointEq A B → Proof (.pointEq A B)
| pointNe {A B} : PointNe A B → Proof (.pointNe A B)
| angleEq {a b} : AngleEq a b → Proof (.angleEq a b)
| angleNe {a b} : AngleNe a b → Proof (.angleNe a b)
| lengthEq {a b} : LengthEq a b → Proof (.lengthEq a b)
| lengthNe {a b} : LengthNe a b → Proof (.lengthNe a b)
| similar {T₁ T₂ s} : Similar T₁ T₂ s → Proof (.similar T₁ T₂ s)
| coll {l} : Coll l → Proof (.coll l)
| ncoll {l} : NColl l → Proof (.ncoll l)
| cyclic {l} : Cyclic l → Proof (.cyclic l)


class ProofClass (p : Proposition) where
  pf : Proof p


-- inductive Angle : (L : List (Int × Angle)) → (θ : RatAngle) → Type where
-- | perm {l₁ l₂ θ} : l₁.Perm l₂ → Angle l₁ θ → Angle l₂ θ
-- | nil : Angle [] 0
-- | append {l₁ l₂ θ₁ θ₂} : Angle l₁ θ₁ → Angle l₂ θ₂ → Angle (l₁ ++ l₂) (θ₁ + θ₂)
-- | zero {a} : Angle [(0, a)] 0
-- | add {n₁ n₂ a} : Angle [(n₁, a), (n₂, a), (-(n₁ + n₂), a)] 0
-- | smul {l θ} (n : Int) : Angle l θ → Angle (l.map fun x => (n * x.1, x.2)) (n • θ)
