import Mathlib.Tactic.Linarith
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Data.Nat.Prime.Defs

instance : Hashable Rat where
  hash | { num, den, ..} => mixHash (hash num) (hash den)

@[ext]
structure RatAngle where
  q : Rat
  q_ge : 0 ≤ q := by norm_num
  q_lt : q < 1 := by norm_num
deriving DecidableEq, Hashable, Ord
instance : Repr RatAngle := ⟨fun r _ => s!"{r.q}τ"⟩
instance : Lean.ToMessageData RatAngle := ⟨(m!"{·.q}τ")⟩

namespace RatAngle

instance : Zero RatAngle where
  zero := { q := 0 }

instance : Inhabited RatAngle := ⟨0⟩

instance : Neg RatAngle where
  neg θ := {
    q := if θ.q = 0 then 0 else 1 - θ.q
    q_ge := by split <;> linarith [θ.2, θ.3]
    q_lt := by cases θ.2.eq_or_gt with
      | inl h => simp [h]
      | inr h => simp [h.ne', h]
  }

instance : Add RatAngle where
  add θ θ' := {
    q := let s := (θ.q + θ'.q); if s < 1 then s else s - 1
    q_ge := by dsimp; split <;> linarith [θ.2, θ'.2]
    q_lt := by dsimp; split <;> linarith [θ.3, θ'.3]
  }

theorem q_zero : (0 : RatAngle).q = 0 := rfl
theorem q_neg (θ : RatAngle) : (-θ).q = if θ.q = 0 then 0 else 1 - θ.q := rfl
theorem q_add (θ θ' : RatAngle) : (θ + θ').q = if θ.q + θ'.q < 1 then θ.q + θ'.q else θ.q + θ'.q - 1 := rfl

local macro "add_circle_tac" : tactic =>
  `(tactic| ((repeat intro ⟨_,_,_⟩); ext; simp [q_zero, q_neg, q_add]; (repeat' split) <;> linarith))

instance : AddCommGroup RatAngle where
  add_assoc := by add_circle_tac
  zero_add := by add_circle_tac
  add_zero := by add_circle_tac
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel := by add_circle_tac
  add_comm := by add_circle_tac

end RatAngle



structure PrimePow where
  prime : Nat
  exp : Rat

/-- `PrimeProd` stores the prime factors of a number, in order from smallest to largest. -/
def PrimeProd := List PrimePow
deriving Inhabited

namespace PrimeProd

instance : One PrimeProd := ⟨[]⟩

mutual

partial def ofNat (n : Nat) (hn : n ≠ 0) : PrimeProd :=
  if hn' : n = 1 then 1 else
  let p := n.minFac
  have := n.minFac_pos
  takeFactors p (n / p) 1 (Nat.div_ne_zero_iff.mpr ⟨by omega, Nat.minFac_le (by omega)⟩)

partial def takeFactors (p n acc : Nat) (hn : n ≠ 0) : PrimeProd :=
  if h : p ∣ n then
    takeFactors p (n / p) (acc + 1) (by obtain ⟨c, h⟩ := h; simp_all)
  else
    ⟨p, acc⟩ :: ofNat n hn

end

instance {n : Nat} [n.AtLeastTwo] : OfNat PrimeProd n := ⟨ofNat n (NeZero.ne n)⟩

def mul (prod prod' : PrimeProd) : PrimeProd :=
  match prod, prod' with
  | [], prod => prod
  | prod, [] => prod
  | prod@(p :: ps), prod'@(p' :: ps') =>
    match compare p.prime p'.prime with
    | .lt => p :: mul ps prod'
    | .gt => p' :: mul prod ps'
    | .eq => match p with
      | ⟨p, n⟩ =>
        let n := n - p'.exp
        if n = 0 then
          mul ps ps'
        else
          ⟨p, n⟩ :: mul ps ps'
termination_by prod.length + prod'.length

def inv (prod : PrimeProd) : PrimeProd :=
  prod.map fun ⟨p, n⟩ => ⟨p, -n⟩

def pow (prod : PrimeProd) (n : Rat) : PrimeProd :=
  if n = 0 then 1 else prod.map fun ⟨p, n'⟩ => ⟨p, n * n'⟩


instance : Mul PrimeProd := ⟨mul⟩
instance : Inv PrimeProd := ⟨inv⟩
instance : Pow PrimeProd Rat := ⟨pow⟩

end PrimeProd



def PRat := { q : Rat // 0 < q }
deriving DecidableEq, Hashable, Ord

namespace PRat

local macro "prat_tac" : tactic =>
  `(tactic| ((repeat intro ⟨_,_⟩); apply Subtype.ext))

instance : CommGroup PRat where
  one := ⟨1, by decide⟩
  inv q := ⟨q.val⁻¹, Right.inv_pos.mpr q.prop⟩
  mul q q' := ⟨q.val * q'.val, Left.mul_pos q.prop q'.prop⟩
  mul_assoc      := by prat_tac; apply Rat.mul_assoc
  one_mul        := by prat_tac; apply Rat.one_mul
  mul_one        := by prat_tac; apply Rat.mul_one
  inv_mul_cancel := by prat_tac; apply Rat.inv_mul_cancel; positivity
  mul_comm       := by prat_tac; apply Rat.mul_comm

instance : Inhabited PRat := ⟨1⟩

instance : AddCommSemigroup PRat where
  add q q' := ⟨q.val + q'.val, add_pos' q.prop q'.prop⟩
  add_assoc := by prat_tac; apply Rat.add_assoc
  add_comm  := by prat_tac; apply Rat.add_comm

end PRat



inductive ENNRat where
| prat : PRat → ENNRat
| zero : ENNRat
| infty : ENNRat
| undef : ENNRat
deriving Inhabited, DecidableEq, Hashable, Ord

namespace ENNRat

instance : One ENNRat  := ⟨prat 1⟩
instance : Zero ENNRat := ⟨zero⟩
scoped notation "∞" => infty
instance : Bot ENNRat := ⟨undef⟩

instance : Inv ENNRat where
  inv
    | ⊥ => ⊥
    | ∞ => 0
    | 0 => ∞
    | prat r => prat r⁻¹

instance : Mul ENNRat where
  mul
    | ⊥ => fun _ => ⊥
    | ∞ => fun | ⊥ | 0 => ⊥ | _ => ∞
    | 0 => fun | ⊥ | ∞ => ⊥ | _ => 0
    | .prat r => fun | .prat r' => prat (r * r') | x => x

local macro "ennrat_tac" : tactic =>
  `(tactic| ((repeat' first | rfl | rintro (-|-|-|-) | intro h; injection h); change prat _ = prat _))

instance : DivisionCommMonoid ENNRat where
  mul_assoc     := by ennrat_tac; rw [mul_assoc]
  one_mul       := by ennrat_tac; rw [one_mul]
  mul_one       := by ennrat_tac; rw [mul_one]
  inv_inv       := by ennrat_tac; rw [inv_inv]
  mul_inv_rev   := by ennrat_tac; rw [mul_inv_rev]
  inv_eq_of_mul := by ennrat_tac; rw [inv_eq_of_mul_eq_one_right (by assumption)];
  mul_comm      := by ennrat_tac; rw [mul_comm]

end ENNRat



inductive SignGroup where | pos | neg
deriving Inhabited, DecidableEq, Hashable, Ord

namespace SignGroup

instance {α} [Neg α] : SMul SignGroup α := ⟨fun | .pos => fun a => a | .neg => fun a => -a⟩

instance : One SignGroup := ⟨.pos⟩
instance : Inv SignGroup := ⟨fun s => s⟩
instance : Neg SignGroup := ⟨fun | .pos => neg | .neg => pos⟩
instance : Mul SignGroup := ⟨SMul.smul⟩

local macro "sign_tac" : tactic =>
  `(tactic| repeat first | rintro (- | -) | rfl | intro)

instance : CommGroup SignGroup where
  mul_assoc      := by sign_tac
  one_mul        := by sign_tac
  mul_one        := by sign_tac
  inv_mul_cancel := by sign_tac
  mul_comm       := by sign_tac

instance {α} [InvolutiveNeg α] : MulAction SignGroup α where
  one_smul _ := rfl
  mul_smul := by sign_tac; symm; apply neg_neg

instance {α} [SubtractionCommMonoid α] : DistribMulAction SignGroup α where
  smul_zero := by sign_tac; apply neg_zero
  smul_add  := by sign_tac; apply neg_add

end SignGroup
