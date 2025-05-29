import Std
import Mathlib.Algebra.Notation.Defs
import Mathlib.Data.Rat.Defs

/-- keep the invariant that `a = a₁ * x + a₂ * y` and `b = b₁ * x + b₂ * y` -/
partial def Int.xgcdAux (a a₁ a₂ b b₁ b₂ : Int) (_ : b ≠ 0) : Int × Int × Int :=
  if h : a % b = 0 then
    (b, b₁, b₂)
  else
    Int.xgcdAux b b₁ b₂ (a % b) (a₁ - (a / b) * b₁) (a₂ - (a / b) * b₂) h

/-- returns `(gcd, a, b)` such that `gcd = a * x + b * y`. -/
def Int.xgcd (x y : Int) : Int × Int × Int :=
  if h : y = 0 then
    (x, 1, 0)
  else
    Int.xgcdAux x 1 0 y 0 1 h



inductive LSum (G α : Type) where
| cons : G → α → LSum G α → LSum G α
| nil : LSum G α
deriving Inhabited, BEq, Hashable

namespace LSum

attribute [local instance] ltOfOrd
variable {G H α β : Type} [Zero G] [One G] [Add G] [Neg G] [Sub G] [Mul G] [DecidableEq G] [Ord α]

def isNil : LSum G α → Bool
  | .nil => true
  | .cons .. => false

def single (a : α) : LSum G α := .cons 1 a .nil

def cons' (g : G) (a : α) (s : LSum G α) : LSum G α :=
  if g = 0 then s else .cons g a s

@[specialize]
def foldl (f : α → G → β → α) (init : α) : LSum G β → α
| .nil => init
| .cons g b s => foldl f (f init g b) s

@[specialize]
def foldlM {m : Type → Type} [Monad m] (f : α → G → β → m α) (init : α) : LSum G β → m α
| .nil => pure init
| .cons g b s => do foldlM f (← f init g b) s

@[specialize]
def forM {m : Type → Type} [Monad m] (f : G → β → m PUnit) : LSum G β → m PUnit
| .nil => pure ⟨⟩
| .cons g b s => do f g b; forM f s

instance [Repr G] [Repr α] : Repr (LSum G α) where
  reprPrec s := reprPrec (s.foldl (init := []) (fun l g a => (g, a) :: l)).reverse

-- def reprCoeffs [Repr G] (s : LSum G α) : Std.Format := repr (s.foldl (init := []) (fun l g _ => g :: l)).reverse

def reverseAux (s acc : LSum G α) : LSum G α :=
  match s with
  | .nil => acc
  | .cons g a s => reverseAux s (.cons g a acc)

def reverse (s : LSum G α) : LSum G α := reverseAux s .nil

@[specialize]
def mapAux (f : G → H) : LSum G α → LSum H α → LSum H α
  | .nil => reverse
  | .cons g a s => (mapAux f s <| .cons (f g) (a) ·)

/-- Require that `g ≠ 0 → f g ≠ 0`. -/
@[specialize]
def map (f : G → H) (s : LSum G α) : LSum H α := mapAux f s .nil

@[specialize]
partial def addWithAux (f₁ f₂ : G → G) (s₁ s₂ acc : LSum G α) : LSum G α :=
  match s₁ with
  | .nil => reverseAux acc (map f₂ s₂)
  | .cons g₁ a₁ t₁ =>
    match s₂ with
    | .nil => reverseAux acc (map f₁ s₁)
    | .cons g₂ a₂ t₂ =>
      match compare a₁ a₂ with
      | .lt => addWithAux f₁ f₂ t₁ s₂ (.cons (f₁ g₁) a₁ acc)
      | .eq => addWithAux f₁ f₂ t₁ t₂ (.cons' (f₁ g₁ + f₂ g₂) a₁ acc)
      | .gt => addWithAux f₁ f₂ s₁ t₂ (.cons (f₂ g₂) a₂ acc)

@[inline] def addWith (f₁ f₂ : G → G) (s₁ s₂ : LSum G α) : LSum G α :=
  addWithAux f₁ f₂ s₁ s₂ .nil

def insert (g : G) (a : α) (s : LSum G α) : LSum G α :=
  addWith id id (.cons g a .nil) s

instance : Zero (LSum G α) := ⟨.nil⟩

-- @[inline] instance : Neg (LSum G α) := ⟨fun a => a.map (-·)⟩
-- @[inline] instance : SMul G (LSum G α) := ⟨fun g a => a.map (g * ·)⟩
-- @[inline] instance : Add (LSum G α) := ⟨fun a b => addWith id id a b⟩
-- @[inline] instance : Sub (LSum G α) := ⟨fun a b => addWith id (-·) a b⟩

end LSum

structure LComb (G α H π : Type) where
  sum : LSum G α
  const : H
  pf : LSum G π
deriving Inhabited, Repr

namespace LComb

variable {G H α π : Type} [Zero G] [Add G] [Neg G] [Sub G] [Mul G] [DecidableEq G] [Ord α]

def isNil [Zero H] [BEq H] : LComb G α H π → Option (LSum G π)
  | { sum, const, pf } => if sum.isNil && const == 0 then some pf else none

-- def nil [Zero H] : LComb G α H := ⟨.nil, 0⟩
-- def cons (g : G) (a : α) (comb : LComb G α H) : LComb G α H :=
--   match comb with
--   | ⟨s, c⟩ => ⟨.cons g a s, c⟩

-- @[inline] instance [Neg H] : Neg (LComb G α H) := ⟨fun ⟨s, c⟩ => ⟨-s, -c⟩⟩
-- @[inline] instance [SMul G H] : SMul G (LComb G α H) := ⟨fun g ⟨s, c⟩ => ⟨g • s, g • c⟩⟩
-- @[inline] instance [Add H] : Add (LComb G α H) := ⟨fun ⟨s, c⟩ ⟨s', c'⟩ => ⟨s + s', c + c'⟩⟩
-- @[inline] instance [Sub H] : Sub (LComb G α H) := ⟨fun ⟨s, c⟩ ⟨s', c'⟩ => ⟨s - s', c - c'⟩⟩

end LComb

structure IntCombContext (α G π : Type) [BEq α] [Hashable α] where
  ctx : Std.HashMap α (Int × LComb Int α G π) := {}
deriving Inhabited

namespace IntCombContext

variable {G α π} [Add G] [Sub G] [SMul Int G] [BEq α] [Hashable α] [Ord α] [Ord π]

/-
TODO: refactor the code so that the `IntCombContext` isn't modified by `simplifyAux`,
but instead implement a separate procedure to simplify the `IntCombContext` itself.
-/

partial def simplifyAux (sum : LSum Int α) (g : G) (pf : LSum Int π) (acc : LSum Int α) : StateM (IntCombContext α G π) (LComb Int α G π) := do
  match sum with
  | .nil => return ⟨acc.reverse, g, pf⟩
  | .cons n a sum =>
    let ⟨ctx⟩ ← get
    match ctx[a]? with
    | none => simplifyAux sum g pf (.cons n a acc)
    | some (a_n, ⟨a_sum, a_g, a_pf⟩) =>
      modify fun ⟨ctx⟩ => ⟨ctx.erase a⟩
      let a_new@⟨a_sum, a_g, a_pf⟩ ← simplifyAux a_sum a_g a_pf .nil
      modify fun ⟨ctx⟩ => ⟨ctx.insert a (a_n, a_new)⟩

      let div := n / a_n
      if div = 0 then
        simplifyAux sum g pf (.cons n a acc)
      else
        let m := -div
        simplifyAux (.addWith id (m * ·) sum a_sum) (g + m • a_g) (.addWith id (m * ·) pf a_pf) (.cons' (n % a_n) a acc)

def simplify (sum : LSum Int α) (g : G) (pf : LSum Int π) : StateM (IntCombContext α G π) (LComb Int α G π) :=
  simplifyAux sum g pf .nil

variable [Zero G] [BEq G]

partial def insert (comb : LComb Int α G π) : StateM (IntCombContext α G π) (Option (LSum Int π)) := do
  match comb with
  | ⟨.nil, g, pf⟩ => if g == 0 then return none else return pf
  | ⟨.cons n a sum, g, pf⟩ =>
    let ⟨ctx⟩ ← get
    match ctx[a]? with
    | none =>
      let red ← simplify sum g pf
      modify fun ⟨ctx⟩ => ⟨ctx.insert a (n, red)⟩
      return none
    | some (a_n, ⟨a_sum, a_g, a_pf⟩) =>
      if n % a_n = 0 then
        let m := -n / a_n
        insert ⟨.addWith id (m * ·) sum a_sum, g + m • a_g, .addWith id (m * ·) pf a_pf⟩
      else
        modify fun ⟨ctx⟩ => ⟨ctx.erase a⟩
        let (gcd, x, y) := Int.xgcd n a_n
        let red ← simplify (.addWith (x * ·) (y * ·) sum a_sum) (x • g + y • a_g) (.addWith (x * ·) (y * ·) pf a_pf)
        modify fun ⟨ctx⟩ => ⟨ctx.insert a (gcd, red)⟩
        let m := -n / gcd
        insert ⟨.addWith id (m * ·) sum red.sum, g + m • red.const, .addWith id (m * ·) pf red.pf⟩

end IntCombContext

class MonadIntComb (α G π : Type) [BEq α] [Hashable α] (m : Type → Type) where
  take : m (IntCombContext α G π)
  set : IntCombContext α G π → m Unit

instance {α G π m n} [BEq α] [Hashable α] [MonadIntComb α G π m] [lift : MonadLift m n] : MonadIntComb α G π n where
  take := lift.monadLift MonadIntComb.take
  set s := lift.monadLift (MonadIntComb.set s)

structure RatCombContext (α G π : Type) [BEq α] [Hashable α] where
  ctx : Std.HashMap α (LComb Rat α G π) := {}
deriving Inhabited

namespace RatCombContext

variable {G α π} [Add G] [Sub G] [SMul Rat G] [BEq α] [Hashable α] [Ord α] [Ord π]

partial def simplifyAux (sum : LSum Rat α) (g : G) (pf : LSum Rat π) (acc : LSum Rat α) : StateM (RatCombContext α G π) (LComb Rat α G π) := do
  match sum with
  | .nil => return ⟨acc.reverse, g, pf⟩
  | .cons n a sum =>
    let ⟨ctx⟩ ← get
    match ctx[a]? with
    | none => simplifyAux sum g pf (.cons n a acc)
    | some ⟨a_sum, a_g, a_pf⟩ =>
      modify fun ⟨ctx⟩ => ⟨ctx.erase a⟩
      let a_new@⟨a_sum, a_g, a_pf⟩ ← simplifyAux a_sum a_g a_pf .nil
      modify fun ⟨ctx⟩ => ⟨ctx.insert a a_new⟩
      let m := -n
      simplifyAux (.addWith id (m * ·) sum a_sum) (g + m • a_g) (.addWith id (m * ·) pf a_pf) acc

def simplify (sum : LSum Rat α) (g : G) (pf : LSum Rat π) : StateM (RatCombContext α G π) (LComb Rat α G π) :=
  simplifyAux sum g pf .nil

variable [Zero G] [BEq G]

partial def insert (comb : LComb Rat α G π) : StateM (RatCombContext α G π) (Option (LSum Rat π)) := do
  match comb with
  | ⟨.nil, g, pf⟩ => if g == 0 then return none else return pf
  | ⟨.cons n a sum, g, pf⟩ =>
    let sum := sum.map (n⁻¹ * ·)
    let g := n⁻¹ • g
    let pf := pf.map (n⁻¹ * ·)
    let ⟨ctx⟩ ← get
    match ctx[a]? with
    | none =>
      let red ← simplify sum g pf
      modify fun ⟨ctx⟩ => ⟨ctx.insert a red⟩
      return none
    | some ⟨a_sum, a_g, a_pf⟩ =>
      insert ⟨.addWith id (-·) sum a_sum, g - a_g, .addWith id (-·) pf a_pf⟩

end RatCombContext

class MonadRatComb (α G π : Type) [BEq α] [Hashable α] (m : Type → Type) where
  take : m (RatCombContext α G π)
  set : RatCombContext α G π → m Unit

class MonadLComb (G α H π : Type) (m : Type → Type) where
  simplifyLComb : LComb G α H π → m (LComb G α H π)
  insertLComb : LComb G α H π → m (Option (LSum G π))

export MonadLComb (simplifyLComb insertLComb)

@[inline] instance {α G π m} [BEq α] [Ord α] [Hashable α] [Zero G] [Add G] [Sub G] [SMul Rat G] [BEq G] [Ord π] [Monad m] [MonadRatComb α G π m] : MonadLComb Rat α G π m where
  simplifyLComb l := do
    let ctx ← MonadRatComb.take
    let (l, ctx) := RatCombContext.simplify l.sum l.const l.pf |>.run ctx
    MonadRatComb.set ctx
    return l
  insertLComb l := do
    let ctx ← MonadRatComb.take
    let (pf?, ctx) := RatCombContext.insert l |>.run ctx
    MonadRatComb.set ctx
    return pf?

@[inline] instance {α G π m} [BEq α] [Ord α] [Hashable α] [Zero G] [Add G] [Sub G] [SMul Int G] [BEq G] [Ord π] [Monad m] [MonadIntComb α G π m] : MonadLComb Int α G π m where
  simplifyLComb l := do
    let ctx ← MonadIntComb.take
    let (l, ctx) := IntCombContext.simplify l.sum l.const l.pf |>.run ctx
    MonadIntComb.set ctx
    return l
  insertLComb l := do
    let ctx ← MonadIntComb.take
    let (pf?, ctx) := IntCombContext.insert l |>.run ctx
    MonadIntComb.set ctx
    return pf?
