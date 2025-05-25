import Std.Data.HashMap.Basic
import Lean.Exception

structure Atomic (α : Type) where
  id : Nat
deriving Inhabited
instance {α}: Repr (Atomic α) := ⟨fun ⟨id⟩ _ => s!"⟨{id}⟩"⟩

variable {α : Type} [BEq α] [Hashable α]

instance : BEq (Atomic α) := ⟨(·.1 = ·.1)⟩
instance : LT (Atomic α) := ⟨(·.1 < ·.1)⟩
instance : LE (Atomic α) := ⟨(·.1 ≤ ·.1)⟩
instance : Ord (Atomic α) := ⟨(compare ·.1 ·.1)⟩
instance : Hashable (Atomic α) := ⟨(hash ·.1)⟩

structure AtomContext (α : Type) [BEq α] [Hashable α] where
  encode : Std.HashMap α (Atomic α) := {}
  decode : Array α := #[]
deriving Inhabited

class MonadAtom (α : Type) [BEq α] [Hashable α] (m : Type → Type) where
  get (α) : m (AtomContext α)
  modify (α) : (AtomContext α → AtomContext α) → m Unit

instance {α m n} [BEq α] [Hashable α] [MonadAtom α m] [lift : MonadLift m n] : MonadAtom α n where
  get := lift.monadLift <| MonadAtom.get α
  modify f := lift.monadLift <| MonadAtom.modify α f

variable {m} [Monad m] [MonadAtom α m]

@[specialize] def atomize (val : α) : m (Atomic α) := do
  let { encode, .. } ← MonadAtom.get α
  match encode[val]? with
  | some atom => return atom
  | none =>
    let atom := ⟨encode.size⟩
    MonadAtom.modify α fun { encode, decode } => { encode := encode.insert val atom, decode := decode.push val }
    return atom

@[specialize] def deAtomize [Lean.MonadError m] (val : Atomic α) : m α := do
  let { decode, .. } ← MonadAtom.get α
  match decode[val.id]? with
  | some a => return a
  | none => throwError "couldn't find atom in context"
