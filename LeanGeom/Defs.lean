import LeanGeom.Util
import LeanGeom.LComb
import LeanGeom.Atomize

open Lean

structure Point where
  self : Expr
deriving Inhabited, BEq, Hashable
instance : ToMessageData Point := ⟨(m!"{·.1}")⟩

structure Equal (α : Type) where (lhs rhs : α)
structure NotEqual (α : Type) where (lhs rhs : α)

structure Ray where (A B : Point)
deriving Inhabited, BEq, Hashable
instance : ToMessageData Ray := ⟨fun r => m!"∠{r.A}{r.B}"⟩

structure AngleSum where
  sum : List (Int × Ray)
  θ : RatAngle
deriving Inhabited, BEq, Hashable
instance : ToMessageData AngleSum where
  toMessageData s :=
    let sum := s.sum.map fun (n, r) => m!"{n}*{r}"
    let sum := if sum.isEmpty then m!"0" else .joinSep sum " + "
    m!"{sum} + {s.θ}"

structure Segment where (A B : Point)

structure Ratio where
  prod : List (Segment × Int)
  l : PrimeProd

inductive Proposition where
| angleEqZero (angle : AngleSum)
| angleNeqZero (angle : AngleSum)
deriving Inhabited, BEq, Hashable
instance : ToMessageData Proposition where
  toMessageData
    | .angleEqZero angle => m!"{angle} = 0"
    | .angleNeqZero angle => m!"{angle} ≠ 0"

abbrev AtomProp := Atomic Proposition

local instance : Ord Lean.Name := ⟨Lean.Name.cmp⟩

inductive TermProof where
| app (lem : Name) (args : Array TermProof)
| proved (p : AtomProp)
| hypothesis (h : Name)
| negatedGoal
deriving Inhabited, BEq, Hashable

abbrev AtomTermProof := Atomic TermProof

inductive TacticProof where
| angleComb (comb : List (Int × AtomTermProof))
deriving Inhabited

inductive Proof where
| term (pf : TermProof)
| tac (pf : TacticProof)
deriving Inhabited

inductive CompleteProof where
| byContra (p1 p2 : AtomProp)
| nonzeroEqZero (comb : List (Int × AtomTermProof))


structure Facts where
  angles : Array (AngleSum × AtomTermProof) := #[]
  nangles : Array (AngleSum × AtomTermProof) := #[]
instance : ToMessageData Facts where
  toMessageData facts := m!"{facts.angles.map (·.1)}\n{facts.nangles.map (·.1)}"



structure Ray' where (A B : Atomic Point)
  deriving Inhabited, BEq, Hashable, Repr

structure SolveCtx where
  point : AtomContext Point := {}
  ray : AtomContext Ray' := {}
  angle : IntCombContext (Atomic Ray') RatAngle AtomTermProof := {}



structure GeomState where
  props : AtomContext Proposition := {}
  proofs : Std.HashMap AtomProp Proof := {}
  termProofs : AtomContext TermProof := {}
  result : Option CompleteProof := none
  facts : Facts := {}
  context : SolveCtx := {}


abbrev GeomM := StateRefT GeomState MetaM

def GeomM.run {α : Type} (x : GeomM α) : MetaM α := StateRefT'.run' x {}

instance : MonadAtom Proposition GeomM := ⟨return (← get).props, (modify fun s => { s with props := · s.props })⟩
instance : MonadAtom TermProof GeomM := ⟨return (← get).termProofs, (modify fun s => { s with termProofs := · s.termProofs })⟩

instance : MonadAtom Point GeomM := ⟨return (← get).context.point, (modify fun s => { s with context.point := · s.context.point })⟩
instance : MonadAtom Ray'  GeomM := ⟨return (← get).context.ray  , (modify fun s => { s with context.ray   := · s.context.ray   })⟩

instance : MonadIntComb (Atomic Ray') RatAngle AtomTermProof GeomM := ⟨modifyGet fun s => (s.context.angle, { s with context.angle := {} }), fun ctx => modify ({ · with context.angle := ctx })⟩

@[inline] def modifyFacts (f : Facts → Facts) : GeomM Unit :=
  modify fun s => { s with facts := f s.facts }

def addProof (prop : AtomProp) (pf : Proof) : GeomM Unit := do
  if !(← get).proofs.contains prop then
    modify fun s => { s with proofs := s.proofs.insert prop pf }

def getProof (prop : AtomProp) : GeomM Proof := do
  match (← get).proofs[prop]? with
  | some pf => return pf
  | none => throwError "proposition {← deAtomize prop} doesn't have a proof"

def finishProof {α : Type} (pf : CompleteProof) : GeomM α := do
  modify fun s => { s with result := pf }
  throwError "the problem has been solved"
