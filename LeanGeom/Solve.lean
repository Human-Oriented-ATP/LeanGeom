import LeanGeom.Defs

def addDistinct (A B : Point) (pf : TermProof) : GeomM Unit := do
  let A ← atomize A
  let B ← atomize B
  modify fun s => { s with
    context.distinct := s.context.distinct.insert ⟨A, B⟩ pf |>.insert ⟨B, A⟩ (.dotApp pf `symm #[]) }

def normalizeAngle (angle : AngleSum) (pf : LSum ℤ AtomTermProof) : OptionT GeomM (LComb ℤ (Atomic Ray') RatAngle AtomTermProof) := do
  let (sum, flip) ← (StateT.run · false) <|
    angle.sum.foldlM (init := .nil) fun sum (n, { A, B }) => do
      let A ← atomize A
      let B ← atomize B
      guard ((← getThe GeomState).context.distinct.contains ⟨A, B⟩)
      if B < A then
        modify (!·)
        return sum.insert n (← atomize { A := B, B := A })
      else
        return sum.insert n (← atomize { A, B })
  let const := if flip then angle.θ + { q := 1/2 } else angle.θ
  simplifyLComb { sum, const, pf }


def addAngle (angle : AngleSum) (pf : AtomTermProof) : GeomM Unit := do
  if let some intComb ← OptionT.run <| normalizeAngle angle (.single pf) then
    if let some comb ← insertLComb intComb then
      finishProof <| .nonzeroEqZero <| comb.foldl (init := []) (fun list n pf => (n, pf) :: list)

def checkNonAngle (angle : AngleSum) (pf : AtomTermProof) : GeomM Unit := do
  if let some intComb ← OptionT.run <| normalizeAngle angle 0 then
    if let some comb := intComb.isNil then
      let p1 ← atomize (.angleNeqZero angle)
      addProof p1 (.term (← deAtomize pf))
      let p2 ← atomize (.angleEqZero angle)
      addProof p2 (.tac <| .angleComb <| comb.foldl (fun l n h => (-n, h) :: l) [])
      finishProof <| .byContra p1 p2

-- throws an exception if the problem is solved
def runSolver : GeomM Unit := do
  for (⟨A, B⟩, pf) in (← get).facts.distinct do
    addDistinct A B pf
  for (angle, pf) in (← get).facts.angles do
    addAngle angle pf
  for (angle, pf) in (← get).facts.nangles do
    checkNonAngle angle pf


def getSolution : GeomM (Option CompleteProof) :=
  try
    runSolver
    return none
  catch ex =>
    if let some pf := (← get).result then
      return pf
    else
      throw ex
