import LeanGeom.Defs

open Lean

def normalizeAngle (angle : AngleSum) (pf : LSum ℤ AtomTermProof) : GeomM (LComb ℤ (Atomic Ray') RatAngle AtomTermProof) := do
  let lcomb : LComb ℤ (Atomic Ray') RatAngle AtomTermProof := {
    sum := ← angle.sum.foldlM (init := .nil) fun sum (n, { A, B }) => do
      let ray ← atomize { A := ← atomize A, B := ← atomize B }
      return sum.insert n ray
    const := angle.θ
    pf }
  simplifyLComb lcomb


def addAngle (angle : AngleSum) (pf : AtomTermProof) : GeomM Unit := do
  let intComb ← normalizeAngle angle (.single pf)
  if let some comb ← insertLComb intComb then
    finishProof <| .nonzeroEqZero <| comb.foldl (init := []) (fun list n pf => (n, pf) :: list)

def checkNonAngle (angle : AngleSum) (pf : AtomTermProof) : GeomM Unit := do
  let intComb ← normalizeAngle angle 0
  if let some comb := intComb.isNil then
    let p1 ← atomize (.angleNeqZero angle)
    addProof p1 (.term (← deAtomize pf))
    let p2 ← atomize (.angleEqZero angle)
    addProof p2 (.tac <| .angleComb <| comb.foldl (fun l n h => (-n, h) :: l) [])
    finishProof <| .byContra p1 p2

-- throws an exception if the problem is solved
def runSolver : GeomM Unit := do
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
