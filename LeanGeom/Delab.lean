import LeanGeom.Defs
import LeanGeom.Tactics

open Lean

def delabInt (n : Int) : MetaM Term :=
  if n ≥ 0 then
    `($(Syntax.mkNatLit n.natAbs))
  else
    `(-$(Syntax.mkNatLit n.natAbs))

def delabRat (q : Rat) : MetaM Term := do
  if q.den = 1 then
    delabInt q.num
  else
    `($(← delabInt q.num) / $(Syntax.mkNatLit q.den))

def delabRatAngle (angle : RatAngle) : MetaM Term := do
  if angle = 0 then
    return Syntax.mkNatLit 0
  else
    let q ← delabRat (2 * angle.q)
    `($q * Real.pi)

def delabPoint : Point → MetaM Term
  | ⟨.fvar fvarId⟩ => return mkIdent (← fvarId.getUserName)
  | ⟨point⟩ => throwError "don't know how to delaborate {point}"

def delabRay (r : Ray) : MetaM Term := do
  let A ← delabPoint r.A
  let B ← delabPoint r.B
  `(∠ $A $B)


def delabAngleSum (angle : AngleSum) : MetaM Term := do
  if angle.sum.isEmpty then
    delabRatAngle angle.θ
  else
    let sum ← delabSum angle.sum
    if angle.θ = 0 then
      return sum
    let θ ← delabRatAngle angle.θ
    `($sum + $θ)
where
  delabSum : List (Int × Ray) → MetaM Term
  | (n, r) :: s => do
    let r ← delabRay r
    let (n, n_pos) := (n.natAbs, (n ≥ 0 : Bool))
    let r ←
      if n = 1 then
        pure r
      else
        `($(Syntax.mkNatLit n) • $r)
    if s.isEmpty then
      if n_pos then
        return r
      else
        `(-$r)
    else
      let s ← delabSum s
      if n_pos then
        `($s + $r)
      else
        `($s - $r)
  | [] => unreachable!

def delabProposition (prop : Proposition) : MetaM Term := do
  match prop with
  | .angleEqZero angle => `($(← delabAngleSum angle) = 0)
  | .angleNeqZero angle => `($(← delabAngleSum angle) ≠ 0)



structure DelabState where
  nameGen : NameGenerator := { namePrefix := `h }
  names : Std.HashMap AtomProp Ident := {}

abbrev DelabGeomM := StateT DelabState GeomM

def delabTermProof (pf : TermProof) : DelabGeomM Term := do
  match pf with
  | .app lem args =>
    let argNames : Array Term ← args.attach.mapM (fun ⟨arg, _⟩ => delabTermProof arg)
    return Syntax.mkApp (mkIdent lem) argNames
  | .proved p => return (← get).names[p]!
  | .hypothesis h => return mkIdent h
  | .negatedGoal => throwError "need to revert the goal (using `by_contra`) before using it"


def delabLinearComb : List (Int × AtomTermProof) → DelabGeomM Term
  | (n, h) :: s => do
    let (n, n_pos) := (n.natAbs, (n ≥ 0 : Bool))
    let h ← delabTermProof (← deAtomize h)
    let h ←
      if n = 1 then
        pure h
      else
        `($(Syntax.mkNatLit n) * $h)
    if s.isEmpty then
      if n_pos then
        return h
      else
        `(-$h)
    else
      let s ← delabLinearComb s
      if n_pos then
        `($s + $h)
      else
        `($s - $h)
  | [] => unreachable!

def delabTacticProof (pf : TacticProof) : DelabGeomM Syntax.Tactic := do
  match pf with
  | .angleComb comb => `(tactic| linear_combination (norm := abel_angle) $(← delabLinearComb comb):term)


def delabProofAsTerm (pf : Proof) : DelabGeomM Term := do
  match pf with
  | .term pf => delabTermProof pf
  | .tac pf => do `(by $(← delabTacticProof pf):tactic)

def delabProofAsTactic (pf : Proof) : DelabGeomM Syntax.Tactic := do
  match pf with
  | .term pf => do `(tactic| exact $(← delabTermProof pf):term)
  | .tac pf => delabTacticProof pf
