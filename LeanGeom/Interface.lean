import LeanGeom.Reify
import LeanGeom.Delab
import LeanGeom.Solve

open Lean Elab.Tactic

/-- Returns all used proposition, in order, except `pos` and `neg` in `.byContra pos neg`-/
partial def collectUsedProps (pf : CompleteProof) : StateT (Std.HashSet AtomProp) GeomM (Array AtomProp) := do
  match pf with
  | .byContra p1 p2 => return (← go (← go #[] p1).pop p2).pop
  | .nonzeroEqZero comb => comb.foldlM (do goTerm · <| ← deAtomize ·.2) #[]
where
  go (props : Array AtomProp) (prop : AtomProp) : StateT (Std.HashSet AtomProp) GeomM (Array AtomProp) := do
    if (← get).contains prop then return props
    modify (·.insert prop)
    (·.push prop) <$> match ← getProof prop with
      | .term pf => goTerm props pf
      | .tac pf => goTac props pf

  goTerm (props : Array AtomProp) (pf : TermProof) : StateT (Std.HashSet AtomProp) GeomM (Array AtomProp) := do
    match pf with
    | .app _ args => args.foldlM goTerm props
    | .proved prop => go props prop
    | .hypothesis _
    | .negatedGoal => pure props

  goTac (props : Array AtomProp) (pf : TacticProof) : StateT (Std.HashSet AtomProp) GeomM (Array AtomProp) := do
    match pf with
    | .angleComb comb => comb.foldlM (do goTerm · <| ← deAtomize ·.2) props



def delabLine (prop : AtomProp) (pf : Proof) : DelabGeomM Syntax.Tactic := do
  let nameStx := mkIdent (← nextName)
  modify fun s => { s with names := s.names.insert prop nameStx }
  let propStx ← delabProposition (← deAtomize prop)
  let pfStx ← delabProofAsTerm pf
  `(tactic| have $nameStx : $propStx := $pfStx)

def TermProof.hasNegatedGoal : TermProof → Bool
  | .app _ args => args.attach.any (fun ⟨arg, _⟩ => arg.hasNegatedGoal)
  | .proved _ | .hypothesis _ => false
  | .negatedGoal => true

def TacticProof.hasNegatedGoal : TacticProof → DelabGeomM Bool
  | angleComb comb => comb.anyM fun (_, pf) => return (← deAtomize pf).hasNegatedGoal

def Proof.hasNegatedGoal : Proof → DelabGeomM Bool
  | .term pf => return pf.hasNegatedGoal
  | .tac pf => pf.hasNegatedGoal

def delabCompleteProof (proof : CompleteProof) (props : Array AtomProp) : DelabGeomM Unit := do
  for prop in props do
    addProofLine (← delabLine prop (← getProof prop))
  match proof with
  | .byContra p1 p2 =>
    let pf1 ← getProof p1
    let pf2 ← getProof p2
    if (← get).revertedGoal.isNone then
      if pf1 matches .term .negatedGoal then
        unless ← pf2.hasNegatedGoal do
          addProofLine (← delabProofAsTactic pf2)
          return
      else if pf2 matches .term .negatedGoal then
        unless ← pf1.hasNegatedGoal do
          addProofLine (← delabProofAsTactic pf1)
          return
    match pf1 with
    | .term pf =>
      let absurd ← `(tactic| absurd $(← delabTermProof pf):term)
      let exact ← delabProofAsTactic pf2
      addProofLine absurd
      addProofLine exact
    | _ =>
      let absurd_pf ← delabLine p1 pf1
      let absurd ← `(tactic| absurd $(← delabTermProof (.proved p1)):term)
      let exact ← delabProofAsTactic pf2
      addProofLine absurd_pf
      addProofLine absurd
      addProofLine exact
  | .nonzeroEqZero _ => throwError "not yet implemented"

def obtainTacticProofScript : TacticM (TSyntax ``Parser.Tactic.tacticSeq) := withMainContext do
  let goal ← getMainTarget
  let pf ← GeomM.run do
    obtainFacts goal
    let some pf ← getSolution | throwError "no solution was found"
    let props ← collectUsedProps pf |>.run' {}
    delabCompleteProof pf props |>.run
  `(tacticSeq| $[$pf]*)

elab "lean_geom" : tactic => do
  let pf ← obtainTacticProofScript
  logInfo m! "{pf}"
  evalTactic pf
  done

elab stx:"lean_geom?" : tactic => do
  let pf ← obtainTacticProofScript
  evalTactic pf
  Meta.Tactic.TryThis.addSuggestion stx {
    suggestion := .tsyntax pf,
    style? := some .success
  }

example : 0 = ((2 * 2 * Real.pi : ℝ) : Real.Angle) := by
  abel_angle

example (A B C D E F P : ℂ) (h : E ≠ P) (h : F ≠ P) (h : D ≠ P) (h : C ≠ E) (H : A ≠ E)
    (h₁ : ∠ A E - ∠ A F - ∠ P E + ∠ P F = 0)
    (h₂ : ∠ B F - ∠ B D - ∠ P F + ∠ P D = 0)
    (h₃ : ∠ C D + ∠ E C - ∠ D P + ∠ P E = 0)
    (l₁ : ∠ E A = -∠ E C) (l₂ : ∠ A F ≠ ∠ B F) :
    (∠ B D ≠ ∠ C D) := by
  lean_geom

example (A B C D E F P : ℂ)
    (h₁ : ∠ A E - ∠ A F - ∠ E P + ∠ F P = 0)
    (h₂ : ∠ B F - ∠ B D - ∠ F P + ∠ D P = 0)
    (h₃ : ∠ C D + ∠ C E - ∠ D P + ∠ E P = 0)
    (l₁ : ∠ A E = -∠ C E) (l₂ : ∠ A F = ∠ B F) :
    (∠ B D = ∠ C D) := by
  lean_geom
  -- linear_combination (norm := abel) -h₁ - h₂ - h₃ + l₁ - l₂

example (B C D : ℂ) (h : ∠ B D = ∠ C D) (g : ∠ B D ≠ ∠ C D) : False := by
  lean_geom
