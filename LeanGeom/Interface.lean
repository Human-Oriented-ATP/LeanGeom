import LeanGeom.Reify
import LeanGeom.Delab
import LeanGeom.AngleArith

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


partial def nextName : DelabGeomM Name := do
    let { nameGen, .. } ← get
    modify ({ · with nameGen := nameGen.next })
    let name := match nameGen.namePrefix with
      | .str p s => Name.mkStr p (s ++ "_" ++ toString nameGen.idx)
      | n       => Name.mkStr n ("_" ++ toString nameGen.idx)
    if (← getLCtx).findFromUserName? name |>.isSome then
      nextName
    else if (← getEnv).find? name |>.isSome then
      nextName
    else
      return name

def delabLine (prop : AtomProp) (pf : Proof) : DelabGeomM Syntax.Tactic := do
  let nameStx := mkIdent (← nextName)
  modify fun s => { s with names := s.names.insert prop nameStx }
  let propStx ← delabProposition (← deAtomize prop)
  let pfStx ← delabProofAsTerm pf
  `(tactic| have $nameStx : $propStx := $pfStx)



def delabCompleteProof (proof : CompleteProof) (props : Array AtomProp) : DelabGeomM (Array Syntax.Tactic) := do
  let mut lines := #[]
  let mut revertedGoal : Option Name := none
  for prop in props do
    let pf ← getProof prop
    let pf ←
      if pf matches .term .negatedGoal then
        if let some h := revertedGoal then
          pure (.term <| .hypothesis h)
        else
          let h ← nextName
          lines := lines.push (← `(tactic| by_contra $(mkIdent h):ident))
          pure (.term <| .hypothesis h)
      else
        pure pf
    lines := lines.push (← delabLine prop pf)
  match proof with
  | .byContra p1 p2 =>
    let pf1 ← getProof p1
    let pf2 ← getProof p2
    if revertedGoal.isNone then
      if pf1 matches .term .negatedGoal then
        return lines.push (← delabProofAsTactic pf2)
      else if pf2 matches .term .negatedGoal then
        return lines.push (← delabProofAsTactic pf1)
    match pf1 with
    | .term pf => lines := lines.push (← `(tactic| absurd $(← delabTermProof pf):term))
    | _ =>
      lines := lines.push (← delabLine p1 pf1)
      lines := lines.push (← `(tactic| absurd $(← delabTermProof (.proved p1)):term))
    return lines.push (← delabProofAsTactic pf2)
  | .nonzeroEqZero _ => throwError "not yet implemented"


elab "lean_geom" : tactic => withMainContext do
  let goal ← getMainTarget
  let pf ← GeomM.run do
    obtainFacts goal
    let some pf ← getSolution | throwError "no solution was found"
    let props ← collectUsedProps pf |>.run' {}
    delabCompleteProof pf props |>.run' {}
  let pf ← `(tacticSeq| $[$pf]*)
  logInfo m! "{pf}"
  Elab.Tactic.evalTactic pf

example : 0 = ((2 * 2 * Real.pi : ℝ) : Real.Angle) := by
  abel_angle

example (A B C D E F P : ℂ)
    (h₁ : ∠ A E - ∠ A F - ∠ P E + ∠ P F = 0)
    (h₂ : ∠ B F - ∠ B D - ∠ P F + ∠ P D = 0)
    (h₃ : ∠ C D + ∠ C E - ∠ P D + ∠ P E = 0)
    (l₁ : ∠ A E = -∠ C E) (l₂ : ∠ A F = ∠ B F) :
    (∠ B D = ∠ C D) := by
  lean_geom
  -- have h_1 : ∠ B D = ∠ C D := by linear_combination (norm := abel) -h₁ - h₂ - h₃ + l₁ - l₂
  -- absurd nl₃
  -- exact h_1

example (B C D : ℂ) (h : ∠ B D = ∠ C D) (g : ∠ B D ≠ ∠ C D) : False := by
  lean_geom
