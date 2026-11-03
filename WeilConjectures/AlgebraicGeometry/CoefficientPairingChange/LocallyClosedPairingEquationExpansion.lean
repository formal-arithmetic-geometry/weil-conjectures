/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CoefficientPairingChange.InternalAdjunctionPairingChange
/-! # Expansion of the locally closed pairing equation
-/
@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry.Etale.CoefficientPairingChange
attribute [local irreducible] derivedHom derivedTensor upperStar lowerStar
attribute [local irreducible] internalAdjunction evaluationComparison
  ordinaryComparison compactComparison
/-- Expansion of the locally closed pairing equation into its categorical word.
Source: thm-coef-finite-hom, proof paragraph 4.
(blueprint: lem-coef-locally-closed-pairing-equation-expansion).
Proof: the defining equality of `PairingChangeEquation` is the displayed word; the two
differ only in the instance proofs inside `compactComparison`, so `hp` is transported
along congruence steps with proof irrelevance at those arguments. -/
theorem pairingEquation_expanded
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    {S Z X : Scheme.{u}} (φ : A →+* B) (g : Z ⟶ X) [IsClosedImmersion g]
    (j : S ⟶ Z) [IsOpenImmersion j]
    (L : DerivedCategoryModule A S) (M : DerivedCategoryModule A X)
    (b : (scalarExtension φ S).obj ((exceptional A g j).obj M) ≅
      (exceptional B g j).obj ((scalarExtension φ X).obj M))
    (hp : PairingChangeEquation φ g j L M b) :
    ordinaryComparison φ g j
        (((derivedHom (ModuleCat A) S).obj (op L)).obj ((exceptional A g j).obj M)) ≫
      (star B g j).map
        (evaluationComparison φ S L ((exceptional A g j).obj M) ≫
          ((derivedHom (ModuleCat B) S).obj
            (op ((scalarExtension φ S).obj L))).map b.hom) ≫
      internalAdjunction B g j ((scalarExtension φ S).obj L) ((scalarExtension φ X).obj M) ≫
      ((derivedHom (ModuleCat B) X).map (compactComparison φ g j L).op).app
        ((scalarExtension φ X).obj M) =
    (scalarExtension φ X).map (internalAdjunction A g j L M) ≫
      evaluationComparison φ X ((shriek A g j).obj L) M := by
  -- The equation contains abstracted instance proofs. Comparing the whole categorical
  -- word by definitional equality unfolds its maps. Instead, retain each congruence
  -- step and use proof irrelevance explicitly at the differing proof arguments.
  run_tac do
    let goal ← Lean.Elab.Tactic.getMainGoal
    goal.withContext do
      let hp ← Lean.Meta.getLocalDeclFromUserName `hp
      let some source ← Lean.Meta.unfoldDefinition? hp.type | throwError "not a definition"
      let target ← Lean.instantiateMVars (← goal.getType)
      let source ← Lean.instantiateMVars source
      let mut pending := [(source, target, false)]
      let mut proofs : Std.HashMap (Lean.Expr × Lean.Expr) Lean.Expr := {}
      let mut congruences : Std.HashMap (Lean.Expr × Nat) Lean.Meta.CongrTheorem := {}
      for _ in [:100000] do
        if pending.isEmpty then break
        let (a, b, ready) := pending.head!
        pending := pending.tail!
        let a := a.consumeMData.headBeta
        let b := b.consumeMData.headBeta
        let key := (a, b)
        if proofs.contains key then continue
        if a == b then
          proofs := proofs.insert key (← Lean.Meta.mkHEqRefl a)
        else if (← Lean.Meta.isProof a) && (← Lean.Meta.isProof b) then
          proofs := proofs.insert key (← Lean.Meta.mkAppM ``proof_irrel_heq #[a, b])
        else
          let f := a.getAppFn
          let xs := a.getAppArgs
          let ys := b.getAppArgs
          unless f == b.getAppFn && xs.size == ys.size && !xs.isEmpty do
            throwError "unsupported congruence:\n{a}\n{b}"
          if !ready then
            pending := (a, b, true) :: pending
            for x in xs, y in ys do
              pending := (x, y, false) :: pending
          else
            let congr ← match congruences[(f, xs.size)]? with
              | some congr => pure congr
              | none => Lean.Meta.mkHCongrWithArity f xs.size
            congruences := congruences.insert (f, xs.size) congr
            let mut proof := congr.proof
            for i in [:xs.size] do
              let child := (xs[i]!.consumeMData.headBeta, ys[i]!.consumeMData.headBeta)
              let some h := proofs[child]? | throwError "missing congruence proof"
              let h ← if congr.argKinds[i]! == .eq then Lean.Meta.mkEqOfHEq h else pure h
              proof := Lean.mkAppN proof #[xs[i]!, ys[i]!, h]
            proofs := proofs.insert key proof
      let key := (source.consumeMData.headBeta, target.consumeMData.headBeta)
      let some proof := proofs[key]? | throwError "congruence traversal unfinished"
      let eq ← Lean.Meta.mkEqOfHEq proof
      goal.assign (← Lean.Meta.mkAppM ``Eq.mp #[eq, hp.toExpr])

end AlgebraicGeometry.Etale.CoefficientPairingChange
