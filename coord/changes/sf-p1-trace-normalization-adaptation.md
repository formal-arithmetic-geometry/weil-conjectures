# AlgebraicGeometry.Etale.exists_presentedFiniteP1TraceNormalization

## Reason

Forced adaptation of Sheaf.SixFunctors.ProjectiveLineTraceNormalization (unclaimed).
Reviewer C-1473a at returned head 1473a6fb3 reported that the original module compiles
on main but fails against this packet's new trace body: traceProofCongruence unfolds
trace, reaches traceComposite, and reports "non-proof disagreement". A concrete
trace-equality bridge also exceeded the kernel's deterministic limit during review.

Keep the constructed trace body. Recognize its polymorphic composition in the private
structural congruence tactic, and first regroup the raw formula using the proved
presentationTrace_assoc equation. This changes only a private tactic whitelist and
the public theorem's proof. Public signatures, attributes, visibility, imports and
docstrings stay identical. No target or definition is weakened; no hole is added.

## Old

The private unfolding whitelist has trace followed immediately by
ordinaryFiniteTwistedPullback, with no traceComposite entry.

```lean
theorem exists_presentedFiniteP1TraceNormalization
    (A : Type (u + 1)) [CommRing A] [Finite A] (N : ℕ) (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    {X Y : Scheme.{u}} (q : X ⟶ Y) [IsProper q]
    (e : X ≅ ProjectiveLine Y) (w : e.hom ≫ (ProjectiveLine Y ↘ Y) = q)
    (hY : IsUnit (N : Γ(Y, ⊤))) (d : ArbitraryBaseFiniteP1Splitting A N hA t Y hY) :
    ∃ a : (ordinaryFiniteLine A N hA X)⟦(2 : ℤ)⟧ ≅
        (ordinaryFiniteLine A N hA X)⟦(2 : ℤ)⟧,
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) q).map a.hom ≫
          SfP1Transport.trace A N hA t q e w hY d.trace =
        (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} A) q).hom.app
          ((ordinaryFiniteLine A N hA X)⟦(2 : ℤ)⟧) ≫
          presentedFiniteP1Trace A N hA t q e w hY d ≫
          (singleFunctorObjUnitIso (ModuleCat.{u + 1} A) Y).hom := by
  obtain ⟨a, ha⟩ := exists_presentedFiniteP1RawAdjustment A N hA t q e w hY d
  refine ⟨a, ?_⟩
  conv_rhs =>
    arg 2
    arg 2
    rewrite [← constantUnit_eq]
  run_tac
    let g ← Lean.Elab.Tactic.getMainGoal
    g.withContext do
      let h := (← Lean.Meta.getLocalDeclFromUserName `ha).toExpr
      let lhs ← Lean.Meta.inferType h
      let rhs ← g.getType
      let heq ← traceProofCongruence 150 lhs rhs
      let eq ← Lean.Meta.mkAppM ``eq_of_heq #[heq]
      g.assign (← Lean.Meta.mkAppM ``Eq.mp #[eq, h])
    Lean.Elab.Tactic.replaceMainGoal []
```

## New

The private unfolding whitelist additionally contains `SfP1Transport.traceComposite`.

```lean
theorem exists_presentedFiniteP1TraceNormalization
    (A : Type (u + 1)) [CommRing A] [Finite A] (N : ℕ) (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    {X Y : Scheme.{u}} (q : X ⟶ Y) [IsProper q]
    (e : X ≅ ProjectiveLine Y) (w : e.hom ≫ (ProjectiveLine Y ↘ Y) = q)
    (hY : IsUnit (N : Γ(Y, ⊤))) (d : ArbitraryBaseFiniteP1Splitting A N hA t Y hY) :
    ∃ a : (ordinaryFiniteLine A N hA X)⟦(2 : ℤ)⟧ ≅
        (ordinaryFiniteLine A N hA X)⟦(2 : ℤ)⟧,
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) q).map a.hom ≫
          SfP1Transport.trace A N hA t q e w hY d.trace =
        (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} A) q).hom.app
          ((ordinaryFiniteLine A N hA X)⟦(2 : ℤ)⟧) ≫
          presentedFiniteP1Trace A N hA t q e w hY d ≫
          (singleFunctorObjUnitIso (ModuleCat.{u + 1} A) Y).hom := by
  obtain ⟨a, ha⟩ := exists_presentedFiniteP1RawAdjustment A N hA t q e w hY d
  rw [← SfP1Transport.presentationTrace_assoc A q e w
    ((ordinaryFiniteLine A N hA (ProjectiveLine Y))⟦(2 : ℤ)⟧)
    (d.trace ≫ (SfP1Transport.constantUnit A Y).hom)] at ha
  refine ⟨a, ?_⟩
  conv_rhs =>
    arg 2
    arg 2
    rewrite [← constantUnit_eq]
  run_tac
    let g ← Lean.Elab.Tactic.getMainGoal
    g.withContext do
      let h := (← Lean.Meta.getLocalDeclFromUserName `ha).toExpr
      let lhs ← Lean.Meta.inferType h
      let rhs ← g.getType
      let heq ← traceProofCongruence 150 lhs rhs
      let eq ← Lean.Meta.mkAppM ``eq_of_heq #[heq]
      g.assign (← Lean.Meta.mkAppM ``Eq.mp #[eq, h])
    Lean.Elab.Tactic.replaceMainGoal []
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SixFunctors.ProjectiveLineTraceNormalization | unclaimed | Forced private tactic and proof adaptation above. |
| Sheaf.SixFunctors.ProjectiveLineTraceAdjunction | not consulted (unchanged) | Direct importer; compile against the adapted theorem. |

The data module's nine current direct importers and the other trace consumers are
listed in sf-p1-trace-factorization.md. The current --uses scan for this theorem
returns exactly the two modules above. The normalization theorem's statement and
its existing DAG attachment are unchanged. The node's proof and proof origin now
record regrouping by associativity; its dependencies already cite the data node.

The adapted normalization module and the unchanged ProjectiveLineTraceAdjunction both
compiled successfully in the coherent 19-module repair validation.

## Status

landed 20261027T054555-L-964137 2026-10-27 (merge of deliver/E1/Sheaf.AlgebraicGeometry.SfP1ProjectionTraceTransportTrue)
