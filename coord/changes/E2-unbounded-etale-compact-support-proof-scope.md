# AlgebraicGeometry.Etale.UnboundedEtaleCompactSupportComparisons proof scope

## Reason

This administrative record accompanies the stage-3 proof of
`Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons` by E2.
The preflight's command-level scan flags the new universe, section-variable, open,
instance and attribute commands, so it requires a change record. All 24 existing
public declaration signatures, all nine existing public definition bodies and the
ordered public imports are unchanged. The existing node changes only its proof
route, proof dependencies, proof origin and obsolete tool approvals.

The two private formalism instances are explicitly local to this file. The
irreducibility commands affect private proof elaboration or are local attributes;
the additional open commands and universe names serve private categorical helpers.
No target statement or definition used by a target changes its meaning.

## Old

The original module's initial scope commands are verbatim:

```lean
universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
```

Its existing local attribute is verbatim:

```lean
attribute [local irreducible] unboundedEtaleCompactSupportBaseChange
```

These commands remain. The original module has no declarations named
`unbounded_has_base_change`, `unbounded_has_proper_exchange` or
`right_derived_identity_iso`; these are new private proof helpers. The eleven
existing theorem bodies listed in report.md contain `sorry` in the original.
No original signature or public definition is replaced.

## New

The new private local instances and the private identity wrapper are verbatim:

```lean
private local instance unbounded_has_base_change
    (A : Type (u + 1)) [CommRing A] : (unboundedFormalism A).HasBaseChange where
  isIso_baseChange sq := by
    rw [unbounded_open_base_change A sq]
    infer_instance
```

```lean
private local instance unbounded_has_proper_exchange
    (A : Type (u + 1)) [CommRing A] [Finite A] :
    (unboundedFormalism A).HasProperExchange where
  isIso_exchange sq := by
    rw [unbounded_open_exchange A sq]
    exact isIso_openImmersionLowerShriekLowerStarExchange_of_isAddTorsion_ring A
      isAddTorsion_of_finite sq
```

```lean
@[irreducible]
private noncomputable def right_derived_identity_iso
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    [HasKInjectiveResolutions C]
    (T : C ⥤ C) [T.Additive]
    [PreservesFiniteLimits T] [PreservesFiniteColimits T] (e : T ≅ 𝟭 C) :
    T.rightDerivedFunctor ≅ 𝟭 (DerivedCategory C) :=
  T.rightDerivedFunctorIsoMapDerivedCategory ≪≫
    Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryIdIso C
```

After `end UnboundedFormalism`, the file reactivates the proof instances locally
for its remaining proofs:

```lean
attribute [local instance] unbounded_has_base_change unbounded_has_proper_exchange
```

This registration ends with the enclosing namespace. All three helpers have
complete constructions or proofs. The wrapper's explicit
unfolding equation is proved by `unfold right_derived_identity_iso; rfl`.
It is used only by private proofs and never occurs in a public signature or public
definition body.

The proof also opens `TwoSquare`, `Abelian` and `CategoryTheory.Abelian`, introduces
private categorical universes and the variables in `NormalizationModels`, and uses
`attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits`
inside `ExactOpenComposition`. Its `attribute [local irreducible]` commands refer to
`upperStar`, `lowerStar`, `openImmersionLowerShriek`, the derived functor constructors,
derived functor natural/composition isomorphisms, the open-immersion and inverse/direct
image adjunctions, and their derived and bounded-below adjunction constructors.
These local commands end with their section or namespace; none registers a new
public instance, notation or global attribute on an existing declaration.
The scoped transparency options and theorem-local recursion-depth options guide
proof elaboration. There is no diagnostic option, skipped kernel check or increased
compile-time limit.

Existing proof imports are pruned and three private proof imports remain, as listed
in report.md. No source-library module or public import is changed.

## Users

The read-only command
`tools/downstream.py Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons
--uses unbounded_has_base_change unbounded_has_proper_exchange right_derived_identity_iso`
reports 33 transitive consumers and zero external textual users of the new private
names. Every consumer is listed below. Claim holders were read from `coord/claims/`
when preparing this record. No consumer changes are needed: the existing public
statements and data are identical, and the new proof instances are local.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons | E2 | Proves the eleven holes using private helpers and local proof instances. |
| Sheaf.AlgebraicGeometry.AffineLinearActionFamily | unclaimed | Public signatures, definitions and public imports unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineLinearExchangeCoherence | unclaimed | Public signatures, definitions and public imports unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineSpaceAmbientAdjunction | unclaimed | Public signatures, definitions and public imports unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineSpaceLinearTraceInvariance | unclaimed | Public signatures, definitions and public imports unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.AmbientAffineTranslationTrace | unclaimed | Public signatures, definitions and public imports unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleHorizontalSupportMate | unclaimed | Public signatures, definitions and public imports unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleHorizontalSupportTower | unclaimed | Public signatures, definitions and public imports unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleShriekOpenExchangeAdjoint | unclaimed | Public signatures, definitions and public imports unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleSupportMapCompatibility | N3 | Public signatures, definitions and public imports unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.OpenExchangeTower | unclaimed | Public signatures, definitions and public imports unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.OpenSourceComposition | unclaimed | Public signatures, definitions and public imports unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperCompositionSiteTransport | unclaimed | Public signatures, definitions and public imports unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.QuasiFiniteCompactSupportExact | U1 | Public signatures, definitions and public imports unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ShriekTensorComposition | unclaimed | Public signatures, definitions and public imports unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.UnboundedCompactSupportProperComposition | unclaimed | Public signatures, definitions and public imports unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.VectorBundleIntegration | unclaimed | Public signatures, definitions and public imports unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.VectorBundleIntegrationCharts | unclaimed | Public signatures, definitions and public imports unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.VectorIntegrationLocalTraceCompatibility | unclaimed | Public signatures, definitions and public imports unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.VectorIntegrationMate | unclaimed | Public signatures, definitions and public imports unchanged; no adaptation. |
| Sheaf.Paper.CompositeIntegrationCounit | unclaimed | Public signatures, definitions and public imports unchanged; no adaptation. |
| Sheaf.Paper.DeltaProperPushforward | S7 | Public signatures, definitions and public imports unchanged; no adaptation. |
| Sheaf.Paper.DualizingLocallyClosedInheritance | unclaimed | Public signatures, definitions and public imports unchanged; no adaptation. |
| Sheaf.Paper.FiniteCoefficientDualConstructible | unclaimed | Public signatures, definitions and public imports unchanged; no adaptation. |
| Sheaf.Paper.FiniteExceptionalInternalHom | unclaimed | Public signatures, definitions and public imports unchanged; no adaptation. |
| Sheaf.Paper.FixedFinitePositiveCoefficientTwist | unclaimed | Public signatures, definitions and public imports unchanged; no adaptation. |
| Sheaf.Paper.PurityFiniteExceptionalComposition | unclaimed | Public signatures, definitions and public imports unchanged; no adaptation. |
| Sheaf.Paper.PurityFrameClass | unclaimed | Public signatures, definitions and public imports unchanged; no adaptation. |
| Sheaf.Paper.PurityFrameKummer | unclaimed | Public signatures, definitions and public imports unchanged; no adaptation. |
| Sheaf.Paper.PurityFramePrincipalBoundary | unclaimed | Public signatures, definitions and public imports unchanged; no adaptation. |
| Sheaf.Paper.VectorPurityBaseChange | unclaimed | Public signatures, definitions and public imports unchanged; no adaptation. |
| Sheaf.Paper.VectorPurityDirectSum | unclaimed | Public signatures, definitions and public imports unchanged; no adaptation. |
| Sheaf.Paper.VectorPurityNormalization | unclaimed | Public signatures, definitions and public imports unchanged; no adaptation. |
| Sheaf.SmoothPurity.TensorMateEtalePrecomp | unclaimed | Public signatures, definitions and public imports unchanged; no adaptation. |

## Status

landed 20261021T021912-L-2791212 2026-10-21 (merge of deliver/E2/Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons)
