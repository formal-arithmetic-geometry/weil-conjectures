# CategoryTheory.ConstantCompletion.quotientPresentation_exists

## Reason

Prove the existing quotient-presentation theorem, including its normalized unit law.
All existing public signatures and public definition bodies remain verbatim. No target
statement or consumer interface changes. The record covers private proof helpers,
the relocation of three existing private helpers and local transparency settings.

## Old

```lean
theorem quotientPresentation_exists (b : Bool) : Nonempty (QuotientPresentation J A I b) := by
  sorry
```

## New

The signature is unchanged:

```lean
theorem quotientPresentation_exists (b : Bool) : Nonempty (QuotientPresentation J A I b)
```

The proof derives the additive reduction-tower functor from K-flat resolutions.
Evaluation reduces preservation of quasi-isomorphisms to the existing scalar-extension
comparison and exact restriction. The ordinary constant-tower/limit adjunction unit and
two universal left-derived lifts supply the normalized completion unit. The proof uses
only the ordinary adjunction unit as a degreewise natural transformation on complexes,
then two left-derived lifts; it constructs no complex adjunction or counit.

Added private proved helpers: `resolving_derived_cochain`,
`change_preserves_kFlat_quasiIso`, `derived_tower_unit`, `module_kFlat_resolution`,
`reductionTower_preserves_kFlat_quasiIso`, and `derived_tower_presentation`.
The private definition `towerOrdinaryUnit` chooses the morphism characterized uniquely
by the fully proved `complexLimitUnit` theorem. Its specialization is definitionally
the existing `ordinaryUnit`, by proof irrelevance. No private declaration occurs in a
public signature or object-valued public definition. The three existing private helpers `kan_precomp`, `kan_change`
and `cochain_derived_counit` are moved before their new use, with unchanged proofs.

The generic helper proofs use the existing scoped options:

```lean
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
```

A local irreducibility attribute keeps `completed` behind its named maps. The two
existing projection proofs explicitly unfold `projection` and `completed`; the
original semireducibility is temporarily restored for `completedMap`. Its body remains
verbatim. Consumer attributes remain unchanged. No definition of a coefficient object,
scalar extension, ordinary unit, quotient law, or derived category changes.

The final specialization supplies `M := Mod O` explicitly, preventing repeated category
inference through the reduction tower.

The following additional local attributes keep chosen universal records behind their
field APIs, and end with the namespace; no consumer attributes change:

```lean
attribute [local irreducible] derivedExtension
attribute [local irreducible] strictLimit
attribute [local irreducible] quotientPresentation
attribute [local irreducible] derivedPull
```

The final theorem alone is enclosed in a section with
`attribute [local irreducible] HasDerivedCategory.standard`, and its proof uses
`set_option backward.isDefEq.respectTransparency.types true in`. This prevents repeated
unfolding of standard derived-category objects during the concrete specialization.
The section ends before the next declaration. No consumer option or attribute changes.
The complete submitted module compiled through `lcompile.py` in 50.0 seconds.

Both added imports are private proof imports. Three redundant private imports are
removed, as listed in report.md. No source under `lean/WeilConjectures/` is changed.

## Users

The item is held by Q1. The direct-importer scan reports these 22 modules. Every existing
public declaration retains its signature, visibility and meaning; no consumer is adapted.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.AlgebraicGeometry.CoefficientProEtaleTorAmplitude` | unclaimed | Unchanged; no adaptation. |
| `Sheaf.Paper.AdicConstructibleFiniteReductions` | unclaimed | Unchanged; no adaptation. |
| `Sheaf.Paper.CompletedConstantAlgebraFlatQuotients` | unclaimed | Unchanged; no adaptation. |
| `Sheaf.Paper.CompletedConstantCoefficientEquivalence` | unclaimed | Unchanged; no adaptation. |
| `Sheaf.Paper.CompletedConstantPresentationTransport` | unclaimed | Unchanged; no adaptation. |
| `Sheaf.Paper.CompletedExtensionZeroComparison` | unclaimed | Unchanged; no adaptation. |
| `Sheaf.Paper.CompletedKoszulConstantTransport` | unclaimed | Unchanged; no adaptation. |
| `Sheaf.Paper.CompletedPullbackAdjunction` | unclaimed | Unchanged; no adaptation. |
| `Sheaf.Paper.CompletedPullbackUnitTower` | claimed | Unchanged; no adaptation. |
| `Sheaf.Paper.CompletionMateComparison` | unclaimed | Unchanged; no adaptation. |
| `Sheaf.Paper.ConstantCompletionUnitNormalization` | unclaimed | Unchanged; no adaptation. |
| `Sheaf.Paper.ConstantDirectImagePreservesComplete` | unclaimed | Unchanged; no adaptation. |
| `Sheaf.Paper.ConstantInverseImageSection` | unclaimed | Unchanged; no adaptation. |
| `Sheaf.Paper.ConstantPullbackScalar` | unclaimed | Unchanged; no adaptation. |
| `Sheaf.Paper.ConstantReductionsFiniteProjectiveModel` | unclaimed | Unchanged; no adaptation. |
| `Sheaf.Paper.ConstantScalarDirectImageCompleteness` | unclaimed | Unchanged; no adaptation. |
| `Sheaf.Paper.ExactPullbackDerivedAdjunction` | unclaimed | Unchanged; no adaptation. |
| `Sheaf.Paper.FiniteFreeCompletedScalarComparison` | claimed | Unchanged; no adaptation. |
| `Sheaf.Paper.IntegralStratifiedPerfectCharacterization` | claimed | Unchanged; no adaptation. |
| `Sheaf.Paper.LisseNormalizedTowerLocalModels` | unclaimed | Unchanged; no adaptation. |
| `Sheaf.Paper.RationalThickEvaluation` | unclaimed | Unchanged; no adaptation. |
| `Sheaf.Paper.WContractibleConstantReductionsML` | unclaimed | Unchanged; no adaptation. |

## Status

landed 20261021T061627-L-1802320 2026-10-21 (merge of deliver/Q1/Sheaf.Paper.ConstantCompletionEquivalence)
