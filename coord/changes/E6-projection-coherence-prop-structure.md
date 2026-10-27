# AlgebraicGeometry.ProEtale.CompactificationProjectionCoefficientCoherence

## Reason

The final proof checks each unit, associativity and domain argument quickly, but its
assembly against the Prop-valued definition exceeds the 60-second single-file limit.
The definition abstracts nested monoidal instance proofs into auxiliary constants;
conversion between those constants and the ordinary canonical instances is expensive.
Replace the Prop-valued definition by a Prop structure with a single `laws` field.
That field has exactly the former body, with the same quantifiers, hypotheses,
canonical maps, equations and domain assertions. Constructor and projection give
both directions of the equivalence. There is no weakening, added assumption, choice,
or change to any mathematical object. No compile limit is changed.

This definition is below the targets. Its representation changes, so its meaning is
submitted for renewed independent review. No target declaration is edited.

## Old

```lean
def CompactificationProjectionCoefficientCoherence
    (cx tx : ObjectProperty (DerivedCategory (Sheaf (Scheme.ProEt.topology X) V)))
    (cy ty : ObjectProperty (DerivedCategory (Sheaf (Scheme.ProEt.topology Y) V))) : Prop :=
  ∀ (M : DerivedCategory (Sheaf (Scheme.ProEt.topology X) V))
    (B B' : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) V)),
    cx M → ty B → ty B' →
    ∀ (hunit : IsIso (((projectionMapOfCompactification V c).app M).app (𝟙_ _)))
      (hprod : IsIso (((projectionMapOfCompactification V c).app M).app (B ⊗ B')))
      (hleft : IsIso (((projectionMapOfCompactification V c).app
        ((L((f)^*[V])).obj B' ⊗ M)).app B))
      (hright : IsIso (((projectionMapOfCompactification V c).app M).app B')),
      CompactificationProjectionUnit (rightDerivedLowerShriekOfCompactification V c)
        (L((f)^*[V])) (leftDerivedUpperStarUnitIso V f).hom M
        (inverseCompactificationProjection V c (𝟙_ _) M hunit) ∧
      CompactificationProjectionAssoc (rightDerivedLowerShriekOfCompactification V c)
        (L((f)^*[V])) B B' M (leftDerivedUpperStarTensorIso V f B B').hom
        (inverseCompactificationProjection V c (B ⊗ B') M hprod)
        (inverseCompactificationProjection V c B ((L((f)^*[V])).obj B' ⊗ M) hleft)
        (inverseCompactificationProjection V c B' M hright) ∧
      CompactificationProjectionDomains V c cx tx cy ty M B B'

```

## New

```lean
structure CompactificationProjectionCoefficientCoherence
    (cx tx : ObjectProperty (DerivedCategory (Sheaf (Scheme.ProEt.topology X) V)))
    (cy ty : ObjectProperty (DerivedCategory (Sheaf (Scheme.ProEt.topology Y) V))) : Prop where
  /-- The unit and coefficient-associativity laws, together with every input domain. -/
  laws : ∀ (M : DerivedCategory (Sheaf (Scheme.ProEt.topology X) V))
    (B B' : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) V)),
    cx M → ty B → ty B' →
    ∀ (hunit : IsIso (((projectionMapOfCompactification V c).app M).app (𝟙_ _)))
      (hprod : IsIso (((projectionMapOfCompactification V c).app M).app (B ⊗ B')))
      (hleft : IsIso (((projectionMapOfCompactification V c).app
        ((L((f)^*[V])).obj B' ⊗ M)).app B))
      (hright : IsIso (((projectionMapOfCompactification V c).app M).app B')),
      CompactificationProjectionUnit (rightDerivedLowerShriekOfCompactification V c)
        (L((f)^*[V])) (leftDerivedUpperStarUnitIso V f).hom M
        (inverseCompactificationProjection V c (𝟙_ _) M hunit) ∧
      CompactificationProjectionAssoc (rightDerivedLowerShriekOfCompactification V c)
        (L((f)^*[V])) B B' M (leftDerivedUpperStarTensorIso V f B B').hom
        (inverseCompactificationProjection V c (B ⊗ B') M hprod)
        (inverseCompactificationProjection V c B ((L((f)^*[V])).obj B' ⊗ M) hleft)
        (inverseCompactificationProjection V c B' M hright) ∧
      CompactificationProjectionDomains V c cx tx cy ty M B B'
```

## Users

Checked with `python3 -B tools/downstream.py
Sheaf.Paper.ProjectionFormulaCoefficientCoherence --uses
CompactificationProjectionCoefficientCoherence`, and a whole-library textual search
for this predicate and `compactificationProjection_coefficient_coherence`.
Only the item module uses either declaration. A textual check confirms that the
new `laws` field is identical to the old definition body, and that all nine other
public definitions and the main theorem signature occur verbatim in the new file. The eight downstream modules below
import its public interface transitively, but do not unfold or apply the predicate.
No module of `WeilConjectures` is changed. No other held module is adapted.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ProjectionFormulaCoefficientCoherence | E6 | Constructor supplies the original quantified assertion; theorem statement unchanged. |
| Sheaf.Paper.CompositionModelOrientationDefinitions | unclaimed | No reference to the changed predicate or theorem; unchanged meaning, no adaptation. |
| Sheaf.Paper.CompositionModelOrientationDescent | unclaimed | No reference to the changed predicate or theorem; unchanged meaning, no adaptation. |
| Sheaf.Paper.CompositionTensorMate | G8 (claim dated 2026-10-25) | No reference to the changed predicate or theorem; unchanged meaning, no adaptation. |
| Sheaf.Paper.ModelAffineIntegrationOrientation | unclaimed | No reference to the changed predicate or theorem; unchanged meaning, no adaptation. |
| Sheaf.Paper.ModelChartOrientationAssembly | unclaimed | No reference to the changed predicate or theorem; unchanged meaning, no adaptation. |
| Sheaf.Paper.ModelOrientationChartDescent | unclaimed | No reference to the changed predicate or theorem; unchanged meaning, no adaptation. |
| Sheaf.Paper.ModelOrientationSourceNaturality | unclaimed | No reference to the changed predicate or theorem; unchanged meaning, no adaptation. |
| Sheaf.Paper.ModelOrientationTateDetection | unclaimed | No reference to the changed predicate or theorem; unchanged meaning, no adaptation. |

## Status

landed 20261026T001338-L-4185567 2026-10-26 (merge of deliver/E6/Sheaf.Paper.ProjectionFormulaCoefficientCoherence)
