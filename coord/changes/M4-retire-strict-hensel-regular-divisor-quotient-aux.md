# AlgebraicGeometry.Scheme.strictHenselizationRing_divisor_quotient_noetherian_and_local_regular

## Reason

Complete the listed retirement in `coord/retire-items.tsv` for
`retire:Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotientRegularAux`.
The assigned module has zero holes. The retained upstream theorem is proved, but its
ring is the full affine-neighbourhood colimit `strictHenselization`; the sole Sheaf
consumer uses the canonically isomorphic small colimit `strictHenselizationRing`.

Retire the duplicate theorem and apply the upstream theorem in the consumer after
transporting the structural map along `smallStrictHenselizationColimitIso`. Its inverse
preserves the nonunit condition. Assemble regularity from the upstream Noetherianity
and prime-local regularity conclusion. Use `Ideal.quotientEquiv` for the inverse
comparison and Mathlib `IsRegularRing.of_ringEquiv` to return to the original quotient.
No source-library declaration, proof, attribute, public import, or definition changes.

## Old

The retired Sheaf module declared the following proved theorem:

```lean
theorem strictHenselizationRing_divisor_quotient_noetherian_and_local_regular
    (R : CommRingCat.{u}) [IsRegularRing R] (f : R)
    [IsRegularRing (R ⧸ Ideal.span {f})]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (barY : Spec (.of Ω) ⟶ Spec R)
    (b : R ⟶ strictHenselizationRing barY)
    (hb : Spec.map b = strictHenselizationStructuralMap barY)
    (hg : ¬ IsUnit (b.hom f)) :
    IsNoetherianRing (strictHenselizationRing barY ⧸ Ideal.span {b.hom f}) ∧
      ∀ (p : Ideal (strictHenselizationRing barY ⧸ Ideal.span {b.hom f}))
        [p.IsPrime],
    IsRegularLocalRing (Localization.AtPrime p)
```

The sole consumer imported:

```lean
public import Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap
import Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotientRegularAux
```

It applied the retired theorem directly to `R f barY b hb hg`.

The old contextual node statement was:

> The strict henselization divisor quotient is Noetherian and all its prime localizations are regular local.

Its `stmt_deps` contained only
`lem-sbc-strict-hensel-regular-divisor-quotient-regular-part`, the parent theorem.

## New

Withdraw the item with `deleted.txt`; the delivery tool supplies its empty module.
The mathematical node remains attached to the retained upstream owner
`WeilConjectures.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotientRegularAux`:

```lean
theorem strictHenselizationRing_divisor_quotient_noetherian_and_local_regular
    (R : CommRingCat.{u}) [IsRegularRing R] (f : R)
    [IsRegularRing (R ⧸ Ideal.span {f})]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (barY : Spec (.of Ω) ⟶ Spec R)
    (b : R ⟶ strictHenselization barY)
    (hb : Spec.map b = strictLocalizationToBase barY)
    (hg : ¬ IsUnit (b.hom f)) :
    IsNoetherianRing (strictHenselization barY ⧸ Ideal.span {b.hom f}) ∧
      ∀ (p : Ideal (strictHenselization barY ⧸ Ideal.span {b.hom f}))
        [p.IsPrime],
    IsRegularLocalRing (Localization.AtPrime p)
```

The sole consumer now imports:

```lean
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
import WeilConjectures.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotientRegularAux
```

The public structural-map import supplies the same small-colimit definitions used by
its unchanged theorem signature. The old Sheaf import also declares
`strictHenselizationStructuralMap_eq`, which collides with the upstream extension
needed by the replacement proof. Use the upstream owner, as the former auxiliary
module already did. Existing theorem signatures, visibility and docstrings of the
consumer stay identical. The only new helper is the fully proved private
`comparison_base`, moved from the retired module.

The consumer's DAG proof now records its actual dependency on the auxiliary node
and the canonical transport. The auxiliary node keeps its three mathematical proof
dependencies and is attached to the proved upstream theorem. The auxiliary node's contextual sentence is made self-contained with the same
hypotheses. Its incorrect statement-dependency edge to its parent is replaced by
the actual definition nodes, preventing a cycle with the parent's actual proof
dependency. The clarification has no base DAG citers; mathematical content is unchanged.

The clarified statement is:

> Let R be a commutative regular ring [def-weil-regular-scheme], f in R, and assume R/(f) is regular. Let Ω be an algebraically closed field and barY : Spec Ω → Spec R a geometric point [def-weil-geometric-point]. Let b : R → strictHenselizationRing barY [def-weil-pbc-strict-henselization-limit] induce the canonical structural morphism [def-weil-pbc-strict-henselization-structural-map] on spectra, and assume b(f) is not a unit. Then strictHenselizationRing barY/(b(f)) is Noetherian [def-weil-pbc-noetherian-ring], and its localization at every prime [def-weil-pbc-localization-at-prime] is regular local. The canonically isomorphic full affine-neighbourhood colimit has the same properties. No new nodes, public compatibility declarations,
axioms, unfinished statements, or arbitrary data witnesses are introduced.

The argument includes `f = 0` and dimension-zero rings. Nonunits stay nonunits under
the comparison because its inverse maps units to units. The quotient equivalence
identifies the actual principal ideals; it requires no extra regularity, reducedness,
nonzerodivisor or dimension assumption. No target definition changes.

## Users

`tools/downstream.py --uses` finds twelve downstream modules. Only `RegularPart`
imports the item and calls its declaration. No quarantined Lean source imports it
or mentions the retired declaration. All other DAG mentions of the auxiliary node
are provenance; its live mathematical use is explicitly retained in the parent.
The unit `sk-prop-input-spreading` and all its steps are preserved.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.Morphisms.RegularDivisorStrictHenselRootSection | unclaimed | Transitive consumer. No source change; existing statement and definitions are preserved. |
| Sheaf.AlgebraicGeometry.Morphisms.RegularDivisorStrictLocalLimit | unclaimed | Transitive consumer. No source change; existing statement and definitions are preserved. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotient | unclaimed | Transitive consumer. No source change; existing statement and definitions are preserved. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotientDomainPart | unclaimed | Transitive consumer. No source change; existing statement and definitions are preserved. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotientNoetherian | unclaimed | Transitive consumer. No source change; existing statement and definitions are preserved. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotientRegular | unclaimed | Transitive consumer. No source change; existing statement and definitions are preserved. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotientRegularPart | unclaimed | Sole direct caller. Replace the duplicate import with its upstream owner; transport across the canonical colimit and quotient equivalences. Public theorem signature and docstring stay verbatim. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootFiniteEtaleModel | unclaimed | Transitive consumer. No source change; existing statement and definitions are preserved. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootNormalizationFinite | unclaimed | Transitive consumer. No source change; existing statement and definitions are preserved. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootNormalizationGenericEtale | unclaimed | Transitive consumer. No source change; existing statement and definitions are preserved. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootPurityData | unclaimed | Transitive consumer. No source change; existing statement and definitions are preserved. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootTameNormalization | unclaimed | Transitive consumer. No source change; existing statement and definitions are preserved. |

Validation: the adapted consumer compiles without warnings in 3.9 seconds. The
original consumer against the withdrawn empty item fails at line 35 with
`Unknown identifier strictHenselizationRing_divisor_quotient_noetherian_and_local_regular`.
The original and adapted theorem signatures and existing docstrings are identical.
All twelve downstream modules compile against the adapted sandbox consumer and the
withdrawn stub, taking 2.5–15.4 seconds per file. The upstream auxiliary and adapted
consumer axiom probes each report exactly `propext`, `Classical.choice`, and `Quot.sound`.

## Status

landed 20261021T013348-L-2290566 2026-10-21 (merge of deliver/M4/Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotientRegularAux)
