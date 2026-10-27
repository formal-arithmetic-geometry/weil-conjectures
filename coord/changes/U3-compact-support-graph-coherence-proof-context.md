# AlgebraicGeometry.Etale.etaleCompactSupportGraph_coherence

## Reason

The completed proof uses generic categorical calculations and explicit formula lemmas
to avoid unnecessary expansion of derived-functor constructions. This record describes
the local elaboration context requested by the static interface check.
The coherence module, `EtaleCompactSupportNormalizationData`, and the two unclaimed
formula consumers listed below are edited.
Every pre-existing public signature, public import and exported attribute is unchanged.
The homotopy-comparison and derived-comparison definitions are factored through their
identical generic formulas. The identity-comparison body uses the same abelian
preadditive projections as the generic calculation. All added proof helpers are fully proved. The three shared normalization helpers
are public and attached to the existing definition node; the coherence helpers are private.

The five duplicate helpers identified in return `0b1d3eae651` are removed. The independent
prerequisites `EtaleCompactSupportGraphGeometricBaseChange` and
`UnboundedProperOpenComposition` supply the existing homotopy cancellation and open
comparison monicity. No duplicate helper is relocated.

## Old

```lean
set_option autoImplicit false

universe u
```

The theorem body was `by sorry` in the library. Its signature remains:

```lean
theorem etaleCompactSupportGraph_coherence
    (A : Type (u + 1)) [CommRing A] [Finite A] :
    EtaleCompactSupportCoherence A (canonicalEtaleCompactSupportCore A)
```

## New

```lean
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u v w
```

Inside the existing namespace:

```lean
attribute [local instance 2000] Abelian.toPreadditive
attribute [local irreducible] upperStar lowerStar
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Functor.rightDerivedFunctor
```

The open graph normalization calculation unfolds the two adjunction constructions
explicitly and identifies their components by congruence. A generic, proved private
`mono_comp_iso` lemma accepts the monomorphism proof and the final isomorphism explicitly,
so the geometric applications need no isomorphism instance search on an expanded direct
image. Explicit arguments to graph normalization and the direct-image right-unit equation
prevent the identity proof from unfolding large sheaf functors during rewrite matching.
These options and attributes apply only to proof elaboration in this module.
The shared `normalizationHomotopyComponent` is the same five-arrow formula formerly
written directly in `compactSupportComparisonOnHomotopy`:

```lean
S.mapDerivedCategoryFactorsh.hom.app K ≫
  DerivedCategory.Qh.map ((a.mapHomotopyCategory (.up ℤ)).app K) ≫
  DerivedCategory.Qh.map
    ((Functor.mapHomotopyCategoryCompIso (Iso.refl (O ⋙ R)) (.up ℤ)).inv.app K) ≫
  R.rightDerivedFunctorUnit.app ((O.mapHomotopyCategory (.up ℤ)).obj K) ≫
  R.rightDerivedFunctor.map (O.mapDerivedCategoryFactorsh.inv.app K)
```

The concrete homotopy definition now specializes this formula with the etale extension functor,
open extension functor and direct image of the compactification. Its signature remains
verbatim. The natural transformation is likewise assembled generically from the exact factors,
homotopy compositor, derived unit and associators. `compactSupportDerivedComparison`
descends its specialization through the unchanged localization construction. The
proved generic component equation supplies the existing component theorem.
No factor, object, choice, or direction of composition changes. In particular its
homotopy compositor is retained; generic coherence proofs simplify it using the imported
`homotopy_comp_inv`. This refactor makes the general-category formula and concrete
normalization share a term instead of repeatedly comparing expanded sheaf constructions.
The three shared helpers belong to the existing definition node; no new proof obligation is introduced.
Scoped priority 2000 for `Abelian.toPreadditive` in the homotopy-normalization and
identity-normalization sections keeps the same definitional preadditive structure
throughout these formulas. These priorities are local and export no attribute change.
The identity calculation works degreewise on complexes, and the exact identity factor
uses the existing `mapDerivedCategoryIdIso_hom_app_Qh_obj` theorem.
The public theorem is proved from these complete private calculations and the imported
results, with its original signature.

## Users

The theorem's public consumers retain the same signature and public imports.
No public statement, instance or notation changes. The normalization definitions
retain their original formulas via the generic helpers described above.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.EtaleCompactSupportGraphCoherence | U3 | Complete proof; private helpers and local elaboration context. |
| Sheaf.AlgebraicGeometry.EtaleCompactSupportNormalizationData | unclaimed | Shared homotopy formula; same constructed map. |
| Sheaf.AlgebraicGeometry.EtaleCompactSupportFiniteGraphIso | unclaimed | Add the shared component to the existing `dsimp` formula unfolding. |
| Sheaf.AlgebraicGeometry.EtaleSupportMapCompatibility | unclaimed | Add the shared component to the existing `simpa only` formula unfolding. |
| Sheaf.AlgebraicGeometry.EtaleCompactSupportNormalization | unclaimed | No adaptation; existing public interface preserved. |
| Sheaf.AlgebraicGeometry.ChartNormalizedModelIdentification | unclaimed | No adaptation; existing public interface preserved. |

## Verification

The coherence proof closes its original hole and adds none. The isolated generic and
sheaf prefix checks in 10.4 seconds; the full coherence proof checks in 44.4 seconds.
The original support-map consumer fails at its `simpa only` step: simplification
leaves `IsIso (H.map (normalizationHomotopyComponent ...))` instead of the desired
isomorphism of the sheaf-map factor. Adding the shared component to the existing
unfolding list restores the same five-arrow cancellation. The finite-graph consumer
needs the same unfolding in its existing `dsimp` before inferring invertibility.
No signature, visibility or unrelated proof line changes in either consumer. Their nodes and module claims are unclaimed.

## Status

landed 20261024T191343-L-315095 2026-10-24 (merge of deliver/U3/Sheaf.AlgebraicGeometry.EtaleCompactSupportGraphCoherence)
