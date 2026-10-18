## What changed

Proved `CategoryTheory.siteRestrictScalars_exact` by composing with the unchanged additive
sheaf and reflecting preservation of finite limits and colimits. The original signatures,
the definition of `siteDerivedRestrictScalars`, and the main theorem statement are unchanged.

Completed step 1 with `siteRestrictScalars_preservesLimits`,
`siteRestrictScalars_reflectsIsomorphisms`, `siteRestrictScalars_quasiIso_iff`,
`siteDerivedRestrictScalars_reflectsIsomorphisms`, and
`siteDerivedRestrictScalars_locallyDerivedComplete_iff`. The completeness comparison uses
the existing restriction lemma, proves the extension-ideal hypothesis, and explicitly
compares the exact derived functor with restriction of the chosen complex representative.
Constructed `siteCompleteRestrictScalars` by an explicit full-subcategory lift and proved
`siteCompleteRestrictScalars_reflectsIsomorphisms`.

Proved the categorical assembly `siteCompleteRestrictScalars_equivalence_of_inverse`.
Also proved `siteCompleteRestrictScalars_equivalence_of_completion`: given the ambient
coefficient-Hom functor, its comparison with the Cech completion functor, and the
augmentation-evaluation identity, it lifts the inverse to complete objects, constructs the
R-side natural isomorphism, lifts the B-side map, and proves its invertibility by
conservativity. This implements the categorical content of steps 4 and 5, including
naturality, rather than assuming an inverse on complete objects as input.

Added three fully proved modules implementing the chain-level part of step 3:
`Sheaf.Paper.RestrictedCoefficientHom` constructs the arbitrary-site internal-Hom
bifunctor with its B-action, natural restriction comparison, explicit action formula,
and additivity in both variables. All module structures and maps are constructed.
`Sheaf.Algebra.Homology.BilinearHomComplex` generalizes the existing sheaf Hom-complex
construction to a separately additive coefficient bifunctor between different categories.
Its product terms, differential, square-zero proof, and chain-map functoriality are explicit.
`Sheaf.Paper.RestrictedCoefficientHomComplex` specializes it to the coefficient action,
retaining the action formula and the product, differential, and induced-map formulas.
It also constructs a natural isomorphism from its restriction to the library's chosen
R-valued Hom-complex bifunctor, with restriction of the first complex argument. The
comparison uses preservation of products, uniqueness of product cones, the differential
formulas, and the induced-map formulas; both chain commutation and naturality are proved.

The new proposition `ProductHomComplexSpecification` packages these formulas while the
preadditive hom structures are abstract. Direct specialization of the expanded formulas
exceeded the ordinary typeclass heartbeat budget when inferring integer-unit scalar
multiplication on sheaf morphisms. The named proposition makes the specialization compile
without increasing any limit or weakening a formula.

Added proof imports for the coefficient-complex construction and the exact-derived-functor
homology comparison. Added public imports for the local Cech description and completion-unit
objects appearing in the new supporting theorem's statement. Recorded all supporting
public declarations in the parent node. No existing signature or visibility was changed.

## Proved and sorry left

Original module: two holes. Closed one:
`CategoryTheory.siteRestrictScalars_exact`.

One original hole remains, unchanged:
`CategoryTheory.flat_ringed_ideal_complete_equivalence`
(blueprint: `lem-weil-pbc-flat-ringed-ideal-complete-equivalence`).
No holes added and no split-offs. This is a partial proof delivery.

The nine supporting public declarations in the assigned module have complete proofs or
explicit constructions. All three new module theorems have complete proofs:
`SheafOfModules.exists_restrictedCoefficientHomFunctor`,
`CategoryTheory.exists_bilinearHomComplexFunctor`, and
`SheafOfModules.exists_restrictedCoefficientHomComplexFunctor`.
The new specification is an explicit proposition containing all the formulas, with no hole.

The exactness, limit preservation, conservativity, and quasi-isomorphism assertions, and
the three new coefficient/Hom-complex theorems were checked with `#print axioms`.
They use only `propext`, `Classical.choice`, and `Quot.sound`. The complete-subcategory
interfaces continue to use existing separately assigned completeness and reflector results;
their existing holes are not claimed closed here. All four delivery modules compile.

## No longer needed

No mathematical dependency pruned. The direct proof import of
`Sheaf.Paper.RestrictedCoefficientHom` is replaced by
`Sheaf.Paper.RestrictedCoefficientHomComplex`, which publicly imports the former.
This is an import-chain change, not pruning that mathematical dependency.

The main equivalence theorem remains open, so its existing Cech-model, flat-comparison,
restriction, and Hom-complex dependencies remain part of the unfinished plan. None is
pruned merely because the remaining proof is still open.

## Where the brief, the DAG or earlier work was wrong

No false statement or definition repair found. The local completeness dependency computes
restriction on a chosen complex representative, whereas this item's statement uses the
specified exact derived functor. Their comparison is now proved explicitly.

Still to implement: the global Cech base-change quasi-isomorphism in step 2; inserting
functorial K-injective resolutions and descending the functor to derived categories; and the augmentation-evaluation map with its compatibility identity. The new
ambient assembly theorem proves the passage from those data to the asserted equivalence.
The coefficient action, chain-complex identities, and natural restriction comparison
with the existing R-valued Hom complex are proved here.

## New nodes

`lem-weil-pbc-restricted-coefficient-hom`: the constructed arbitrary-site internal-Hom
coefficient action, its restriction comparison and formula, and separate additivity.
The scheme-specific `lem-sc-sheaf-coinduction-action` cannot be applied to this arbitrary
site and arbitrary B-module; its explicit construction pattern was adapted.

`lem-weil-pbc-bilinear-hom-complex`: the general product Hom-complex construction with its
three defining formulas. The existing sheaf Hom-complex proof pattern was generalized.
Mathlib's bifunctor totalization uses coproducts; using opposite categories would also
require reindexing and a sign comparison. The direct product argument retains the needed
Hom differential and does not assume products exact.

`lem-weil-pbc-restricted-coefficient-hom-complex`: specialization to coefficient module
sheaves, retaining the action formula and all chain-complex formulas, and naturally
comparing restriction with the existing R-valued Hom complex. It does not claim derived
descent. All three new nodes are fully proved,
add zero holes, and are named by the relevant parent proof step.

Change records: `coord/changes/B4-site-complete-restrict-scalars.md` and
`coord/changes/B4-bilinear-hom-complex-specification.md`.

## Second reading by B4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
