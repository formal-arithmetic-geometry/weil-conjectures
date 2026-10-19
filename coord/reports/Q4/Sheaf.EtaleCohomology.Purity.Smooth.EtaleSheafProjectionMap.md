## What changed

Proved `AlgebraicGeometry.Etale.etaleLowerShriekProjectionMap` using the inverse of the
existing `etaleLowerShriekTensorIso`. Joint naturality follows from its naturality
square. The section and geometric-stalk equations are proved in two new modules,
`EtaleProjectionSectionNormalization` and `EtaleProjectionStalkNormalization`.

The stalk proof cancels the comparison isomorphisms, uses direct-sum extensionality,
and checks pure tensor germs on a common source neighbourhood. The étale localization
comparison represents the second section as a graph-restricted inverse-image unit.
The canonical unit-germ equation is proved directly with module coefficients.

The eleven original helper definitions moved verbatim to the publicly re-exported
`EtaleSheafProjectionData` to allow the normalization modules to import them. The
original theorem signature and all helper bodies are unchanged. The change record is
`coord/changes/etale-projection-helper-relocation.md`.

Validation (2026-10-19): the required delivery dry run passed compilation, axiom
checks and preflight for all four modules. Literal comparisons against current sources
confirm the unchanged helper block and parent signature. The unchanged downstream
`Sheaf.Paper.EtaleSumTensorTotalization` also compiles against the delivered modules
through `lcompile.py` (18.8 seconds).

## Proved and sorry left

Closed the original one hole:
`AlgebraicGeometry.Etale.etaleLowerShriekProjectionMap`
(`lem-pur-etale-sheaf-projection-map`).

Also proved both new normalization theorems:
`AlgebraicGeometry.Etale.etaleProjection_section_normalization`
(`lem-pur-etale-projection-section-normalization`) and
`AlgebraicGeometry.Etale.etaleProjection_stalk_normalization`
(`lem-pur-etale-projection-stalk-normalization`).

Original item: 1 hole; now 0. Added holes: 0. Split off unfinished obligations: 0.
No delivered definition or theorem contains `sorry`. The proof uses the existing
named sum-stalk theorem; its uniquely normalized comparison determines the chosen
linear equivalence. It does not choose arbitrary data from a mere existence theorem.
The empty lift fibre, zero modules and arbitrary commutative coefficient rings need
no extra hypotheses.

## No longer needed

Removed proof-only imports of
`WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`,
`Sheaf.Algebra.Category.ModuleCat.Presheaf.SheafificationBilinearExtension`,
`WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal`, and
`WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint` from the parent/data
construction. All original public imports are retained through the data module.
The new stalk module also needs no import of
`WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm`: its module-valued canonical
unit-germ equation is proved directly. Removed the unused proof import
`WeilConjectures.Mathlib.CategoryTheory.Sites.Pullback` from the new stalk module;
its needed APIs are already available from the retained imports.

The existing Kan projection replaces the separate bilinear construction and uniqueness
steps. Thus `lem-pc-sites-module-sheafification-bilinear-extension`,
`lem-pc-sites-sheaf-tensor-bilinear-universal`, and
`lemma-weil-pbc-geometric-stalk-conservative`, and
`lem-weil-pbc-inverse-image-stalk-germ` are no longer proof dependencies of this
item; their obsolete tool approvals were removed. Exact inverse image is not needed
to construct the comparison. The sum-stalk and tensor-stalk theorems remain used.
Also removed direct proof imports of
`Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`,
`Sheaf.AlgebraicGeometry.PointedEtaleStalk`, and
`WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap`; the definitions and proof APIs
needed here are supplied by retained imports.
The inverse-image germ node describes the calculation whose actual module-valued
canonical version is proved privately here, rather than supplying an imported theorem.
No whole module is claimed globally unreachable, since other targets may import it.

## Where the brief, the DAG or earlier work was wrong

The original plan omitted the existing canonical Kan projection isomorphism and its
joint naturality in `WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMapProjection`.
Reusing them avoids a separate stalk-conservativity proof of invertibility.

The existing `inverseImage_stalk_germ` uses abelian-group coefficients and asserts
existence of a comparison. The fixed module-valued canonical comparison here therefore
needs its own direct unit-germ proof, now completed. Étale localization also avoids
the originally planned separate fibre-product refinement of two germs.

The retained sandbox already contains complete normalization proofs. This resumed
session verifies them against current sources and repairs the delivery metadata:
the data node records only its signature, and the existing-source node has no
`lean.file` field.

## New nodes

`def-pur-etale-projection-data` records the unchanged eleven relocated definitions.

`lem-pur-etale-projection-kan-comparison` records the existing source-library
isomorphism and joint naturality and adds no declaration.

`lem-pur-etale-projection-section-normalization` records the proved section equation.

`lem-pur-etale-projection-stalk-normalization` records the proved stalk computation
for any section-normalized map, independently of invertibility and naturality.

All belong to the parent's chapter and unit. The unit's realized lists are empty at
this level and the unit route is preserved. Change record:
`coord/changes/etale-projection-helper-relocation.md`.

## Second reading by Q4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
