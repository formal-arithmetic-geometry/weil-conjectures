## What changed

Prove `CategoryTheory.SfbFlatHom.evaluationRoof` from the existing strict-numerator
transpose and flat scalar-evaluation model. Construct the total-to-termwise scalar
tensor identification explicitly and check its pure-section normalization. Prove
the denominator condition by the natural resolution augmentation and Hom
invariance. Match the chain evaluations on actual generators, apply closed
transposition and resolution naturality, and invert the recorded denominator.
Use the model's derived naturality and coefficient-composition laws for the
remaining fields. All private helpers are proved. A categorical evaluation-to-transpose lemma
keeps the final calculation behind a small closed-category interface.

Share the original field conditions through seven named predicate definitions
and the tensor comparison types through two transparent abbreviations. Existing
map bodies are unchanged; explicit result types and three ordinary definitions
control unfolding. Preserve all field names and generated structure declarations.
The change record is `coord/changes/J2-flat-hom-evaluation-roof-api.md`.
Only this item module changes; no adopted source-library module changes.

The private proof uses a proved equation for total-tensor generators before hiding
that construction locally. It reuses the library's proved tensor-map factorization
and total-pure extensionality lemmas. Explicit universe arguments and explicit
unfolding at the scalar-comparison step keep those definitions behind their API.
The private isomorphism definitions need no exported implementation bodies.

The private inclusion API names the homogeneous summand inclusions of the total
tensor and proves their naturality. Generator mapping then uses that square
and the existing pure-tensor map formula, keeping the colimit construction
out of subsequent elaboration. This adds only proved private helpers.

A proved private evaluation-transport lemma matches the two chain evaluations on
homogeneous tensor generators. Its interface states only the needed normalization
law, so the final roof calculation does not repeatedly unfold the representative data.


The tensor-section extensionality argument uses the sheafification universal property:
its unit remains inverted after tensoring, and sectionwise triple-tensor generation
then tests equality. Resolution-comparison naturality reuses the library's proved
private `RingedHomUniverses.resolutionComparison_naturality` API. These replace local
reconstructions; they add no statements or holes.


Validation: `lcompile.py --all` compiled the complete item (54.5 s), the temporary
interface checks (7.7 s), and the unchanged
`Sheaf.Paper.QlbarInternalHomCoefficientComparison` consumer (39.7 s).
All seven shared predicate definitions equal the original field expressions by
reflexivity. The temporary check modules were removed before delivery.

## Proved and sorry left

Closed: `CategoryTheory.SfbFlatHom.evaluationRoof`
(`lem-sfb-hom-flat-evaluation-roof`), the item's only original hole: 1 of 1.

Added holes: 0. Remaining holes in the item: 0. Split-off statements: 0.
The proof uses the existing declared dependencies, including
`FlatScalarEvaluation.model_exists` and `strict_numerator_transpose`;
this delivery does not claim to close their existing holes.

## No longer needed

No existing module becomes unused, and no public import or existing declaration
is removed. The strict-numerator and flat scalar-evaluation dependencies remain
necessary. No direct proof imports of
`Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses` or
`Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients` are needed:
the existing public imports already provide their declarations. Both modules
remain needed.

The proof does not directly invoke the planned
`lem-weil-pbc-exact-functor-complex-cohomology`,
`lem-weil-pbc-exact-functor-derived-functor`, or
`lem-pur-rhom-well-defined`. The model packages the exact-derived comparison,
Mathlib supplies preservation of quasi-isomorphisms, and the proved
`lem-pur-rhom-well-defined-universes` supplies Hom invariance with independent
universes. Remove those three direct proof dependencies from this node;
this does not withdraw their modules or declarations. Add the actually used
`lem-pc-kflat-resolution` and `lem-pur-rhom-well-defined-universes` dependencies.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement repair was necessary. The two tensor presentations
(total tensor with a single-zero complex and termwise tensor) are isomorphic,
rather than definitionally identical; their normalization is checked explicitly.
The private comparison-uniqueness proof uses a K-flat resolution of the arbitrary
first complex. The DAG now records that dependency and the actual universe
companion used for Hom invariance. The definition changes only share the
original expressions; the change record describes their consumer and semantic
checks.

## Second reading by J2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
