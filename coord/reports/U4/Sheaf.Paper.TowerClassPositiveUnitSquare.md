## What changed

Proved `AlgebraicGeometry.ProEtale.SpTowerClasses.positivePullback_unit_square`
from the existing normalized ordinary pullbacks. Its statement is unchanged.
The ordinary argument transposes through the recorded adjunction. The normalized
unit isomorphism shows every source section is a tensor `1 ⊗ y`, so these
sections suffice to test equality. The coefficient normalization at `1`, the positive
pullback normalization, and the twisting unit normalization identify the two
paths. Naturality of ordinary direct-image evaluation justifies the section
calculation. All auxiliary lemmas in the item are private and proved. Three
new support modules provide a computed section-adjoint wrapper, its naturality,
and equality detection; every theorem in them is proved.

A private proof import of
`WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFunctor`
supplies the already proved single-complex coherence equations. These transport
the ordinary equation through the exact derived functors. The node's proof and
proof origin now describe this argument. No existing shared definition or interface is
changed. The wrapper states its actual target carrier explicitly, avoiding repeated
expansion of direct-image coefficient comparisons. Local irreducibility attributes
hide irrelevant scalar-comparison data during these proofs. Profiling motivated
separating the self-contained wrapper and its two APIs after these optimizations.
All three support modules compile cleanly. The complete item proof compiled in
30.9 seconds with development profiling; profiling and progress markers have
been removed for delivery.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtale.SpTowerClasses.positivePullback_unit_square`
(`lem-sfb-positive-pullback-unit-square`).

No holes remain in the item; no holes or split statements are added elsewhere.
The new `sectionAdjoint` is a direct computation from `adjointSection`, not a
choice from an existence theorem. Its compatibility, source and target
naturality, and equality-detection theorems are all proved.

## No longer needed

No modules, nodes, or existing imports are pruned. All three original declared proof
dependencies remain used. The root-restriction normalization of `LinePullback`
is unnecessary for this square: positive pullback is already normalized relative
to the same line isomorphism. Its module remains necessary for that isomorphism
and for the ordinary adjoint definitions. The public import of
`TowerClassProjective` remains necessary for `LinePullback.derivedIso`.

## Where the brief, the DAG or earlier work was wrong

The statement is correct. The planned section calculation can be shortened to
`1 ⊗ y`, avoiding root restriction and multiplication under scalar transport.
The DAG's two prose steps concealed the adjunction-evaluation naturality and
exact-single coherence required by Lean; these are now explicit proved steps.
The normalized unit isomorphism avoids a general tensor-generation argument.
The argument also covers empty charts and the zero coefficient ring, without a
nonvanishing assumption.

## New nodes

`def-sfb-tower-class-section-adjoint` records the computed `sectionAdjoint`
wrapper and `sectionAdjoint_heq` in `TowerClassSectionAdjoint`. It changes only
the displayed carrier, retaining the recorded ordinary adjoint and evaluation.

`lem-sfb-tower-class-section-adjoint-naturality` records
`sectionAdjoint_precomp` and `sectionAdjoint_postcomp` in
`TowerClassSectionAdjointNaturality`. They follow from ordinary adjunction
naturality and naturality of `ordinaryPushEvaluation`.

`lem-sfb-tower-class-section-adjoint-faithful` records `sectionAdjoint_ext` in
`TowerClassSectionAdjointFaithful`. It uses injectivity of the adjunction's
hom-equivalence and the invertible evaluation comparison.

No change record is needed: no other existing module or node is changed.

## Second reading by U4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
