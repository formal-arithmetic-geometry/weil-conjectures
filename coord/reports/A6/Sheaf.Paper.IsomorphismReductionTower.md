## What changed

Replaced the proof of `WeilConjectures.isomorphismReductionTower`. The ordinary
comparison is the mate of the restriction-of-scalars square under the normalized
extension/restriction adjunctions. Its unit equation gives the pure tensor formula;
tensor generation proves transition compatibility. The comparison is mapped
termwise to complexes, giving chain-map naturality.

The derived argument transports the pointwise universal counit from the homotopy
category to complexes and through the exact sectionwise equivalence. Naturality
and counit cancellation identify the recorded canonical resolution comparisons.
Existing statement signatures, definitions, public imports, and docstrings stay
unchanged. Private helpers and proof imports supply the argument. The node's
proof and dependencies are updated to this route.

The original public signatures and definition bodies were checked against the
shared source; all remain verbatim. The DAG proof dependencies equal the union
of the recorded steps. Compiler validation is performed by the delivery tool.

## Proved and sorry left

The proof replaces the one original hole, in
`WeilConjectures.isomorphismReductionTower`. The item contains zero remaining
`sorry`; zero holes are added or split off. All new helpers are private and proved.
The tensor, transition, and derived-comparison portions have passed single-file
checks; the delivery tool checks the assembled module and its axioms.

## No longer needed

The ordinary comparison is constructed directly from the normalized adjunctions,
so the proof does not need `lem-pur-isomorphism-inverse-image-tensor-hom` or its
module `Sheaf.Paper.PurInverseImageTensorHom`.

The universal-counit comparison uses only the K-flat image hypotheses already
present in the statement. It needs no auxiliary common K-flat refinement, and
therefore does not directly need `lem-pc-kflat-resolution`,
`lem-pur-quasi-isos-saturated-triangulated`,
`lem-weil-pbc-ringed-pullback-preserves-kflat`,
`lem-weil-sheaf-scalar-extension-ring-iso`, or
`lem-pur-left-derived-from-kflat-class`.
These are dependencies pruned from this proof, not declarations withdrawn from
the source library; other consumers and the proofs of retained dependencies may
still use them. No module is withdrawn. The unit's realized statement and steps
are preserved.

Removed proof imports:
`Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`,
`Sheaf.Algebra.Category.ModuleCat.Sheaf.ScalarExtensionRingIso`,
`Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`,
`WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated`,
`WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass`,
`Sheaf.Paper.KFlatRingedToposPullback`, and
`Sheaf.Paper.PurInverseImageTensorHom`.
The needed K-flat and derived-counit interfaces are already supplied by the
retained tower and scalar-reduction modules.

## Where the brief, the DAG or earlier work was wrong

The previous DAG route is valid but unnecessarily introduces a common refinement
and a general K-flat pullback theorem. The universal pointwise derived counit
supplies the required comparison directly. No statement or definition repair was
needed. No forced adaptation or new node was required.

## Second reading by A6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
