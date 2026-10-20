## What changed

Repaired the landing return for delivery `334bc3fd5e`: the change record's
`## Users` table now explicitly includes
`Sheaf.SecSmoothPurity.ScalarPullbackTensorCompatibility`, the additional consumer
of `scalarSheafPullbackIso` and `scalarCoefficientPullbackIso` named by the landing
checker. The definitions' signatures, values and public reexport remain unchanged,
so this consumer requires no source adaptation. Its source and claim are absent
from the current shared checkout; the record preserves the server-reported user
without claiming an unavailable consumer compilation. The current claim holder
of `ProperFiniteCoefficientExtension` is corrected to F1.

Implemented the mate/counit calculation in
`Sheaf.Paper.PurEtaleScalarMateProjection`. The private lemma
`restricted_mate_tensor` proves the abstract comparison for two adjunctions.
`scalar_natTrans_ext` proves extensionality on K-flat cochain representatives,
and `scalar_tensor_pullback_square` descends the representative square to all
objects of the ambient derived category. Tensor naturality then identifies the
transpose with the specified projection morphism.

The separately stated representative computation is
`Sheaf.Paper.ScalarTensorPullbackNormalization`. This restores the mathematical
step recorded in the archived B7 module and node, using the specified shared comparison
constants in its type. It has no direct image, mate or boundedness assumptions, and
its conclusion is only the pullback/tensor square on one K-flat complex.
The proof of descent and the whole subsequent adjunction calculation are complete
Lean proofs in the assigned module.

Moved the four existing comparison definitions
`scalarSheafPullbackIso`, `scalarSheafPullbackComplexIso`,
`scalarGeometricRepresentative` and `scalarCoefficientPullbackIso` verbatim to
`Sheaf.Paper.ScalarPullbackRepresentativeData`, publicly reexported by the
assigned module. This permits the separate representative theorem to refer
to their names rather than duplicating expanded formulas, and avoids an import
cycle. The resulting named API also removes expensive repeated kernel reductions.
The change record is `coord/changes/R3-scalar-pullback-representative-data.md`.
No existing declaration signature or definition value changes. Derived functors
and chosen adjoints are locally irreducible while elaborating the diagrams;
these attributes do not change importers. Existing public imports are preserved.

The three delivery modules and both unchanged consumers compiled without errors
or warnings through lcompile.py. The consumers were
`Sheaf.Paper.AcyclicFlatProperCoefficientModel` (U3) and
`Sheaf.SecSmoothPurity.ProperFiniteCoefficientExtension` (now F1).

## Proved and sorry left

Original item: two holes. Closed the body of
`AlgebraicGeometry.Etale.scalarMate_restrict_eq_projection`
(node `lem-pur-etale-scalar-mate-projection`) by a complete proof from the
representative square and the existing definitions.

One original hole remains, unchanged:
`AlgebraicGeometry.Etale.scalarPullbackIso_existsUnique`
(node `def-pur-etale-scalar-pullback-iso`).

One lower hole is added:
`AlgebraicGeometry.Etale.scalarTensorPullback_normalization_kFlat`
(node `lem-pur-scalar-tensor-pullback-normalization`). Its docstring and node
contain the complete representative argument in words. This isolates step 2
of the existing plan, rather than restating the mate theorem.

Thus one upper hole is closed and one lower hole added: this is a decomposition,
with zero net holes closed. The resulting packet has two holes in total: one
in the assigned module and one in the representative-square module. The shared
data module has zero holes. No private helper contains a hole.

## No longer needed

Removed these private proof imports from the assigned module:

- `WeilConjectures.AlgebraicGeometry.EtaleRestrictScalarsAdjunctionIdentities`
- `Sheaf.AlgebraicGeometry.BaseChangeMapAbelianAndSets`
- `Sheaf.AlgebraicGeometry.ExactUnboundedExchange`
- `WeilConjectures.Algebra.Homology.ChangeOfRingsTensorComparison`
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`

The specialized bounded-below adjunction identity node
`lem-sbc-restrict-scalars-derived-adjunction-identities`, the base-change-map
node `sbc-def-base-change-map`, and the unbounded-exchange node
`def-kun-unbounded-exchange` are unnecessary for the mate calculation:
`scalarRestrictionDirectImageMap` is already defined as an ambient mate, so
Mathlib's two mate counit identities suffice. The retained bounds are unused
in this ambient argument.

The scalar balancing, K-flat, change-of-rings and tensor-pullback nodes remain
needed by the separate representative square; they are not globally pruned.
No module is withdrawn and no unit statement or realized unit step is bypassed.
The existing public imports remain available to consumers.

## Where the brief, the DAG or earlier work was wrong

The plan's bounded-below adjunction transport is unnecessary after using the
actual ambient mate definition. The supplied boundedness hypotheses can be
retained without entering the proof. This changes no statement.

The declared generic ringed-module comparison interfaces do not directly state
the compatibility of the constant-coefficient comparisons fixed in this module:
one must still match their ordinary scalar-unit and coefficient-unit
normalizations. The restored node records precisely this separate computation.
The archived B7 source was used only as a starting statement and mathematical
proof plan; it was not treated as a current proved declaration.

For the representative square, the ordinary monoidal route has concrete APIs:
`CategoryTheory.isMonoidal_conjugateEquiv_symm` in
`WeilConjectures.CategoryTheory.Monoidal.Conjugate`, and
`composeAndSheafifyMonoidal` with `isMonoidal_sheafAdjunction` in
`WeilConjectures.CategoryTheory.Sites.SheafComposeMonoidal`. They supply the
monoidal scalar adjunction and its conjugate comparison; one must still match
the specified restriction/pullback comparison and transport the resulting
ordinary unit/tensor square through the derived tensor counit square. Neither
of these last compatibilities is assumed by the completed mate proof beyond
the explicitly listed representative-normalization theorem.

For the retained existence/uniqueness theorem, a concrete continuation is to lift
the ordinary scalar-extension/restriction adjunction using preservation of
K-flat quasi-isomorphisms, as in the proof of
`AlgebraicGeometry.ProEtale.pbcRestriction_isRightAdjoint`. Then compare its left
adjoint with the published chosen scalar extension. The additional compatibility
needed is that this uniqueness isomorphism followed by the derived counit is
exactly `scalarExtensionRepresentative`, with its specified ordinary unit and
homotopy quotient factors. The ordinary scalar/pullback isomorphism can then be
transported through the composite derived counits. This compatibility has not
been added as an unproved assumption or claimed as a completed proof here.

The dependency audit also found a pre-existing cycle below the retained
interfaces: `lemma-weil-pbc-derived-exchange-replacement` uses
`lem-weil-pbc-derived-exchange-termwise`, which uses
`lem-weil-pbc-derived-exchange-bounded-comparison`, which in turn uses
`lemma-weil-pbc-derived-exchange-replacement`. These three edges are present
in the read-only source, independently of this packet. Neither new node lies
on a cycle (their complete reachable dependency sets were checked). No changes
to those unrelated nodes are included; this records the existing DAG issue
for the maintainer.

## New nodes

`lem-pur-scalar-tensor-pullback-normalization`, in
`dag/nodes/sec-smooth-purity/lem-pur-scalar-tensor-pullback-normalization.json`,
states only the normalized scalar/tensor pullback square at a K-flat cochain
representative. Its public theorem is in
`lean/Sheaf/Paper/ScalarTensorPullbackNormalization.lean`. The source is
Stacks Tags 07A4, 0G7E, 07A7 and 0GL6, specifically step 2 of the parent plan.
The statement applies to arbitrary coefficient ring maps: it never asserts
flatness of B over A. The zero complex, zero coefficient ring, and identity
ring/scheme maps all give the same canonical zero or identity squares. The
hypothesis fixes the morphism c through invertible K-flat representative maps;
it does not assume any mate/projection conclusion.

`def-pur-scalar-pullback-representative-data` owns the four existing definitions
moved to the shared data module. This adds no theorem and no hole. Both original
node attachments are adjusted to move ownership of these data;
the scalarPullbackIso definition and its existence/uniqueness theorem stay in
the assigned module. See `coord/changes/R3-scalar-pullback-representative-data.md`.

The new data node has `lean.existing: false` because it delivers a new module,
although its four declarations are moved unchanged. Existing nodes retain their
original `stmt_deps`, as required by the stage-3 field whitelist. Their updated
Lean attachments identify the declaration locations, and the parent reaches the
new data through the normalization theorem's statement dependency.

## Second reading by R3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
