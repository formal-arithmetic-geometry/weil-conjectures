## What changed

Preserved the statement of `AlgebraicGeometry.ProEtale.mixedBaseChange`.
Extracted its five specified constructions, without changing their names, types or
bodies, into `Sheaf.SecSmoothPurity.MixedBaseChangeOperations`, publicly reexported
by the item. The change record is
`coord/changes/R2-mixed-base-change-operations.md`.

The main theorem applies `mixedCompactSupportScalar` in the inverse-comparison
form of the first identity. It then constructs the
legitimate Dctf source, transposes the exceptional maps under `adjBp`, and proves
equality of their transposes using hcp, heA, heB, hc and naturality. The common
precomposition is invertible by the first identity and the existing coefficient
comparison theorem. No inverse is chosen from bare existence, no axiom is added,
and no target changes.

Added proof imports of `MixedCompactSupportScalar` and `MixedBaseChangeInput`.
Removed the unused public import `CanonicalFiniteLevelCompactSupportBaseChange`
and replaced the public `ReductionExceptional` import by its objects interface.
The sole direct consumer imports `ReductionExceptional` explicitly. These public
import changes are recorded with the operations extraction.

## Proved and sorry left

Closed the one original hole: `AlgebraicGeometry.ProEtale.mixedBaseChange`
(node `det-sp-mixed-base-change`), with a complete Lean calculation from the
specified dependencies. The adjunction/counit calculation is a complete private generic lemma; its concrete
application is checked with the parent. The proper/open compatibility remains in
the smaller direct-image statement below.

Added two strictly smaller holes, each the whole proof of a public named theorem
in its own module, with source and proof in words:

- `AlgebraicGeometry.ProEtale.mixedCompactSupportScalar`
  (`lem-sp-mixed-compact-support-scalar`): the proper/open compatibility square
  on arbitrary ambient inputs, with the specified maps. It contains no exceptional
  comparison, adjunctions, or constructible-input claims.
- `AlgebraicGeometry.ProEtale.mixedBaseChange_input`
  (`lem-sp-mixed-base-change-input`): pullback membership and invertibility of
  the fixed compact-support exchange at one constructible input. This contains
  no coefficient-change square or exceptional comparison.

This is a decomposition: 1 upper hole closed, 2 lower holes added.
The local hole count increases from 1 to 2; this is not counted as a proof.
The pinned targets-closure ledger, rather than these local counts, measures progress.
The operations module contains zero holes. The complete parent proof compiled in
27.2 seconds during profiling. After removing profiling and temporary checks,
`lcompile.py --all` accepted all four packet modules and the unchanged sole direct
consumer, `Sheaf.Paper.SmoothPurityTowerMateEvaluationReduction`. That consumer
copy was removed from the packet after the check. The parent signature and all
five construction blocks were compared verbatim with the current source; the
new nodes' Lean signatures and proof-dependency unions were checked as well.

## No longer needed

Removed these unused private proof imports from the item:

- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekPlusBaseChange`
- `Sheaf.SixFunctors.CtfStabilityDirectImages`
- `Sheaf.AlgebraicGeometry.ProEtaleExtensionZero`
- `Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.Paper.FiniteRingConstructibleDerivedOrigin`
- `Sheaf.CategoryTheory.RingedSliceExtensionTensor`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
- `WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange`
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap`
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`
- `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero`
- `Sheaf.SecSmoothPurity.ScalarExtensionFunctor`

Also removed the unused public import
`Sheaf.Paper.CanonicalFiniteLevelCompactSupportBaseChange`, and narrowed
`Sheaf.SecSmoothPurity.ReductionExceptional` to `ReductionExceptionalObjects`.

Removed these obsolete direct tool-use approvals from the parent node (the
corresponding mathematical dependencies are retained on the lower nodes when needed):

- `def-cbc-compact-support-square`
- `def-cbc-exchange-map`
- `def-weil-extension-by-zero`
- `def-weil-pbc-proetale-operations`
- `lem-cbc-proetale-extension-zero`
- `lem-cbc-proetale-extension-zero-base-change`
- `lem-cbc-proetale-extension-zero-comparison`
- `lem-pc-kflat-resolution`
- `lem-sbc-smooth-relative-dimension-permanence`
- `lem-weil-pbc-finite-ring-constructible-derived-origin`
- `lem-weil-pbc-ringed-slice-extension-tensor`
- `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`
- `lem-weil-pbc-transport-identifies-exchange`
- `prop-weil-pbc-proetale-constant-ring-map`
- `thm-cbc-finite-level-proetale`
- `det-thm-sf-ctf-stability-direct-images`

The old direct proof plan for smooth relative-dimension permanence is unnecessary:
all four right adjoints and adjunctions are already supplied by the unchanged
statement. The scalar/pullback cube and proper mixed calculation are supplied by
the existing `directImageScalarExchange`, so the item does not separately use
K-flat resolutions, ringed-slice extension tensor, or constant-ring inverse-image
construction. The direct-image compatibility and geometric-input arguments are retained in
their smaller nodes, rather than silently dropped. Original proof dependencies needed
there remain dependencies of those nodes. No module is withdrawn, and no claim is
made that an indirectly imported module has left the targets' closure.

## Where the brief, the DAG or earlier work was wrong

The direct-image scalar exchange is already proved in the library and replaces
the proper-factor transposition argument of DAG Step 2. The open exchange theorem
is also proved, but in ringed-adjoint coordinates; the item specifies an ordinary
open exchange transported through realization equivalences. Their normalized
identification is a genuine remaining step, so it is retained explicitly.

The supplied Dctf adjunctions do not certify membership of a pullback source.
That certification and invertibility of beta are isolated in the input lemma,
following DAG Step 4, before applying adjBp. The full subcategory's faithful
inclusion carries the exact ambient maps without changing them.

The original exchange was well-typed. The direct-image compatibility remains a
named mathematical step with its full proof plan. The exceptional transposition
is proved in the parent. The concrete calculation uses the recorded functor
expressions directly, and the input lemma separates the ambient complex from its
membership witness to keep derived-functor conversions small. A private generic
cancellation lemma takes the available isomorphism proof explicitly.

The direct-image sublemma’s proof plan uses the already proved proper and open
scalar exchange theorems; the new input lemma retains the original proof's constructible stability and
finite-base-change dependencies. No blueprint unit route is bypassed.

## New nodes

`def-sp-mixed-base-change-operations` records the five specified constructions
in the operations module. It has no holes; all five original declaration bodies
and signatures are preserved.

`lem-sp-mixed-compact-support-scalar` records the direct-image Steps 1--5 with the
exact specified maps. Its plan identifies the unit-preserving open coordinate
transport, applies the existing open and proper scalar exchanges, pastes using naturality, and cancels the two scalar/pullback isomorphisms. It is strictly the direct-image part, without exceptional adjoints or
geometric input assertions.

`lem-sp-mixed-base-change-input` records the membership and invertibility checks
of Step 4 in the ordinary intrinsic categories, for general finite ell-primary
coefficients. It is strictly below the mixed identities.

Change record: `coord/changes/R2-mixed-base-change-operations.md`.

## Second reading by R2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
