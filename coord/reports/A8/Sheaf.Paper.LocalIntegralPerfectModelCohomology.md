## What changed

Proved `AlgebraicGeometry.Scheme.local_integral_perfect_model_cohomology` in
`Sheaf.Paper.LocalIntegralPerfectModelCohomology`, with its signature and all public
imports unchanged. Repaired the return at `1258cccfe7d`: removed the duplicate
`localIntegralConstantExact` private helper and use
`CompletedConstantReduction.constant_exact` directly. The latter theorem was private;
made it public in its existing unclaimed `CompletedConstantSheafReduction` module,
with its signature and proof unchanged and a source/proof docstring added. Its existing
node now lists the exposed helper. See
`coord/changes/A8-completed-constant-exact-public.md`.

The coefficient tower is identified with the constant-sheaf image of its ring-valued
tower. Finite-tower preservation and the canonical finite-level comparisons construct
the required coefficient isomorphism. Its projection formula is proved using the two
standard limit comparison identities. Existing exact pullback and slice instances,
completion flatness, and constant realization exactness supply the six functor instances.
Finite generation of cycles follows from their injection into the finite term over the
Noetherian coefficient ring. The homology projection gives finite homology and hence
finite presentation. The specified comparison map is a composite of isomorphisms.

Updated the existing node's proof, proof dependencies and proof origin to this argument.
No public definition, mathematical declaration signature, target, or consumer changed.
The only visibility change exposes the existing exactness theorem. All changes to the
item relative to current main are retained proof work; the returned duplication is removed.
`lcompile.py --all` compiled both modules cleanly: 28.6 seconds for the companion
module and 9.2 seconds for the item. The delivery tool runs the final preflight.
The quotient calculation uses an explicit equality of ideals. No diagnostic options remain.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.local_integral_perfect_model_cohomology`
(node `lem-sfb-local-integral-perfect-model-cohomology`).
Added 0 holes; 0 holes remain in the delivered Lean module. No split-off statements.
The duplicate private `localIntegralConstantExact` helper was removed; the existing
`CompletedConstantReduction.constant_exact` proof is reused unchanged. The companion
module has 0 holes; this packet adds 0 holes there.

## No longer needed

Removed proof imports:

- `Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation`;
- `Sheaf.CategoryTheory.ConstantLeftModuleInverseImage`;
- `Sheaf.Paper.ConstantModuleSectionProperties`;
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits` (from the returned packet);
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits` (from the returned packet).

The corresponding nodes `lem-weil-pbc-proetale-immersion-limit-preservation`,
`lem-pe-constant-left-module-inverse-image`, and
`lem-weil-pbc-constant-module-section-properties` are not needed by this proof.
Their entries were removed from this node's proof dependencies and tool-use approvals.
The finite coefficient tower theorem gives the needed limit comparison directly;
constant exactness is supplied by the existing completed-constant reduction helper. These are
local dependency removals, with no claim that other consumers no longer need them.
All public imports are preserved because they form the existing statement interface.
No library module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No statement defect was found. The original plan used a general immersion limit result
whose ring-sheaf case would require an additional forgetful comparison; the existing
finite constant tower theorem fits this coefficient tower immediately. Exact module
pullback already has proved instances in `ProEtaleOperations`, so its exactness does
not require invoking the longer immersion-limit theorem. Constant section properties
are unnecessary for exactness of the actual sheafification construction.

The earlier attempt copied a private helper whose statement already existed word for
word. The return correctly required reuse; exposing the original theorem removes this
duplication without introducing another mathematical assertion. The user scan found
an existing qualified use in `AdicReductionCohomologySequence`; it requires no edit.

## Second reading by A8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
