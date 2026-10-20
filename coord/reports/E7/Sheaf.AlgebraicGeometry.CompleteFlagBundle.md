## What changed

Proved three declarations in `lean/Sheaf/AlgebraicGeometry/CompleteFlagBundle.lean`.
All existing public signatures, recursive equations, public imports and docstrings
are unchanged. An explicit structural termination annotation was added to
`completeFlagBundle` while investigating elaboration cost.

`completeFlagKernel_chart` constructs the section using the coefficient of the free
line generator. A proved private linear-algebra lemma constructs the kernel basis:
the coordinates away from the normalized index give a linear equivalence with a
finite function space. Evaluation preserves kernels, transporting this basis to
the sections of the sheaf kernel.

`completeFlagBundle_mono` uses the existing
`completeFlagKernel_pullback_locally_split` statement at the identity map.
Restriction preserves kernels; a split epimorphism has a split kernel inclusion.
The resulting local retractions remain retractions after arbitrary pullback.
Monicity is local on the scheme, and rank induction then proves every inclusion
monic. The identity cases use the zero and identity inclusions.

`completeFlagBundle_step_unique` constructs the successive factors by rank
induction. Private general category lemmas handle the dependent conditional levels,
including the boundary and levels above the rank. Cancellation against the next
monic inclusion proves uniqueness.

No imports added. All Mathlib declarations used by the new proofs are already
exposed by the original public imports.
Local reducibility attributes prevent unnecessary unfolding of tensor pullbacks,
comparison isomorphisms, chosen limit objects and the rank recursion. They do not
change the exported definitions. The complete module compiled cleanly through
`lcompile.py` in 29.0 seconds after adding private constructor lemmas and
enabling the transparency safeguard during the recursive proofs and final
property statement. Local irreducibility also prevents unfolding the chosen
cokernel and successive-step data during instance search.

## Proved and sorry left

Closed 3 of the original 8 holes, with 0 holes added and 0 split off:

- `AlgebraicGeometry.completeFlagKernel_chart`.
- `AlgebraicGeometry.completeFlagBundle_mono`.
- `AlgebraicGeometry.completeFlagBundle_step_unique`.

Five original named theorem holes remain unchanged, all attached to
`def-pur-complete-flag-bundle` with their existing source and proof docstrings:

- `AlgebraicGeometry.exists_completeFlagProjectivization`.
- `AlgebraicGeometry.completeFlagKernel_pullback_locally_split`.
- `AlgebraicGeometry.completeFlagKernel_rank`.
- `AlgebraicGeometry.completeFlagBundle_last_quotient`.
- `AlgebraicGeometry.completeFlagBundle_properties`.

The monomorphism proof uses the existing local-splitting theorem, and the rank
recursion uses the existing kernel-rank theorem. These are retained original
holes, not newly asserted assumptions. All new private helpers are proved.

## No longer needed

Removed redundant proof imports `Mathlib.LinearAlgebra.Basis.Basic`,
`Mathlib.LinearAlgebra.Pi` and `Mathlib.CategoryTheory.Limits.FunctorCategory.Basic`
from the development version; all are already exposed by the original imports.
No original import, node or module is removed. All five statement
dependencies remain necessary for the construction. The node has no proof
steps or proof dependencies to prune, and the proof implements the existing
source argument and theorem docstrings without changing the unit route.

The alternative `ProjectiveBundleQuotientGeometry` presentation was examined but
is not imported: its symmetric-algebra projectivization and quotient require
comparison with this module's `ProjectiveBundleRealization`, including its
normalized twist restrictions. The delivered proofs need no such comparison.
No scratchpad module is part of the delivery.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement or construction was changed; only the recursion
termination mode was made explicit. No new node is required: the private helpers carry out elementary parts of the
already documented chart, local-splitting and rank-induction arguments.
The bare restriction functor does not expose finite-limit preservation to
instance search; a private proof obtains it by its underlying-presheaf
precomposition comparison. This is an implementation issue rather than a
missing geometric hypothesis.

The static checker requested a record for local elaboration commands; see
`coord/changes/complete-flag-proof-elaboration.md`. No consumer adaptation is needed.

## Second reading by E7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
