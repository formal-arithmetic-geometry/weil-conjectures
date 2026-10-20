## What changed

Restored `lean/Sheaf/AlgebraicGeometry/EulerCharZeroDimSupport.lean` from its
quarantine archive. Promoted `WeilConjectures.AlgebraicGeometry.Coherent` to a
public import to repair the recorded unknown-constant error in the public theorem.
Proved `AlgebraicGeometry.Scheme.Modules.eulerChar_zero_dim_support` without
changing its signature. The proof uses both prescribed main dependencies:
`coherent_zero_support_finite_scheme` and `finiteSchemeCohomologyTensor`.
It transports vanishing through module-derived cohomology, tensor invariance
through affine pushforward over k, and identifies H0 with global sections by a
k-linear equivalence. Updated the node's proof and proof dependencies accordingly.

The source read is Stacks `varieties.tex`, `lemma-chi-tensor-finite` (Tag 0AYT),
parts (3)--(5). The empty scheme, zero sheaf and zero finite-support algebra are
included: no nonempty-support or nontrivial-algebra assumption was added.
LeanFinder, Loogle and grep searches found no direct replacement theorem.

Change record: `coord/changes/E2-EulerCharZeroDimSupport-coherent-export.md`.
Single-file compilation passed cleanly in 3.8 seconds. The first delivery dry run
also passed server preflight, including the generated axiom/proof probe. A direct
comparison confirms that the theorem signature is byte-for-byte identical to the
archived source. No active consumer imports this quarantined module; the change
record lists the six archived direct consumers and their current claim status.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.Modules.eulerChar_zero_dim_support`
(node `lem-pc-chi-zero-dim-support`). Added 0 holes; split off 0 statements.
No sorry remains in the delivered Lean file.

## No longer needed

Removed direct proof imports `WeilConjectures.Mathlib.Topology.KrullDimension`
and `Sheaf.AlgebraicGeometry.CoherentFiniteType`. The finite-support reduction
already handles support closedness and finiteness; `lem-sc-dim0-finite` and
`pqf-def-coherent` are therefore no longer separate proof dependencies of this
node. They remain needed by its dependencies or statement, so no module is
withdrawn or claimed globally pruned. The coherence module import was promoted,
not removed. Both main dependency modules and the item's Lean attachment remain.

## Where the brief, the DAG or earlier work was wrong

The quarantined source had a private import for a declaration appearing in its
public signature. The explicit public coherence import repairs this defect.
The plan omitted two interface steps now made explicit in Lean and the node:
tensor-formula pullback is compared to ordinary pullback by adjunction uniqueness,
and module-derived cohomology is compared to the source H model before asserting
Subsingleton. Affine-pushforward Euler invariance directly transfers the finite
scheme's tensor calculation while retaining the k-action.

## Second reading by E2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
