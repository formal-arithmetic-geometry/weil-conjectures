## What changed

Reduced `WeilConjectures.adicPurityRootComparison_existsUnique` using the existing
finite Tate descent theorem for existence and a new local root-tensor map detection
lemma for uniqueness. The proof combines these by comparing the two normalized values
on each test tensor and applying `Iso.ext`. Added the private proof import
`Sheaf.Paper.FiniteTateLocalRootTensorsExt`. Existing signatures, definitions,
attributes and public imports are unchanged. Updated the owning node's proof route.

## Proved and sorry left

Closed one of three original holes in the item module:

- `WeilConjectures.adicPurityRootComparison_existsUnique` is decomposed into existing
  descent existence and a strictly smaller local-generator detection obligation.

Two original holes remain unchanged, both attached to `def-pur-adic-root-comparisons`:

- `WeilConjectures.adicPurityEtaleDiagonal_existsUnique`.
- `WeilConjectures.adicPurityRootQuotients_existsUnique`.

One new hole is added:

- `AlgebraicGeometry.Scheme.finiteTate_local_root_tensors_hom_ext`
  (`lem-pur-finite-tate-local-root-tensors-ext`).

This is a decomposition: one hole closed, one added, net zero holes closed. The new
statement is only local-generation detection for arbitrary target sheaves and arbitrary
morphisms. It asserts neither existence nor normalization nor invertibility of a
comparison. The three earlier arithmetic and flatness proofs are preserved.

## No longer needed

None. The existing public imports and the flatness proof import remain needed by the
retained statements, definitions and proofs. No module or node is withdrawn. The unit's
realized route is preserved. The added lemma isolates a genuine remaining argument,
without replacing any prescribed object or constructing a second tensor product.

## Where the brief, the DAG or earlier work was wrong

Finite Tate site descent supplies a normalized comparison and uniqueness of descent up
to a comparison-preserving isomorphism. Its last clause does not assert uniqueness among
all comparisons satisfying root normalization. The missing argument is detection on
local root lifts. The new lemma extracts exactly that step, using finite root comparison,
local surjectivity of the root tower projection, tensor generation and separatedness.

The local-generator statement assumes l invertible, exactly as the original comparison
theorem. In degree zero the tuple is empty and constant scalar generators suffice. Empty
schemes and zero coefficient rings are included. The quotient family retains its original
statement without an invertibility hypothesis; its proof should use scalar-extension
and tensor generation, not primitive-root trivialization on an arbitrary scheme.

A diagonal proof by equality of recursive endpoint presentations and heterogeneous
transport was attempted and profiled. Kernel checks of the existing diagonal predicate
and shifted recursion equality each took roughly 7--13 seconds, and complete attempts
exceeded the per-file limit. That attempted proof and all profiling commands were removed;
the original named diagonal obligation is unchanged. No file or proof was split to evade
a compile limit, no compiler limit was changed, and no launcher script was modified.

## New nodes

`lem-pur-finite-tate-local-root-tensors-ext`, in
`lean/Sheaf/Paper/FiniteTateLocalRootTensorsExt.lean`: maps from a compared finite Tate
power to any module sheaf are detected on comparison-unit root tensors after pro-etale
local lifts to the root tower. This is the uniqueness step of the existing argument,
without comparison existence or prescribed outputs. The node includes the source,
complete proof in words, Mathlib searches and Lean attachment. No change record is needed:
all existing public signatures and definitions are preserved.

## Second reading by K1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
