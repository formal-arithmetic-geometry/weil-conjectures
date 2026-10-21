## What changed

Proved `AlgebraicGeometry.normal_topologicallyNoetherian_components` with its original
signature. The proof uses only Mathlib: the continuous image of the spectrum of a
stalk domain is the irreducible set of generizations of its point. Every component
through that point is its closure, by the component's generic point and maximality.
Consequently components are disjoint. Finiteness makes each component the complement
of a finite union of the others, hence open. Open-immersion stalk isomorphisms preserve
normality; irreducibility and reducedness give integrality.

Added the private proof import `Mathlib.AlgebraicGeometry.Stalk`. Updated the existing
node's proof, proof_deps and proof_origin to this argument. Removed obsolete top-level
tool_uses approvals. No signatures, definitions, public imports or consumers change.
The existing declaration docstring records the original valid affine proof plan;
the node and the Lean proof now record the shorter implemented argument.

## Proved and sorry left

Closed 1 hole: `AlgebraicGeometry.normal_topologicallyNoetherian_components`
(node `lem-trf-normal-topologically-noetherian-components`). Added 0 holes;
0 holes remain in the delivered module. No intermediate theorem was split off.
The empty scheme is covered by the finite-component theorem and the vacuous component
quantifier; the proof does not require a point or nonempty ambient scheme.

## No longer needed

Removed proof imports `Mathlib.AlgebraicGeometry.AffineScheme` (replaced by Stalk),
`Mathlib.Topology.Sets.Closeds`, and
`WeilConjectures.RingTheory.ReducedNormalIffIntegrallyClosedTotalFractions`.
The latter module is pruned from this theorem's proof dependencies; it is preserved
unchanged in the adopted source tree and may still be needed by other consumers.

The following planned node dependencies are unnecessary for this proof:

- `lem-weil-pbc-affine-open-spec-points`: no affine-open presentation is needed.
- `lem-weil-pbc-spec-irreducible-components-minimal-primes`: no prime/component
  correspondence is needed.
- `lem-weil-pbc-affine-open-stalk-localization`: the canonical stalk-spectrum morphism's
  range is supplied directly by Mathlib, without localizing affine section rings here.
- `def-weil-pbc-normal-ring`: the proof works with the already given stalk properties.
- `lem-weil-pbc-reduced-normal-iff-integrally-closed-total-fractions`: the domain-stalk
  generization argument avoids the finite-product decomposition entirely.
- `lem-weil-pbc-open-subspace-irreducible-closed-correspondence`: no affine traces of
  global components need to be glued.

Removed all three obsolete top-level tool_uses entries: the minimal-prime correspondence,
affine stalk localization, and reduced-normal total-fractions theorem listed above.
The unit `sk-i-curve-zero` and its realized route are unchanged.

## Where the brief, the DAG or earlier work was wrong

The statement is correct. The eight-step affine/product plan was longer than necessary.
The source-library proof `irreducibleSpace_of_isDomain_stalk` already contains the
shorter generization argument; applying it directly to global components avoids its
algebraically locally Noetherian hypothesis. The canonical-morphism node is used only
for its range clause, supplied by Mathlib `Scheme.range_fromSpecStalk`; no source-library
proof import or new unproved dependency is needed.

## Second reading by P1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
