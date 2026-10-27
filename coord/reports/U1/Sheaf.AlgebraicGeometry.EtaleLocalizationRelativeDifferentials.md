## What changed

Proved `AlgebraicGeometry.Scheme.Hom.etale_localization_relativeDifferentials`
without changing its statement or any public interface. The comparison is the composite
of the canonical source transitivity arrow, transport along the square equation, and the
base transitivity arrow. Rank-zero differential vanishing and exactness make both arrows
isomorphisms. Existing transitivity declarations are imported as proof dependencies. The proved rank-zero
vanishing lemma is reused through a private import of
`WeilConjectures.AlgebraicGeometry.Curve.RiemannRochCoherent`.

Private proved helpers establish etale differential vanishing, equality transport of the
universal derivation, a tensor-pullback restriction isomorphism normalized on every module
section, the differential restriction formula, and section evaluation of a general
commuting restriction square. The latter keeps elaboration independent of the large
concrete tensor-sheaf construction. The restricted comparison is explicitly
constructed from the original comparison using these isomorphisms. A generic composite-of-isomorphisms helper prevents the
kernel from unfolding the concrete tensor maps during their composition. No data definition
or other existing module was changed. Updated the item's DAG proof to match this argument.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.Scheme.Hom.etale_localization_relativeDifferentials`
(node `lem-sfb-etale-localization-relative-differentials`). Added zero holes; none remain
in the delivered module. This proof uses the existing stated right-exact transitivity and
smooth short-exact transitivity theorems; their own outstanding proofs are unchanged.

## No longer needed

Removed proof import `Sheaf.AlgebraicGeometry.EtaleSmoothZeroDimensionalFibres` and
proof dependency/tool use `lem-weil-pbc-etale-smooth-zero-dimensional-fibres`.
Mathlib already supplies the relative-dimension-zero smooth instance of an etale map;
this proof does not use its separate assertion about the dimension at fibre points.
This is pruning of this item's dependency, not a claim that the module has no other users.

The proof no longer needs the separate differential-generation dependency
`def-weil-pbc-kahler-differentials`: the existing canonical pullback-map formula and
adjunction unit identities suffice. No Lean modules were withdrawn. No unused private
imports remain.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was changed. The DAG's last step called the restriction
normalization elementary but did not supply an all-module-section formula; the private
`tensor_restrict` helper proves it directly from normalized adjunctions. The explicit
fibre-dimension theorem is stronger than the smooth instance required in this proof.

Validation: the full proof compiled through `lcompile.py` in 24.9 seconds. The
per-helper axiom checks confirmed that the zero-sheaf, tensor restriction, differential
restriction, section naturality, canonical pullback formula, and generic composition
helpers use only `propext`, `Classical.choice`, and `Quot.sound`. The two transitivity
consequences and their composite also reach the pre-existing transitivity `sorryAx`;
these obligations are unchanged. Development profiling and axiom-print commands were
removed before delivery.

The existing dependencies remain the source of the two transitivity exactness results.
No split-off statements, axioms, definition repairs, forced adaptations, or new nodes.

## Second reading by U1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
