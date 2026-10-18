## What changed

Proved `AlgebraicGeometry.etale_rees_chart` with its exact existing signature and all six
conjuncts. The polynomial compatibility is the published origin-chart equivalence;
the inverse-coordinate equation follows by applying that equivalence and calculating
in Laurent polynomials. The canonical tensor map is the linear equivalence supplied by
`Ideal.isBaseChange_extendedReesAlgebraAlgHom`. Its pure-tensor formula is calculated
from its definition. The Rees pushout and `Algebra.Etale.baseChange` give an etale chart;
ring equivalences transport it across the origin-chart equivalence and both universe
lifts. Polynomial standard smoothness, transported across the universe lifts, and
composition with the etale chart give relative dimension `0 + d = d`.

No definition, public signature, universe parameter, or target is changed. A private
proved helper composes etale ring maps across arbitrary ring universes. The node proof
is updated to describe this route. No new nodes or statements with holes are introduced.

## Proved and sorry left

Closed the sole original hole: `AlgebraicGeometry.etale_rees_chart`
(node `lem-pur-dnc-etale-rees-chart`). Original holes: 1; closed: 1; added: 0;
remaining: 0. This is a proof, not a decomposition.

The complete module compiles with no errors or warnings. An explicit `#print axioms`
check of `AlgebraicGeometry.etale_rees_chart` reports exactly `propext`,
`Classical.choice`, and `Quot.sound`.

## No longer needed

The proof uses the existing, proved flat-base-change API for extended Rees algebras,
rather than reconstructing its flat tensor argument. The separate scheme-level flat
comparison, explicit affine fibre-product isomorphism, and extra fibre-dimension-zero
comparison are unnecessary for this ring-level argument. Removed proof imports:

- `Mathlib.AlgebraicGeometry.Morphisms.Flat`
- `Mathlib.AlgebraicGeometry.Pullbacks`
- `Mathlib.RingTheory.RingHom.Flat`
- `Mathlib.RingTheory.Flat.Basic`
- `Mathlib.RingTheory.TensorProduct.Basic`
- `Mathlib.RingTheory.TensorProduct.Maps`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth`
- `Sheaf.AlgebraicGeometry.EtaleSmoothZeroDimensionalFibres`

The single proof import is now
`WeilConjectures.Mathlib.RingTheory.Smooth.StandardSmooth`; all original public imports
are preserved. Removed direct node dependencies:

- `lem-weil-pbc-flat-ring-map-iff-flat-affine`: flatness is inferred directly from the
  etale algebra instance, without passing through schemes.
- `lem-weil-pbc-fibre-product-affine-spectra`: the existing Rees algebra pushout and
  its algebra equivalence suffice, without a chosen scheme pullback.
- `lem-weil-pbc-etale-scheme-base-change`: replaced by the already proved ring-level
  `Algebra.Etale.baseChange` and `Algebra.Etale.of_equiv`.
- `sbc-lem-affine-space-smooth`: the exact polynomial presentation is handled directly
  by the existing standard-smooth polynomial instance, including the universe lifts.
- `lem-weil-pbc-etale-smooth-zero-dimensional-fibres`: the required relative-dimension
  predicate follows from the existing Mathlib etale instance; the separate pointwise
  fibre-dimension conclusion is unused.

The obsolete tool approvals for `sbc-lem-affine-space-smooth` and
`lem-weil-pbc-etale-smooth-zero-dimensional-fibres` are removed from the node's
top-level `tool_uses`. The relative-dimension permanence approval is retained.

The unit `sk-def-purity-conv` has no realized statements or steps that this change
bypasses. The blueprint coordinate calculation and etale-base-change route are retained.
No claim is made that any removed dependency is unused by all other target branches.

## Where the brief, the DAG or earlier work was wrong

The planned argument is mathematically sound. The existing source library already
proves its substantial Rees-algebra steps, and Mathlib already identifies etale
morphisms with smooth morphisms of relative dimension zero. Thus the additional
fibre-dimension-zero comparison is unnecessary here. The universe lifts are
retained exactly; the proof handles unrelated universes `u` and `v`.

The edge cases `d = 0`, either coefficient ring being the zero ring, and nonreduced
coefficient rings require no extra assumptions: all invoked equivalences and base-change
lemmas hold for arbitrary commutative rings, and the proof imposes no nonemptiness,
nontriviality, domain, or reducedness assumption.

## Second reading by B5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
