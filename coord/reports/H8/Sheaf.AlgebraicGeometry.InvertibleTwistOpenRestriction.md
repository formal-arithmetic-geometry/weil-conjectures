## What changed

Filled both theorem proofs in `Sheaf.AlgebraicGeometry.InvertibleTwistOpenRestriction`.
The degree-zero equality follows by applying the tensor-pullback adjunction Hom
bijection, using left-adjoint uniqueness and the ordinary structure-module adjunct.
The main theorem uses the existing invertibility instances for powers, tensor
products and ordinary pullbacks. It transfers these across the canonical pullback
comparison and the specified restriction isomorphism, then applies ampleness
invariance under isomorphism. Existing signatures and the actual restriction
isomorphism construction are unchanged. The item node now records this shorter
proof route. No other existing module was changed.

## Proved and sorry left

Closed 2 of 2 original holes:

- `AlgebraicGeometry.Scheme.Modules.invertibleTwistOpenRestriction_power_zero`.
- `AlgebraicGeometry.Scheme.Modules.invertible_twist_open_restriction`.

Both belong to `lem-sfb-invertible-twist-open-restriction`. No sorry remains in
the item, no hole was added, and no statement was split off.

## No longer needed

Removed the private proof import
`WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor` and the
corresponding proof dependency `lem-weil-pbc-invertible-pullback-tensor`.
Its residue-fibre, section, symmetry, and finite-permutation clauses are not
needed: the proved basic invertibility instances and the already specified
canonical comparisons suffice. This is pruning of this item's route only;
no adopted source declaration or source module is withdrawn.

The proof also does not require
`lem-weil-pbc-module-pullback-structure-sheaf` as a theorem dependency: it proves
the degree-zero equation directly from the two definitions and the Mathlib
adjunction calculation. Its module remains a public import because it defines
`tensorPullbackObjUnitToUnit` in the unchanged theorem statement.
The existing tensor/power comparison and normalized pullback definition nodes
are now explicit proof dependencies. All public statement imports are retained.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was changed. The old plan's literal positive-power
convention differs from the existing `tensorPow` recursion: exponent one is
`M tensor O`, and a successor is `M tensor M.tensorPow a`. The module already
explained the canonical associator/unitor identifications. The updated node
uses the actual recursion, including its invertible unit base case. The large
invertible-pullback-tensor package is unnecessary for this proof. The unit route
and the specified comparison are preserved; no arbitrary isomorphism is chosen.
The proof applies uniformly at exponent zero and on empty schemes or opens.

Searches used the required leanfinder, loogle and grep services, plus local source
searches. They found the existing Mathlib pullback structure-module adjunct and
left-adjoint uniqueness API, and the proved source invertibility instances;
no new mathematical helper statement was needed.

The first server compile accepted both proofs in 5.2 seconds. Its only warnings
requested the current Lean `have` syntax instead of `haveI`; those were corrected
before the delivery compile and mechanical checks. All lines are at most 100
characters. No definitions, theorem signatures, attributes or public imports
were changed.

## Second reading by H8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
