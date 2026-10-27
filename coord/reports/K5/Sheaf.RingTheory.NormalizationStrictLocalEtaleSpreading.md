## What changed

Filled `Algebra.normalization_strictLocal_etale_spreading` in the assigned module,
keeping its signature, both canonical map definitions and all public imports unchanged.
All auxiliary lemmas are private and proved. Updated the existing node's proof,
proof_deps and proof_origin to follow the implemented algebraic argument.

Normalization finiteness uses the existing normal-ring finite-domain decomposition,
the Mathlib description of etale algebras over a field, and
`IsIntegralClosure.finite`. An injective linear map into the product of the component
closures proves finiteness, without constructing an isomorphism of integral closures.
Denominator clearing constructs the actual localization instance for E to F.
The injective lift of C_g into the total fraction ring proves its closure equality.

Strict-local descent uses `Module.flat_iff_strictHenselization` and the canonical
residue map descended from the specified pointed-etale colimit. The maximal-ideal
criterion upgrades flatness to faithful flatness. Tensor reassociation is an explicit
ring equivalence with its pure-tensor formula; a checked commuting square permits
Mathlib's faithfully flat etale tensor descent.

The finite-map closed-image argument spreads etaleness: remove the closed image in
Spec B of the complement of the etale locus in Spec E, then choose a basic open
containing v. This avoids constructing an inverse-limit diagram. Localization-prime
identifications prove the etale-locus assertions in both directions. A pushout
identification proves tensor-map finiteness, and tensor-product localization proves
the final clause with exactly `normalizationCoverBaseChangeMap` as its algebra action.

Validation: the complete proof compiled through lcompile.py in 28.0 seconds with
exit code 0 and no warnings. The declaration signature and the two canonical map
definitions were compared byte for byte with the current repository versions.
The revised proof dependency graph has no path back to the item.

## Proved and sorry left

Closed 1 of 1 original holes:
`Algebra.normalization_strictLocal_etale_spreading`
(node `lem-sfb-normalization-strict-local-etale-spreading`).
Added 0 holes; split off 0 statements. No sorry remains in the delivered module.

The proof uses the existing, still unproved
`Module.flat_iff_strictHenselization`
(node `lem-sfb-strict-henselization-module-flatness`); it is not a newly added hole.
The normal-ring decomposition and total-fraction membership declarations used here
already have complete proofs. This is a proof from the stated library dependencies,
not a claim that every transitive dependency is axiom-free already.

## No longer needed

Removed proof imports (the public statement imports remain intact):

- `Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra`
- `Mathlib.LinearAlgebra.TensorProduct.Defs`
- `Mathlib.AlgebraicGeometry.Noetherian`
- `Sheaf.AlgebraicGeometry.NormalTopologicallyNoetherianComponents`
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`
- `WeilConjectures.AlgebraicGeometry.Morphisms.FiniteEtaleOpenIntegralClosure`
- `WeilConjectures.RingTheory.IntegralClosureFinitePi`
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`
- `WeilConjectures.AlgebraicGeometry.Morphisms.NormalDenseOpenIntegralSection`
- `WeilConjectures.RingTheory.StrictHenselizationFaithfullyFlat`
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`
- `WeilConjectures.AlgebraicGeometry.FpqcDescentEtale`
- `WeilConjectures.AlgebraicGeometry.LimitAffineTransition`
- `WeilConjectures.AlgebraicGeometry.EtaleInverseLimitDescent`

The rewritten proof no longer directly needs these old node dependencies:

- `lem-sc-affine-noetherian-underlying-space`
- `lem-trf-normal-topologically-noetherian-components`
- `lem-sbc-finite-etale-open-integral-closure`
- `lem-weil-pbc-finite-product-integral-closure`
- `def-sbc-locally-finite-presentation`
- `lem-weil-pbc-finite-iff-integral-lft`
- `lem-sbc-normal-dense-open-integral-section`
- `lem-sc-strict-henselization-faithfully-flat`
- `lem-weil-pbc-faithfully-flat-surjective-spectrum`
- `lem-weil-pbc-flat-ring-map-iff-flat-affine`
- `def-weil-pbc-fpqc-covering`
- `lem-galois-fpqc-descend-etale`
- `lem-weil-pbc-limit-affine-transition`
- `lem-weil-pbc-descend-etale`

These are local dependency removals, not withdrawals of their modules or declarations.
In particular, the finite-product integral-closure lemma remains used transitively by
the existing normal-ring decomposition; no claim of global pruning is made for it.
The normal-domain, strict-henselization and inverse-limit source modules are preserved.

Deleted obsolete entries of this node's top-level tool_uses, retaining the order of
all remaining approvals:

- `lem-trf-normal-topologically-noetherian-components`
- `lem-sbc-finite-etale-open-integral-closure`
- `lem-sbc-normal-dense-open-integral-section`
- `lem-sc-strict-henselization-faithfully-flat`
- `lem-weil-pbc-faithfully-flat-surjective-spectrum`
- `lem-galois-fpqc-descend-etale`
- `lem-weil-pbc-limit-affine-transition`
- `lem-weil-pbc-descend-etale`
- `lem-weil-pbc-finite-product-integral-closure`

New existing-node uses are the normal-ring total-fraction/decomposition results,
`lem-sfb-strict-henselization-module-flatness`, and the Mathlib leaves for etale
algebras over fields, separable normalization finiteness and integral closed maps.
The first two are already proved source results; strict-henselization module flatness
belongs to the same unit. No new tool_uses approval was inserted by the worker.

## Where the brief, the DAG or earlier work was wrong

The old plan was mathematically usable but longer than necessary in Lean. The
finite-normalization statement can be proved algebraically from the existing normal
ring decomposition, and finiteness lets the closed non-etale image replace inverse
limit descent. No statement or definition was repaired or weakened.

Edge cases checked in the argument: zero C gives the empty family of domain factors;
a zero cover algebra is allowed as an empty product of fields; g a unit is harmless;
g = 0 with injective multiplication forces the trivial case. Component regularity
uses the coordinate idempotent rather than an unjustified nonzero image of g. The
point v is any prime, with h outside v supplied by a basic open containing it. All
canonical maps are retained, including the action in the last localization clause.

## Second reading by K5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
