## What changed

Proved `AlgebraicGeometry.Scheme.Modules.nonempty_iso_unit_of_mvPolynomial_field`
in `Sheaf.AlgebraicGeometry.AffineSpaceInvertibleTrivial`, without changing its
statement or either public import. Added the private proof import
`Mathlib.RingTheory.Polynomial.UniqueFactorization`.

Transport factoriality across `Scheme.ΓSpecIso`, use invertibility of affine
sections and triviality of the UFD Picard group to get a rank-one basis, and
apply the already proved source-library affine free-generator criterion. The
proof explicitly constructs multiplication by the generator as a morphism of
sheaves and reflects the componentwise isomorphisms. The theorem docstring and
its existing DAG node now describe this route. No other existing module changes.

The argument includes zero variables and arbitrary fields: neither the UFD
instance nor the affine criterion requires a positive number of variables or
an algebraically closed field. No data is chosen from an unproved existence
statement to define any library object; the choices here occur only inside the
proof of the existence assertion.

## Proved and sorry left

Closed the one existing hole:
`AlgebraicGeometry.Scheme.Modules.nonempty_iso_unit_of_mvPolynomial_field`
(node `lem-sfb-affine-space-invertible-trivial`).

Holes closed: 1 of 1. Holes added: 0. Sorries left in the delivery: none.
No split-off statements.

Validation: the changed module compiled cleanly through `lcompile.py` in 3.1 s
(exit code 0). The only node fields changed are `proof`, `proof_deps`, and
`proof_origin`; the proof-step dependency union agrees with `proof_deps`.

## No longer needed

Removed the direct private imports `Mathlib.AlgebraicGeometry.Modules.Tilde` and
`Mathlib.RingTheory.PicardGroup`. The latter is already provided by
`WeilConjectures.AlgebraicGeometry.Modules.InvertibleSections`; its Picard API is
still used. Tilde also remains a transitive dependency of that source module.
Thus no whole module is claimed to leave the target import closure.

Removed the direct proof dependencies `lem-weil-pbc-affine-tilde-gamma-adjunction`
and `lem-weil-pbc-spec-module-tilde-sections` from this node's proof plan. The
proved affine free-generator criterion replaces the explicit construction of
the counit and the comparison of the tilde of the ring with the structure sheaf.
These generic affine-equivalence results may still be needed elsewhere. All
other declared dependencies are retained. No unit statement or unit proof step
is bypassed, and no upstream declaration is removed.

## Where the brief, the DAG or earlier work was wrong

The planned final tilde reconstruction is unnecessary because
`AlgebraicGeometry.Scheme.Modules.isFreeGenerator_of_bijective_smul` already
supplies the precise affine bridge in the same source module as the existing
affine invertible-sections dependency. This is a shorter implementation of the
same affine argument, not a statement repair. No false statement was found.

## Second reading by E9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
