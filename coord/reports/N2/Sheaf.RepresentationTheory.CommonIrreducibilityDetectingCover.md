## What changed

Proved `AlgebraicGeometry.Scheme.exists_common_irreducibility_detecting_cover` from the
Galois--lisse correspondence, stable lattice theorem, existing finite-matrix witness, and
finite G-set realization. The public statement and model structure are unchanged.

Added `Sheaf.RepresentationTheory.LAdicSubrepresentation` to justify that categorical
simplicity detects every invariant vector subspace. It constructs a finite coefficient
model using inclusion and projection matrices, with a canonical tensor comparison.

The common finite group is the quotient by the intersection of open congruence kernels.
Compactness makes it finite; the regular action realizes the required connected cover.
The construction includes the empty family and arbitrary, possibly nonclosed subgroups.
Both modules compiled cleanly through lcompile.py --all; the main module took 27.2 seconds.
The original theorem signature and model structure were compared with the source and
are unchanged. Import-cycle and DAG dependency-union checks also passed.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.exists_common_irreducibility_detecting_cover` (1 of 1).
Added and proved `Representation.isLAdic_subrepresentation`; no new holes or split-off
unproved results remain. All helpers are private and proved.

## No longer needed

Removed proof imports `Sheaf.CategoryTheory.Galois.AutProfinite`,
`Mathlib.Topology.Algebra.Valued.LocallyCompact`,
`WeilConjectures.AlgebraicGeometry.FundamentalGroup.Basic`,
`WeilConjectures.AlgebraicGeometry.FundamentalGroup.Connected`, and
`Sheaf.CategoryTheory.Galois.GaloisTransitive`.
The Basic and Connected modules remain available through the public imports of
OpenSubgroups; their mathematical interfaces are still used.

The direct node dependencies `lem-galois-aut-profinite`,
`lem-weil-valued-dvr-finite-quotients`, and `lem-galois-transitive` are unnecessary for
this proof. The group is already profinite. Congruence kernels are open by continuity
and finite-basis evaluation; an open subgroup of a compact group has finite index, so
finite residue-ring quotients are unnecessary. The existing finite G-set realization
already gives the equivariant fibre bijection, and transitivity of the regular quotient
action proves connectedness directly. Corresponding obsolete `tool_uses` were removed.
No upstream declarations or modules were removed.

The comparison with a second stable lattice in proof step 4 is unnecessary: the current
finite-matrix witness applies directly to the integral basis of the chosen lattice.
The unit's detecting-cover route is retained.

## Where the brief, the DAG or earlier work was wrong

The planned proof described invariant-subspace descent without an existing declaration
for that step. The new proved lemma supplies it. A projection-matrix formula replaces
echelon coordinates: the restricted action has matrix P rho(g) J, so adjoining the finite
entries of P and J suffices. This is the same finite-coordinate descent argument.

The DAG's compactness, lattice-comparison and finite-residue-quotient steps were stronger
than needed by the available interfaces; its proof and dependencies now match the Lean.
No existing statement or definition was changed.

## New nodes

`lem-zl-ladic-invariant-subspace-descent`, in
`dag/nodes/sec-deligne-laumon-general/lem-zl-ladic-invariant-subspace-descent.json`, records
`Representation.isLAdic_subrepresentation`. It is strictly the invariant-subspace step
of the original argument and is proved in this delivery. Zero subspaces are included.
No change record is needed because no existing interface was changed.

## Second reading by N2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
