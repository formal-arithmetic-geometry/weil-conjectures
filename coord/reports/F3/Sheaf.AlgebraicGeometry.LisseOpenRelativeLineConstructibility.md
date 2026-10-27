## What changed

Proved the lisse open relative-line constructibility theorem from constant-coefficient
constructibility, finite étale filtration, trace, and the two-open extension-by-zero
short exact sequence (the sheaf-level Mayer–Vietoris argument).
The declaration's signature and public imports are unchanged. The private proof
API and scoped instance commands are documented in
`coord/changes/F3-lisse-open-relative-line-private-proof-api.md`.

The proof first treats affine smooth relative curves and prime-torsion sheaves.
It assembles the constant filtrations on the finite étale cover's disjoint affine
components and descends along the trace retraction. Induction on a positive
annihilator, using the kernel–image sequence for multiplication by a prime,
handles arbitrary finite coefficients. A finite affine cover and
Mayer–Vietoris then give the requested open relative affine line.

Private object-property helpers assemble short-exact-sequence triangles, quotient
isomorphisms, and finite sums. Private irreducible functors name compact support
and its composite with the degree-zero inclusion. Their generic composition and
exact-sequence APIs avoid repeatedly unfolding derived-category data. Private
instance-reducible names for the canonical abelian and derived-category structures let the helpers share those structures,
avoiding repeated kernel comparisons of independently generated instances.
The instance attributes are confined to the private section; the public theorem's
statement is elaborated with the original instances.

## Proved and sorry left

Closed: `AlgebraicGeometry.Etale.isConstructibleEtaleModuleSheaf_lisse_openRelativeLine_shriek`.

Added: none. Remaining holes in the delivered module: zero.
No intermediate theorem is split off.

## No longer needed

Removed direct imports:

- `Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle`
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`
- `Mathlib.AlgebraicGeometry.Noetherian`
- `Sheaf.AlgebraicGeometry.EtaleConstantModuleDirectImageLeftExact`
- `Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives`
- `Sheaf.Paper.ProjectionCompactification`
- `Sheaf.AlgebraicGeometry.EtaleShriekRelativeMayerVietoris`
- `WeilConjectures.AlgebraicGeometry.FiniteEtaleModuleTraceDegree`
- `WeilConjectures.ConstructibleSheaf.KernelCokernel`
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus`
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`

Most source-library imports are redundant public dependencies of the retained
imports. Their declarations and modules remain unchanged.

The existing filtration-devissage theorem is retained. A private generic adapter
converts the zero initial subobject and transports the quotient isomorphisms before
specializing to concrete sheaves.

`ProjectionCompactification` concerns a different interface and is unused here.
Direct-image left exactness and enough-injectives instances are already supplied
by the retained shriek API. The public trace-degree theorem is replaced only
within this proof by its algebraically closed stalk calculation. No source-library
declaration is removed. No module is withdrawn. The relative Mayer–Vietoris
declaration is replaced here by `EtaleOpenCoverShriekNaturalSES`: its short exact sequence gives the same
triangle after the degree-zero inclusion and compact support. This avoids a
separate transport of the derived restriction vertices. The unit route is preserved.

The proof does not need these planned nodes as separate inputs:

- `lem-weil-pbc-etale-shriek-relative-mayer-vietoris`: the natural sheaf short
  exact sequence supplies its required triangle directly.
- `lem-weil-pbc-open-relative-line-principal-geometry`: compactness gives a finite
  affine cover, and separatedness gives affine intersections. Principal opens and
  their polynomial descriptions are unnecessary.
- `lem-weil-pbc-finite-etale-shriek-transfer-retract`: the proved generic
  composition API, finite exactness, and the explicit trace retraction give this
  special prime-annihilated case directly. The more general prime-power version
  is unnecessary after prime-factor induction.

The two latter nodes have no Lean attachments in the current shared snapshot.
Their mathematical steps are implemented here using the existing declarations.
They realize no fixed unit step. No source declaration or module is withdrawn.

Validation: the complete module compiled cleanly through `lcompile.py` in 35.5 seconds.
Its one original hole is closed, with no new holes, and its public signature is
textually identical to the shared source.

## Where the brief, the DAG or earlier work was wrong

The filtration theorem specifies fibre cardinalities over algebraically closed
fields, whereas the public trace-degree theorem assumes cardinalities over all
separably closed fields. The private trace argument reuses the existing reverse
adjunction and geometric-stalk calculation, which needs only algebraically
closed points. It does not change either public declaration.

The primary-idempotent decomposition planned in the DAG is unnecessary:
prime-factor induction through finite locally constant kernels and images
reduces directly to sheaves killed by one prime.

## Second reading by F3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
