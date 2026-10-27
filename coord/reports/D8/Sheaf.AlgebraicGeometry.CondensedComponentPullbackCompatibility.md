## What changed

Replaced the single hole in `condensed_component_pullback_compatibility` by a Lean
assembly of the original HRS argument. Its statement and public imports stay unchanged.
The proof lifts the monoidal point comparison to coefficient monoids, obtains the
normalized realization square, supplies triangulatedness from exact derived pullback,
and extracts the unit isomorphism from the derived monoidal structure.

Added three smaller compatibility obligations, each in its own module. Added proved
transport of perfect complexes along a ring isomorphism, a lisse-equivalence assembly
from the existing contractible evaluations, and composition of the scalar comparison.
All proof imports are private. The existing node now records this route.

## Proved and sorry left

Closed the original one hole in
`AlgebraicGeometry.ProEtale.CondensedRing.condensed_component_pullback_compatibility`.
This is a decomposition, not a net proof: one original hole is replaced by three holes.
The item module contains zero remaining holes.

New remaining holes (each exactly `:= by sorry`):

- `AlgebraicGeometry.ProEtale.CondensedRing.component_point_monoidal_factorization`
  (`lem-zl-component-point-monoidal-factorization`): the monoidal natural factorization
  on abelian sheaves; it has no coefficient-ring or derived-category conclusions.
- `AlgebraicGeometry.ProEtale.CondensedRing.component_derived_symmetry`
  (`lem-zl-component-derived-symmetry`): braidedness of the fixed exact derived functor;
  it assumes a coefficient isomorphism and constructs neither the point factorization,
  section-ring square nor lisse equivalence.
- `AlgebraicGeometry.ProEtale.CondensedRing.component_section_realization`
  (`lem-zl-component-section-realization`): normalized section-ring identification and
  the two realization squares, assuming the monoidal factorization; it does not assert
  derived symmetry, triangulatedness, unit preservation or the lisse equivalence.

New proved declarations:

- `CategoryTheory.RingDerivedScalarExtension.ring_iso_perfect_scalar_equivalence`.
- `AlgebraicGeometry.ProEtale.CondensedRing.component_lisse_equivalence`.
- `AlgebraicGeometry.ProEtale.CondensedRing.component_final_scalar_comparison`.

The ring transport proof handles zero rings and independent derived localization
universes. The site compatibility statements include empty affine schemes and zero
coefficients; their prose proofs explain these cases. No data definition, axiom, target,
or existing declaration signature changes.

## No longer needed

No existing Lean imports were removed: the original module imported only its model.
No existing module is withdrawn. No source-library declaration is removed or changed.

The old direct dependency `lem-zl-condensed-component-inverse-image` is unnecessary:
the assigned statement already assumes the continuity, braidedness and exactness
structures it would supply. The old direct relative-site, geometric exactness, tensor
pullback, K-flat, tensor-descent, clopen-refinement, point-evaluation and constant-scalar
nodes are now dependencies of the three corresponding smaller compatibility lemmas.
They remain needed there and are not claimed as globally pruned. W-contractibility,
contractible tensor evaluation and contractible lisse evaluation remain used in the
proved lisse assembly. The profinite scalar compatibility remains used in the proved
final scalar assembly. The generic perfect-scalar transport replaces no adopted source
declaration and is proved directly from the module-equivalence and perfect-representative
APIs. No unit statement or step is bypassed.

## Where the brief, the DAG or earlier work was wrong

All seven packet modules compile through lcompile.py --all; the updated dependency
graph has no cycles. Explicit functor associators are required in the lisse inclusion
comparison.

No disputed statement or definition repair. The previous node combined the monoidal
site factorization, derived braiding and normalized realization comparisons into one
obligation without the intermediate interfaces needed by this Lean assembly. This packet
separates those actual steps and proves their lisse and scalar consequences. It preserves
the scalar normalization introduced by Q3, including the specified unit section.

## New nodes

`lem-zl-component-point-monoidal-factorization` records Construction (4.1) at the level
of the actual abelian inverse-image functors.

`lem-zl-component-derived-symmetry` records the exact derived tensor and Koszul-braiding
step for the actual component module functor.

`lem-zl-component-section-realization` records the normalized section-ring and point
realization comparisons from HRS Remark 3.2 and Proposition 4.3(3).

`lem-zl-ring-iso-perfect-scalar-equivalence` records the proved termwise transport of
bounded finite-projective representatives and uniqueness of the derived left adjoint.

`lem-zl-component-lisse-equivalence` records the proved conjugation by the two
contractible evaluation equivalences, with the inclusion comparison spelled out.

`lem-zl-component-final-scalar-comparison` records the proved composition of the scalar
comparison isomorphisms. There are no change records because no existing interface changes.

## Second reading by D8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
