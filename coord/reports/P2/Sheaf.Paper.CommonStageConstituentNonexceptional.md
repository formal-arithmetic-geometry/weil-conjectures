## What changed

Filled all four proof holes in `Sheaf.Paper.CommonStageConstituentNonexceptional`.
All existing signatures, definitions, docstrings, and public imports are preserved.
The node is `def-a1-constituent-nonexceptional`; it is a definition node with no
numbered proof steps or declared proof dependencies. Its unit route is unchanged.

- `sfFourierCharacterScale_existsUnique`: multiplicative shifts of the trace character
  are injective by `AddChar.compTrace_ne_one`,
  `AddChar.IsPrimitive.of_ne_one`, and `AddChar.to_mulShift_inj_of_isPrimitive`. Distinct characters are linearly
  independent as functions, so their number is at most the field cardinality.
  The injection is therefore surjective, giving existence and uniqueness, including
  the trivial base-field character.
- `sfAffineLine_curve`: affine space is smooth of relative dimension one. The
  nonempty smooth-dimension theorem computes its dimension. Its unique irreducible
  component is the whole line, so that dimension is pure.
- `sfAffineOpen_geometry`: density makes the arithmetic open nonempty. The map from
  the geometric field spectrum is surjective, and its pullback remains surjective,
  making the geometric open nonempty. Its finite-type structure morphism gives
  local Noetherianity and quasi-compactness gives compactness. The base field maps
  injectively into the nonzero global-section ring, transferring characteristic p.
- `sfAffineLinearArtinSchreier_mem`: use the existing explicit integral representative
  at `fourierCoefficientStage`. It is a derived single object in degree zero, so
  the standard derived-category vanishing lemmas give both standard heart bounds.
  Rationalization and common-stage inclusion are the defining representatives.

Added only non-public proof imports: `Mathlib.LinearAlgebra.LinearIndependent.Lemmas`
and `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth`. Existing public
imports already provide induced trace characters and the derived t-structure.
The final single-file compile passed without warnings. The required delivery dry
run additionally checks every declaration and its axioms.

## Proved and sorry left

Closed 4 original holes, all under `def-a1-constituent-nonexceptional`:

- `WeilConjectures.sfFourierCharacterScale_existsUnique`
- `WeilConjectures.sfAffineLine_curve`
- `WeilConjectures.sfAffineOpen_geometry`
- `WeilConjectures.sfAffineLinearArtinSchreier_mem`

Zero direct `sorry` remain in the item; zero holes added; zero results split off.
Existing dependency theorems, including `fourierAdicArtinSchreier_mem`, are reused
without modification. This delivery does not claim to close their own holes.

## No longer needed

No original imports, declarations, nodes, or modules are removed or pruned.
No new intermediate theorem is needed. The experimental broad import
`WeilConjectures.AlgebraicGeometry.AffineSpace.Line` was replaced by the specific
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth` proof import: no
Noether normalization or affine-curve reduction is used.
The definition node has no listed proof dependencies to prune.

## Where the brief, the DAG or earlier work was wrong

No mathematical defect in the statements was found. The empty-open case is
excluded by density; the whole-line case and arbitrary geometric scalar a remain
included. The heart proof also handles zero a and trivial Psi because the
construction is a degree-zero object for every character and function.

The interrupted packet had an outdated completion report: the geometry proof was
still missing, and the resumed compile identified missing local instances for the
finiteness of the character type and nonemptiness of the affine line. These are now
supplied by linear independence and the standard affine-space instances. Compactness
is supplied explicitly through `QuasiCompact.compactSpace_of_compactSpace`; no
definition or interface change and no increased compile limit is needed. The final
compile completed cleanly in 18.8 seconds.

## Second reading by P2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
