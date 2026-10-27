## What changed

Proved `AlgebraicGeometry.exists_nestedOpen_regular_alteration` from the current
three geometric dependency declarations, without changing its statement or public
imports. Added proved private helpers for canonical generic-stalk maps and finite
composition, and for identifying the displayed SNC divisor family with the
irreducible components of the boundary support. The final degree is the finite
etale rank at the generic point; local constancy on the integral open makes it
constant, and surjectivity makes it positive.

## Proved and sorry left

Closed one original hole:
`AlgebraicGeometry.exists_nestedOpen_regular_alteration`
(node `lem-sfb-nested-open-regular-alteration`).
No holes added; no `sorry` remains in the delivered module. The proof uses the
existing declared geometric results, including
`AlgebraicGeometry.Scheme.Hom.exists_generic_radicial_etale_factorization`,
whose independent proof remains its own item. This is a proof from existing
stated dependencies, not a new decomposition.

Validation: the complete module passed single-file compilation through `lcompile.py`
(exit code 0, 9.7 seconds). Delivery preflight also checks compilation and declaration axioms. Empty boundaries, zero components,
coincident nested opens, and degree one are preserved by the construction.

## No longer needed

The obsolete direct imports from the old seven-step plan were replaced by the
three current geometric dependencies. Removed proof imports:

- `WeilConjectures.AlgebraicGeometry.WeilPbcNormalizationInResidueFieldExtension`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Normalization`
- `Mathlib.AlgebraicGeometry.Normalization`
- `WeilConjectures.Blowup.AdmissibleBlowup`
- `Sheaf.AlgebraicGeometry.NagataBoundaryDivisorCartier`
- `WeilConjectures.Blowup.BlowupUniversal`
- `WeilConjectures.Blowup.Complement`
- `WeilConjectures.Blowup.Proper`
- `WeilConjectures.AlgebraicGeometry.Regular`
- `Sheaf.AlgebraicGeometry.RegularNormalDecomposition`
- `Sheaf.RingTheory.RegularLocalUFDBoundaryFactorization`
- `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible`
- `Sheaf.AlgebraicGeometry.Morphisms.GenericFiniteOpenNeighborhood`
- `WeilConjectures.AlgebraicGeometry.LocalizedSeparablePolynomialModel`
- `WeilConjectures.AlgebraicGeometry.SpreadPurelyInseparableFactors`
- `Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant`
- `Mathlib.FieldTheory.PurelyInseparable.Basic`
- `Mathlib.FieldTheory.PrimitiveElement`
- `Mathlib.RingTheory.Etale.StandardEtale`

These ingredients remain below the three geometric dependencies where needed;
no existing dependency node or source-library declaration is withdrawn. The
current six direct proof dependencies are retained. The prescribed factorization's
additional sheaf-rank and separable-closure-identification clauses are unused;
Mathlib's local constancy of `Scheme.Hom.finrank` suffices. No module is claimed
to be globally unreachable. `Mathlib.AlgebraicGeometry.Noetherian` is now supplied
by the public interface already present; its redundant direct proof import was
also removed.

## Where the brief, the DAG or earlier work was wrong

The original Lean docstring and imports describe the earlier seven-step plan;
the current DAG already packages it into the three declared geometric inputs.
Their interfaces require some assembly absent from the prose: an explicit lift
of the generic point into S, transport of finite field maps along the supplied
field-spectrum isomorphisms, identification of the divisor family with actual
irreducible components, and restriction of the generic field extension to opens.
All of that glue is proved privately in the item. No statement repair was needed.

## Second reading by P3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
