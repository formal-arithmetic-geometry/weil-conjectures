## What changed

Proved `AlgebraicGeometry.smooth_iff_regularLocalRing_finitelyGenerated_field_baseChange`
with its original signature and public imports unchanged. Added five proved private helpers
in the same module for algebraic separability, the residue-field rational-point argument,
regularity along open immersions, regularity of smooth schemes over fields, and the converse
on an affine chart. No other Lean module is changed.

The forward implication uses scheme base change of smoothness, affine charts, the declared
`Algebra.smooth_over_field_regular_local`, and isomorphisms on stalks. For the converse,
`AlgHom.liftEquiv` constructs the multiplication map from the residue-field tensor product.
Its kernel contracts to the original prime. `Ideal.ResidueField.liftₐ` embeds its residue
field into the base field, proving the needed separability directly. The declared
`Algebra.regularLocal_iff_smoothAtPrime` and
`Algebra.isSmoothAtPrime_of_fieldExtension` then give smoothness at the original prime.
Mathlib's algebraic smooth locus assembles these local results, and its source-local
criterion assembles the affine charts.

Updated only the item's proof, proof dependencies, proof origin, and obsolete tool-use entry
in its DAG copy. The fixed proper-base-change unit route is unchanged.

Searches before proving: Lean Finder returned smooth-algebra base change/composition and
finite-type model lemmas, but no matching criterion; Loogle with `"Smooth",
"IsRegularLocalRing"` returned zero results. The server grep search for
`geometrically.?regular|smooth.*isRegular|isRegular.*smooth` returned zero results.
Source searches found the perfect-field
converse elsewhere, which does not apply to an arbitrary base field; the declared
separable-residue and field-extension descent criteria do apply. Read the local Stacks
proofs of Tags 038X, 00TV, and 02UQ.

Validation: the complete proof compiled, then the pruned module compiled cleanly through
`lcompile.py` (9.8 seconds of compiler time). All lines have at most 100 characters.
The first dry run flagged a new global tensor-notation scope command as a visibility
change. Removed that command and wrote the tensor expressions with explicit names;
no interface change or change record is needed.
The tensor construction uses the actual residue field in the given universe, so the
finite-generation hypothesis applies without any change of universe or extra hypothesis.
The source-local cover argument also handles the empty scheme.

## Proved and sorry left

Closed 1 original hole:
`AlgebraicGeometry.smooth_iff_regularLocalRing_finitelyGenerated_field_baseChange`
(node `lem-weil-pbc-geometric-regularity-smooth-field-criterion`).

Added 0 holes; split off 0 statements. No `sorry` remains in the delivered module.
All five private helpers are proved. Imported declarations retain their existing proofs
and dependency obligations; this delivery does not claim to close those obligations.
A separate `#print axioms` check reports `propext`, `Classical.choice`, `Quot.sound`,
and inherited `sorryAx`, as expected when using existing unfinished dependency proofs.

## No longer needed

Removed direct proof imports:

- `WeilConjectures.AlgebraicGeometry.AffineChartBaseChangeIso`: the standard affine
  fibre-product isomorphism and `pullback.map` give the needed open immersion directly.
- `Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties`: already available through
  the smoothness imports.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: already available through affine schemes.
- `Mathlib.RingTheory.Smooth.Basic`: replaced by `Mathlib.RingTheory.Smooth.Locus`.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: already available through the
  retained residue-field and smoothness imports.
- `Mathlib.RingTheory.TensorProduct.Maps`: the required `AlgHom.liftEquiv` is in Basic.
- `WeilConjectures.FieldTheory.SeparableExtension`: re-exported by the retained
  separable-residue criterion; its definition is still used.

The following planned dependencies are not needed by this proof and are removed from
its `proof_deps`:

- `lem-weil-pbc-affine-chart-base-change-iso` and its module above; also removed its
  obsolete top-level tool-use approval entry.
- `lem-weil-pbc-smooth-ring-map-base-change-composition`: the forward implication
  invokes scheme-level smooth base change directly.
- `lem-weil-pbc-principal-localization-open-immersion`: the algebraic smooth-locus
  API assembles the principal localizations before passing back to schemes.

Reused the existing Mathlib leaf `lem-weil-pbc-fibre-product-affine-spectra` instead
of the specialized affine-chart comparison. Added the existing Mathlib leaf
`lem-weil-pbc-finite-type-noetherian-finite-presentation` to record the finite-presentation
hypothesis required by the smooth-locus API. No globally unreachable module is claimed:
the pruning listed here is of this item's proof dependencies.

## Where the brief, the DAG or earlier work was wrong

No false statement or unusable declared dependency was found. The existing proof plan
can be formalized without new obligations. Its explicit residue-field isomorphism and
principal-open scheme cover are unnecessary: an embedding into the base field suffices
for separability, and Mathlib already assembles the algebraic smooth locus. The standard
affine fibre-product isomorphism suffices in place of the specialized chart theorem.

## Second reading by H4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
