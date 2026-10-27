## What changed

Implemented the affine-coordinate part of
`AlgebraicGeometry.bertini_singular_fibre_polynomial_equations` and its final algebraic
argument, without changing its statement. The item privately imports
`Sheaf.AlgebraicGeometry.BertiniSingularFibreJetTensor`.

The new module `Sheaf.AlgebraicGeometry.BertiniSingularFibreCoordinates` contains a complete
proof, with no holes, of the following construction. Polynomial base change is a pullback,
using Mathlib's polynomial algebra pushout instance. The actual coefficient projection of
the singular fibre and its residue-field projection define a unique map to coefficient
affine space over the residue field. Pullback pasting and cancellation identify this map
as a base change of the composite of the two closed inclusions. It is therefore a closed
immersion. Mathlib then proves that the fibre is affine and its actual polynomial
coordinate homomorphism is surjective. Gamma-Spec naturality reconstructs the map from
that ring homomorphism. This construction does not use smoothness or invertibility.

The item takes its coordinate algebra to be the global sections of this actual affine
fibre. The scalar algebra structure is the coordinate homomorphism composed with `C`.
A proved private algebra lemma contracts a first-jet tensor relation against any linear
functional, obtaining the requested polynomial relations. Polynomial extensionality and
the proved projection identity give exactly the coefficient-morphism compatibility.

The local geometric calculation is isolated in the new module
`Sheaf.AlgebraicGeometry.BertiniSingularFibreJetTensor`. It fixes the actual coordinate
homomorphism and asserts just that the universal value-and-differential tensor vanishes.
Its docstring and node give the local-frame expansion, the one-way hypersurface criterion,
vanishing-ideal argument, and differential base-change argument. This is the original
node's local calculation (steps 2 and 3), not another existential presentation theorem.
Affineness, existence of the presentation, surjectivity, the isomorphism, contraction
against functionals, and the coefficient-map equality are all proved outside this hole.

Validation: all three modules compile via `lcompile.py`; the latest individual compile
of the item took 4.1 seconds. The coordinate module compiled in 5.0 seconds and the
jet-tensor statement in 3.5 seconds. No signature, definition, attribute, or public import
of any existing module was changed. Empty fibres, an empty section index type, zero
sections, cotangent rank zero, arbitrary residue fields, and nonaffine U are covered.
The construction does not assume the singular fibre is reduced: the reduced structure
is used before taking its potentially nonreduced scheme-theoretic fibre.

## Proved and sorry left

Original holes closed: one,
`AlgebraicGeometry.bertini_singular_fibre_polynomial_equations`
(node `lem-zl-bertini-singular-fibre-polynomial-equations`). The item's module now has zero
`sorry` declarations.

Holes added: one,
`AlgebraicGeometry.bertini_singular_fibre_jet_tensor`
(node `lem-zl-bertini-singular-fibre-jet-tensor`). This is the only remaining hole in the
three delivered modules. Its proof is exactly `by sorry`.

This delivery is a decomposition, with one hole closed and one added, net zero. It does
not claim a complete proof of the geometric vanishing step. The whole coordinate module,
including `bertini_singular_fibre_coordinates_isClosedImmersion`,
`bertini_singular_fibre_ringMap_surjective`, and `bertini_singular_fibre_ringMap_spec`,
and the item's private `polynomial_relation_of_jet_tensor` are fully proved.

## No longer needed

No existing imports, nodes, or modules are pruned. All original public imports remain.
The item's direct proof dependencies are now the proved coordinate construction and the
jet-tensor vanishing step. The old dependencies concerning the zero scheme, relative
differentials, smooth base change, locally free smooth differentials, and the hypersurface
criterion remain dependencies of the local geometric calculation; none is represented
as globally unnecessary. The first-jet spanning theorem and projective immersion
hypotheses are not used here, as already required by the original statement.

The new coordinate module imports `WeilConjectures.PointCount` privately for the geometric
characterization of `residueFieldAlgebraMap`, and Mathlib's ring pushout and polynomial
tensor-product modules privately for the polynomial base-change square. Its statement
imports are public. No unused proof import is retained.

## Where the brief, the DAG or earlier work was wrong

No false statement or unit-route departure was found. The original declared dependencies
supply the smooth hypersurface criterion and local freeness separately. They do not
already state the remaining sheaf calculation identifying the universal section's
value and differential, restricting them to the vanishing-ideal subscheme, and transporting
them to the specified cotangent fibre. That calculation is the one explicit remaining
hole. The affine-coordinate construction and the contraction argument require no
additional unproved statement.

The existing unit and latest blueprint route are preserved: this remains the Tag 0FD6
smooth Bertini input to the prescribed-point curve construction. No parent is withdrawn,
and no upstream declaration or module is changed.

## New nodes

`lem-zl-bertini-singular-fibre-coordinates` records the actual canonical coordinate map,
its two projection identities, its closed-immersion property, its surjective coordinate
ring map, and its Gamma-Spec reconstruction. Its module is
`Sheaf.AlgebraicGeometry.BertiniSingularFibreCoordinates`, with no holes.

`lem-zl-bertini-singular-fibre-jet-tensor` records only the remaining universal-jet
vanishing calculation in the actual ring of sections tensored with the cotangent fibre.
Its module is `Sheaf.AlgebraicGeometry.BertiniSingularFibreJetTensor`. It retains the
original local geometric dependencies and explicitly cites the existing relative
differential sheaf base-change theorem and reduced vanishing-ideal construction.

Both nodes contain source citations, full natural-language proofs, searches, Lean
attachments, and the original chapter, unit, and blueprint ancestry. The item's node
is updated only in `proof`, `proof_deps`, and `proof_origin`. No change record is needed:
all added interfaces are new modules, and all existing signatures remain identical.

## Second reading by K2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
