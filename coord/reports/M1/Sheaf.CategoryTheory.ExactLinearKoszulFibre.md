## What changed

Replaced the sorry in `CategoryTheory.exists_exactLinear_signedKoszulFibre` by a
matrix/projection proof and explicit localization descent, preserving its statement
and all existing public definitions and imports. Added proof imports for homological
complex limits, additive biproduct comparisons, and the one-site model construction.

The proof first conjugates `F.mapBiproduct` by the two finite coordinate isomorphisms.
`finiteCompare_matrix` reduces chain and naturality equations to the specified
matrix entries. A-linearity proves the scalar equations. The canonical product
comparison gives preservation of `Discrete ℕ` limits; product universal properties
construct beta and its inverse. Binary biproduct comparison gives the fibre map;
its differential is checked at both projections, including the degree cast. The
empty-subset inclusion equation and zero second coordinate prove the strict unit
identity. The same chain comparison for the identity functor compares any two models.

`SignedKoszulModelExists` constructs the actual countable product, shift, diagonal,
two-coordinate fibre and unit from finite tensor data. Its differential squares to
zero by the chain equation of `1-shift`. The localized product is a limit by
`derivedCategory_termwiseProduct_isLimit`; the inverse of the localized product map
is constructed from inverse level maps. `quasiIso_of_roos_coordinates` then gives
quasi-isomorphism preservation of the fibre.

The completion functors and their units descend by `Localization.lift` and
`Localization.liftNatTrans`. Fully faithful precomposition by Q descends the chain
isomorphism. The factorization equations and localization faithfulness prove the
derived unit equality on every derived object; its isomorphism consequence follows
by composition. All auxiliary data constructions are explicit and all private
helper theorems are proved. The finite data are determined by their normalization:
the pure-tensor summand equation fixes every coordinate inverse, the matrix equations
fix the transitions and inclusions, and no arbitrary existence witness defines data.

## Proved and sorry left

Original hole closed: `CategoryTheory.exists_exactLinear_signedKoszulFibre`
(node `lem-cbc-exact-linear-koszul-fiber`), 1 of 1 in the item module.

Also proved: `CategoryTheory.exists_ringedSignedKoszulCompletionModel`
(node `lem-cbc-signed-koszul-model-exists`).

Added hole: `CategoryTheory.exists_ringedSignedKoszulFiniteCoordinates`
(node `lem-cbc-signed-koszul-finite-coordinates`), exactly one named public theorem
whose proof is `by sorry`. It states only the finite ordered tensor expansion,
its pure-tensor normalization, transition/inclusion equations and finite tensor
quasi-isomorphism preservation. It has no products, fibre, localization or
coefficient-functor comparison. Its docstring gives the finite-factor induction,
transition coefficient calculation, and finite-filtration proof in words.

This is a decomposition: 1 original hole closed and 1 lower hole added, net zero.
The comparison, product/fibre construction and localization assembly are complete
Lean proofs from that separate finite calculation. No hole is inside a definition.

Validation: the finite-coordinate statement compiles, and the complete one-site model
construction compiles without warnings in 7.1 seconds through `lcompile.py --all`.
The final sandbox-wide check compiles all three modules without warnings; the
comparison item takes 30.6 seconds. The unused countable-product section instance
was removed from the generic comparison helpers.

## No longer needed

No original public import is removed. No module is withdrawn.

The item's direct proof dependencies on `def-pur-sheaf-tensor-product` and
`def-pc-tensor-complex-sheaves` move to the finite-coordinate construction node.
Those notions remain needed there; this delivery does not claim them globally pruned.

The item's direct dependency on `lem-sbc-koszul-fibre-linear-descent`
(`Sheaf.CategoryTheory.KoszulFibreLinearDescent`) is unused: its Lean declaration
uses the earlier internal-Hom dual tower, whereas the assigned model uses actual
ordered negative two-term tensor factors and normalized pure-tensor coordinates.
The explicit product/fibre construction and finite tensor lemma provide precisely
the required model and quasi-isomorphism invariance. No proof import of
`KoszulFibreLinearDescent` is added. Its obsolete parent `tool_uses` entry is removed.
Its other consumers remain untouched.

No extra Roos chain-comparison theorem is imported: the supplied coordinate axioms
allow the direct matrix/projection proof in this item. The derived countable-product
and Roos-coordinate quasi-isomorphism results are used in the construction module.
Its `split_report.tool_uses` records both as generic tools from other units.

## Where the brief, the DAG or earlier work was wrong

The prose descent statement is mathematically appropriate, but its current Lean
attachment does not expose an isomorphism to `ringedNegativeKoszulTensor` or the
specified pure-tensor normalization. Applying it directly would leave an unstated
finite-tensor identification. The new finite-coordinate lemma isolates that exact
calculation; it does not repackage the two-site comparison theorem.

Edge cases were checked against the formulas: r=0 has only the empty coordinate
and identity transitions; r=1 has scalar differential (-1)^(q+1) a_0^(m+1) and
transition a_0 on its negative coordinate. Zero scalars, unit scalars and zero rings
require no inversion. Products and biproducts use their universal properties, so
zero categories and empty sites are allowed. No boundedness is imposed on K.

No statement, definition, universe, visibility, or target signature is changed.
The unit's route stays intact. There are no forced adaptations. Preflight requested a record for the added private
proof-section commands; see `coord/changes/exact-linear-koszul-proof-sections.md`.
The three existing public declarations and their signatures remain unchanged.

## New nodes

`lem-cbc-signed-koszul-finite-coordinates`, realized by
`Sheaf.CategoryTheory.SignedKoszulFiniteCoordinates`: the genuinely finite tensor
calculation from Stacks 0A0E and the signed refinement of the parent proof.

`lem-cbc-signed-koszul-model-exists`, realized by
`Sheaf.CategoryTheory.SignedKoszulModelExists`: a proved construction of the
normalized completion model from the finite data, with explicit product/fibre maps,
unit, and quasi-isomorphism preservation. Both nodes retain the parent's chapter
and unit, and the parent node records the actual Lean argument.

Change record: `coord/changes/exact-linear-koszul-proof-sections.md` documents only
the added namespace, section variables, universes and local elaboration options
required by the private proof helpers.

## Second reading by M1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
