## What changed

The ordinary-complex comparison is constructed by uniqueness of limit cones.
`RingedHomComplexColimitCone` supplies the canonical Hom cone of any sequential
colimit. `RingedKoszulFiniteEvaluation` isolates finite-stage evaluation and its
coefficient, transition and unit compatibilities. The item postcomposes the Hom
cone by finite evaluation, compares it with the degreewise strict-tower limit,
and proves naturality and the unit equation by its projections.

Existing public declaration signatures and public imports are unchanged. No
source-library declaration or target statement is changed. New proof imports are
private imports of the two intermediate modules and the Mathlib complex-limit API.

## Proved and sorry left

The general theorem `CategoryTheory.ringedHomComplexColimitCone_isLimit`
is proved with no new hole. Its final module compiled in 37.3 seconds.
The finite-stage obligation remains exactly one named hole:
`CategoryTheory.exists_ringedKoszul_finiteEvaluation`, node
`lem-weil-pbc-ringed-koszul-finite-evaluation`.

The original hole
`CategoryTheory.exists_ringedKoszul_colimitHom_ordinaryLimit_iso` is closed by a
complete combination proof using that finite-stage obligation. The item has zero
holes left; the delivery closes one original hole and adds one hole, named above.
This is a one-hole decomposition, not a net hole reduction. No hole occurs in a
definition or private declaration.

## No longer needed

No original import, node or module is pruned. The new general cone module uses
`RingedExtendedCech` for the existing complex abbreviation and `HomComplex` for
its statement; it does not import `RingedKoszulSystem`. Both original declared dependencies
remain needed: the actual Koszul system and the Hom-complex construction. No
K-injectivity, derived inverse-limit acyclicity, localization or restriction
comparison is used in this ordinary-complex argument.

## Where the brief, the DAG or earlier work was wrong

The original plan is mathematically sound, but its two stated dependencies are
construction APIs, not the finite evaluation or Hom-colimit universal-property
theorems. The delivery exposes those two strictly separate mathematical steps.
The finite-stage theorem contains no colimit or limit, and the general cone
theorem contains no Koszul or finite-free hypothesis and no unit normalization.
Thus neither repeats the parent statement. The existing
`RingedSiteBoundedEvaluation.assembly` and module finite-free evaluation APIs
provide a route for the finite-stage obligation, but they do not state its
Koszul boundedness, source transition or unit-normalization clauses.

The source check used the current blueprint and the Stacks source. Tag 0A0A
states the derived result; the ordinary-complex refinement is the parent node's
explicit plan, using its Hom-of-colimit and finite-duality arguments. Empty
lists, zero generators and invertible generators require no additional hypothesis.

## New nodes

`lem-weil-pbc-ringed-hom-complex-colimit-cone` records the general sequential
Hom-colimit cone and its degreewise universal-property proof. Its two public
declarations are in `Sheaf.CategoryTheory.RingedHomComplexColimitCone`.

`lem-weil-pbc-ringed-koszul-finite-evaluation` records finite Koszul evaluation as
an inverse-diagram isomorphism natural in coefficients, with its finite-stage
augmentation equation. It is in `Sheaf.CategoryTheory.RingedKoszulFiniteEvaluation`.

Validation: the import-order check compiled the general cone module and
finite-stage statement in 37.3 and 4.5 seconds. The parent compiled in 34.8 seconds;
a redundant `change` identified by its unused-tactic warning was then removed.
The delivery check recompiles the packet. Both new parent imports pass the
import-cycle check. The private abstract cone proof avoids unfolding the sheaf
constructions. The concrete application uses the existing parametrized tensor-Hom
adjunction. The parent keeps large construction definitions locally irreducible
and unfolds only their small aliases at the component calculations.

No change record is required: no existing statement, definition or public import
changes.

## Second reading by V4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
