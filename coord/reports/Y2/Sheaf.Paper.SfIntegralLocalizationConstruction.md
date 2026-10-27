## What changed

Reduced `WeilConjectures.sfIntegralLocalizationConstruction` to one finite-level
construction and qualitative integral comparisons. The original statement, hypotheses,
visibility and docstring remain unchanged. Its proof now constructs the finite family,
obtains ordinary integral recollement, obtains the normalized qualitative comparisons,
proves the two direct-image limit fields from existing existence and comparison
theorems, transports each of the five finite Tor interval estimates through its reduction
isomorphism, derives all five integral finite-Tor preservation clauses, and assembles
the original record.

Four private helpers are fully proved: `directImageLimit`, `amplitude_of_iso`,
`integralInterval_of_reductions`, and `integralFiniteTor_of_interval`.
The limit helper constructs each actual image limit from the existing theorem,
identifies its object with the recorded image, and retains all actual reduction maps.
The amplitude helper works directly with all module-sheaf tensor tests and representative isomorphisms.
The interval helper uses the actual inclusion applied to each natural reduction isomorphism.
The preservation helper chooses one ordered interval, retaining constructibility from the output category.
The inequalities use nonnegativity of `2*d+c`, including `d=c=0`.

New module `Sheaf.Paper.SfPositiveFiniteLocalizationConstruction` states construction at
one positive quotient only. New module `Sheaf.Paper.SfIntegralLocalizationComparisons`
contains qualitative integral data and its realization theorem given a finite family
and ordinary recollement. Its record adds closed-pullback reduction to the existing
qualitative fields, without a Tor field or image-limit existence field. The record is actual data with no proof hole
in a definition; the existence theorem is a named public hole. No operation is defined
by choosing an arbitrary existence witness. Finite witnesses are chosen only locally
inside the original existential proof.

All work is in the sandbox. No adopted source-library declaration or existing definition
is edited. The original `SfIntegralLocalization` and `SfFiniteLocalization` records stay
verbatim. Their existing consumers need no adaptation. The theorem signature is identical; its local instance/options setup has a change record,
so `SfLocalizationAllStages`, the sole direct user of the theorem, has the same input.
Validation: the first set compile found a universe constraint while elaborating the
new comparison record. As in the existing ordinary-recollement module, two overly
general completed-coefficient instances are disabled locally. The corrected set is
queued with `lcompile.py --all`. Added DAG edges were checked and introduce no cycle;
`import_direction.py may` confirms the ordinary-recollement import is allowed.

## Proved and sorry left

Original item holes: 1. Original holes closed syntactically: 1. Holes added: 2.
This is a decomposition, with net hole change +1, not a completed proof from standard
axioms. The original theorem has a complete combining proof, and both image-limit fields and all ten uniform
integral Tor fields are derived there rather than deferred.

- Closed: `WeilConjectures.sfIntegralLocalizationConstruction`, node
  `lem-sf-integral-localization-construction`.
- Added hole: `WeilConjectures.sfPositiveFiniteLocalizationConstruction`, node
  `lem-sf-positive-finite-localization-construction`.
- Added hole: `WeilConjectures.sfIntegralLocalizationComparisons`, node
  `lem-sf-integral-localization-comparisons`.

The comparison-data structure has zero holes. The four private helpers have zero holes.
`sfIntegralOrdinaryRecollement_realization` is an existing dependency with a hole,
left unchanged. All other existing dependency holes are unchanged. No new hole is
inside an operation, instance, record field, anonymous declaration, or partial proof.

## No longer needed

The direct imports removed from the assigned module are:

- `Sheaf.Paper.FiniteKernelConstructibleLocalization`
- `Sheaf.Paper.SfIntegralOrdinaryRecollementRealization`
- `Sheaf.Paper.SfExceptionalReductionTransitions`
- `Sheaf.Paper.FiniteExceptionalSiteNormalization`
- `Sheaf.Paper.SupportedTorReductionPropagation`
- `Sheaf.Paper.ImmersionResidueTorIntervals`
- `Sheaf.Paper.ProEtaleOpenResidueTorBound`
- `Sheaf.AlgebraicGeometry.OpenGeneralFieldUniformBound`

Their mathematics remains in the two construction obligations or in the explicit
ordinary-recollement application; no existing module or node is withdrawn. The new combining proof imports its two construction obligations,
`Sheaf.Paper.SfIntegralDirectImageConstructible` and the Noetherian geometry API. The nine original direct
proof dependencies are replaced in the parent by the finite constructor, ordinary
recollement qualitative comparison and integral direct-image nodes. All nine remain reachable through those
nodes. The general supported-Tor propagation theorem is not needed to transfer uniform
integral intervals here: that step is proved directly, from definition and natural
reduction isomorphisms. Its finite exceptional-bound argument remains part of the
finite constructor, so no global pruning count is claimed. No unit statement or step
is bypassed, including the ordinary open/closed Hom argument.

## Where the brief, the DAG or earlier work was wrong

The original plan already noted two actual interface gaps. The finite exceptional
normalization theorem has a finite-field datum, whereas the assigned statement allows
arbitrary fields. The finite constructor explicitly retains the task of reproducing
its Hom-adjunction normalization using the arbitrary-field torsion site comparison;
it does not falsely apply the finite-field theorem. The immersion residue interval
lemma has `E : Type (u+1)`, whereas the intrinsic records have `E : Type u`.
Its realization/universe bridge stays explicitly in the finite constructor.

The original integral record stores closed image, open image, open pullback and
exceptional reduction, but no closed-pullback reduction. The uniform closed-pullback
Tor field needs that comparison too. The auxiliary comparison record explicitly adds
it; the original public record does not change.

The generic supported-Tor theorem requires a large setup with all six adjunction
normalizations and both stages. Once finite bounds and the actual reduction
isomorphisms are supplied, the integral interval transfer is elementary and strictly
shorter directly. This is the proved part of this delivery.

Duplicate searches covered the DAG, current blueprint, and both Lean roots.
`lem-sf-finite-kernel-constructible-localization` supplies ambient operations and
constructibility but not the specified exceptional comparison or quantitative Tor
fields. `lem-sf-finite-exceptional-site-normalization` has the finite-field mismatch
and does not give the whole finite record. `lem-sf-supported-tor-reduction-propagation`
assumes operations and reductions; it does not construct them. The new integral
comparison theorem assumes both finite records and ordinary recollement and excludes
all quantitative Tor claims; the original item constructs both stages and proves
those claims. Thus neither new hole restates the item. The new qualitative data
record is the smaller comparison interface used in this proof, not another definition
of any coefficient category or geometric operation.

No false statement or target change was found. The current blueprint source was read.
Empty pieces, zero inputs, positive exponent one, and the zero cohomological-dimension
bound were checked in the natural-language proofs; the integral arithmetic proof also
covers them without additional hypotheses.

## New nodes

`lem-sf-positive-finite-localization-construction`: one positive finite level, including
its conditional finite Tor fields; no integral operation or reduction compatibility.

`def-sf-integral-localization-comparison-data`: qualitative integral operation
and comparison fields for an input finite family, plus closed-pullback reduction;
no limit-existence or Tor assertion.

`lem-sf-integral-localization-comparisons`: qualitative integral construction from a
supplied finite family and ordinary integral recollement, including the normalized
counit and open-unit equations; no image-limit or integral quantitative Tor field.

All three nodes carry source places, complete proof plans where applicable, actual
Mathlib search records, and their Lean signatures. `citations.json` records verbatim
statement evidence for each proof dependency. Change record: `coord/changes/Y2-integral-localization-elaboration.md`. It lists
all 40 transitive importers and the unchanged-interface consumer check. The two
instance removals and elaboration options follow the existing ordinary-recollement
module and are included for independent review.

## Second reading by Y2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
