## What changed

Reduced `AlgebraicGeometry.Scheme.qbarCompactSupportBaseChange` to construction
of its normalized model and proved all its universal conclusions for every model.
Finite-stage invertibility follows by applying
`completeCompactSupportProetale_isIso` to the actual completed integral exchange,
reflecting its isomorphism through the full subcategory and preserving it under
rational localization. This avoids transport from the unlifted valuation-ring
presentation of `finiteExtension_compactSupportBaseChange` to the canonical small
coefficient model. The endpoints and arrow are identified by `source`, `target`
and `normalized`; completeness is supplied by `wfConstructible_complete`.
The generic stage-system component/inclusion formulas and `Hom.comm` give the
overfield representative. Descended naturality identifies both conjugated maps
with the component at the fixed input object.

Extracted the seven public model/scalar definitions unchanged into
`Sheaf.Paper.QbarCompactSupportExchangeModel`, publicly reexported by the item.
This permits the new construction theorem to import the model without a cycle.
Change record: `coord/changes/N4-qbar-compact-support-model-extraction.md`.
The extraction preserves every signature, data body and consumer; only blueprint
tags identify the new definition node. No adopted source-library file is edited.
Local transparency attributes keep elaboration from expanding the large derived
functors; they do not change any exported attribute or definition.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.qbarCompactSupportBaseChange` (node `thm-cbc-qbar`).
The item now has zero holes. Its private helpers `cbcIsIso_of_heq`,
`cbcModel_stage_isIso`, `cbcDescended_atStage`, `cbcConjugate_naturality`
and `cbcDescended_properties`
have complete proofs.

Added one named hole:
`AlgebraicGeometry.Scheme.cbcQbarExchangeModel_exists`, in
`Sheaf.Paper.QbarCompactSupportExchangeModelExists`, node
`lem-cbc-qbar-exchange-model-exists`. It asserts only nonemptiness of the
normalized construction, not invertibility for arbitrary models or any of the
descent/representative conclusions. Its docstring and node give the complete
assembly argument using the existing normalized coefficient families. This is a
decomposition: 1 original hole closed, 1 lower hole added, net 0; no claim of an
axiom-free final theorem is made. The extracted definitions contain no holes.

Validation: all three modules compiled through the server compiler; the complete
parent proof compiled in 33.6 seconds during profiling. A subsequent delivery
compile exposed variable elaboration cost; the final assembly is therefore bounded
by a generic proved stage-system properties API, with local limit transparency.
Explicit category and stage-system arguments avoid expensive inference in the
final application. Bounding the scalar-localization category instances avoids
expanding their derived data; the final parent compiled cleanly in 10.3 seconds. Profiling
options were removed before delivery. The original public theorem signature was compared
verbatim with the source and is unchanged.

The direct assembly attempt obtained preservation, completion-unit and integral
localization fields from `rationalCompactSupportCoefficientCoherence`; the
remaining substantial glue is composition of the two normalized inverse-beta
specifications. The attempt also found shift-instance bookkeeping for the exact
composite families. Rather than retaining holes inside this construction, its
whole strictly smaller construction step is a named public theorem `:= by sorry`.

## No longer needed

Removed the item's private imports of `Sheaf.Paper.CommonStageCalculus`,
`Sheaf.Paper.FiniteStagePairCategory`, `Sheaf.Paper.IntrinsicQbarCategory`, and
`Sheaf.Paper.RationalCompactSupportCoefficientCoherence`. The finite-stage
interfaces remain available through public dependencies, and coefficient
coherence is retained by the new model-construction module.

The item's proof no longer calls `prop-weil-pbc-common-stage-calculus` or imports
its module directly: descended naturality already gives the required equality.
The explicit coefficient-model transport through
`thm-cbc-finite-extension` is unnecessary for invertibility: its integral-exchange
argument applies directly to the fixed canonical coefficient datum. Its module
remains a public statement dependency and is not withdrawn. The qbar category and
finite-stage pair-category definitions remain needed. No module is globally
withdrawn; no adopted declaration or completed upstream proof is pruned.
The obsolete top-level tool-use entries for common-stage calculus and direct
coefficient-coherence use are removed from the parent node, while the latter is
retained in the construction node's proof dependencies.

## Where the brief, the DAG or earlier work was wrong

The DAG's final common-stage lifting argument is longer than necessary for the
stated representative-independence equation: naturality of the already descended
transformation proves it directly. No mathematical statement was changed.

The newest blueprint snapshot no longer contains the old standalone
`thm-cbc-qbar` leaf; its current compact-support unit describes condensed
coefficient categories. This delivery preserves the assigned, reviewed raw PBC
statement and its existing category definitions, and follows its stored integral,
rational and common-stage unit route. The new nodes cite the current unit and
pinpoint the assigned node's existing construction steps; no target is silently
retargeted to the newer blueprint convention.

## New nodes

`def-cbc-qbar-normalized-exchange-model` records the extracted existing model and
its six scalar-comparison definitions. It introduces no duplicate construction.
Its Lean attachment lists all seven declarations; the parent attachment now lists
only its theorem. The parent's statement dependencies include this definition.

`lem-cbc-qbar-exchange-model-exists` isolates only the construction/nonemptiness
step (old proof steps 2--3). It uses the already stated rational coefficient
coherence and exact-descent interfaces and has no isomorphism conclusion. Edge
cases retain arbitrary base change, equality of coefficient fields and every
finite generating tuple; constituent normalization laws cover identity fields,
and the parent chooses a generating tuple from the actual finite-generation
witness, including the empty tuple if it generates the ideal.

## Second reading by N4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
