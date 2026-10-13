## What changed

Replaced the earlier unfinished attempt with a complete Lean reduction of
`AlgebraicGeometry.Scheme.CompletionGluingData.exists_affine_chart_realization`.
Its signature and original docstring remain unchanged. Its proof first establishes
that E and the inverse-image principal charts are affine, using the finite-morphism
and open-immersion APIs. The empty index case is constructed directly with
Gamma(E,top); no existence theorem supplies that data.

Added three modules. PuncturedCompletionAffineChartTransitions contains the raw
transition fields, their section identifications, structural scalar equations, and
the existence theorem without square or cocycle. The structural actions are actual
ring homomorphisms, not chosen witnesses. PuncturedCompletionAffineChartGeneratorCoherence
states the square and cocycle identities only on original module elements.
PuncturedCompletionAffineChartCoherence proves the full equations from those
identities using localization uniqueness twice. Its private scalar, localization,
and base-change endomorphism lemmas are all proved. The target constructs
FormalGlueing.Data explicitly and retains the four section equations of the same
transition witness.

All four modules compiled individually in dependency order, with no remaining
partial proof. Source checked: Stacks Tags 0BLH and 05EL, first two proof paragraphs
and item (1) respectively. No unit or chapter route changes. No existing dependency
module, statement, definition, or public import changed.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.CompletionGluingData.exists_affine_chart_realization`.
The original module has no sorry. Also proved the new theorem
`AlgebraicGeometry.Scheme.CompletionGluingData.affine_chart_transition_coherence`
(node lem-sbc-punctured-completion-affine-chart-coherence), including extension
from original elements to arbitrary fractions.

Two new named theorem holes remain, each the whole proof in its own module:

- `AlgebraicGeometry.Scheme.CompletionGluingData.exists_affine_chart_transitions`
  (lem-sbc-punctured-completion-affine-chart-transitions).
- `AlgebraicGeometry.Scheme.CompletionGluingData.affine_chart_transition_generator_coherence`
  (lem-sbc-punctured-completion-affine-chart-generator-coherence).

This is a decomposition: one original hole closed, two added, net -1 before any
further proofs. It is not a claim of a sorry-free affine realization theorem.
The existence statement omits both coherence laws; the generator statement
constructs nothing and asserts equations only on original elements. The intermediate
full-coherence theorem is proved using IsLocalizedModule.ext, not left sorry.

Edge checks: t=0 is handled directly by Fin.elim0. Zero principal charts give
zero section rings, localized modules, and scalar extensions, so all equations
hold without nonzero hypotheses. Repeated chart elements, non-Noetherian A,
and nonflat completion require no additional hypothesis. The transition existence
statement requires affineness explicitly; the target proves it from finiteness.
The generator coherence statement also has this hypothesis explicitly. The b and
d scalar conditions prevent arbitrary additive identifications from being used
as linear maps when further localizing them.

## No longer needed

No original import or existing dependency node is pruned: finite affineness,
CompletionGluingData, and FormalGlueing.Data all remain necessary. The target's
old proof-dependency occurrence of def-sbc-punctured-completion-matching-sections
is now below the transition and coherence statements; it remains a statement
and transitive proof dependency, so this is not pruning.

The abandoned sandbox theorem exists_affine_chart_realization_data and its
uncommitted node lem-sbc-punctured-completion-affine-chart-realization-data were
discarded. They were never library declarations and are not counted as pruning.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt left sorry inside the target after obtaining arbitrary data,
provided no complete combination proof, and recorded an incomplete node. The lack
of previously proved geometric declarations is not an obstacle in this stage.
The present delivery turns the construction and coherence steps into explicit
statements, proves the localization extension, and completes the target assembly.
No mathematical error in the existing statement or unit route was found.

Searches: LeanFinder returned affine localization and section-map APIs; Loogle
returned IsLocalizedModule.ext; grep found isLocalization_basicOpen and
pullbackSpecIso, but no complete transition realization. A second LeanFinder search
for uniqueness on iterated localizations returned IsLocalizedModule.ext and
linearMap_ext. LeanSearch returned Internal Server Error (unavailable, not a
negative search). Blueprint searches for 05EL and affine chart transitions found
no blueprint duplicate; rg found no existing AffineChartTransitions or generator
coherence declaration. No new interface change forces adaptation of another module.

## New nodes

lem-sbc-punctured-completion-affine-chart-transitions records existence of section
transition equivalences with generator and scalar formulas, without coherence.
Its new module is PuncturedCompletionAffineChartTransitions.

lem-sbc-punctured-completion-affine-chart-generator-coherence records the two
geometric equalities on original module elements, for any such section transitions.
Its new module is PuncturedCompletionAffineChartGeneratorCoherence.

lem-sbc-punctured-completion-affine-chart-coherence records the proved promotion
from generator equalities to full linear-map equations. Its new module is
PuncturedCompletionAffineChartCoherence. The original node's proof and proof_deps
now follow this assembly. There are no change records or forced adaptations.

## Second reading by T1

1. Interface preservation: PASS. Diffed the delivered realization module against
   the repository. Its only existing theorem signature is byte-for-byte identical,
   including the finite-morphism hypotheses, four section formulas, universes and
   local module structures. The original docstring and both public imports are
   unchanged. The added coherence import is proof-only. The three other modules
   are new; there are no forced adaptations or changes to existing definitions.
2. Proof and axioms: PASS as a decomposition. Independently compiled all four
   modules in import order with lcompile.py, without warnings or errors. The only
   two textual sorries are the entire proofs of the two public named theorems
   listed above. No forbidden declaration or hollow definition is present.
   Scratch-copy #print axioms checks give only propext, Classical.choice,
   Quot.sound, and sorryAx for the target and the three new theorems; the two
   structural-action abbreviations have no sorryAx. The target retains sorryAx
   through the two geometric holes, so it is not an axiom-free final proof.
   The private scalar-endomorphism constructions and their unit-transport proofs
   were read in full; localization uniqueness is applied in the correct order
   with invertibility proved in each actual codomain.
3. Split statements: PASS. Read the two complete docstring arguments against
   Stacks https://stacks.math.columbia.edu/tag/0BLH and
   https://stacks.math.columbia.edu/tag/05EL. The transition theorem constructs
   section modules and identifications without the coherence laws. The generator
   theorem checks given maps on original elements and constructs no data. Neither
   merely renames the target: the delivered proof separately establishes
   affineness, promotes generator equalities by two localization uniqueness
   arguments, and assembles the formal data. On the diagonal b_right and b_scalar
   force c to respect A-scalars; d_scalar forces the completed identifications
   to respect C-scalars. These conditions are necessary for the fraction argument.
   Checked empty index sets, zero and unit chart elements, repeated charts,
   empty schemes, and the absence of flatness or Noetherian assumptions. No false
   case was found. No public definition selects arbitrary data from either hole;
   the existential transition witness is eliminated only inside the target proof.
   Independent LeanFinder search for compatibility of affine restriction with
   tensor base change found appLE/fromSpec APIs, not either split theorem.
   Independent Loogle search for IsLocalizedModule and ext found ext and
   linearMap_ext; the latter does not remove the codomain invertibility work
   here. Launcher grep and rg in both source roots found affine chart base-change
   tools, including exists_affineChart_baseChangeIso, but no complete transition
   construction or geometric generator-coherence theorem. The existing tools
   could help prove the remaining construction, but do not close it in a short
   second-reading repair. Searches are recorded in searches.jsonl.
4. Route and pruning: PASS. Read the imported definitions and the original
   dependency plan from the target downward. Both original public imports are
   needed by the target signature; all new imports are needed either in a
   signature or a proof, with the proper visibility. No original module is
   pruned. The old direct proof dependency
   def-sbc-punctured-completion-matching-sections is no longer a direct proof step,
   as recorded under No longer needed, but remains a statement dependency and a
   transitive dependency of the geometric holes. Read
   dag/units/sk-prop-input-spreading.json: its realized arrays are already empty,
   unchanged by this delivery. The new nodes stay in the same unit and refine
   the affine construction and object check below it; no unit step or chapter
   route is replaced or bypassed.
5. DAG consistency: PASS. Checked all four node files against their Lean modules.
   Each recorded Lean statement occurs verbatim, and each proof_deps set equals
   the union of the proof steps' uses. The existing node changes only proof,
   proof_deps and proof_origin. Each new node has its source, search records,
   creation record, blueprint ancestry, chapter, unit, and full Lean record.
   The realization node describes the finite-affineness reduction, direct empty
   chart construction, coherence application, and explicit final assembly.

Second-reading changes: added this independent review and search evidence to the
report. No Lean repair was needed. No additional hole was closed or added: one
original hole closed, two split off, net -1; the proved full-coherence theorem is
an intermediate result. Removed all temporary axiom-check copies before delivery.
