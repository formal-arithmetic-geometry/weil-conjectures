# Worker report: lem-sfb-space-proper-fpqc-descent

## Files written
- dag/nodes/sec-six-functors-basics/lem-sfb-space-proper-fpqc-descent.json: statement, split; unchanged statement and statement dependencies; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-space-fpqc-descend-universally-closed.json: statement only, unsplit; no Mathlib match.
- citations.json: full verbatim statements for each proof-step citation.
- searches.jsonl: eight actual searches; all services answered.

## Attachments
None. Searched WeilConjectures by the item tag and proper/fpqc and universally-closed/descent concepts. FieldExtensionDescent.isProper_descendsAlong_surjective_inf_flat_inf_quasiCompact is scheme-only, so is not an attachment for this item. No Lean was written and no compiler or Lake was run.

## WANTED
None: the Stacks sources are available locally.

## Problems and corrections
The statement is correct and unchanged. The imported node had no proof. Stacks 0422 proves precisely this by constituent-property locality. A direct reuse of lem-sfb-space-flat-proper-fp-locality would be invalid: it gives only fppf coverings, whereas an fpqc covering need not be locally finitely presented. Its open-image argument for universal closedness cannot simply be used for arbitrary flat covering arrows. I instead expose the general 041O descent input as a statement-only node. The blueprint ancestor command returns None on the inherited created.item chain. I retain that existing null ancestor and exact via chain, describe the supporting place, and read the latest blueprint unit and direct-image proof (3); there is no change of unit or chapter route.

The qc/separated descent node uses existence of a quasi-compact etale atlas, while def-sfb-space-morphism-properties uses compact point spaces on affine scheme tests. Step 3 explicitly invokes the existing finite-subatlas comparison rather than silently identifying those definitions.

## Not duplicates
lem-sfb-space-fpqc-descend-universally-closed vs lem-sfb-space-proper-fpqc-descent: universal closedness alone is strictly weaker than properness; the new input has no finite-type or separatedness assumption or conclusion. The item assembles this input with two independent descent results and proper-base-change stability, rather than delegating its whole assertion.
lem-sfb-space-fpqc-descend-universally-closed vs lem-weil-pbc-fpqc-descend-universally-closed: the existing statement has a scheme source; the new statement permits any algebraic space, including non-schematic ones. The scheme-only Mathlib instance cannot specialize to it.
lem-sfb-space-fpqc-descend-universally-closed vs lem-sfb-space-flat-proper-fp-locality: the existing statement supplies properness descent only for fppf coverings, not universal-closedness descent for fpqc coverings, and no clause applies to a universally closed map lacking finite type or separation.

## Review by Q81
I read Stacks spaces-descent.tex Tag 0422 (lemma-descending-property-proper), its definition of fpqc locality 03YH, and the constituent proofs 041O, 0421, 041U, 041L and 041S. The item follows their conjunction route. For the one new node I read all of 041O: the proof reduces to affine faithfully flat covers, tests closedness after arbitrary affine base change, uses the fpqc quotient topology of schemes and surjectivity of the map from points of the sheaf fibre product to the topological fibre product. That is a genuine further descent lemma, not a restatement of properness; it remains statement-only as required. Its future split should expose that quotient and point-lifting argument, not use flat-lfp openness without local finite presentation.

For Step 1 I opened lem-sfb-space-proper-base-change and checked its statement allows arbitrary algebraic-space base changes and imposes none of the missing Noetherian, finite-presentation or representability conditions. The projections in its conclusion are exactly f_i. I read spaces-morphisms.tex 04WP as the source.

For Step 2 I opened def-sfb-space-morphism-properties. It explicitly defines finite type as quasi-compact plus chartwise local finite type and proper as its conjunction with separatedness and universal closedness. Unpacking that conjunction is elementary, and the cited definition provides all four properties.

For Step 3 I opened lem-sfb-space-fpqc-qc-separated-descent and verified it descends each property separately for scheme coverings; choose S=T, so its base hypotheses are met. Its separatedness definition is identical to the item’s definition. I also opened lem-a1-space-finite-affine-subatlas, read spaces-properties.tex 03E4 and its affine-atlas input 03FX: compact point spaces give finite subatlases and a quasi-compact surjective etale atlas gives compact point space. Applied on each affine scheme test, that gives the needed convention comparison without claiming a topology theorem from a mere definition. There is no reliance on the proofs of cited nodes.

For Step 4 I opened lem-sfb-space-lft-smooth-fpqc-locality. Its statement explicitly supplies the fpqc target equivalence for chartwise local finite type, not just smooth source-and-target locality. I opened lem-galois-fpqc-covering-base-change, whose statement says scheme base changes of the given scheme fpqc family are again fpqc; this verifies the scheme-pullback covering convention of the lft node. Its conclusion combines with Step 3 by the finite-type definition.

For Step 5 I checked the new statement supplies exactly universal closedness from the universal closedness of all f_i, with the same scheme covering and without assuming qc, finite type or separation. Properness is then the written conjunction of Steps 3–5. Each uses entry has a verbatim full-statement quote in citations.json, retaining hypotheses rather than only the conclusion.

I tested empty X, empty T (including the empty covering), singleton identity covers and redundant empty covering members. All statements remain valid; empty T forces X empty, so there is no nonempty uncovered exception. I checked an arbitrary universally closed map need not be separated or finite type, so the new input cannot be replaced by proper descent. I checked no step assumes flatness of f, finite presentation of the cover, connected fibres, or Noetherian bases. The reverse implication uses flatness only through the definition of the covering in its cited descent nodes. All steps are shorter than 2000 characters. The one elementary step is only conjunction elimination. The new node has no proof or proof dependencies, introduces its own objects, and uses actual definition nodes. Searches of the entire DAG by 041O, label, and concept and blueprint_refs.py searches found no general algebraic-space fpqc universal-closedness node. Mathlib hits were read in Proper.lean (Scheme variables), UniversallyClosed.lean (Scheme variables) and FlatDescent.lean:48–62 (MorphismProperty Scheme), so neither the item nor the new input is a Mathlib leaf. No SGA source is used. No independent-reader claim is made.

## Unfinished work
None for this one-level split. The new 041O node is intentionally queued unsplit. Server dry run passed: deliver.py --no-push exited 0 and printed OK (not pushed) at aa2d1d5140e; server preflight passed. The final delivery follows this successful check.
