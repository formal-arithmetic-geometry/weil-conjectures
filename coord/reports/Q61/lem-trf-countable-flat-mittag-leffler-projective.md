# Q61 stage-1 delivery

Item: lem-trf-countable-flat-mittag-leffler-projective

## Files written

- dag/nodes/sec-trace-formula/lem-trf-countable-flat-mittag-leffler-projective.json: unchanged statement; seven-step split of Stacks Tag 059X.
- dag/nodes/sec-trace-formula/lem-trf-ml-countable-colimit.json: statement; unsplit, no Mathlib match. Tag 059W countable extraction from a given finitely presented directed presentation, using the tensor definition through 059M.
- dag/nodes/sec-trace-formula/lem-trf-mittag-leffler-hom-systems.json: statement; unsplit, no Mathlib match. Tags 059M and 059E(4), the bridge from the tensor-product module notion to stabilization of Hom-system images.
- citations.json: one verbatim statement quotation for every use in all seven steps.

## Attachments

None. Searched the read-only WeilConjectures source for the item id and the module Mittag-Leffler, countably generated, countable flat and projectivity terminology. No project declaration states the item or the two new facts. The existing generic category-theoretic and algebraic declarations returned by Mathlib searches do not state these assertions.

## WANTED

None. All mathematical sources are in literature/stacks-project/algebra.tex. Verified the tag/label correspondences in literature/stacks-project/tags/tags: 059X lemma-countgen-projective; 059W lemma-ML-countable-colimit; 059E proposition-ML-characterization; 059M proposition-ML-tensor; 058G theorem-lazard; 0598 lemma-ML-exact-sequence.

## Corrections and findings

No statement dispute and no change to the item's statement or hypotheses. The unsplit input had no proof. Its definition node def-trf-mittag-leffler-module defines the tensor condition, not the inverse-Hom condition used by 059X; I added a real smaller theorem for this equivalence consequence rather than using a definition as a theorem. I retained all pre-existing metadata and searches and added searches actually run through msearch.py. Failed identifier queries and the incorrectly scoped Mathlib/RingTheory grep returned zero results; they are not evidence for absence. The final new-node records use the successful well-scoped whole-Mathlib grep and a valid Loogle query, plus two natural-language phrasings and LeanSearch, recorded from searches.jsonl. The finite-presentation projectivity hit needs finite presentation and is not a one-line specialization under mere countable generation.

Both new nodes state auxiliary facts without proof. They neither assert projectivity nor repeat any clause of the item's conclusion. The countable-extraction node does not assume flatness; the Hom-system node assumes neither flatness nor countable generation. The finite-free Hom exactness, cofinal-sequence change, and Hom universal-property identifications are short explicit elementary arguments in the parent, not extra nodes. All parent steps are under 800 characters, so there is no long step hiding a standard lemma.

I read the chapter and sk-i-curve-zero unit and the current main-20261015 ancestor proof/update. This algebra branch is inherited through the Tag 05DP/05FT support for the semistable-alteration part of the older ancestor split. The current ancestor instead emphasizes the contracting-correspondence proof. This worker does not change the ancestor or its maintained unit binding: the assigned algebra lemma is proved by its given Stacks source, with its historical blueprint provenance retained. The two generic off-unit tools are declared in split_report.tool_uses: lem-kun-lazard-flat-module supplies precisely the Lazard presentation quoted by 059X; lem-weil-pbc-mittag-leffler-limit-exact supplies precisely its countable inverse-limit exactness. No trace-formula-unit node replaces either algebra tool. No SGA source is used.

## Unfinished work

None in the one-level split. The two new unsplit nodes are deliberate queued auxiliaries, not unfinished parent steps.

## Not duplicates

lem-trf-ml-countable-colimit vs def-trf-mittag-leffler-module: the existing node defines the tensor injection property; it does not extract a countable directed presentation.
lem-trf-ml-countable-colimit vs lem-trf-countable-flat-mittag-leffler-projective: the new node extracts a subsystem of a given finitely presented presentation and assumes no flatness; it has no projectivity conclusion.
lem-trf-ml-countable-colimit vs lem-kun-lazard-flat-module: Lazard produces an unrestricted directed finite-free presentation from flatness, but makes no countability assertion. The new node extracts a countable subsystem from any finitely presented presentation under countable generation and Mittag-Leffler.
lem-trf-mittag-leffler-hom-systems vs def-trf-mittag-leffler-module: same 059M source tag, different assertions: tensor condition definition versus its non-elementary implication for all Hom inverse systems of a directed finitely presented presentation.
lem-trf-mittag-leffler-hom-systems vs lem-weil-pbc-mittag-leffler-limit-exact: stabilization for Hom systems from a module tensor condition versus exactness of limits of already-ML inverse sequences.
lem-trf-mittag-leffler-hom-systems vs lem-trf-ml-countable-colimit: the former gives stabilization, with arbitrary directed index and no countability on M; the latter gives countable extraction, with no stabilization conclusion.

Before creating each auxiliary I searched the whole DAG for the tags, the Stacks labels, and the conceptual terms; searched the whole blueprint with blueprint_refs.py search for 059W, 059E, 059M and Mittag-Leffler; and searched the read-only Lean project for ids and concepts. The only tensor-ML definition with tag 059M is the definition above; no blueprint statement duplicates either new node.

## Review by Q61

I read the entire local Stacks proof of Tag 059X. For the countable auxiliary I read Tag 059W including its generator-lift, countable directed closure, and kernel-control argument, as well as the following cofinal-sequence paragraph. For the Hom auxiliary I read 059E's full equivalence and 059M's tensor equivalence (including (2) implies (1)), so the tensor-product assumption in the existing definition really does give condition (4) of 059E. The new statements introduce their own commutative ring, module, small nonempty directed index, maps and colimit; finite presentation is defined inline as a finite matrix cokernel. Both remain statement-only, as the brief requires.

Step 1: I opened the exact statements of both tensor nodes and the Lazard node. Flat-tensor exactness supplies the left end and middle exactness, while right exactness supplies surjectivity. Together they meet Lazard's explicit short-exact-sequence-preservation hypothesis. The Lazard conclusion gives every piece used: a small nonempty directed poset, finite free stages, compatible maps and a colimit isomorphism.

Step 2: I checked that finite free modules meet the new countable-extraction node's finite-presentation definition via the zero-relations presentation. Its countability and tensor-ML hypotheses are exactly the item's hypotheses, with no Noetherian, local, or finite-generation restriction added.

Step 3: I checked the explicit upper-bound recursion, including finite J with repeated enumeration and J a singleton. The compatible-cocone extension verifies cofinal reindexing from the colimit definition; no unquoted theorem on colimits is used. The resulting index is literally n >= 1, as required by the existing limit-exactness node.

Step 4: I opened the new Hom-system statement and def-weil-pbc-mittag-leffler-system. The former applies to this finite-free presentation, and its eventual image equality is word for word the content needed by the latter when I is the positive integers. I do not confuse stabilization for an inverse system with the tensor condition on P.

Step 5: The finite-free Hom exactness is proved coordinatewise in the step, including lifts of every coordinate and commutation of pre- and postcomposition. This is a two-to-three-line elementary argument, not a missing projective-module theorem. It includes rank zero without an exception.

Step 6: I opened lem-weil-pbc-mittag-leffler-limit-exact. Its part (3) is exactly the short-exact-sequence conclusion used, assuming only countable inverse sequences with ML kernel. Those hypotheses were established in steps 3--5. Forgetting to abelian groups introduces no extra hypothesis and exactness is unchanged when the maps are linear.

Step 7: I opened the colimit definition and projective-module definition. The former supplies bijectivity on compatible Hom families; the displayed compositions verify naturality, so it identifies all maps of the exact sequence, not just its objects. The latter explicitly defines projectivity by exactness of Hom, which is now proved for an arbitrary short exact sequence.

Small cases: the zero module and the zero ring work with zero stages; a constant finite-free presentation has constant, hence ML, Hom systems; a finite or singleton index is safely repeated in the sequence. A countably generated flat nonprojective example such as Q over Z does not satisfy the tensor-ML hypothesis; I never infer ML from countable generation or flatness. The countable extraction lemma permits finite presentations with noninjective transitions and does not assert that the extracted subsystem is cofinal in the original I. The proof only makes a cofinal sequence within the extracted J. These checks avoid a stronger false countable-cofinality claim.

I checked B--E of delivery-errors against the final files: standalone statements and correct Stacks labels, actual recorded searches, verbatim node statements for every citation, no duplicate or clause restatement, no proof content in the two unsplit statements, explicit hypotheses at every application, and no route replacement. I corrected the initially bundled presentation/Hom statement into two independent smaller source lemmas, and corrected the characterization source tag to 059E (059M is the tensor-equivalence proposition). I also corrected the new-node ancestry via list to start with the assigned item, not with the new node itself. No compiler, Lake, Lean-writing, or shared-repository git operation was run.
