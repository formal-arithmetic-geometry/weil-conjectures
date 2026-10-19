# Worker report

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-henselian-pair-proper-clopen-lift.json: statement, split into five steps; not in Mathlib after the recorded searches. Original statement retained verbatim. No new nodes and no new Mathlib leaves.
- citations.json: one verbatim statement quotation for each node cited by each numbered step.
- report.md: this report and self-review. searches.jsonl retains the search-command audit trail.

## Attachments

None for the item. Search of WeilConjectures in the read-only slopmaster2 and master sources by the exact blueprint id and henselian/clopen/proper terms found no declaration stating this item. The existing declaration AlgebraicGeometry.NagataCompactification belongs to the existing node thm-nagata-compactification; it is a generic input, not an attachment for our item. I read its definition at WeilConjectures/Compactification/NagataCompactification.lean:183–197 and the node's closed slopmaster2 audit.

## WANTED

None. The item source and all input statements are available. No downloads, Lean writes, builds or compiles were run.

## Findings and route

The initial item was statement-only and agrees with Stacks 0CT9, more-morphisms.tex, label lemma-split-off-proper-part-henselian. In particular the ambient X need not be proper, A need not be local or Noetherian, and no finite generation of I is needed. There is no statement dispute.

The source uses Chow's lemma, compactifies the quasi-projective cover, descends its proper part, and then uses Stein factorization to lift a clopen on the proper ambient scheme. Our proof uses the existing Lean-closed general Nagata compactification tool instead of this preliminary Chow cover, and reuses the existing proper henselian clopen-restriction theorem instead of repeating its Stein proof. The substantive boundary-removal argument is the second paragraph of 0CT9. This is a choice below the unit level, not a change of chapter or unit route. The inherited local-duality / partial-algebraization / Elkik ancestry and blueprint.from.place are retained. The current main-20261015 ancestor and unit were read; this generic scheme lemma supports the already recorded Step 1 local-duality input, not a replacement perverse argument.

The item's inherited Mathlib searches had generic verdict language mentioning unrelated completion and etale-algebra results. The new logged searches address this precise item. LeanFinder and LeanSearch returned properness criteria, diagonals and quasi-finite clopen singletons; Loogle with IsProper and HenselianRing and source grep over AlgebraicGeometry returned no hits. None states the lifting theorem. No search is claimed for a new node, because there are none.

## Unfinished work

None at stage 1. The cited unsplit inputs remain owned by their existing nodes; this delivery does not purport to prove or change them.

## Not duplicates

No new nodes. Searches of the whole DAG for 0CT9, the source label, henselian clopen/proper lifting, proper-source-to-separated-target, compactification, and Chow inputs found the existing tool nodes used below. Whole-blueprint searches with blueprint_refs.py for henselian, compactification and proper open closed found the proper-scheme theorem, but no blueprint node with the present nonproper-ambient statement. No duplicate lemma was introduced.

## Review by Q68

I read Stacks 0CT9 in more-morphisms.tex with all three reduction paragraphs, Stacks 01W6 (lemma-image-proper-scheme-closed) in morphisms.tex, Stacks 0A0B (lemma-zariski-h0-proper-over-henselian-pair) in etale-cohomology.tex including its Stein connectedness proof, and the main-20261015 Nagata theorem and proof. I also read the statement of every node cited by the five steps. There are no new-node source obligations.

Step 1 uses lem-weil-pbc-qcqs-over-affine on the identity of Spec A: its target is affine and its identity is quasi-compact and separated. This gives precisely the qcqs base needed by thm-nagata-compactification. The latter's current blueprint_update and source say exactly that a separated finite-type morphism admits an open immersion followed by a proper morphism. def-nagata-compactification and def-nagata-compactifiable unpack these data; no density, projectivity or Noetherianity is taken from them. The theorem is already Lean-closed, so its reuse does not create another proof task or assume completion of its imported prose proof.

Step 2 uses lem-weil-pbc-open-immersion-base-change for j_0, and part (b) of lem-weil-pbc-proper-fp-permanence for properness of the ambient closed fibre. def-weil-proper-morphism gives both separatedness and closedness from properness. The hypotheses of lem-weil-pbc-proper-over-separated are met with base S_0, source Y proper by the item, and target the proper, hence separated, ambient fibre. Its conclusion really is properness of the map Y into that target. Universal closedness makes its image closed, and the open immersion already identifies that image with the restricted open subscheme. No image is silently assigned a different scheme-theoretic structure.

Step 3 uses the surjectivity clause of lem-weil-pbc-henselian-clopen-restriction only on the proper compactification, where all its hypotheses hold; it does not apply it to the original nonproper X. The elementary local sheaf check makes a clopen inclusion a closed immersion. Clause (c) of lem-weil-pbc-closed-immersion-proper then gives properness over S. Open-immersion base change proves the fibre has the restricted structure sheaf, so the lift agrees with Y^c as a subscheme. These statements are precisely the quoted clauses in citations.json.

Step 4 uses only the irreducible-closed-subset assertion of lemma-weil-pbc-stein-connectedness, not its proof or just its definition of Stein factorization. That assertion explicitly says every irreducible closed subset of a proper scheme over a henselian pair meets the closed fibre nontrivially. The closure of a putative boundary point is a nonempty irreducible closed subset of the proper lift, and remains in the closed boundary. The step writes out irreducibility. The closed fibre lies wholly in j(X), so the required meeting is impossible. This supplies the exact boundary argument without an unstated Jacobson-radical lemma or a local-base hypothesis.

Step 5 is elementary restriction along an open immersion: a clopen contained in its image has exactly that inverse image and is isomorphic to it with the restricted structure sheaf. The statement of def-weil-open-immersion supplies this scheme identification; the base-change node supplies its fibre version. Transport of properness along this explicit isomorphism and inverse images of subsets finish the proof. The conclusion is equality of open subschemes of X_0, including their sheaves, rather than just equality of underlying sets.

I checked B–E: no new nodes, no clause moved to a fresh node, no statement-only node with an inline proof, no invented source tag, and no new searches without log records. Every non-elementary input has a node citation and verbatim quotation; proof_deps is exactly their union. Generic off-unit tools are declared in split_report.tool_uses. Definitions are used for their actual contents. The route uses no SGA source. All five steps are below 2,000 characters. I tested Y empty (take the empty lift), I=0 (the assertion reduces to W=Y), A=0 (all relevant schemes empty), a proper X (direct proper clopen lifting), and X=Spec k[[t]] disjoint union Spec k((t)) over k[[t]] with I=(t) (the empty-fibre nonproper component must be excluded). The proof handles each without adding a hypothesis or claiming the whole ambient scheme is proper. No corrections to the item statement or another worker's node were needed.
