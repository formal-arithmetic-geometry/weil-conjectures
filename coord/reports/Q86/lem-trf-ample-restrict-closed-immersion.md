# Worker report

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-ample-restrict-closed-immersion.json`: statement, split; no exact Mathlib match. The statement and its five statement dependencies are unchanged. Three proof steps replace the empty proof.
- `citations.json`: eight verbatim statement excerpts, one for every step/node citation.
- `searches.jsonl`: actual msearch results for this attempt; the node retains its inherited search records and appends these records.

New nodes: 0. New Mathlib leaves: 0. The only DAG file changed is the item. This is not the unit key node, so no unit record was changed.

## Attachments

None. Read the project declaration `AlgebraicGeometry.IsAmple.pullback`, `WeilConjectures/AlgebraicGeometry/Modules/VeryAmple.lean:146`, and its definition at line 131. That theorem assumes a structure morphism to a field and the projective-over-a-field predicate `AlgebraicGeometry.IsAmple`; the item uses absolute ampleness on an arbitrary scheme. For instance the trivial line bundle on affine one-space is absolutely ample but fails that project's predicate. Thus the theorem does not state this item, even though its prose title is similar. The exact blueprint tag was absent from project source searches.

## WANTED

None. All literature needed for this split is present locally.

## Problems found and corrections

No statement dispute. The imported item was a true, unsplit statement of Stacks 01PU. Its empty proof needed the quasi-compactness condition in the definition of ampleness, invertibility of pullback, transport of sections of positive powers with the correct nonvanishing predicate, and affine inverse images under a closed immersion. All four facts already have nodes. The new proof uses those statements directly instead of leaving the section transport implicit in the source's word “clear”. No hypothesis of Noetherianity, finite type, properness, separation, finite presentation, or a base field has been introduced.

Searches for the tag 01PU, closed-subscheme restriction, and ample pullback were made in the whole DAG; whole-blueprint searches used `tools/blueprint_refs.py search` for `ample restrict closed immersion`, `ample closed`, and `01PU`. The blueprint searches returned no matching blueprint statement. `lem-weil-pbc-pullback-ample-invertible` is a more general existing affine-morphism theorem, but this delivery creates no duplicate node: the assigned existing closed-immersion item is proved directly along its source's proof. The effective-Cartier restriction clause in `lem-sc-intersection-effective-cartier` assumes a proper scheme over a field and a particular divisor, so is not the arbitrary-scheme statement. No new node was warranted. The item preserves its historical `blueprint.from` and empty `same_as`.

Mathlib searches were run with the prescribed msearch command, with two semantic phrasings, two Loogle patterns and two grep patterns. LeanFinder returned affine-open/ideal-sheaf statements for the first phrasing and closed-immersion/base-change statements for the second; none states ampleness. The first Loogle query reported unknown `IsAmple`; the second had no hits. The broad grep's ten hits are occurrences in “example(s)”, not an ampleness API; the focused grep had zero hits. LeanSearch was rate-limited and is recorded as unavailable, not a negative search. Exact queries and actual summaries are in the node and log. No search was invented or replayed unnecessarily.

## Unfinished work

None for this one-level split. No Lean was written or compiled. The server-side `check_dag` returned OK before this report was written.

## Review by Q86

I read Stacks `properties.tex`, Tag 01PU, label `lemma-ample-on-closed`, including its entire short proof, and Definition 01PS, label `definition-ample`. They assert restriction to every closed subscheme, with no hypotheses on the ambient scheme beyond being a scheme. The item's statement agrees with that assertion. I also read the source's affine ingredient, Schemes Tag 01IH, label `lemma-closed-immersion-affine-case` in `schemes.tex`, and Topology Tag 005C, label `lemma-closed-in-quasi-compact` in `topology.tex`. There are no new-node sources to audit. I read the chapter and dedicated unit record; this item supplies the closed-restriction argument of unit Step 3, as required. Nothing replaces the unit's graded-Proj argument.

For Step 1 I opened all four cited node statements. `lem-weil-pbc-invertible-pullback-invertible` says precisely that an invertible module pulls back to an invertible module under any scheme morphism; its local trivialization clause does not need flatness. `def-weil-pbc-ample-invertible-module` includes quasi-compactness of Y. `def-weil-closed-immersion` gives the homeomorphism onto a closed subset. `lem-weil-pbc-closed-in-quasi-compact` applies to that closed subset and gives compactness in its subspace topology. Transport across the specified homeomorphism gives compactness of X; no assertion that an arbitrary subset of a compact space is compact is used.

For Step 2 I reread the full ampleness criterion and the statement of `lem-weil-pbc-tensor-power-section-nonvanishing-pullback`. Ampleness gives a global section of an actual positive tensor power of M whose nonvanishing open is affine and contains i(x). The second citation explicitly produces a section of the matching power of i^*M with equality of the two open loci; it is not merely an isomorphism of modules without section compatibility. Its only assumptions are a scheme morphism, an invertible module, and n>0, all in force. Thus it gives the section needed here exactly. This node is recorded Lean-closed in the shared DAG; the corresponding source module is not present in this machine's older read-only source checkout, so I rely on its explicit DAG statement, not on a nonexistent local proof or a new attachment claim.

For Step 3 I opened `lem-weil-pbc-closed-immersion-affine-cover-criterion` and used only clause (1): every affine open has affine inverse image under a closed immersion. This is stronger than merely having an affine cover and matches the chosen open Y_s. Its conclusion concerns the open subscheme itself, so the equality of opens in Step 2 supplies the correct scheme structure on X_t. The final appeal to the definition combines this pointwise positive-power criterion with the global compactness and invertibility already established. Each step is marked non-elementary because it invokes these real theorems; the choices, substitutions, and concluding definition check are routine. No proof step exceeds 2000 characters.

I checked the edge cases X empty (the pointwise condition is vacuous and compactness still holds), i the identity (the original affine-section witnesses work), an arbitrary closed subscheme Spec(R/I) of an affine scheme (the inverse image of D(f) is Spec((R/I)_f)), and a nonreduced closed subscheme (neither compactness nor the cited pullback-locus lemma assumes reducedness). No finite-type assumption on I is needed. An arbitrary non-quasi-compact closed immersion also causes no missing hypothesis: Y is compact because M is ample, and its closed subset is compact. All cited notions are defined by the statement dependencies, every non-elementary fact is cited by a node whose statement was read, and citations.json copies its needed text verbatim. There are no new statements that could hide a clause of the item, no new duplicate, and no data-valued definition or sorry. The earlier stronger-field notion was explicitly rejected as an attachment, and unavailable LeanSearch was recorded correctly. These are the substantive C1/C4 and B–E checks underlying my signature.
