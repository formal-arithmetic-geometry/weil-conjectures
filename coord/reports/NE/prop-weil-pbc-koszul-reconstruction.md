# Stage-1 worker report

## Files written

- `dag/nodes/sec-proper-base-change/prop-weil-pbc-koszul-reconstruction.json`: item split; no new nodes; Mathlib searches found no match.
- `citations.json`: verbatim citations for both proof steps.

## Attachments

None. No sorry-free Lean declaration states this item.

## WANTED:

WANTED: a comparison theorem identifying the completed-coefficient derived category built from `A_T = lim_n (P_n)_T` with the constant-coefficient derived category used by Stacks Tags 091N/091Z and by `lemma-weil-pbc-koszul-quotient-limit`.

## Source error

`def-weil-pbc-adic-coefficient-datum` explicitly says that its completed coefficient sheaf `A_T` is not identified with the constant coefficient sheaf from `def-weil-pbc-proetale-site`. The existing node `lemma-weil-pbc-koszul-quotient-limit` proves the Koszul/quotient comparison only for the constant coefficient datum `def-weil-pbc-complete-coefficient-datum`. Thus the imported proposition's proof silently changes coefficient categories and is not valid as written. I did not alter the proposition's mathematical claim; the split records the missing comparison as `STATEMENT-DISPUTED` and leaves the consequence conditional on that theorem.

STATEMENT-DISPUTED: the Stacks comparison cited by the source applies to constant coefficients, while the proposition quantifies over the completed coefficient sheaf `A_T`; the DAG explicitly forbids identifying these ambient categories without a separate comparison theorem.

## Not duplicates

No new nodes were created. The existing `lemma-weil-pbc-koszul-quotient-limit` is related but differs in coefficient category: it assumes `def-weil-pbc-complete-coefficient-datum` (constant sheaves), whereas this item assumes `def-weil-pbc-adic-coefficient-datum` (completed sheaf `A_T`).

## Review by NE

I read the imported item and its blueprint source `prop-weil-pbc-koszul-reconstruction.md`, including the qualification that Tags 091N/091Z and 099M are stated for constant Noetherian coefficients. I read the complete statements of `def-weil-pbc-adic-coefficient-datum`, `def-weil-pbc-intrinsic-completion`, and `lemma-weil-pbc-koszul-quotient-limit`. Step 1 uses only the latter node's displayed natural isomorphism and completion-map compatibility, then checks its hypothesis against the adic-datum statement; that check exposes the explicit no-identification clause. Step 2 uses the intrinsic-completion definition for the implication from Koszul completeness to the quotient-limit isomorphism, but records that transport across the missing coefficient comparison is still required. I verified the edge case that the two coefficient sheaves are distinct by definition even before any ideal or tower is chosen, so the mismatch cannot be removed by a special case. The Mathlib searches were run with `msearch.py` for LeanFinder, Loogle, and grep and found no general derived Koszul/quotient reconstruction theorem.

## What was wrong or unfinished

The imported proof treated the constant-coefficient Stacks theorem as if it applied to the completed coefficient category. No Lean proof exists in the source, and no existing node supplies the needed comparison. The item therefore remains mathematically blocked until that comparison theorem is added; no hollow or duplicate node was introduced.

## Second reading by NE

The first-reader sections above are retained as history. Their WANTED, STATEMENT-DISPUTED and blocked verdict are superseded by this reading: absence of an identification in a definition is not a counterexample, and the required comparison already exists. I opened both existing comparison statements and their source passages, not just their titles. The entire derived categories are not identified; the comparison is a theorem about completion towers, valid for every object over the completed ring sheaf.

- Original step 1: checked against lemma-weil-pbc-koszul-quotient-limit and def-weil-pbc-adic-coefficient-datum; the constant/completed distinction is correct, but the claim that a comparison is missing is false after searching the whole DAG.
- Original step 2: checked against the same coefficient hypotheses and the completion definitions; rejected as a conditional non-proof, with an uncited transport and a missing completeness-definition citation.
- Repaired step 1: checked the full statements of lem-weil-pbc-completed-constant-sheaf-reduction and def-weil-pbc-adic-coefficient-datum against sites-modules.tex Tag 093M, label lemma-completion-flat. Pass: Noetherian A and finite P_n are in force; the cited node explicitly identifies the locally constant finite coefficient sheaf with (P_n)_T, its actual limit with A_T, and finite reductions. This uses the node's statement, not an argument hidden in its proof.
- Repaired step 2: checked the final paragraph of lem-weil-pbc-constant-completion-equivalence against proetale.tex Tags 099L/099M, labels section-derived-completion-noetherian/lemma-naive-completion; algebraization.tex Tags 099I/0A0E, labels lemma-restriction-derived-complete-equivalence/lemma-derived-completion-koszul; more-algebra.tex Tags 091N/091Z, labels section-derived-completion/lemma-characterize-derived-complete-Koszul. Pass: its explicit completed-coefficient comparison applies to every N in D(A_T), uses precisely the Koszul transitions and strict derived limits here, and respects the units. No Noetherian property of A_T, no equivalence of all derived objects, and no assumption of completeness of K is inferred. Naturality is the levelwise commuting augmentation square followed by the functorial strict derived limit.
- Repaired step 3: checked against the definition of completeness now stated in the item and the unit identity in step 2. Pass: the two inverse compositions are written, and this really is elementary.
- Item statement: checked hypothesis by hypothesis against the imported proposition, its explicit constant-Noetherian source qualification, and the completed-coefficient comparison above. Pass after clarification: the scheme, original adic hypotheses, completed module category, Koszul transitions, strict derived limits, completion units, compatibility and completeness consequence are all specified. The claim is not restricted to constant coefficients or to complete objects in its first clause. The prior imported statement left the Koszul object unbound in stmt_deps; using def-weil-pbc-intrinsic-completion would introduce a cycle because that definition cites this item. Inline specification resolves the type/definition defect without that cycle.
- New nodes: none; B1–B7 and duplicate/new-node Mathlib-leaf checks are vacuous. Existing lemma-weil-pbc-koszul-quotient-limit is constant-coefficient only; existing lem-weil-pbc-constant-completion-equivalence already supplies the needed completed-coefficient assertion, so a new comparison node would duplicate it.

Small cases checked: K=0 gives two zero limits and the zero-object identity; the empty scheme has the zero module category. For r=0, I=0, Q_m=A_T[0] and the quotient tower is constant; both units are identities. For r=1 over A=Z, I=(p), and T a geometric point, A_T(T)=Z_p while the constant Z sheaf has sections Z, explicitly showing why the two categories must not simply be equated. The flat scalar comparison nevertheless applies and gives the correct completed-coefficient formula. For the finite field A=F_p and I=0 both towers are constant, including the empty-generator case. Tower indices start at 1 throughout; no nonexistent zeroth quotient is used.

Changes and reasons:

- Replaced both original conditional steps by three actual proof steps citing two existing completed-coefficient comparison nodes. Removed the WANTED dependency from the proof and the incorrect constant-coefficient lemma application.
- Expanded the item statement to bind K, Q_m, both completion units and the meaning of derived completeness, preserving its mathematical conclusion and original coefficient hypotheses. The source's literal constant-coefficient theorem alone would not justify the original application; the additional existing comparison now supplies precisely that justification. No statement dispute remains unresolved.
- Removed split_report.tool_uses for the unused constant-coefficient lemma. All cited comparison nodes lie in this unit, so no off-unit tool is introduced.
- Rebuilt citations.json from the actual cited statements, with one verbatim full statement per citation.
- Ran independent Mathlib searches with msearch.py: LeanFinder for sheaf-complex homotopy limits of quotient tensors (8 hits, ordinary completion/local cohomology); Loogle for "Koszul" (0 hits); source grep for derivedCompletion|derived_completion|koszul|homotopyLimit (3 unrelated hits). No declaration states this result; actual searches remain in searches.jsonl. No new Mathlib leaf is claimed.

The fixed chapter/unit route is unchanged. The exact master and slopmaster2 Lean trees were treated as read-only reference material; no Lean was written or compiled. Neither a sorry declaration nor an existing DAG proof status was treated as a finished Lean proof.

Validation: deliver.py NE prop-weil-pbc-koszul-reconstruction --no-push printed OK at 607c16104c (preflight passed). Citation checks, dependency/cycle delta checks and stage-1 delivery checks passed. No compiler or Lake command was run.
