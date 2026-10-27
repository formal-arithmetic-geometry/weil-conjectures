## Worker report

Files written:

- `dag/nodes/sec-six-functors-basics/lem-sfb-weyl-word-operators.json`: item, statement, split. The statement and statement dependencies are unchanged. Six explicit proof steps construct the maps and prove all four commutator identities. No new nodes or new Mathlib leaves.
- `citations.json`: four verbatim quotations, one for each step using `def-wf-lie-algebra`.
- `report.md`: this report and direct-delivery self-review. `searches.jsonl` is the search command's unchanged output log.

Attachments: none. I searched `lean/WeilConjectures/` for the item id and for Weyl, Verma, raising and word-operator terminology. No project declaration states this item. Unrelated uses of “raising” concern degree shifts and powers. The existing item has no Lean declaration to attach and no released stage-1 repair note. The sandbox initially contained no item, split or report, so I continued from the live item rather than replacing previous work. All inherited source records, citations, blueprint metadata and Mathlib search records are retained; five freshly executed search records are appended.

WANTED: Bourbaki, Lie Groups and Lie Algebras, Chapter VIII, section 4, no.2, the direct proof of the Weyl-only presentation cited by Milne Theorem 23.63, for lem-sfb-weyl-word-operators. This is not needed as a black-box lemma for the explicit calculations now written out.

Available source read: Milne, Algebraic Groups (2017), Theorem 23.63, first proof, printed pp.503–504 (PDF pp.515–516). Milne asserts the Weyl-only triangular decomposition and points to Bourbaki for its direct proof. He does not state these word operators or their arbitrary-rational-matrix version. Accordingly every proof step identifies the calculation as agent-supplied and `proof_origin.by` is `agent`; no missing source is represented as read. This is Lie-algebra material, so no Stacks tag is claimed. I also read Q13's existing normal-form report, which explicitly explains the intended word-operator prerequisite and includes the motivating checks; this split makes those calculations the item's actual proof.

What was incomplete: the item was a statement-only prerequisite. The proof now supplies construction by terminating recursion, unique linear extension, diagonal commutation, the recursion commutator, the prepending weight change, and an explicit induction for the raising commutator. No part is hidden behind a new node restating the conclusion. No statement correction or statement dispute is necessary. Nothing remains unfinished in this item's natural-language proof; no Lean or compiler work was performed.

I read the fixed chapter and unit records, the three blueprint levels in SETUP, GOAL, and the current latest blueprint's six-functor unit and direct-images proof (3). This is an existing deeply nested supporting algebraic prerequisite of that route. Neither chapter nor unit is changed. The inherited `blueprint.from.node` is null, as confirmed by `tools/blueprint_refs.py ancestor`; its precise supporting place and via list are preserved. Whole imported-blueprint searches for “word operators” and “Weyl” returned zero matches. A whole-DAG and latest-blueprint search for word operators, words/commutator, raising operators, Verma and weyl-word found the item, its normal-form parent and unrelated statements. The Verma monomial weight-basis theorem concerns an induced module for a finite-dimensional split semisimple Lie algebra, and the pure coface word-relations theorem concerns simplicial syntax; neither proves these operators for arbitrary rational B.

## New nodes

None. The calculations are kept as proof steps: no elementary fact, clause of this item, or duplicate is promoted to a new node. Zero new Mathlib leaves.

## Not duplicates

No new node pairs arise. The existing item is an operator calculation, whereas `lem-sfb-weyl-relations-free-normal-form` asserts freeness and a direct sum for a presented Lie algebra. It depends on this item, so it is not used in the proof. The finite-type highest-weight and Serre-presentation results impose different hypotheses and do not replace this arbitrary-matrix calculation.

## Mathlib searches and readings

All five Q103 queries were run with the required msearch.py command and their exact queries and returned summaries are appended to the item. LeanSearch, Loogle, grep and both LeanFinder phrasings succeeded. None was unavailable. The full search command outputs were read before assigning verdicts. The Loogle query `Module.End, FreeAlgebra` had zero hits. The grep query in Algebra/Lie found SerreConstruction and unrelated Cartan material. Both semantic formulations found formal Cartan relations and the Geck construction, not a word representation.

I opened Mathlib/Algebra/Lie/SerreConstruction.lean:94–147: HH, EF, HE and HF define elements of a free Lie algebra to be imposed as relations; Matrix.ToLieAlgebra is a quotient including the Serre relations. They neither define E on finite words nor prove these endomorphism identities. I also read Mathlib/LinearAlgebra/RootSystem/GeckConstruction/Basic.lean:64–75 and 131–156 and Relations.lean:36–96. These are matrices indexed by a crystallographic root pairing, with additional domain and characteristic assumptions, acting on a different finite space; the analogous Lie brackets cannot specialize in one line to an arbitrary rational matrix and arbitrary word space. FreeLieAlgebra's recursors and Lie instances from LeanSearch do not supply the missing concrete operator computation. No Mathlib leaf is asserted.

## Source error

The Milne p.504 display prints `[X_i,X_i]=H_i`, which would force H_i=0 by alternation, and its final displayed relation repeats X where the intended negative-generator relation has Y with a minus sign. The existing parent report already records the intended corrections `[X_i,Y_i]=H_i` and `[H_i,Y_j]=-n(i,j)Y_j`. The item's statement already uses these correct signs. This split does not silently copy those printing errors and does not change the statement.

## Review by Q103

I reread the item, Milne pp.503–504, the normal-form parent report, the actual statement of `def-wf-lie-algebra`, and the corresponding latest blueprint Lie-definition text. The cited definition explicitly says that End(V) is a Lie algebra with [X,Y]=XY-YX. This is exactly its sole mathematical use here, and the four citation quotes are copied verbatim from that statement. It is a definition/Mathlib leaf, so its use across units is permitted without importing any other unit's proof route. No source proof, quotient theorem, PBW theorem or root-system theorem is borrowed implicitly.

Step 1 has no external dependency: every nonempty word has a unique first letter and shorter tail; its recursive value is a finite sum of finite sums already defined. Thus the construction is genuine data, with unique linear extension on a basis, and the weight identity is the displayed finite sum with its first term separated. This is elementary basis arithmetic, not an existence theorem or hollow definition.

Step 2 cites def-wf-lie-algebra only for the commutator meaning. I checked that both diagonal composites multiply the same two rational scalars, so the equality holds on the basis and hence on the entire free vector space. There is no finite-dimensionality assumption.

Step 3 again uses that exact bracket definition. Subtracting the first term in the recursion proves the whole EF relation, including i=j and i≠j and the empty input word. It does not assume any of the other identities.

Step 4 uses the same bracket definition and the step-1 weight formula. The two scalars differ by minus b_ij, with row i and prepended letter j; I checked the minus sign and did not transpose the matrix. Linearity makes this an identity on every vector before step 5 uses it.

Step 5 cites the same bracket definition and uses only identities already proved in steps 2–4. It is marked non-elementary because it contains the explicit induction, rather than marking the entire raising commutator obvious. Its claim is D(w)=b_ij E_j(w) for a basis word of the induction length. The empty-word base follows from E_j(1)=0, including the term E_j(H_i(1)). For the successor F_k w, expanding H_iE_jF_k-E_jH_iF_k gives exactly the five terms written in the node. HH cancels the Cartan difference; EF changes the remaining b_ik term into delta_jk b_ik H_j(w). The induction hypothesis is invoked only on the shorter w. Splitting j=k and j≠k gives delta_jk b_ik=delta_jk b_ij. The last use of EF combines the two surviving terms into b_ij E_jF_k(w). This proves the induction without a hidden comparison, simultaneous assumption of HE, generic commutator lemma, or citation cycle. No separate lemma remains to expose: it is precisely the displayed routine expansion proving this clause.

Step 6 records that no diagonal, rank, sign or symmetry restriction has entered, and handles the empty set, where the word space is one-dimensional but no indexed relation must be checked. It has no external dependency. All six proof steps are shorter than 2000 characters, and their combined text is under 3000 characters.

For small cases, I checked w=1 explicitly: E_iF_j(1)=delta_ij lambda_i 1, HF has coefficient -b_ij, and both sides of HE vanish. For a singleton I, the recursion gives E(t^n)=(n lambda-b n(n-1)/2)t^(n-1) for n≥1. Its successive difference is lambda-nb, the EF coefficient on t^n, and its H-weight changes by b, as required. The n=0 case is handled by E(1)=0, without a negative-length word. For B=0 and lambda=0 the raising and Cartan operators vanish; prepending still works and all relations hold.

I additionally ran a plain-Python exact-rational calculation of all four commutators on every two-letter word of length 0 through 4, for every pair of indices, with four matrices: zero, nonsymmetric with fractional entries and negative diagonal, singular, and zero diagonal with unequal off-diagonal entries. Weights include zero and nonzero rational values. All 1984 equality checks passed. This was not Lean compilation and serves only as an edge-case check supplementing the complete induction. Empty I was checked directly as above.

Against delivery-errors B–E: there are no new statements or leaves to misstate; the self-contained statement and definition dependency are retained verbatim; TeX is encoded once; no fabricated source, line claim, search or tag is recorded. The one cited node was opened and supplies exactly the bracket used, and no non-elementary external theorem is missing. The proof carries the calculations itself rather than renaming them, its induction is well founded with explicit base and successor, and no new hypothesis or false transport is used. No SGA source, alternate purity route, compiler invocation, repository write, git command or subagent was used. This is the requested direct-delivery self-review for the maintainer's independent reading.
