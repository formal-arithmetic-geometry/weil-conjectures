# Stage-1 report: lem-sfb-semisimple-group-perfect

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-semisimple-group-perfect.json: item, statement unchanged, now split into four steps. Existing searches retained in substance and rerun through Q129's required logged command.
- dag/nodes/sec-six-functors-basics/lem-sfb-reductive-root-subgroup-parametrizations.json: new statement-only node; no Mathlib match. Root groups, additive parametrizations, torus conjugation, and the root-coroot square identity.
- dag/nodes/sec-six-functors-basics/lem-sfb-semisimple-root-subgroups-generate.json: new statement-only node; no Mathlib match. A closed subgroup containing every root subgroup of a split semisimple group is the whole group.
- citations.json: seven verbatim statement excerpts, one for each step/node citation.

Two new nodes, zero Mathlib leaves. The search-plan.json, search-results.json and searches.jsonl retain the actual queries and hits. Scripts used to assemble the JSON are confined to this sandbox.

## Attachments

None. Searched WeilConjectures for the blueprint tag, semisimple/perfect/derived-subgroup concepts and root-group concepts. The existing linear algebraic group files treat monodromy, representations and Lie-algebra statements; none gives this arbitrary-characteristic affine group-scheme assertion. No Lean was written or compiled.

## WANTED

None. All mathematical sources used are in literature/milne-algebraic-groups_iAG2017.pdf.

## Corrections and scope

No statement dispute. The item agrees with Milne Corollary 21.50, printed p.440, over an algebraically closed field. Its imported proof was empty. Removed only the unused def-pc-scheme statement dependency: the statement already introduces schemes through the group-scheme and closed-subgroup nodes, and never refers to that generic definition. The hypothesis and conclusion are unchanged.

The proof follows Milne's root-group generation argument. Instead of adding a separate theorem that rank-one groups are perfect, step 3 writes the elementary commutator calculation supplied by the root-group conjugation identity. This retains the source's rank-one reasoning without a second perfection node or a node restating the item's conclusion. No SGA source is used. The latest blueprint direct-images proof and the chapter/unit records were read: this remains the inherited semisimple-group prerequisite along the existing alteration/GIT route and changes no chapter or unit.

The inherited blueprint ancestor is null: tools/blueprint_refs.py ancestor explicitly returned None. Both children preserve that result and add the item to the exact inherited via chain, with concrete Milne places appended to from.place. Searches of the whole imported blueprint for root group, root subgroup, SL2, and semisimple algebraic found no same statement; same_as is empty.

## Not duplicates

lem-sfb-reductive-root-subgroup-parametrizations vs lem-sfb-reductive-borel-pair-structure: both cite Milne Theorem 21.11, but the existing node supplies a maximal torus/Borel and the abstract root datum. It does not supply subgroup schemes U_alpha, their additive parametrizations, or the conjugation identity. Its coroot identity is also available there, but the new theorem's substantive missing content is the root subgroup and its algebraic conjugation action.

lem-sfb-semisimple-root-subgroups-generate vs lem-sfb-semisimple-group-perfect: generation by specified root subgroup schemes is a different assertion from equality with the derived subgroup. The item still proves the essential commutator factorization before generation can be applied.

lem-sfb-semisimple-root-subgroups-generate vs lem-sfb-reductive-borel-pair-structure: the existing node constructs root data and a torus/Borel pair, but does not assert generation by root subgroups. The semisimple generation theorem is Proposition 21.49(a), not the existing Theorem 21.11 root-datum clauses.

lem-sfb-reductive-root-subgroup-parametrizations vs lem-sfb-semisimple-root-subgroups-generate: the first gives root subgroup structure for a reductive group; the second asserts generation under the additional semisimplicity hypothesis. A nontrivial torus has no roots and shows why the latter conclusion cannot be included for all reductive groups.

## Review by Q129

I read Milne Corollary 21.50 and Proposition 21.49 on printed pp.439--440, then Theorem 21.11 and the root-group definition on pp.428--430 and formula (135) in 21.19 on p.431. These give the item, the root-group structure node and the generation node respectively. I checked the source's all-algebra-valued conjugation formula, rather than replacing it by an identity on F-points. Root weights here are characters of the algebraic torus; no Lie-algebra differential of a root is being treated as a nonzero character in positive characteristic.

Step 1 cites the actual statement of lem-sfb-reductive-borel-pair-structure: its final sentence says a semisimple group is reductive, and its existence clause supplies a split maximal torus. It also cites lem-sfb-smooth-connected-derived-subgroup: its statement supplies the smallest closed commutator-containing subgroup and the factorization, not merely a definition of derived groups. H is smooth, connected, affine and finite type exactly as both cited statements require, over the same algebraically closed F. I opened both node files and verified these clauses.

Step 2 cites the new root parametrizations statement. Its hypotheses hold for the pair obtained in step 1. Its statement explicitly gives the isomorphisms from G_a, conjugation by T on every F-algebra, and coroots with alpha(alpha-vee(s))=s^2. No existence of root-group morphisms is inferred from the abstract root datum of the Borel node.

Step 3 uses only that root-parametrization statement, algebraic closedness as defined in def-weil-algebraic-closure, and the derived-subgroup factorization statement opened for step 1. The monic cubic s^3-s-1 is nonconstant in every characteristic. A root obeys s(s^2-1)=1, so both s and c=s^2-1 are invertible. Thus t=alpha-vee(s) is a well-defined F-point; constants s,c are units in every F-algebra A. The displayed commutator follows from additivity, and the explicit map a |-> (t,u_alpha(a/c)) composes with the commutator morphism to u_alpha. Consequently the factorization through D holds as morphisms of schemes, including on nonreduced algebras. This is a few-line substitution in the two cited identities, so it is an elementary step, not a new lemma. The argument neither identifies closed subschemes from point sets nor assumes that the centre is reduced.

Step 4 cites the full statement of the generation node with K=D. D is closed by step 1 and contains every specified root subgroup by step 3. The semisimple and split-maximal-torus hypotheses are exactly those in force. This yields equality, including when the roots are empty. All step/node citations have verbatim excerpts checked against their statements in citations.json.

For B1--B10 I checked that both children are statement-only, self-contained, cite the relevant definitions, have single-escaped TeX after JSON parsing, and carry actual Mathlib search outputs. There are no Stacks citations requiring tag correction and no claimed Mathlib leaves. LeanFinder was tried twice in different words for each new node; LeanSearch, Loogle and grep were also run and their hits read. They return abstract root systems, Lie algebras, or abstract groups, not this group-scheme content. Existing DAG and whole-blueprint searches were done before creating either child. The only shared source place with an existing node is explained above.

For C1--C8 I checked every non-elementary input against a node's statement and avoided proof-only data. All proof dependencies are the union of the uses lists. The two existing mathematical inputs have the item's unit; definitions are generic notions. There is no off-route tool citation. For D1--D5 the children are genuinely distinct root-group results, with the actual commutator argument retained in the item's proof. No child restates perfection and none is proved in the item and then cited circularly.

For E1--E7 I tested the trivial group (empty roots), a nontrivial torus (structure node vacuous but generation inapplicable), SL2 in characteristic 2 (the square character remains nontrivial even though its differential vanishes), and arbitrary F-algebras in the commutator identity. Neither a characteristic-zero assumption nor a simply connected hypothesis is used. Every proof step is under 1000 characters; no step exceeds 2000 or hides an additional comparison lemma. The proof totals 1920 characters. The only presentation correction was removing the unused generic scheme dependency; no mathematical statement needed repair.

## Unfinished

The two supporting nodes are intentionally unsplit, as required for one-level stage 1. No other work remains in this delivery apart from the required server checks and push.
