# Q132 — lem-coef-ordinary-bar-evaluation-naturality

## Changes and result

The statement is unchanged. The item is split into seven explicit operator calculations; there are no new nodes and no Mathlib leaves. No Lean is written or compiled. The sandbox initially had only dispatcher marker files, so I copied the current unsplit repository item and retained all its original fields, citations, searches and ancestry. Added searches are genuine msearch.py runs recorded in searches.jsonl.

The proof gives the operation of every monotone map in each simplicial direction, checks the mixed identity, checks evaluation against both operators, verifies the change-of-data maps and their square, writes the composition formula for two triples, and restricts to the diagonal. Every step is below 2000 characters. There is no hidden homotopy-invariance assertion: only the displayed BK construction and ordinary functor/naturality equations are used.

## Sources and blueprint route

I read Dwyer–Kan, *Calculating simplicial localizations*, proof 9.10, printed pp.32–33 (PDF pages 16–17), online at https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/dwyer-kan-2.pdf. The regrouping there has an A-chain, an arrow into P(A_0), the slice W/P(A_0), and evaluation to the coefficient at P(A_0). It matches the item's orientation after reversing the source's chain indices. The source discusses a weak equivalence; the present item establishes only the operator/naturality prerequisite. In particular this split never invokes the terminal-object weak-equivalence assertion as an uncited theorem.

WANTED: Dwyer–Kan, *Calculating simplicial localizations*, proof 9.10, pp.32–33, for lem-coef-ordinary-bar-evaluation-naturality (not present in this machine's literature list; read online, no download or repository write performed). The detailed proof is marked agent-written because the paper does not spell out these strict operator and composition checks. No Stacks tag states this chain-indexed construction, and none is invented. No SGA source is used.

I read the sec-six-functors chapter and sk-prop-sf-biduality-general unit records, the ancestral prop-coef-integral-exceptional-adjoint statement and proof in the old master snapshot, and its current main-20261015 statement and separate .proof.md under sec-six-functors/sk-thm-sf-package. This supplies the existing ancestry's paragraph-2 coefficient-adjunction foundation, through the ordinary two-sided bar comparison. The current blueprint moved that ancestor's file; I record its current path without changing maintainer-owned unit metadata or the inherited ancestry. The item's own statement has no blueprint_update. The auxiliary combinatorial proof replaces no chapter or unit step.

Whole-blueprint searches for “simplicial replacement”, “Bousfield”, and “bar evaluation” found no matching imported statement. DAG searches included comma-chain and terminal-slice terminology and the wider evaluation/augmentation terms. The ordinary two-sided bar comparison is the parent, not a lemma available to prove its own descendant. The Thomason comparison concerns nerves of Grothendieck constructions and their weak equivalences, and the slice-cone prism concerns joins of arbitrary simplicial sets; neither states this item. No new node is needed for any of the elementary equations.

## Attachment and Mathlib searches

The search in /home/ubuntu/weil-src-slopmaster2/WeilConjectures for the exact item id, Bousfield/bousfield, comma-chain, two-sided-bar, and simplicial-replacement terminology found only unrelated Bousfield-localization imports. There is no exact project attachment and no declared upstream proof used. No declaration from the read-only master checkout is treated as a finished proof.

Ran LeanFinder with two phrasings, LeanSearch, Loogle and three concept/source grep queries plus a targeted augmentation grep. All returned successfully; their exact queries and service digests are preserved in searches.jsonl and added to mathlib_searches without altering inherited records. I read SimplicialObject.augment and augment_hom_zero in Mathlib/AlgebraicTopology/SimplicialObject/Basic.lean:504–523, CategoryTheory.nerve/nerveMap in AlgebraicTopology/SimplicialSet/Nerve.lean:35,53, the NatTrans definition/naturality field in CategoryTheory/NatTrans.lean:55–59, and lanEvaluationIsoColim in CategoryTheory/Functor/Flat.lean:302. The generic augmentation construction requires supplied compatibility, ordinary nerves do not include this simplicial coefficient diagram, and ordinary Kan-extension evaluation does not state this bisimplicial construction. NatTrans.naturality is one of the defining equations written out in the proof, not a Mathlib leaf for the entire item. Thus the item is not a one-line specialization of a hit. A file-scoped grep returned its line numbers as file labels; I retained that result unchanged and used a directory-scoped query to obtain the real file and line for augment.

## Review by Q132

For the item I checked the source's slice orientation and coefficient placement against Dwyer–Kan 9.10 as above, and checked the exact statements of lem-coef-bousfield-kan-comparison-calculus, def-coef-zigzag-homotopy-calculus, and def-weil-pbc-simplicial-set. There are no new nodes requiring source reviews. The zigzag definition is retained solely as an inherited statement dependency for the nerve convention; the proof does not use its homotopy-calculus assertions. Each quote in citations.json is copied verbatim from a cited statement, never from a cited proof.

Step 1 cites the simplicial-set definition: its contravariant functor law is exactly the requirement being verified. The formula postcomposes every slice structure map by P(v), and the displayed composite-arrow equation proves all i-direction identities, including degeneracies. Step 2 cites only the BK comparison-calculus statement, whose coproduct construction and face/degeneracy prescription give the q row over the small category C/Px_0. This use takes no weak-equivalence conclusion. I wrote the general beta formula to expose the mixed-variable check, rather than infer it from a generic naturality assertion.

Step 3 cites the simplicial-set definition's statement that morphisms are natural transformations, used for the equality beta* X(t) = X(t) beta*. The other equality is exactly the given slice relation t_b h_0b = t_0, and the i-direction check is functoriality of X. Step 4 cites that same definition for the simplicial components of eta and writes both its ordinary naturality equations. The strict equality PK=HP' is used on objects to type the target slice, and on arrows to compare postcomposition and the first coefficient face. No comparison is substituted for an equality of functors.

Steps 5 and 6 cite no nodes: the first is the naturality axiom of the given eta at the given t'_0, evaluated on a simplex; the second explicitly multiplies the two induced functions and identifies their coefficients with lambda_d = eta_{Jd} theta_d. These are elementary equations in the stated data, not extra lemmas or clauses shifted into children. Step 7 cites the BK node's chain/operator formula and its explicit definition of diagonal. Equalities of the bisimplicial maps restrict pointwise to bidegrees (n,n), so no diagonal homotopy theorem is used. The exact cited sentences are sufficient for the use in each step (C4), and every remaining operation is a supplied definition or a displayed equation (C1).

The hypotheses checked are smallness of the slice and chain-indexed coproducts (they are subsets/unions of the object and morphism sets of the given small categories); covariance of X, P and H; the orientation t_{a+1}h_{a+1}=t_a; and that eta is a natural transformation valued in simplicial sets. There is no finality, cofinality, fibrancy, objectwise equivalence, or terminal-object hypothesis used. I tested i=q=0, deletion of the first vertex (the sole face changing the coefficient), an arbitrary monotone map skipping several initial vertices, and constant monotone maps (identities inserted in the selected chain). When alpha(0)=0 or beta(0)=0 the transport arrow is an identity, so the same formulas still apply. Empty A gives empty source and target in every bidegree, with unique maps; when C is empty a functor P forces A empty. For the terminal category the equations reduce to simplicial naturality of the coefficient map. Arbitrary noninvertible eta also satisfies the written identities. The item needs no statement correction or STATEMENT-DISPUTED marker.

I reviewed delivery-errors B–E in full: no new statement-only nodes or missing hypotheses; no fake Stacks tags or Mathlib leaves; exact citations and no appeal to another node's proof; no dependency on the parent or another descendant; no moved clause, hidden standard comparison, or unit-route replacement; and the strict compatibility and composition computations are written explicitly. All proof steps remain shorter than 2000 characters.

## Not duplicates

No new nodes were created, so there are no new/existing node pairs requiring a duplicate exemption. The proof reuses the existing BK construction and simplicial-set definition.

## Dependencies and remaining work

Statement dependencies are unchanged. Proof dependencies are exactly lem-coef-bousfield-kan-comparison-calculus and def-weil-pbc-simplicial-set, the union of step uses. No Lean imports or sorry declarations are added or removed. These existing nodes retain their own independent stage status; this delivery splits this item by one level only. No off-unit statement tool is used.

## Validation

The citations were checked against the current dependency statements while producing citations.json. The required server `review_split` and full `deliver.py --no-push` preflight both pass on the retained split. The latest dry run completed successfully:

```
OK (not pushed) deliver/Q132/lem-coef-ordinary-bar-evaluation-naturality at 52c3de8a38: preflight passed
```

The earlier dry-run failures citing malformed JSON in the shared `lem-coef-terminal-local-kan-corepresentability.json` were external to this delivery and have since cleared in the shared server snapshot; no unrelated file was edited. No Lean imports or sorry declarations are added or removed.
