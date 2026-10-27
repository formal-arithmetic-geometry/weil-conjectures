# Worker report: lem-sfb-henselian-colimit-stage-root

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-henselian-colimit-stage-root.json`: existing statement, now split into five steps; no exact Mathlib match.
- `citations.json`: verbatim statements for each of the three step citations.
- `report.md`: this report. `searches.jsonl` was produced by the prescribed search command.

New nodes: 0. New Mathlib leaves: 0. No Lean written or compiled.

## Attachments

None. I searched `lean/WeilConjectures/` for the exact blueprint tag and for henselian/local-ring colimit notions. The existing `filteredColimit_henselianPair` concerns existence of a henselian colimit pair, not the requested polynomial, residue representative, and stage root. `IsLocalRing.idempotent_lifting_iff_monic_simple_root_lifting` supplies the criterion already represented by the existing root-lifting node, not this stage-descent item. No declaration found states all the item's clauses.

## WANTED

None: the sources used are present.

## Audit and changes

The statement is unchanged. The source is Stacks algebra.tex, Tag 04GI, `lemma-colimit-henselian`, lines 42926--42960, specifically the monic-polynomial and simple-root portion of its proof. The source first identifies the local colimit and residue colimit; this item correctly assumes those facts and proves only the subsequent stage lifting. I read the source's earlier `definition-henselian` (04GF), and the existing root-criterion statement against more-algebra.tex `definition-henselian-pair` (09XE) and `lemma-characterize-henselian-pair` (09XI), including the local-ring remark. Thus the idempotent formulation in the item's terminology is connected to simple-root lifting by a theorem, not treated as a definition.

The imported item had no proof. I supplied the monic lift with degree exactly n by descending only its n lower coefficients and setting the leading coefficient equal to 1. I made the source's inference from a zero image in the residue colimit explicit: locality of alpha_i makes rho_i reflect zero. Consequently no unstated eventual-equality lemma or injectivity of the ring transitions is needed. I wrote the two finite evaluation sums, including the integer coefficients in the derivative, instead of merely asserting compatibility.

I read the chapter and unit records and the current blueprint direct-image proof, `sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`, paragraph (3). This split retains the inherited root-tower/local-ring permanence input below that paragraph. `blueprint_refs.py ancestor` returns None because the inherited created.item chain has no imported blueprint ancestor; I retained its existing from.node, via, and specific place, and did not invent an ancestor or change another node. Whole-blueprint searches for henselian, simple root, monic, henselian colimit, and finite data found no exact blueprint duplicate of this stage-root statement. The finite-data search did find the existing Nagata node, which is reused.

## Mathlib and duplicate searches

The inherited search history is retained. Fresh searches were run only through msearch.py and recorded as returned in searches.jsonl: LeanSearch and LeanFinder on stage descent and simple-root lifting; Loogle `HenselianLocalRing, DirectLimit`; a RingTheory grep combining henselian/simple-root/monic with colimit/DirectLimit; and a second LeanFinder phrasing about finite coefficients. All services answered. The semantic hits include HenselianLocalRing.TFAE, is_henselian, and Polynomial.lifts_and_natDegree_eq_and_monic. The former supply root lifting in an already henselian ring; the latter assumes coefficient lifts along a single map. None supplies the whole directed stage-descent statement in one specialization. I read Henselian.lean lines 94--145 to check that distinction. The empty Loogle and grep results are recorded as such. No new node or invented search was added.

DAG searches included 04GI, lemma-colimit-henselian, simple residue roots, finite-data descent, eventual equality and the root-lifting criterion. The three mathematical ingredients already have nodes, so creating polynomial-descent or simple-root-stage clauses would duplicate existing ingredients or the item itself. No new-node duplicate pairs require a Not duplicates section.

## Review by Q65

I checked the five proof steps against the open source and the statements of every cited node.

Step 1 is coefficient arithmetic: a monic degree-zero polynomial is 1, and the residue field is nonzero because its maximal ideal is proper. The root hypothesis therefore excludes n=0 without adding a hypothesis. The coefficient expansion uses exactly the given degree n.

Step 2 cites `lemma-nagata-filtered-colimit-finite-data`. Its statement explicitly gives simultaneous lifts of finitely many selected elements in a nonempty directed commutative-ring colimit; the list of equations may be empty. These are precisely the item's A_i and A, so the hypotheses apply. I use only its element-lifting clause. Setting the top coefficient to 1 proves monicity and degree n even when transition maps kill lower coefficients. This is a generic tool from the Nagata unit, declared in split_report.tool_uses, not a change to the geometric route.

Step 3 cites clause (1) of `lem-pc-filtered-colimit-commrings-elementwise`, which explicitly supplies a representative of every element in any small filtered commutative-ring colimit. The index is small by assumption and filtered by the directed-poset argument written in the step. The k_i are commutative rings and the statement assumes their ring colimit is k; no colimit of fields or large indexing category is substituted. Directedness provides a common upper bound for p and q. The quotient transitions are well-defined because local transitions carry maximal ideals into maximal ideals. The displayed cocone equalities prove both required image equalities. This existing Mathlib leaf is a generic element-representative tool.

Step 4 is elementary and self-contained. A representative x of a residue class mapping to zero has alpha_i(x) in m, hence x in m_i by the explicitly assumed inverse-image equality. This proves exactly the zero reflection needed. The first finite sum has image zero and therefore is zero; the derivative sum has nonzero image and therefore cannot be zero. Preservation of sums, products and integer multiples proves the formulas in every characteristic. I checked that this argument never assumes injective transitions A_i to A_j, or that a merely vanishing image of a general ring element already vanishes at its stage.

Step 5 cites `lem-weil-pbc-henselian-local-root-lifting`. Its statement explicitly equates the idempotent notion used by the item with monic simple-residue-root lifting, giving both f_i(a_i)=0 and the prescribed residue class. The ring A_i is henselian local by assumption, step 3 gives monicity, and step 4 gives both root conditions, so every hypothesis is available. This is the other generic off-unit tool declared for maintainer review. Its statement, not an internal construction in its proof, is what is used.

For B--E: there are no new statement-only nodes to check; all non-elementary inputs have named nodes and verbatim quotations in citations.json; the proof dependencies are exactly the union of uses. No parent or descendant is cited. The longest step is 784 characters, below the long-step threshold. The proof carries the assembly itself rather than transferring a clause to a new node. I tested degree zero (inconsistent root hypothesis), degree one (the derivative is 1), constant diagrams, positive characteristic (integer coefficients may vanish but the assumed derivative value remains nonzero), and noninjective local maps such as k[epsilon]/(epsilon^2) to k. Residue zero reflection and the explicitly monic polynomial still work in the last case. No false statement, missing hypothesis or source correction was found.

## Unfinished work

None in the stage-1 split. Independent maintainer review and the later Lean formalization remain outside this worker's delivery scope.
