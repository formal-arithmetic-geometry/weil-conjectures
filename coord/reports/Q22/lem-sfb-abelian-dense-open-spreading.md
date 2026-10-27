# Q22: lem-sfb-abelian-dense-open-spreading

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-abelian-dense-open-spreading.json`: statement, split; unchanged statement; seven explicit proof steps using existing nodes. Not a Mathlib leaf.
- `citations.json`: 16 step/node pairs with verbatim excerpts of the cited statements.
- No new DAG nodes and no Mathlib leaves created. `searches.jsonl` is the search tool's own log; `prepare.py` is sandbox-only preparation code, not delivery content.

## Attachments

None. Searched the current project `lean/WeilConjectures/` for the blueprint id and the notions abelian scheme, abelian spreading, and `AbelianScheme`. There is no declaration of this dense-open extension theorem. `IsAbelianVariety` in `AlgebraicGeometry/AbelianVariety/Defs.lean` only defines an abelian variety. The existing commutativity and geometric-integrality declarations belong to their existing nodes; no attachment claim is needed.

## Wanted literature

WANTED: Bosch–Lütkebohmert–Raynaud, Néron Models, §1.4 printed pp.19–20, for lem-sfb-abelian-dense-open-spreading. The referenced local PDF is absent. Read the primary-source scan at https://www.math.stonybrook.edu/~kamenova/homepage_files/Bosch_Raynaud_Neron_Model_tc.pdf, PDF pp.25–26, especially the paragraph before Theorem 3 allowing the direct limit argument. The operative proof is independently written from the local Stacks source, so `proof_origin.by` is `agent`.

## Audit findings and corrections

The imported item had no proof. Its statement is true and has not been changed. Removed `def-weil-finite-type-morphism` from statement dependencies because the statement does not use finite type; its properness definition supplies this notion transitively. Retained the inherited source, creation data, earlier recorded searches and blueprint ancestry. The blueprint ancestor command reports `None`; the null ancestor and inherited chain are preserved, and the source-place description is made precise. Read the latest blueprint's `sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md` and the current `thm-pd-spreading-out.md`. The former concerns the six-functor statement, not a separate spreading assertion; this node is a generic tool deep below it, and no unit/chapter route is replaced. No unit realization fields apply to this created auxiliary node.

Searched the whole DAG for tags 01ZM, 0C0C, 081F and 055G and for spreading, smooth/proper descent, connected generic fibres and finite-presentation permanence. Read and reused `thm-pd-spreading-out`, `lem-weil-pbc-descend-smooth-qcqs`, `lem-weil-pbc-eventually-proper`, and `lem-sbc-generic-geometrically-connected-spread`, rather than making duplicates. Also reused the existing ring-localization colimit and affine scheme-limit nodes and existing finite-presentation permanence nodes. `blueprint_refs.py search` was run for spreading, abelian scheme, abelian, geometrically connected generic, and smooth descent; no blueprint statement equals this item. The latest blueprint text search found `cor-pd-finite-level`, which instead descends a specified Jacobian descent datum to a finite separable field, not a group scheme to an open subset.

Current logged Mathlib searches used LeanFinder twice with different formulations, LeanSearch, Loogle and grep. LeanFinder found integral Weierstrass equations or basic-open coordinate identities, LeanSearch smooth localization maps, Loogle no hits, and grep the TODO in `Mathlib/AlgebraicGeometry/SpreadingOut.lean:44`. Read that file's lines 14–44: it spreads a morphism between already fixed schemes and explicitly does not yet spread morphism properties. These are not one-line specializations to the item. No service was unavailable. No fabricated search was added; existing searches from the original node remain historical material.

## Review by Q22

I read the actual BLR §1.4 discussion before Theorem 3, which permits constructing the dense-open abelian scheme directly by limit arguments instead of using the full Néron-model argument. I expanded that permitted limit argument using Stacks `algebra.tex`, Tag 00CR (`lemma-localization-colimit`); `limits.tex`, Tags 01YW/01YX (affine limits), 01ZM (`lemma-descend-finite-presentation`), 0C0C (`lemma-descend-smooth`) and 081F (`lemma-eventually-proper`) in Situation 081D; and `more-morphisms.tex`, Tag 055G (`lemma-geometrically-connected-generic-fibre`). I also read `groupoids.tex`, the connected group-scheme lemma and the abelian-variety commutativity lemma. There are no new nodes requiring a separate source review.

Step 1 uses exactly the ring-localization colimit statement and the affine case of the scheme-limit statement. I used finite subsets of nonzero elements as the directed *set*, avoiding conflating a divisibility preorder with a partial order. The colimit comparison is written via the universal property: each nonzero element is inverted at its singleton stage. The domain hypothesis ensures every finite product is nonzero and the principal open contains the generic point.

Step 2 reads smoothness and properness from `def-sc-abelian-variety` and their actual definitions: local finite presentation, quasi-compactness and separatedness imply finite presentation, with quasi-separatedness supplied by the closed diagonal. Clause (1) of `thm-pd-spreading-out` supplies an underlying finitely presented scheme and a generic identification, and nothing about a group law or smoothness at the finite stage is assumed. This corrects the possible shortcut of attributing group descent or property descent to 01ZM alone.

Step 3 uses the actual base-change and source-permanence clauses of `lem-weil-pbc-qcqs-morphism-permanence` and the two ring-map finite-presentation clauses of `lem-weil-pbc-finite-presentation-base-change-composition`. The latter is applied on affine charts, not quoted as an already-stated scheme theorem. These verify finite presentation and qcqs for the product sources. Clause (2) of `thm-pd-spreading-out` then extends each of multiplication, inverse and identity; it applies to schemes of finite presentation, not just etale schemes. Product identifications are their universal properties. The finite common upper bound is the union of the relevant finite subsets.

Step 4 uses `lem-sc-av-commutative` only for the generic commutativity equality, and clause (3) of `thm-pd-spreading-out` only for eventual equality of parallel maps. It spells out associativity, both unit laws, both inverse laws and commutativity with the correct sources (triple product, single copy or double product). No appeal is made to a proof hidden inside either cited node. All six relations are finite in number and stay equal after further restriction. Thus the model and its chosen generic identification really are group-theoretic.

Step 5 uses the geometric-integrality conclusion actually present in `lem-sc-abelian-variety-characterization`, which gives geometric connectedness of the generic fibre, and the full open-neighbourhood conclusion of `lem-sbc-generic-geometrically-connected-spread`. Its finite-type and irreducible-base hypotheses hold: the model is finitely presented and the base ring is a localization of a domain. There is no appeal to ordinary connectedness being geometric for an arbitrary scheme. I choose a principal-open neighbourhood inside the produced open so all subsequent work stays in the same limit system. Later stages are open restrictions, so their residue fields and fibres agree with those already checked. The identity section also precludes empty fibres.

Step 6 uses the exact statements of the eventual-smoothness and eventual-properness nodes. The stages, source and target are qcqs; the stage structural morphism is locally of finite presentation, hence locally of finite type; the limit map is the original smooth proper map. I apply eventual smoothness first, then properness on that cofinal tail. This uses the eventual smoothness node's explicit persistence clause, avoiding an unrecorded preservation assertion to combine independent stages. A cofinal tail has the same fraction-field colimit by step 1's universal-property argument. Group equalities and connected fibres persist by the explicit preceding arguments.

Step 7 is elementary collection of the data already constructed. All its assertions were established in the preceding steps. Every non-elementary input is an existing cited node, and `citations.json` was checked by exact substring membership in those nodes' current statements. Off-unit generic tools are declared individually in `split_report.tool_uses`; I did not write maintainer-owned `tool_uses`.

For B–E I checked that no auxiliary node restates a clause, no new statement hides a proof, all dependencies exist, and no new object or notion is left implicit in a new node (there are none). The statement needs no extra excellence, completion or perfect-residue-field hypothesis; no such hypothesis enters any of the limit tools. Tested dimension zero for A (the trivial group extends by the base itself), a discrete valuation base (the resulting open is allowed to be only its generic point), arbitrary characteristic and imperfect fraction fields (the abelian-variety geometric-integrality input applies over every field), and empty removed complement (no shrinking is forced if a model already works). Each stage is nonempty even if elements used for denominators are units. No good reduction at all closed points is asserted. Every proof step is below 2000 characters; none conceals an unnamed comparison or a separate standard lemma. No SGA route or source is used.

## Not duplicates

No new nodes. Existing spreading and descent nodes are cited directly.

## Unfinished work

None in the authorized stage-1 split. Remaining lower-level lemmas retain their existing DAG states; no Lean or compiler was invoked. Delivery validation follows below.

The first completed dry-run diagnostics requested a longer citation excerpt for the principal-localization colimit; expanded that quote to the full colimit clause, retaining the same argument and dependency.
