# lem-sp-affine-counit-scalar — Q62 stage-1 delivery

## Files written

- `dag/nodes/sec-smooth-purity/lem-sp-affine-counit-scalar.json`: statement, unchanged; split into eight proof steps using fourteen existing nodes. No new nodes and no new Mathlib leaves.
- `citations.json`: twenty entries, one per cited node per proof step, copied verbatim from the corresponding existing statements.
- `searches.jsonl`: the five new searches actually run with the prescribed msearch command. Their results are appended to the item's inherited searches without removing earlier research.
- `report.md`: this report. The sandbox also contains the local writing script, which is not a delivered project file.

## Attachments

None. Searched `lean/WeilConjectures/` for the blueprint tag, affine counits, scalar/coefficients and the affineTrace names. There is no declaration stating this item. Read `WeilConjectures/EtaleCohomology/Purity/Smooth/Reduction.lean`: `map_smoothPurityTrace` assumes coefficient-counit compatibility (`hS`); it does not prove the compatibility sought here. Its other scalar results also take compatibility data as hypotheses, so they do not attach this node.

## WANTED

None. All sources used are in the read clone. No source was downloaded.

## What needed expansion

The item had no proof. Its existing statement already fixes the actual ordered adjunction and the coefficient map for a specified compactification; no statement correction was necessary. The source Charts paragraph's assertion that iterated integration commutes with coefficients needs both a finite-Tor domain check and identification of the left scalar map after composition/refinement. An unspecified isomorphism of compact-support functors would not suffice.

The current unit is `sk-lem-sp-reduction`, step 2. Its chapter, unit statement and route are retained. This item is not the unit's key node, so no unit record is changed. The unit's use of the projective-line package and integral open evaluation is realized by the existing smaller nodes `lem-sp-p1-counit-scalar` and `lem-sp-etale-sum-counit-scalar`, rather than by creating new versions of those claims.

## What remains unfinished

Nothing in this one-level split. The existing smaller nodes are cited as statements; proving their currently unsplit assertions is outside this item's scope. No Lean was written or compiled.

## Not duplicates

No new nodes. Whole-DAG keyword searches and whole-blueprint searches (`affine coefficient`, `ordered affine`, `projective counit`, `counit scalar`, and the relevant affine/counit concepts) found no second blueprint node stating this arbitrary finite-ring, ordinary-etale, actual-counit assertion. The ordered-affine blueprint hits concern normalized purity/composition in more restricted coefficient conventions, rather than this coefficient comparison. The DAG already contains all the needed primitive scalar and coherence statements, which are reused.

## Review by Q62

I read `coord/brief-stage1.md`, `stages/1-dag.md`, the three-level requirements in SETUP, GOAL, the worker role, and delivery-errors B–E, including the repeated B–E checklist. I read the smooth-purity chapter record, the current `sk-lem-sp-reduction` unit and its main-20261015 section, and the complete Charts paragraph of `sk-lem-sp-reduction-exceptional.proof.md`. This is an agent-written expansion of that blueprint argument; the proof origin is marked agent. I checked the categorical counit formula against Stacks Tag 0DV0, `categories.tex`, `lemma-compose-counits` (statement and proof), and against Mathlib `Adjunction.Basic` lines 567–582. I read `Adjunction.Mates`' actual mate correspondence, its counit equation at line 122, and the horizontal-pasting statement at line 209. The compactification background was checked in Stacks Tag 0F7J, `more-etale.tex`, `lemma-shriek-composition`, and Tag 0GL6, `remark-Rf-lower-shriek-change-of-rings`. Those tags alone are not claimed to prove the enhanced coefficient/refinement square: that stronger square is explicitly supplied by the existing `lem-sp-et-proet-coefficient-compatibility` statement.

For step 1 I opened `def-amb-affine-trace-tower` and checked that it supplies the ordered tower and the standard projective-line compactifications. I opened `lem-sp-etale-ctf-chart-domain`: its last sentences really assert preservation by coefficient extension and by every standing pullback with positive Tate twist and shift, and its first assertion gives compact-support preservation. Thus applying the scalar lemmas to the intermediate right-adjoint objects is legal. Standing finite-type schemes over the field, and the coordinate affine/projective schemes over them, meet the same hypotheses; N is invertible because ell differs from the characteristic. The proof uses bounded-below comparisons only on these bounded objects and their bounded coefficient extensions. In particular it does not infer that an arbitrary nonflat tensor functor preserves D+.

For step 2 I read all of `def-weil-pbc-etale-sum-extension`, `lem-sp-etale-sum-counit-scalar`, and `lem-sp-p1-counit-scalar`. The definition explicitly identifies open sum extension with extension by zero. The two lemmas give the two right comparisons as mates of the inverses of the specified left comparisons, for arbitrary finite ell-primary ring maps. Their formulas refer to the evaluation counit and the normalized actual projective-line counit, respectively. This avoids borrowing mere base-change compatibility from `lem-asd-ordinary-finite-p1-adjunction` as if it were a scalar-change theorem. An open chart is separated etale of finite type, and every intermediate input is in Dctf by step 1.

For step 3 I read the full statements of `def-weil-pbc-composite-adjunction`, `def-weil-pbc-adjunction-mate`, and `lem-weil-pbc-mate-pasting`. Clause 2 of the latter is pasting along the adjunctions, exactly the direction required for composing the open and projective adjunctions. I checked the orientation carefully: the left square for taking mates is the INVERSE of the coefficient comparison, while the resulting right square is the forward tensor comparison. The counit equation then becomes the displayed equation after precomposition with the forward coefficient map. The final use of `lem-sp-et-proet-coefficient-compatibility` is justified by its explicit definition of the left comparison as the proper map followed by the extension-by-zero identification, not by a claim about arbitrary isomorphisms.

For step 4 I read `lem-amb-affine-space-top-trace`, `lem-asd-etale-finite-twist-pullback`, `lem-asd-finite-etale-twist-line`, and `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`. Their statements provide the ordered right normal form, compatible pullback of every Tate power, local flatness of the Tate factors, and the K-flat tensor/pullback computation. The remaining check is elementary balanced-tensor reassociation, written out locally and checked before descent; no independent geometric or homological lemma is concealed. In particular this step makes the right square the canonical a from the question. Even shifts do not add a sign. This remains valid for a nonflat map, such as Z/ell^2 -> Z/ell.

For steps 5–6 I checked the identity base case and the actual successor functor types. The left composite is F_r L_u and the right composite is W_u G_r; the two displayed coefficient composites have exactly these sources and targets. The cited composite-adjunction definition fixes the counit, and the same clause 2 of mate pasting applies to the induction hypothesis and the line case. The mate definition turns that conclusion into the counit identity. There is no circular appeal to the item in the successor. It is an induction on the number of coordinates, with a stated invariant and a separate base case.

For step 7 I opened `lem-amb-etale-compact-comparisons` and the whole `lem-sp-et-proet-coefficient-compatibility` statement, not only their proofs. The former supplies coherent bounded-below composition/refinement comparisons. The latter explicitly states BOTH the refinement square and the composition equality for the specified coefficient maps, including common refinements, identities and associativity, and with no flatness assumption. The equality with C_d follows by finite iteration of precisely those equalities. It therefore refers to the fixed compactification c even when the composition construction used a different candidate. The domain condition from step 1 is checked on G_d K and all intermediate inputs.

For step 8 I checked the direction of C_d and the transported-counit formula. Precomposition by T(C_d) is invertible because every functor preserves isomorphisms. Naturality of C_d at a_d makes the left side the ordered counit expression; the right side is the image of the ordered counit. Cancellation proves the required equation with the correct, fixed beta. The cited affine-space trace node defines the ordered adjunction and its bounded-below identification; I do not infer a general coefficient equation from its constant-object trace-isomorphism clause.

I tested d=0, d=1, the empty base, K=0, identity coefficient maps, nonflat quotient maps, and N=1 (which forces the coefficient rings to be zero). The base case and the formulas have the correct identity/zero values. No claim uses a flatness or finite-projective-dimension hypothesis on B. Ordinary etale finite Tate lines are used throughout, with no pro-etale or adic substitution. No SGA route is used.

The B–E checks produce no new-node schema or duplicate issues because no new nodes are introduced. Every proof citation has a quotation in `citations.json`; each quotation was checked against the cited statement. All non-elementary facts used in the steps are cited; the only elementary steps are balanced-tensor normalization, the identity base case, and cancellation/naturality. The longest step is below 2000 characters. The auxiliary off-unit uses are declared as generic tools in `split_report.tool_uses`, with individual reasons; they implement the fixed unit route instead of replacing it. Mathlib's general pasting and composite-counit facts are already existing Mathlib leaves in the DAG, so no redundant leaf was created.

The five new msearch calls were read in full. Loogle finds the general `CategoryTheory.Adjunction.comp_counit_app`; the grep verifies it at Mathlib/CategoryTheory/Adjunction/Basic.lean:580, and I read its formula. The two semantic phrasings find generic adjunction counits, module scalar counits, condensed adjunctions or affine-space maps, not this geometric assertion. The item's inherited searches are retained. No unavailable service was recorded as an absence, and no unrun search was added.

## Validation

The required delivery dry run will run the server's preflight, DAG and split checks before push; no checker is run locally.
