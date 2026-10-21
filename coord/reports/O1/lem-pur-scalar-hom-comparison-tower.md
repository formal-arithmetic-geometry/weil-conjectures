# Worker report: lem-pur-scalar-hom-comparison-tower

## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-scalar-hom-comparison-tower.json`: statement node, split into seven proof steps; not a Mathlib leaf. The statement, its seven statement dependencies, creation record, and blueprint ancestry are unchanged.
- `citations.json`: eight entries covering every node cited by each proof step, with verbatim extracts of its statement.
- `report.md`: this report. `searches.jsonl` is the search command's own log.

No new nodes and no new Mathlib leaves. No unit record is changed: the item is not its unit's key statement.

## Attachments

None. The exact blueprint tag is absent from `lean/WeilConjectures/`. Searches by `scalarHom`, Hom/tower, `closedIhom`, and `ihomComparison` found the general project extension `WeilConjectures/Mathlib/CategoryTheory/Monoidal/Closed/Basic.lean`. In particular its `CategoryTheory.Functor.LaxMonoidal.ihomComparison_comp_app` (line 259), `ihomComparison_app_comp_map_app` (271), and `map_pre_app_comp_ihomComparison_app` (284) express useful abstract parts, with explicit proofs, but do not themselves state all of this item's derived coefficient comparison and identity-unitor clause. I do not claim an attachment for a partial match.

## WANTED

None. The literature needed for the argument is present.

## Source and corrections

I read Stacks `literature/stacks-project/sites-cohomology.tex`, equation-internal-hom and lemma-internal-hom (Tag 08J9), including its proof by K-flat and K-injective representatives; and lemma-pullback-tensor-product (Tag 07A4), including its bifunctoriality and normalized tensor comparison. The tag-to-label correspondence was checked in `literature/stacks-project/tags/tags`. Stacks gives the closed adjunction and tensor comparison; it does not state this exact coefficient-tower equation. The added equality calculations are therefore honestly marked `proof_origin.by = agent`.

I read the main-20261015 blueprint ancestor `sec-proetale-coefficients/sk-def-sf-operations/def-weil-derived-pullback-tensor-hom.md`, especially its last paragraph, and the recorded unit `sk-thm-sf-compatibility`, coefficient clause (7). The split supplies the Hom part of compatible coefficient passage and does not replace the unit route. The chapter and unit records and the three-level rule were read. The two existing theorem tools are explicitly declared in `split_report.tool_uses`.

There is no statement dispute. The item was an unsplit statement-only node. Its hypotheses are already adequate; its use of the tensor coherence equations is an explicit assumption. No additional flatness, perfectness, finite generation, boundedness or completeness is inserted. I made explicit the meaning of the identity clause: for the multiplication unitor $u:T_{id}\cong Id$, the equation is $H(u_P^{-1},u_Q)c^{id}=u_H$. This is an explanation in the proof, not a change of statement.

## Searches and existing nodes

Before writing I searched the DAG by internal-Hom comparison/tower/evaluation vocabulary, read the nearby scalar internal-Hom comparison and tower nodes, and ran `tools/blueprint_refs.py ancestor` plus blueprint searches for `scalar Hom`, `evaluation`, `coefficient tower`, and `scalar extension`. The relevant existing nodes were reused. The scalar restriction-Hom isomorphism nodes (`lem-sfb-closed-scalar-hom-comparison` and `lem-sfb-scalar-internal-hom-tower-coherence`) concern $U Hom(FK,N)\cong Hom(K,UN)$; this item concerns the generally noninvertible map $F Hom(P,Q)\to Hom(FP,FQ)$. They are not interchangeable. No new node or blueprint alias is needed.

I ran all new Mathlib searches through the required `batch2/msearch.py`, and read the returned hits. The five logged queries comprise two LeanFinder phrasings, Loogle, grep of `CategoryTheory/Monoidal/Closed`, and LeanSearch. Their exact queries and actual results are appended to the item's existing searches, which are retained. The services responded. Loogle reported the identifier `Functor.LaxMonoidal.ihomComparison` unknown. The LeanFinder hits `expComparison` and `expComparison_ev` were checked against `Mathlib/CategoryTheory/Monoidal/Closed/Functor.lean`, especially lines 47-113: these require Cartesian monoidal categories, whereas derived tensor is the tensor product of modules. The LeanSearch extension-scalar adjunction and pseudofunctor hits concern ordinary modules; they do not give this derived ring-sheaf Hom statement. The grep hits define the internal Hom in a groupoid functor category. None is an exact match or a one-line specialization of the item.

## Review by O1

I checked the split against delivery-errors B through E with the source and both cited node statements open. There are no new nodes that could be elementary, duplicate, a clause renamed, insufficiently self-contained, or missing a definition/search/source. The proof stays in the item rather than moving its content to another node. Each step is shorter than 1000 characters; no step exceeds the 2000-character review threshold or hides a source lemma under a phrase such as 'transports' or 'standard'.

Step 1 uses exactly the closed natural Hom bijection and evaluation formula in `lem-sf-ringed-derived-closed-symmetric-monoidal`. Its source convention is $H(P,Q)\otimes P$, while the item uses $P\otimes H(P,Q)$. Composing with the same theorem's natural symmetry gives the latter convention and its injective uncurrying map. Evaluation naturality then follows by applying the natural bijection to a morphism in each variable. The small site and commutative ring sheaf hypotheses hold for each of $R,S,V$, so the theorem applies to every unbounded object in the item.

Step 2 uses that same bijection to spell out the evaluation equation defining each $c$. Step 3 uses its naturality and injectivity, together with the given natural tensor comparison: I wrote the common uncurried map for arbitrary $f:P'\to P$ and $g:Q\to Q'$. Thus the variance and the intermediate source $T_aP'$ are checked, rather than asserted. Step 4 substitutes Step 2 twice, with the naturality square of $\mu_b^{-1}$ between the substitutions. Its displayed expression has source $T_bT_aP\otimes T_bT_aH_R(P,Q)$ and target $T_bT_aQ$.

Step 5 cites precisely the tensor-tower clause of `lem-sfb-scalar-hom-tensor-coherence`. I read its full statement and Lean-record equation to check the order of the tensorators and the direction $\alpha:T_bT_a\to T_{ba}$. The premise of the item expressly assumes these equations for the comparisons in question, so I do not invoke the separate normalized-model existence theorem or assume a new model. Inverting the tensorators gives the displayed equation for $t^K$, with no claim about the Hom map being invertible.

Step 6 uses the closed adjunction node for natural evaluation and injective uncurrying; Steps 4 and 5 already supply its other equations. I checked the contravariant transport is $\alpha_P^{-1}$, whereas the covariant transport is $\alpha_Q$. Both maps being compared run from $T_bT_aH_R(P,Q)$ to $H_V(T_{ba}P,T_{ba}Q)$. The calculation writes out the naturality of $\alpha$ at evaluation and its tensor equation, and ends with the defining uncurried map of $c^{ba}\alpha_H$.

Step 7 cites both the closed adjunction statement and the identity clause of the tensor coherence statement. I checked the inverse unitor occurs in the tensor coherence input and the multiplication unitor occurs in the final transported map. Cancelling those isomorphisms yields the needed tensor identity. The resulting equality of uncurried maps proves the claimed identity after applying the source and target unitors.

For C4, every citation's quoted material is taken verbatim from the cited statement, not its proof or a mere definition; `citations.json` covers all eight uses. For C1, all substantive inputs are either the explicitly assumed comparisons, these two cited theorems, or earlier displayed calculations. Tensor bifunctoriality, naturality of a specified natural isomorphism, cancellation of an isomorphism, and injectivity of a supplied bijection are the elementary operations in Steps 2-7. No K-flat replacement or inverse-limit theorem is used implicitly in these calculations.

I tested the formulas on identity maps (including one identity leg of a tower), on zero arguments, and on the one-object site with nonflat ring maps such as $\mathbf Z\to\mathbf F_2\to\mathbf F_2$. They remain typed without replacing any derived tensor by ordinary tensor. On a one-object site with $R=k[\epsilon]/(\epsilon^2)$ and $S=k$, the same symbolic equations apply to unbounded derived objects, so no finite-projective or perfectness assumption is being smuggled into an invertibility claim. The proof never uses inverse Hom comparisons. These checks also distinguish the item from scalar restriction-Hom isomorphism nodes.

## Not duplicates

No new nodes. The two cited existing results have different statements: closed tensor-Hom adjunction and tensor coherence, respectively. Neither restates the Hom comparison tower conclusion.

## Unfinished work

None in the authorized stage-1 split. No Lean was written, no compiler or build was run, and nothing was written in the shared repository or launcher. Delivery validation is by the required server-side dry run.
