# Stage-1 delivery: lem-sp-scalar-compositor-replacement-pasting

## Worker report

1. Files written: `dag/nodes/sec-smooth-purity/lem-sp-scalar-compositor-replacement-pasting.json` (statement; now split, not a Mathlib leaf), this report, and `citations.json`. Eight elementary proof steps, zero new nodes, zero new Mathlib leaves. The supplied statement, dependencies of the statement, source and earlier recorded searches are retained.
2. Attachments: none. Searched all `lean/WeilConjectures/` for the exact blueprint tag, scalar/compositor/replacement terminology, and model-comparison terminology. No declaration gives this complete assertion. A proof with sorry would not have qualified.
3. WANTED: none.
4. The item had an empty proof and no proof dependencies. No mathematical error or statement correction was needed. The source blueprint's Charts paragraph gives the geometric application rather than this abstract lemma: the eight calculations are explicitly agent-written details of the parent's coefficient/refinement argument, not attributed to a theorem of Stacks. There is no released repair note for this item.
5. Unfinished mathematics: none. No Lean was written and no compiler, Lake, build or local preflight/check_dag/review_split command was run.

## Source and route

Read `GOAL.md`, the three fixed/followed/free blueprint levels in SETUP, chapter `sec-smooth-purity`, unit `sk-lem-sp-reduction`, and the current main-20261015 source `sk-lem-sp-reduction-exceptional.proof.md`, especially Charts and its specified coefficient-compatible left identification. This item is the abstract pasting tool under `lem-sp-chart-left-scalar-normalization`, not the unit's key theorem; neither the unit nor chapter route changes. Its blueprint ancestor is `det-sp-reduction-exceptional` as confirmed by blueprint_refs ancestor.

Read Stacks `categories.tex`, labels `definition-category` (Tag 0014, through the cited definition node), `definition-functor` (Tag 001B), and `definition-transformation-functors` (Tag 001I), including the componentwise composite immediately after the latter. These are the definitions used inline in the item, not uncited substantive lemmas. No SGA source is used.

## Searches and Mathlib verdict

Preserved every imported Mathlib search and added the six searches actually run for Q11, with exact tool/query text and their returned log records in `mathlib_searches`. Read `searches.jsonl` and the displayed hits. The two LeanFinder phrasings returned CatCommSq and Dold--Kan constructions. Read CatCommSq's class field and naturality formulas: its square is an isomorphism, whereas the item's coefficient maps need not be invertible. Read TwoSquare's natural-transformation definition, whiskerings, hComp/vComp, and interchange proof (Mathlib/CategoryTheory/Functor/TwoSquare.lean, lines 47--161), and NatTrans's defining naturality (Mathlib/CategoryTheory/NatTrans.lean, lines 45--63). These are ingredients, not a declaration giving all replacement and independent F/P/Q model-change clauses. LeanSearch returned adjunction conjugateEquiv_comp, which concerns adjunction mates rather than the arbitrary functors here, plus coalgebra/Grothendieck/cone comparisons. No exact or one-line specialization gives the item as a whole.

Whole-DAG keyword searches and blueprint_refs searches for compositor, natural transformation, replacement, and model isomorphism found no duplicate assertion. Read the closest nodes `lem-sp-exact-derived-transformation-pasting`, `lem-sp-chart-left-scalar-normalization`, and `lem-pur-expression-counit-substitution-coherence`: the first assumes an ordinary equality and passes it to derived categories; the second applies this item in geometric categories; the third concerns recursively evaluated completed expressions. None states this arbitrary-category cancellation calculation. They are not dependencies of this split. All proof steps are below 1000 characters, so none meets the long-step threshold.

## New nodes

None. In particular inverse-square cancellation, a single use of defining naturality, and componentwise associativity are steps, not new nodes or restated clauses delegated to new nodes.

## Not duplicates

No new nodes and hence no new/existing source-tag pairs.

## Review by Q11

I read the item and its source Charts paragraph against the scalar-normalization parent's displayed coefficient equation. The functor indices agree: E and F go from 0 to 1, P from 1 to 2, and Q from 0 to 2; lambda is P E to Q. I kept the statement intact. Each component calculation below has a common source and target. The only cited node is `def-nagata-category`; I opened its statement and checked that it gives precisely associativity and both identity laws. Its verbatim law is recorded for every proof step in citations.json. Functoriality, naturality, componentwise invertibility and the assumed squares are written in the item's own statement, so no additional theorem is taken from that definition node or its proof.

Step 1 uses those category laws to explain every subsequent cancellation: compose with the specified inverse, and use functor preservation of composition/identity for functor images of inverses. It never cancels a beta map. Step 2 multiplies the assumed c/beta_F square by c_B inverse and T_1(c_A inverse), proving precisely the inverse-square equation. The placement of the T_0 evaluation is retained.

Step 3 applies beta_P naturality to the actual arrow c_A,x inverse: E_A(x) to F_A(x). Its two sides end in P_B T_1 F_A(x). Substitution of the assumed alpha/beta_Q square and Step 2 gives the full lambda coefficient equation. It invokes no unspecified square-pasting theorem. Step 4 first solves c' r=c for c' inverse=r c inverse, then applies rho_P naturality at c inverse. The assumed alpha model square cancels rho_F and leaves exactly rho_Q lambda. Thus a change of F alone cancels completely.

Step 5 explicitly rewrites the primed left side after precomposing with T_2(rho_P,A E_A), using Step 4 and the Q coefficient square. Step 6 explicitly rewrites the primed right side using the P coefficient square, rho_P,B naturality at the possibly noninvertible sigma_x, and Step 4 for B. The common output identification is rho_Q,B T_0, not rho_F. The proof gives both directions of identification of equations by composing with inverse endpoint identifications, so it is stronger than an assertion of commutativity without explaining transport.

Step 7 verifies that successive model changes again satisfy every assumption: c by substitution, alpha by rho_P' naturality at rho_F, and beta_X by two substitutions for each X. It then computes lambda''(s's)E=t't lambda and the identical composite endpoint identifications. Identity changes delete identity factors. Step 8 checks input naturality directly for inverse, composite and both whiskerings, and explains equality componentwise. These are a few-line uses of definitions, not new non-elementary comparison lemmas. All eight steps therefore legitimately have elementary=true, with the category-law dependency cited for reassociation and identities.

I checked the hypotheses against the calculations: only c and rho, their functor images, and the assumed alpha comparison are invertible; no inverse of any beta or sigma is used. There is no additive/exact/flat argument. For empty input categories the component equalities are vacuous, so no object is selected. For identity models all rho factors disappear. For a one-object category from a monoid with a nonunit zero element, taking all functors to be identity, c=alpha=1 and beta_F=beta_P=beta_Q=sigma=0 satisfies the hypotheses and gives both sides zero; thus the proof does not smuggle in invertibility of coefficient transformations. Naturality at sigma in Step 6 is valid for an arbitrary morphism. With only F changed, s=t=1 and Step 4 yields literal equality of lambda. These tests required no statement correction.

I corrected no prior attempt: this was an empty sandbox. I preserved the imported search history, supplied all missing calculations and exact quotations, and checked delivery-errors B--E against the files: self-contained existing statement, no new-node sketches or duplication, no implicit non-elementary result, no cycle, and explicit formulas wherever the statement asks for transport/coherence.
