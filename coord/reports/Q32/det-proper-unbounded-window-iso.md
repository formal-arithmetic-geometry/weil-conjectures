## Files written

- `dag/nodes/sec-six-functors-basics/det-proper-unbounded-window-iso.json`: statement, split into three steps, no exact Mathlib match.
- `citations.json`: a verbatim statement excerpt for each of the 14 node citations in the three proof steps.
- `report.md`: this report.

New nodes: none. New Mathlib leaves: none. The previous attempt's unit realization file was removed: this item carries the unit's third proof step, but is not its key statement node, so this worker does not change the unit record.

## Attachments

None for the item. Searches of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` by its blueprint id and by window, truncation/proper-pushforward and cohomological-amplitude terminology found no project declaration stating both maps. The existing closed node `lem-pc-right-derived-functor-triangulated` already attaches the generic exactness instances in `WeilConjectures/CategoryTheory/DerivedCategory/RightDerivedFunctor/Triangulated.lean:94-99`; no attachment or duplicate is created here. The exact upstream master checkout is reference material only.

## WANTED

None.

## What was wrong or incomplete

The imported statement used “as above” and had no statement dependencies. It is expanded with the inherited prime, finite extension, condensed coefficient rings, pulled-back coefficient sheaves, and definitions of the two full subcategories. In particular, the algebraic-closure coefficient is the condensed ring of `sk-def-sfb-qlbar-condensed`, not the constant sheaf or a silently substituted topology. The integer fibre-dimension bound is kept as stated in the source; the earlier sandbox version unnecessarily imposed $d\geq0$, which has been removed.

The earlier attempt omitted the fact that the derived module pushforward carries distinguished triangles to distinguished triangles. Step 1 now cites the exact existing statement and verifies its hypotheses using ringed-site Grothendieck categories, K-injective resolutions, additivity, and the definition of the total derived module pushforward. The source of the argument is agent-written blueprint text, so `proof_origin.by` is corrected to `agent`. Actual `.proof.md` files, rather than a nonexistent `## Proof` section in the statement file, identify the two source paragraphs.

The earlier second step claimed a nested-truncation compatibility from a citation that only directly supplies the formulas for single truncations. Step 3 now works with $L=\tau_{\leq q-2d-2}(\tau_{\leq q}K)$ itself. Its upper cohomological bound suffices, so no nested-truncation identification or extra lemma is used. The proof also explicitly puts all three cohomology sheaves in the full category $\IndCons(Y,\Lambda)$ and explains why the ambient inverses are maps in it.

The initial report described the truncated statement as preserving all hypotheses but added $d\geq0$, and it failed to distinguish the blueprint as agent-written. These are repaired without a substantive statement dispute: “as above” has been expanded faithfully to the actual unit and coefficient conventions.

## Not duplicates

No nodes created. DAG and whole-blueprint searches for `window`, `window isomorphism`, `truncation window`, `derived functors`, and `ind-constructible` found the existing proper-window unit and its detail nodes. The more general unit statement contains this clause, so it is not a new duplicate and is not cited back (which would create a cycle). All auxiliary facts used are existing nodes.

## Review by Q32

I read `coord/brief-stage1.md`, `stages/1-dag.md`, the three route levels and tool-lemma distinction in `SETUP.md`, `coord/delivery-errors.md` B–E in full, `GOAL.md`, and `coord/dag-sync.md`. I read the chapter `sec-six-functors-basics`, unit `sk-lem-proper-unbounded-window`, the current main-20261015 item statement and its separate proof file, the arbitrary and bounded-below bounds, and the heart-bound coefficient conventions. The unit route is unchanged: the two amplitude bounds prove the window using two canonical triangles. The local Stacks source `derived.tex`, Remark 08J5 (`remark-truncation-distinguished-triangle`) and Lemma 05RS (`lemma-cohomology-homological`) and the following displayed long sequence were read for the general triangle and cohomology inputs. The item creates no new node, so there is no additional unsplit statement requiring a separate source audit. No SGA source is used.

For step 1, I read each cited statement. `def-weil-pbc-proetale-site` gives the small-skeleton universe convention; only that clause is used, not its later constant-coefficient specialization. `lem-weil-pbc-ring-sheaves-grothendieck` allows any sheaf of rings on that small site, so it applies to the actual pulled-back condensed coefficient sheaf on both X and Y. `lem-sfb-grothendieck-k-injective` then supplies both resolution hypotheses required by the statement of `lem-pc-right-derived-functor-triangulated`. `def-sfb-module-lower-star` explicitly states additivity and left exactness. `sk-def-sfb-module-derived-pushpull` states that the functor at issue is the total derived functor of this composite computed on module K-injective resolutions. The closed triangulated-functor node explicitly gives preservation of distinguished triangles and integer-shift compatibility. I also read its project source instance and surrounding binders in `RightDerivedFunctor/Triangulated.lean`, including lines 94–99; it uses no properness or amplitude result. These are generic tools, not alternative proper-direct-image arguments.

For step 2, the formula statement of `def-kun-truncations` says the truncations retain exactly the specified cohomology and otherwise have zero cohomology; thus the truncated objects remain ind-constructible, because every retained sheaf already is and the zero sheaf is constructible. `lem-sf-derived-truncation-triangle` supplies exactly the canonical triangle at b=q+1. `det-proper-unbounded-window-arbitrary` supplies the lower amplitude inclusion for B and membership in Dic. Its hypotheses are precisely the inherited E/Qlb coefficients, proper p and the same fibre bound d. After step 1, `lem-sf-derived-homology-long-exact` supplies the exact segment with the two zero outside terms in degrees q-1 and q. Hence it is the induced map, not an unspecified choice of isomorphism, that is invertible. The last inference is the elementary abelian-category criterion that a morphism with zero kernel and cokernel is invertible.

For step 3, I again read those four cited statements rather than using their proofs. At r=q-2d-2 the triangle lemma is applied to A itself; it gives L→A→W with W exactly the stated window by substitution. The truncation formulas give the bound on L and membership of L and W in Dic. The arbitrary direct-image theorem gives the upper bound r+2d+1=q-1, making the two outside terms in degrees q and q+1 zero. The long exact sequence therefore gives the second induced isomorphism. The same direct-image theorem guarantees membership in Dic(Y) for K,A,W; fullness in the definition of IndCons makes the inverse maps remain in IndCons. No claim that a definition alone proves exactness or truncation compatibility remains.

I tested the endpoints q=0,d=0 (lower tail ≤-2, image ≤-1, window [-1,0]), q=-3,d=1 (lower tail ≤-7, image ≤-4, window [-6,-3]), the zero complex, and a complex already in the window. The endpoint calculation works for all integers q and d. For d<0 the nonempty-fibre case cannot satisfy the hypothesis since a nonempty scheme has dimension at least zero; the empty-source case has zero direct image and both maps are isomorphisms. Thus no extra d≥0 assumption is needed. These tests also confirm the need for degree q-1,q vanishings in step 2 and q,q+1 vanishings in step 3. No new statements were invented, and no content was moved to a fresh node.

Mathlib queries were run through the required `msearch.py`, with exact queries and actual hits recorded in the item and `searches.jsonl`. Two semantic phrasings returned cochain truncation/quasi-isomorphism statements; Loogle returned `triangleLEGE_distinguished`; the corrected grep subdirectory `CategoryTheory/Triangulated` returned its source line 206. I read that declaration and the cochain truncation criteria at `Algebra/Homology/Embedding/CochainComplex.lean:277-288`. They give the generic inputs but do not combine a proper module direct image with the required amplitude and window isomorphisms, so the item is not a Mathlib leaf. The earlier greps with an extra `Mathlib/` path component were not retained as evidence of absence.

## Unfinished work

None in this one-level split. Its cited amplitude theorem remains another DAG item's work; this delivery does not assert that dependency is already proved.

## Second reading by Q32

- Statement: checked the expanded hypotheses and both canonical maps against the item source and the enclosing `sk-lem-proper-unbounded-window` conventions; verdict **pass**. The coefficient alternatives, pulled-back module categories, properness, fibre-dimension bound, and all integer edge cases are explicit.
- Step 1: checked every cited node statement against the construction of the module total right derived pushforward; `lem-pc-right-derived-functor-triangulated` supplies preservation of distinguished triangles after the Grothendieck and K-injective hypotheses; verdict **pass**.
- Step 2: checked the truncation triangle, the lower amplitude inclusion, and the exact cohomology segment in degrees $q-1,q$; the induced map is the displayed map and is an isomorphism; verdict **pass**.
- Step 3: checked $r=q-2d-2$, the direct triangle $\tau_{\le r}A\to A\to\tau_{\ge r+1}A$, the upper amplitude calculation $r+2d+1=q-1$, and the exact segment in degrees $q,q+1$; substitution gives the stated nested truncation; verdict **pass**.
- New nodes: none; there were no new statements to audit, and no duplicate or Mathlib leaf was introduced.

I changed no node or citation after this reading. I retained the worker's explicit source comparison, searches, and edge-case checks, including $q=0,d=0$, negative $q$, the zero complex, and the empty-source possibility.
