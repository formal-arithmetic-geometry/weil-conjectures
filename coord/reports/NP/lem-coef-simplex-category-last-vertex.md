## Files written

- `dag/nodes/sec-six-functors/lem-coef-simplex-category-last-vertex.json`: statement, split into seven steps; no Mathlib match.
- `citations.json`: one verbatim statement quotation for every step/node citation.
- `report.md`: this report.

No new nodes and no Mathlib leaves. The statement, statement dependencies, provenance, chapter, unit and existing ancestry were preserved. The Mathlib searches were rerun through the required msearch command and the item records only this worker's logged searches, with their exact queries and actual results.

## Attachments

None. Searches under WeilConjectures in both read-only Lean source checkouts for the exact blueprint tag/id, last vertex, last-vertex, category of simplices and simplex-category produced no project declaration stating this item. No Lean was written or compiled.

## Wanted literature

WANTED: Kerodon, The Category of Simplices, tags 01N8, 01NA and 02QS (Construction 11.9.11.2 and Corollary 11.9.11.5), for lem-coef-simplex-category-last-vertex. I read these pages online; no archive was found under literature/. No Stacks tag states this simplicial homotopy theorem. The proof is explicitly marked agent-written: it proves the cited source's result using a bisimplicial resolution, without appealing to the much stronger localization theorem in Kerodon's published proof.

## Problems found and corrections

The item had a correct statement and no proof. Its formula is exactly Kerodon 01NA and the weak-equivalence assertion is exactly 02QS; no STATEMENT-DISPUTED issue arose. The current and historical blueprint ancestor's derived coefficient adjunction paragraph was read; it contains no standalone category-of-simplices theorem. The recorded historical ancestry locates this foundational input through Low's comparison lemma, and no unit or chapter route is changed.

A tempting use of the existing aspherical or Thomason nodes would be circular: they refer to the Bousfield--Kan comparison, which already uses this item. I did not use them. The actual proof uses only the independent bisimplicial diagonal theorem, natural transformations on nerves, realization's finite-product property and Kan--Quillen two-out-of-three.

In developing the resolution I checked which endpoint carries its extra simplex. It must be the initial endpoint: a monotone map t:[q] to [n_0] can be pushed forward when that endpoint is deleted. A map into the last endpoint would have no canonical pullback after deletion of the final object. The delivered step 2 uses the initial endpoint throughout. Consequently the comparison homotopy uses u=b t in the final ordinal, rather than t itself.

## Unfinished work

None in this one-level split. The existing generic dependency nodes remain the project's independent work. No delivery was pushed; the sandbox is for the fresh second reader.

## Not duplicates

No new nodes were created. Whole-DAG searches for last vertex, last-vertex, category of simplices, simplex category, Quillen/aspherical and bisimplicial comparisons, plus blueprint_refs searches for `last vertex` and `category of simplices`, found no duplicate blueprint theorem (both blueprint searches returned zero). The existing nerve-homotopy and diagonal nodes were reused. In particular I did not create nodes for contractibility of standard simplices, for categories with initial objects, for preservation by disjoint unions or for the explicit ordinal calculations.

## Review by NP

I read Kerodon 01N8, 01NA and 02QS online and compared the item's statement clause by clause: all monotone arrows are allowed; degeneracies are retained; n and p may be zero; K is arbitrary and need not be Kan, braced or finite. The last vertex is transported into the final ordinal before K is applied, exactly as in the source. No SGA source is used. I also read the chapter record, the bound unit record sk-prop-sf-biduality-general and both snapshots of the ancestor's derived coefficient adjunction proof. This is work below the unit level, not a replacement of a unit argument.

For step 1 I opened def-weil-pbc-simplicial-set: it defines contravariant operators and morphisms as natural transformations, which are precisely the facts used. The argument writes out composition, monotonicity, arbitrary-operator compatibility and naturality, rather than citing a definition for the weak-equivalence theorem. The tail-composite equation covers omission of the last object, and repetitions cover degeneracies.

For step 2 the same definition supplies functoriality, while the resolution and both augmentation maps are constructed explicitly. I checked that deleting the initial object pushes t forward, deleting the final object leaves its source ordinal intact, and the two simplicial directions commute. Q is constant under horizontal operators by K(at)y=K(t)K(a)y. A and B are constant in the stated direction, so the diagonal maps have exactly the required domains and codomains. Smallness of K makes the object sets, chain sets and C_q small.

For steps 3 and 4 I opened lem-coef-nerve-natural-homotopy-equivalence. Its statement permits natural transformations with noninvertible components and gives a nerve weak equivalence from inverse functors up to such transformations. This applies to [n] versus the point using its terminal object, and to C_{q,z} versus the point using its initial object. Neither use assumes a groupoid or Kan nerve. In step 4 the arrow from ([q],z,id) is exactly t, and its existence condition is exactly K(t)x=z; its uniqueness proves initiality, not merely connectedness. Disjoint unions preserve these weak equivalences by the explicit component/sphere argument in step 3. Their labels are unchanged by realization relations. This avoids hiding any homotopy-cofinality theorem.

For step 5 I opened lem-coef-bisimplicial-diagonal-equivalence and read its statement and dependency lists. It states both rowwise and exchanged-direction detection with no fibrancy requirement. P satisfies its row hypothesis by step 3; Q satisfies its column hypothesis by step 4. Its dependencies do not use the present item, Bousfield--Kan or Thomason. Both source and targets are bisimplicial sets indexed by the small simplex category.

For step 6 I opened lem-coef-realization-finite-limits. Its statement gives finite-limit preservation in k-spaces, in particular the product needed for realizing D times Delta^1. I used exactly that assertion, not an assertion that realization preserves arbitrary products of ordinary spaces. The compact-test-cube argument explains why the resulting k-space homotopy has all the usual consequences for the homotopy groups in the item's definition. The two homotopies are constructed explicitly: max(u,v) is monotone, and the 0-to-1 switch has the required inequality. All ordinal maps preserve binary maxima. I checked the equations cu'=u theta and cv'=v theta after an arbitrary restriction, including when its first and final indices move, so the construction is simplicial rather than only degreewise. These checks are the substance of the comparison; I did not say merely that it transports or is natural.

For step 7 I opened lem-coef-kan-quillen-right-proper. Its statement gives a model structure with exactly the realization weak homotopy equivalences used here, so its model-category two-out-of-three applies to p and lambda p. Before invoking it, the explicit homotopies give the same component map and homotopy-group maps related by the homotopy's basepoint paths. This checks all basepoints, rather than only vertices. The nerve node uses exactly the same realization-based weak-equivalence convention through def-coef-zigzag-homotopy-calculus, whose statement I also opened.

I checked B1--B10: there are no new-node statements, data constructions hidden in sorry, duplicate nodes or unverified Mathlib leaves. I read Simplices.lean, Nerve.lean, and the returned StdSimplex/HomotopyCat/NerveAdjunction declarations. Simplices.lean's preorder is explicitly different from the full simplex category; isoNerve handles a standard simplex, and the homotopy-category/nerve adjunction handles 2-truncated simplicial sets. None proves this last-vertex weak equivalence. Two semantic phrasings and all required search kinds were run and logged; no unavailable service was represented as a negative search.

I checked C1--C8 and D1--D5 against the actual statements and sources: every non-elementary tool has an existing node citation; every use has a verbatim quotation in citations.json; no proof of a dependency is used as its statement; no off-unit statement is invoked; and the proof carries the argument rather than renaming a clause as a new node. Steps 1 and 2 are elementary explicit functor calculations. Steps 3--7 are marked non-elementary and identify their generic inputs.

For E1--E7 I checked the empty simplicial set, a discrete simplicial set, Delta^0 and Delta^1. If K is empty every W set and both endpoints are empty. For discrete K the construction separates into its vertex components. For Delta^0 the full simplex category is Delta (not a single-object category), and the initial-object computation of each C_{q,z} still holds. For Delta^1, both noninjective/constant and injective ordinal maps are admitted; the max homotopies do not require an inequality between u and v. Degree zero permits arbitrary t(0) and v(0)=n_0, and the same formulas apply. No finiteness, nonemptiness or fibrancy hypothesis is inserted. No statement or source error remains.

## Earlier second reading (a previous round; superseded)

- Item statement: checked against Kerodon Construction 11.9.11.2 (tag 01NA, under 01N8) and Corollary 11.9.11.5 (tag 02QS), clause by clause; the full category of simplices, all monotone arrows, the last-vertex formula, naturality, and weak-equivalence conclusion agree, including n,p=0 and the empty simplicial set.
- Step 1: checked against the definition node `def-weil-pbc-simplicial-set`; its composition, identity, monotonicity, restriction, degeneracy, final-face, and naturality calculations establish the asserted category, simplicial map, and naturality. Verdict: correct and elementary.
- Step 2: checked against `def-weil-pbc-simplicial-set`; the bisimplicial resolution, both augmentation formulas, horizontal/vertical compatibility, and smallness are stated explicitly. Deleting the initial object uses the forward composite, as required. Verdict: correct and elementary.
- Step 3: checked against `lem-coef-nerve-natural-homotopy-equivalence`; the ordered category has a terminal object and the coproduct argument preserves weak equivalences, including an empty coproduct. Verdict: cited statement supplies the claimed weak equivalence.
- Step 4: checked against `lem-coef-nerve-natural-homotopy-equivalence`; the categories `C_{q,z}` are correctly defined, split by the constant value, and have initial object `([q],z,id)`, with the unique arrow exactly the map `t`. Verdict: cited statement applies and the disjoint-union argument covers empty degrees.
- Step 5: checked against `lem-coef-bisimplicial-diagonal-equivalence`; P satisfies its rowwise hypothesis by step 3 and Q its exchanged columnwise hypothesis by step 4, yielding the displayed diagonal weak equivalences. Verdict: correct; no Bousfield--Kan or Thomason result is smuggled in.
- Step 6: checked the two max-based simplicial homotopies degreewise, including arbitrary restrictions, repeated operators, the final-face deletion, and both constant endpoints; checked the finite-product realization assertion against `lem-coef-realization-finite-limits`. Verdict: correct comparison of `q` and `lambda_K p`.
- Step 7: checked against `lem-coef-kan-quillen-right-proper`; two-out-of-three for its model-category weak equivalences applies after step 6 identifies the induced component and homotopy-group maps. The empty case is vacuous. Verdict: correct.
- New nodes: none; therefore B1--B7 and duplicate/Mathlib-node checks have no new-node findings. Existing citations were checked by opening each cited statement; all citation quotations are verbatim in `citations.json`. The recorded LeanFinder, Loogle, LeanSearch, and grep searches were rerun/inspected and found no Mathlib or DAG theorem for this full category-of-simplices last-vertex equivalence.
- Changes: appended this second-reading record only. No mathematical or node-file correction was necessary; the worker's statement, seven proof steps, citations, provenance, and blueprint ancestry remain unchanged.

## Repair after NOT MERGED return

The landing return identified `lem-coef-realization-finite-limits` as changed since the reviewed delivery. I rebased the citation check against the current shared node at `dag/nodes/sec-six-functors/lem-coef-realization-finite-limits.json` (commit 9b0114b3b6). I read its current statement and the eleven proof steps. The change adds the explicit definition of `\partial\Delta^n` and expands the proof; it does not remove or alter the clause used by this item. In particular, step 6 uses exactly the current statement sentence `It preserves all small colimits and all finite limits in $\\mathcal K$, naturally in the diagrams.` The verbatim quote in `citations.json` was checked against that current statement and remains valid. The realization node's stated finite-product consequence is therefore still precisely what step 6 takes from it; no proof step or dependency needs alteration. I also re-read the other four cited node statements and found no changes relevant to this split. This repair updates the report to the current DAG base while preserving the mathematically identical split.

## Second reading by NP

- Item statement: checked against Kerodon tags 01N8, 01NA, and 02QS; the object and arrow conditions, last-vertex formula, naturality, and weak-equivalence conclusion agree, including n,p=0 and empty K. Verdict: correct.
- Step 1: checked against `def-weil-pbc-simplicial-set`; composition, identities, operator restriction, last-vertex monotonicity, and naturality are explicitly calculated. Verdict: elementary and correct.
- Step 2: checked against `def-weil-pbc-simplicial-set`; the initial-object simplex parameter, both bisimplicial augmentations, operator compatibilities, and smallness are stated. Verdict: elementary and correct.
- Step 3: checked against `lem-coef-nerve-natural-homotopy-equivalence`; each ordered simplex category has a terminal object and the coproduct argument handles empty chain sets. Verdict: cited statement applies.
- Step 4: checked against `lem-coef-nerve-natural-homotopy-equivalence`; the categories `C_{q,z}` have the displayed initial object and unique arrow, and the disjoint-union argument handles empty degrees. Verdict: cited statement applies.
- Step 5: checked against `lem-coef-bisimplicial-diagonal-equivalence`; step 3 supplies the row hypothesis and step 4 the exchanged column hypothesis, with the stated diagonals. Verdict: correct and non-circular.
- Step 6: checked against `lem-coef-realization-finite-limits`; the maximum maps and restriction equations give simplicial homotopies, and finite-product preservation gives realized homotopies. Verdict: correct, with no hidden transport argument.
- Step 7: checked against `lem-coef-kan-quillen-right-proper`; two-out-of-three applies after the explicit homotopy comparison, including the empty case. Verdict: correct.
- New nodes: none; therefore B1--B7, duplicate-node, and Mathlib-leaf checks are vacuous. Existing cited node statements and verbatim quotations in `citations.json` were reopened and match.
- Edge cases: checked the empty simplicial set, discrete simplicial sets, `Delta^0`, `Delta^1`, and degree zero; no extra finiteness, nonemptiness, or fibrancy hypothesis is used.
- Changes: none to the node or citations; this section records the independent second reading required before delivery.
