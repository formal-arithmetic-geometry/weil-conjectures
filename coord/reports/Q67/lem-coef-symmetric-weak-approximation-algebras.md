## Worker report

Item: `lem-coef-symmetric-weak-approximation-algebras`. Group Q67. Stage 1 only.

## Files written

- `dag/nodes/sec-six-functors/lem-coef-symmetric-weak-approximation-algebras.json`: the existing statement node, split into eleven steps; its statement, source, statement dependencies, ancestry and historical Mathlib searches are retained. No new nodes and no Mathlib leaves.
- `citations.json`: one verbatim statement quotation for every step/dependency pair (46 entries). Complete statements are quoted so that hypotheses and the entire interface used are visible.
- `report.md`: the retained report revised after source review. `prior-attempt/` preserves the previous proof, report and citation file.

## Attachments

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the exact blueprint id, `weak.?approximation`, `symmetric.?operad`, and `2.3.3.23`, case-insensitively; there were no hits. No project declaration stating every clause is available to attach. I did not treat upstream master's sorry declarations as proofs.

## WANTED

WANTED: Jacob Lurie, *Higher Algebra* (2017), Definitions 2.1.1.10, 2.3.3.6 and 2.3.3.20, Remark 2.3.3.7, and Theorem 2.3.3.23(1), especially printed pp. 266–268, for `lem-coef-symmetric-weak-approximation-algebras`. I read the official PDF online at https://people.math.harvard.edu/~lurie/papers/HA.pdf. It is not archived under `literature/`; nothing was downloaded. `proof_origin.by` remains `agent`.

## What was checked and changed

The statement agrees with the symmetric theorem, including arbitrary small quasicategory source, arbitrary categorical-equivalence/categorical-fibration witness, strict unary-fibre equivalence, the local-projection algebra condition and all coherent transformations. No statement correction was needed. The ambient functor-equivalence and witness-independence clauses are proved explicitly, rather than being assumed. The source's product/right-Kan argument is followed without importing presentability or a Kan colour hypothesis.

The retained proof had substantive gaps. Its product citations were to `lem-coef-operadic-algebra-presentability`, whose statement is nonsymmetric over the simplex category; that node cannot supply the symmetric product axiom over finite pointed sets. Step 5 also introduced a category H larger than I and then asserted an inclusion H → I. This has been removed. Its reduction to a categorical-fibration witness failed to justify passage of the strict unary equivalence; the new Step 2 gives that justification using the trivial automorphism group of the unary pointed set. Finally, it did not prove the converse identifying right Kan extensions with X, nor the preservation of every inert arrow. The new Steps 9–10 prove both directions and expand the all-inert argument. I retained the earlier attempt separately rather than losing its proof or report.

The first required dry run was started before repairs and waited for server capacity. While it waited, the repaired node was saved before the repaired citations, so its snapshot diagnosed missing/stale quotes and the provisional nonexistent full-faithfulness id. These diagnostics are repaired: the actual existing `lem-coef-infinity-full-essential-image` is cited and every step has a full verbatim quote. The dry run is rerun on the complete, consistent sandbox below.

## Source proof terminology

On printed p. 267 the source calls the locally cocartesian lift and the unary representative “final” in two coslice computations. With the ordered coslice convention in this item they are initial. For example, the lift category over a fixed arrow of a cocartesian fibration has maps *from* the cocartesian lift to all other lifts; an ordinary coslice of the arrow category 0 → 1 has initial object the identity of 0. The new Steps 6–7 give the mapping-space initiality calculation, and use the existing initial-components lemma. This is a correction of the proof's orientation words, not a change of the theorem or its hypotheses.

## Searches and duplicates

No new node was created. I read the historical Mathlib search queries and actual result records already present on the item, including both LeanFinder phrasings, LeanSearch, Loogle and grep. The ordinary factorization-category, generic weak-equivalence and Dold–Kan hits do not concern quasicategorical operads. Those records were retained unchanged and no unrun query was added. I searched the current DAG for initial objects, relative limits, right Kan extensions, cocartesian mapping criteria, strict-fibre comparisons and essential images. This found the existing `lem-coef-relative-limit-initial-components`, `lem-coef-infinity-full-essential-image` and `lem-coef-cofinal-relative-join-slice-restriction`, preventing unnecessary new nodes. Whole-blueprint search for “weak approximation” returned no matches; the ancestor tool returned `prop-coef-integral-exceptional-adjoint`. I read its current proof paragraph 2. The relative join-coslice theorem `lem-cbc-relative-coslice-left-fibration` belongs to `sk-prop-sf-cbc` and is already a statement dependency. It is used as a generic indexing-category tool in Steps 5–7; no same-unit node states its relative coslice interface. This use is declared in `split_report.tool_uses` for maintainer review; no maintainer-owned top-level `tool_uses` field is written. Every other used proof node is in the item's unit.

## Review by Q67

I read the current item, the chapter `sec-six-functors`, the assigned unit `sk-prop-sf-biduality-general`, the current ancestor proof paragraph 2, the standing worker brief and delivery-errors B–E. I compared the retained sandbox item with the repository: only proof, proof dependencies, proof origin, split report and status originally differed; the original mathematical statement and ancestry remain unchanged. I read Higher Algebra Definitions 2.3.3.6 and 2.3.3.20 and Theorem 2.3.3.23(1), together with the complete proof on printed pp. 266–268. For the symmetric product axiom I used the definition stated in the existing symmetric-recognition node, not the nonsymmetric algebra-presentability theorem.

For Step 1 I opened the exponentiation and isofibration-pullback statements: the first really gives an isofibration on functor categories and the second identifies its degreewise fibre with the categorical fibre. The pointwise-equivalence statement gives preservation of the two inverse transformations under precomposition. The symmetric-recognition statement supplies inert lifts of base bijections; cocartesian initiality and the mapping criterion justify equivalence lifts and invariance of the local projection condition. These same relative functor equivalences compare arbitrary witnesses over P, so the independence clause is covered.

For Step 2 I opened `lem-coef-infinity-full-essential-image`: its statement gives a coherent quasi-inverse to a fully faithful functor onto its full essential image, precisely what is needed after proving essential surjectivity. The new argument checks the strict fibre: equivalences over a unary pointed set have identity base, and mapping spaces split over the discrete hom set. It never assumes e itself is a categorical fibration.

For Step 3 I opened the symmetric-recognition statement, the join-cone mapping formula, homotopy-fibre detection, homotopy-pullback pasting, the relative-cone definition and the cocartesian mapping criterion. They say exactly the inputs used in the displayed mapping-space calculation. Fibre detection is applied over the identity of the base mapping space, so its required equivalence of bases holds. Comparison of the two relative product cones proves the converse and avoids assuming completeness of Q. The empty-product calculation is written explicitly.

For Step 4 I opened Cartesian straightening (the opposite of the stated cocartesian version), Cartesian mapping fibres and Cartesian-colimit localization. The latter states an equivalence of the whole functor infinity category, including noninvertible transformations, with functors inverting Cartesian edges. Its colimit here is P because the classifying diagram is the single arrow D → P. Exponentiation and the strict-pullback theorem are used again to pass to the fixed base, as in Step 1.

For Step 5 I checked the coslice-left-fibration, opposite comma criterion, relative-cone equivalence, relative join-slice restriction and join-cone formula. The weak-approximation hypothesis provides exactly the comma category F_g(d,a), with every coherent comparison retained. The comma criterion is used in the opposite orientation, for limits, and the dual join-restriction clause supplies strict boundary/base representatives. No completeness assumption occurs.

For Step 6 I checked cocartesian cancellation and initiality on the pullback over one fixed colour edge, rather than claiming a local lift is globally cocartesian. Cancellation in P makes the composite condition correct. The chosen locally cocartesian lift lies in the full inert-composite subcategory, so initiality restricts to it. `lem-coef-relative-limit-initial-components` explicitly allows disconnected components and an empty family. The full relative right-Kan theorem states the pointwise condition used; the symmetric product calculation of Step 3 verifies it.

For Step 7 I checked the same mapping criterion against the actual inert arrow x → g(d_i), the unary fully faithful functor from Step 2 and the coslice mapping-space construction. Their composite is an equivalence, hence the stated mapping fibre is contractible. This proves initiality, rather than incorrectly saying that the whole cone category is equivalent to evaluation. The initial-components node then states exactly the existence and detection needed, also when n = 0.

For Step 8 I opened both clauses of `lem-coef-relative-right-kan-universal-restriction`: its cone comparison transfers the relative limit from J to I, and its full restriction theorem produces the extension from D to E. Step 5 transfers from I to K with the prescribed base. At a vertex of D the identity is initial in the indexing coslice. This verifies all pointwise existence hypotheses and yields the explicit inert-leg criterion, not an unspecified appeal to Kan extensions.

For Step 9 the localization statement gives the equivalence with composition by r; mapping criteria and cocartesian composition preserve inertness under the equivalences. Step 8 then proves the required right-Kan condition. In Step 10 I checked both missing reverse tests: two relative product cones with the same boundary force the Cartesian comparison to be an equivalence; to prove preservation of a general inert arrow, factor through a cocartesian lift and compare its output product cones. Cocartesian cancellation and composition give the desired inertness, including zero outputs. The symmetric-recognition statement supplies exactly the needed inert lifts and output products.

For Step 11 I checked that the right-Kan restriction theorem asserts a trivial Kan fibration on *all* transformations and higher simplices. Restricting to the full boundary subcategory preserves this lifting property. Its composite with the specified section A ↦ Ar is exactly precomposition with g, and then with f. This final identification is elementary from the already constructed maps.

The small cases checked were f = identity, empty colour categories, unary arity and its two pointed endomorphisms (identity and the zero map, only the former an automorphism), and arity zero including arrows with zero outputs. All categories and indexing slices stay small in the fixed universe. No Kan condition on the colour category, no presentability, and no extra fibration hypothesis on f was used. I checked dependency paths to the item before reusing the auxiliary nodes; none returned to it. In particular the operadic marked-approximation theorem depending on this item is not cited. No SGA source was used.

## What remains

The only external-source limitation is the WANTED archive noted above. The complete split must pass the required server dry run before handoff. This worker does not deliver.

## Second reading by Q67

I reread the statement against Higher Algebra Definitions 2.3.3.6, 2.3.3.20, Remark 2.3.3.7, and Theorem 2.3.3.23(1), pp. 259 and 264–268; every hypothesis and conclusion agrees, including empty and nullary cases. The official PDF was checked online on 2026-10-17; no Stacks tag states this result.

- Step 1 checked against the exponentiation, pullback-fibre, pointwise-equivalence, cocartesian-initiality/mapping, and symmetric-recognition statements; strict relative functor fibres and witness transport are justified. Verdict: passes.
- Step 2 checked against the full-essential-image statement and the strict fibre mapping-space calculation; the unique unary pointed automorphism forces arity one and gives the witness unary equivalence. Verdict: passes.
- Step 3 checked against symmetric recognition, join-cone mapping, homotopy-fibre detection, pullback pasting, relative-cone definitions, and the cocartesian mapping criterion; the relative product and its converse, including arity zero, are stated. Verdict: passes.
- Step 4 checked against Cartesian mapping fibres, Cartesian-colimit localization, exponentiation, and pullback-fibre statements; the cylinder retraction and strict endpoint representatives are now explicit. Verdict: repaired and passes.
- Step 5 checked against the ordered join-coslice, opposite cofinal-comma, relative-cone equivalence, relative join-slice restriction, and join-cone statements; the weak-approximation comma category has the required orientation and coherent triangles. Verdict: passes.
- Step 6 checked against cocartesian initiality/mapping, initial-components, relative right-Kan restriction, join-coslice, and symmetric-recognition statements; local projection components and the empty arity are handled. Verdict: passes.
- Step 7 checked against cocartesian mapping, join-coslice, join-cone, initial-components, and symmetric-recognition statements; unary components have the required initial objects and mapping fibres. Verdict: passes.
- Step 8 checked against relative right-Kan restriction, initial-components, and cofinal join-slice restriction; extension and the inert-leg criterion are obtained with prescribed base and boundary. Verdict: passes.
- Step 9 checked against Cartesian localization, cocartesian mapping/composition, and relative right-Kan statements; the forward implication sends local projections to inert edges and gives the Kan criterion. Verdict: passes.
- Step 10 checked against relative right-Kan, Cartesian mapping fibres, cocartesian mapping/composition, relative-cone duality, and symmetric recognition; Cartesian-lift uniqueness is now explicitly factored through the canonical lift, and the all-inert converse includes arity zero. Verdict: repaired and passes.
- Step 11 checked against the relative right-Kan trivial-fibration statement and Steps 8–10; it identifies the restriction functor on all coherent transformations. Verdict: passes; marked non-elementary because it packages the main conclusion.

New nodes: none; therefore B1–B7 and duplicate/Mathlib-leaf checks are vacuous. I nevertheless searched the current DAG for the relative-limit, right-Kan, cofinal-slice, Cartesian-lift, and full-essential-image interfaces and reused the existing nodes. The citations file contains one verbatim statement for each of the 47 step/dependency uses.

Changes made: Step 4 now records why the Cartesian localization representative has strict endpoint restrictions; Step 10 cites and applies the existing Cartesian mapping-fibre and relative-cone dual statements to handle every Cartesian edge; Step 11 is no longer marked elementary because it carries the final equivalence; citations.json was regenerated to match these uses. No theorem statement, source, or dependency statement was changed.
