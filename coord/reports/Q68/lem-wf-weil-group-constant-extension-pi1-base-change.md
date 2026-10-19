# Q68 — lem-wf-weil-group-constant-extension-pi1-base-change

## Files written

- `dag/nodes/sec-purity-real-sheaves/lem-wf-weil-group-constant-extension-pi1-base-change.json`: existing statement node, now split into seven proof steps; Mathlib searches found no exact or one-line generalized match for the whole arithmetic scheme statement. Its statement is unchanged. Added the explicit geometric-connectedness definition to statement dependencies.
- `citations.json`: verbatim statement quotations for all 18 step/node citation pairs.

No new nodes; no new Mathlib leaves. A preliminary uncommitted finite-field-etale draft was dropped: the DAG already contains the finite-separable-etale and base-change lemmas it would duplicate. No unit or chapter record is changed.

## Attachments

None for this item. Searched the project Lean source both for its exact blueprint tag/id and for constant-field and fundamental-group base-change language. `WeilConjectures/AlgebraicGeometry/FundamentalGroup/WeilGroup.lean` defines constant covers and their action, but does not prove this item's subgroup and geometric-kernel clauses. Read the existing generic finite-etale interfaces in `FundamentalGroup/Restriction.lean` and the group-theoretic degree exact sequence in `GroupTheory/WeilGroup.lean`; neither states the entire item. Upstream master declarations were not treated as finished proofs.

## WANTED

None. The proof uses existing DAG statement interfaces and the available blueprint and Stacks sources.

## Source error

The first paragraph of `lem-wf-weil-group-constant-extension` says that an arbitrary finite etale cover of the constant extension is the same as a finite etale cover of the original scheme with a condition on its constant-field action. Pullback alone does not supply descent data. For an explicit failure, take `X_0 = Spec F_q` and `m = 2`. The connected degree-two cover `Spec F_(q^4) -> Spec F_(q^2)` does not arise by base change of a finite etale `F_q`-scheme: base changing a connected field extension of degree d yields gcd(d,2) components of degree d/gcd(d,2). Connectedness forces d odd, which rules out degree two; a disconnected original remains disconnected after base change. Equivalently, the only finite etale F_q-algebras of dimension two are F_(q^2) and F_q x F_q, and both base change to a split algebra over F_(q^2).

The arithmetic subgroup conclusion and this item's statement are correct, so no statement correction is needed. The split replaces that erroneous sentence by the marked-fibre stabilizer argument. This changes neither the unit's statement nor the Weil-group route. The error occurs both in the inherited master file and in the current `main-20261015` proof file. It is documented also in the item's split report for the maintainer's review.

## Searches and reuse

Read the whole-DAG matches for finite separable fields, finite/etale base change, field-cover Galois classification, fundamental-group stabilizers, and the degree exact sequence. Whole-blueprint searches `constant extension`, `finite separable`, and `fundamental group` found the existing general tools, but no second blueprint node for this arithmetic scheme statement. Accordingly `blueprint.same_as` remains empty and the specific first-paragraph `from.place` is retained.

The item's inherited Q155 search records were preserved. Q68 made two semantic phrasings with LeanFinder and LeanSearch and two Loogle name-pattern queries; the Loogle unknown-identifier responses are recorded as unavailable. Initial source greps used a redundant `Mathlib/` directory prefix and are explicitly recorded as unusable, not evidence of absence. Corrected greps searched `AlgebraicGeometry` for `fundamentalGroup|FiniteEtale|absoluteGaloisGroup` and `CategoryTheory` for `fiberIsoQuotientStabilizer|stabilizer_normal_of_isGalois`. Read `Mathlib/CategoryTheory/Galois/EssSurj.lean:108-113` and `GaloisObjects.lean:102-112`: they give abstract action/stabilizer facts, not this scheme-specific arithmetic comparison. Search query text and actual outcomes are preserved in `searches.jsonl` and the node. No unrun search is claimed.

## Not duplicates

No new nodes are delivered. The generic tools cited in `split_report.tool_uses` keep their own general statements; the item's argument applies them rather than introducing a special-case node or moving one of its clauses to a child.

## Review by Q68

This is the author's self-review under the direct-delivery brief, not a claimed independent second reader. I read delivery-errors B through E and compared the completed node with the source and each cited statement.

For the item I read the inherited blueprint's first paragraph, the corresponding current `main-20261015` statement and proof, and the unit and chapter records. For the supporting mathematics I read Stacks `morphisms.tex`, labels `lemma-etale-over-field` (02GL), `lemma-base-change-etale` (02GO), and `lemma-base-change-finite` (01WL); `algebra.tex`, `lemma-etale-over-field` (00U3); and `pione.tex`, `lemma-sheaves-point` (03QR), `theorem-fundamental-group` (0BND), and `lemma-fundamental-group-Galois-group` (0BNE). The tag/label mapping was checked in `tags/tags`. The assembled specialized proof is marked agent-written: these sources and the cited DAG interfaces supply ingredients, not a verbatim published proof of this exact item. No SGA source was used.

Step 1 uses the definition's every-field-extension meaning of geometric connectedness and the explicit iterated-base-change clause of `def-pc-base-change`. Thus both schemes needed in the fundamental-group theorem are connected, the geometric fibre is genuinely the same scheme, and the base points are compatible. This is an elementary application of definitions, not a new connectedness lemma.

Step 2 uses the concrete subfield/root-set statement of `lem-weil-unique-subfield-of-closure`, the equality x^Q=x from `lem-weil-finite-field-pow-card`, and the actual minimal-polynomial definition of separability. Finite spanning sets and the derivative -1 give finite separability explicitly. The same calculation for each algebraic element proves that the specified k is a separable closure, so the field-cover classification is applied with the right closure. The affine finite-module definition supplies finiteness of the field-spectrum map. This avoids silently assuming a perfect-field comparison lemma.

Step 3 cites the finite-separable-spectrum-etale lemma for the etale field map and the exact finite-base-change clause (a) and etale-base-change statement for its pullback. All their hypotheses have already been checked; no smoothness or normality hypothesis is introduced.

Step 4 takes injectivity and the marked-fibre stabilizer specifically from the last sentence of `thm-galois-fundamental`, whose statement I opened. That sentence states both assertions, beyond the abstract equivalence alone. The compatible geometric points and finite-etale hypothesis come from steps 1 and 3.

Step 5 takes the natural equivariant pullback-fibre bijection from `lem-galois-pi1-functoriality`, and the explicit stabilizer Gal(K^sep/sigma(L)) clause from `lem-exc-etale-field-galois-classification`. I checked the statement actually contains that clause. The fibre-product description is written as embeddings; all roots of T^(q^m)-T lie in the chosen k, so passing from the geometric-point field Omega to k introduces no missing embedding or path choice. The marked point is the fixed inclusion, so the stabilizer is the subgroup Gal(k/L) itself, not an unspecified conjugate.

Step 6 verifies compatibility of the arithmetic maps on each pulled-back finite cover, using the equivariance formula and the definition of pi1 as natural automorphisms. Since the subgroup inclusion is injective, the kernel calculation is an elementary intersection calculation; it does not assume surjectivity of an arithmetic map.

Step 7 uses only the geometric-kernel clause that is explicitly in `lem-wf-weil-group-exact-sequence`, together with the inverse-image and exponent definitions of `def-wf-weil-group`. It does not use a definition node as a substitute for an exactness theorem. Degree zero is equivalent to arithmetic image one, giving the original geometric kernel; step 6 then identifies the new kernel with it. The common projection from X ensures this is the same natural geometric subgroup. The degree exact-sequence node does not depend on this item, so the use is not circular. Its recorded generic Lean declaration alone was not claimed to prove this scheme-specific statement.

I checked m=1 (identity cover and full arithmetic group), X_0=Spec F_q (the predicted subgroup is Gal(k/L) and the geometric kernel is trivial), and arbitrary m with the fixed subfield inclusion. The proof does not assume a rational point of X_0, a Frobenius lift, smoothness, or normality. All proof steps are below 2000 characters. The non-elementary operations are cited existing statements; the elementary field and kernel calculations remain steps, and no clause-restatement child was created. Every citation is backed by an unaltered verbatim quotation in citations.json. No Lean was written or compiled, and no shared repository file was changed.

## Unfinished work

None in the stage-1 split. The required server dry run and delivery are performed after this report is written; the maintainer provides the independent mathematical review.
