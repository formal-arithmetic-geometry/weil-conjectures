# Q131 — lem-sfb-finite-proper-geometric-cd-bound

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-finite-proper-geometric-cd-bound.json: statement, split into four proof steps; Mathlib searched with two semantic phrasings, Loogle, LeanSearch and two grep patterns; no match.
- citations.json: fifteen verbatim cited statements, with their proof-step numbers.
- report.md: this report. searches.jsonl is the unmodified msearch command log.

No new nodes and no new Mathlib leaves.

## Attachments

None. Searched the current lean/WeilConjectures/ by the item id/docstring tag and by uniform fibre dimension and cohomological-bound concepts. The existing exists_topologicalKrullDim_pullback_le in AlgebraicGeometry/GeometricFibreDimension.lean assumes a finite-type structure over a ground field and does not cover an arbitrary quasi-compact base Y. AlgebraicGeometry.Scheme.subsingleton_H_of_two_mul_lt_of_isSepClosed in AlgebraicGeometry/Sites/CohomologicalDimension.lean covers only the cohomological clause once a dimension bound is supplied. Neither is an attachment for the whole item. The existing DAG lem-kun-dimension-extension, ordinary fibre bound and affine/Leray nodes are reused.

## WANTED

None.

## Statement and source corrections

STATEMENT-DISPUTED: the original phrase “geometric point ... with Ω separably closed” cites def-weil-geometric-point, whose statement requires Ω algebraically closed. Separably closed is insufficient for that definition: for example the separable closure of F_p(t) is separably closed but imperfect, since adjoining t^(1/p) is a nontrivial purely inseparable extension. Thus “all geometric points” would impose an additional algebraic-closure condition not intended by the stated Ω quantifier. The repaired statement explicitly quantifies over every separably closed field Ω and every scheme morphism Spec Ω → Y, removing only the conflicting geometric-point terminology and definition reference. The dimension assertion, all base changes, 2e bound and arbitrary torsion sheaves are unchanged. The source route indeed gives the stronger separably closed assertion: the finite-type torsion bound uses cd_tor(Ω) ≤ 0, without requiring perfection.

The imported proof was empty. Stacks 0F10 alone concerns morphisms between finite-type schemes over a field, so it is not applied directly to the general quasi-compact base in this item. Instead the argument uses the unit’s requested uniform fibre dimension bound (0A3V), field-extension invariance (00P3), and the affine/Leray torsion dimension calculation. The item is not the unit’s key statement, so no unit record was changed.

## Mathlib and duplicate searches

All new searches were run through msearch.py, and their exact query strings, actual hits and verdicts were appended to the existing mathlib_searches rather than replacing the inherited Q60 history. Read both semantic responses: they concern finite/quasi-finite fibres, smooth relative dimension, properness and base-change stability, without the asserted uniform dimension/cohomology conclusion. Loogle returned zero hits; the first source grep returned none; the second returned only explanatory prose in Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean:23, which I opened. LeanSearch returned finite fibres and related infrastructure, not this item. No service was reported unavailable in these searches.

Searched the whole DAG for uniform dimensions, cohomological bounds, arbitrary field extension, finite-type base change, residue-field factorization and Stacks tags, and ran blueprint_refs.py searches for fibre dimension, separably closed, uniform, 0A3V and dimension after. The field-extension result is the existing blueprint node lem-kun-dimension-extension. lem-sfb-proper-geometric-fibre-torsion-bound states only the cohomology clause for algebraically closed points with an unspecified bound c; it does not state the all-base-change dimension clause or the common 2e relation, so it is not same_as this item. No blueprint node states the full conjunction.

## Not duplicates

No new nodes. All generic inputs reuse existing nodes, including lem-fin-finite-type-fibre-dimension-bound, lem-kun-dimension-extension, the base-change permanence node and the affine/Leray bounds.

## Review by Q131

I read the item, its parent det-ctf-finite-proper-localizing proof in the main-20261015 blueprint, the complete chapter and unit records, the three route levels in SETUP.md, GOAL.md, the worker and stage-1 rules, and both copies of delivery-errors.md B–E. The parent’s “uniform bound ... and likewise for p'” is realized without assuming p' has quasi-compact target: one single bound is transported to every field-valued fibre. No six-functor or purity route was substituted.

For step 1 I opened def-weil-proper-morphism and lem-fin-finite-type-fibre-dimension-bound and read Stacks morphisms.tex 0A3V, lemma-morphism-finite-type-bounded-dimension, including its proof by the open fibre-dimension loci and quasi-compactness. Properness supplies exactly the finite-type hypothesis, and quasi-compactness of Y is expressly assumed. The bound is nonnegative and empty fibres are expressly included in the cited statement. No Noetherian hypothesis is inserted.

For step 2 I read each of the seven cited statements. The residue-field naturality node states u∘j_* = j_y∘Spec(r); def-weil-residue-field identifies the source residue field with L. The canonical point of Spec L is the identity, giving the desired factorization. I checked Schemes 01J9 (lemma-characterize-points), the discussion preceding it and the following naturality diagram, not merely the geometric-point definition, so the argument works for every field L. def-pc-scheme-fibre gives X_y as the required pullback; def-pc-fibre-product supplies its universal property. The two directions of the iterated-pullback comparison and their inverse property are written explicitly. The base-change permanence node’s clause (2) applies to arbitrary scheme maps, not only finite-type base maps; I read its source morphisms.tex 01T4, lemma-base-change-finite-type. Hence X_y is finite type over κ(y), exactly the hypothesis of the field-extension clause of lem-kun-dimension-extension. That node’s field-extension equality is what is used; its dense-open clause is not used. I read the source blueprint statement and the correct Stacks algebra.tex 00P3, lemma-dimension-preserved-field-extension, whose Noether-normalization argument covers arbitrary field extensions. The blueprint’s assertion that an arbitrary field-extension projection is finite type is not used. Isomorphism invariance of dimension is explained directly using def-kun-topological-krull-dimension’s chain definition, rather than importing an unrecorded theorem.

For step 3 I opened def-pc-base-change, def-pc-scheme-fibre and def-pc-fibre-product. Their statements give exactly the two pullbacks and the universal property used. The argument is elementary: the S-component is forced, and projectionwise uniqueness proves that the two maps are inverse. It does not appeal to a hidden comparison theorem or to quasi-compactness of S. Its point s is arbitrary, so the original item’s all-fibres/all-base-changes quantifiers are covered.

For step 4 I opened lem-sf-separably-closed-torsion-cd and both new-thm-sc-* cited statements. The field node gives c=0 for every separably closed field. The affine node states the bound for dimension at most e and all torsion abelian étale sheaves, while the reduction node states precisely the resulting 2e+c bound for a finite-type scheme of dimension at most e. Thus the affine statement is the hypothesis requested by the reduction, not a definition or merely a fully faithful functor. I read Stacks etale-cohomology.tex 0F0V, proposition-cd-affine, the comparison with field Galois cohomology in 03QU, lemma-compare-cohomology-point, and the complete affine-to-global Leray proof of the blueprint thm-sc-finite-type-torsion-cd. In particular these inputs concern ordinary cohomology, arbitrary torsion sheaves, and no fixed annihilator or prime-to-characteristic assumption. I deliberately used the existing dimension-at-most reduction instead of the theorem whose statement specifies an exact natural dimension; this avoids excluding the empty fibre.

I checked small cases: the empty base and empty source admit e=0, empty fibres have bottom dimension and are allowed by the at-most statements, zero-dimensional fibres give the positive-degree vanishing, and inseparable extensions (including an imperfect separably closed field) introduce no finite-type or separability requirement on L/κ(y). Nonreduced and disconnected fibres are also allowed by all inputs. No new lemma has been manufactured from an item clause, and no mathematical statement remains to be split in this delivery beyond the existing cited nodes. All four steps are shorter than 2000 characters; each non-elementary input is cited, and citations.json quotes its actual statement verbatim. The five off-unit generic tools are declared in split_report.tool_uses, with their roles, for the maintainer to review.

## Unfinished work

None. No Lean was written and no compiler, Lake or build command was run. All project and launcher files were read-only; writes were confined to this sandbox. Required server-side validation and direct push follow this report.
