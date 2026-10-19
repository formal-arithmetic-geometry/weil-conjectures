# Stage-1 report: prop-sfb-module-left-derived-upper-star-comp

## Files written

- `dag/nodes/sec-six-functors-basics/prop-sfb-module-left-derived-upper-star-comp.json`: statement preserved, four proof steps, status split; no exact Mathlib match.
- `citations.json`: a verbatim statement quotation for each of the seven step/node citations.
- `report.md`: this report. The search command also generated `searches.jsonl`.

No new nodes; no new Mathlib leaves. The chapter, unit, source, creation metadata and ancestry of the existing item were preserved. This is not the unit's key node, so no unit record was changed.

## Attachments

None. I searched the project declarations under `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` both for the blueprint tag and for `leftDerivedUpperStarComp`. The declarations in `SixFunctors/ProEtale/Derived/UpperLowerStar.lean` and the analogous etale file concern sheaves valued in a fixed coefficient category, not module objects over the pulled-back condensed ring. The slopmaster2 checkout has no `SixFunctors/ProEtale/ModuleObject` directory. Its generic exact-left-derived construction is a tool, not the item. The archived master has `AlgebraicGeometry.ProEtale.CondensedRing.leftDerivedUpperStarComp` at `WeilConjectures/SixFunctors/ProEtale/ModuleObject/Derived/UpperLowerStar.lean:226`, but master is reference only and its K-flat-preservation instance at line 177 is sorried. It is not evidence for an attachment.

## WANTED

None. All sources used are present locally. No SGA source is used.

## Source and dependency audit

I read the current main-20261015 chapter, the recorded restricted-functor unit and its two steps, the item statement and proof under `sk-prop-sfb-module-derived-factorization`, that factorization unit and its proof, and the source of the ordinary composition isomorphism. The current item proof explicitly takes the exactness/levelwise route: derive the ordinary natural isomorphism and transport through the canonical identifications with levelwise functors. I retained that route, and expanded the descent so that the induced comparison is specified, not just an unspecified isomorphism of the two functors.

The blueprint proof refers to `prop-sfb-module-left-derived-upper-star-levelwise` and `sk-prop-sfb-module-pullback-exact`, neither of which has a node under that id in this DAG. I searched the whole DAG by concept and declaration and used the existing exactness node `det-prop-sfb-module-pullback-exact-main` and the general exact-derived tools instead. In particular, `sk-def-sfb-module-pushforward-pullback` does not assert exactness of module pullback, so I did not cite that definition as if it supplied exactness. The exactness node's complete statement explicitly supplies additivity and both finite-limit and finite-colimit preservation for every condensed ring and every scheme morphism. Its current blueprint statement and proof were read, including transport, invertibility of alpha and extension along an isomorphism.

The item's original statement mentions ordinary module pullbacks only through the ordinary comparison and derived module pullbacks. Its redundant umbrella `sk-def-sfb-module-pushforward-pullback` statement edge was removed; the three remaining statement edges are precisely the bracketed notions in the preserved statement. Their own dependencies supply the coefficient and module-category definitions.

I read the statements of every cited node in full. I also read Stacks `derived.tex`, Tag 015F, label `lemma-right-derived-exact-functor`, including its omitted-details proof, and `categories.tex`, Tag 04VG, label `lemma-properties-left-localization`, part (3). The natural-transformation version needed here is not claimed to follow from that Stacks sentence alone: it is explicitly supplied by the existing Mathlib-leaf localization node. I verified its source, `CategoryTheory.Localization.fullyFaithfulWhiskeringLeft`, in pinned `Mathlib/CategoryTheory/Localization/Predicate.lean:278`, and read its full/faithful ingredients and `natTrans_ext` immediately below.

The general node `lem-weil-pbc-exact-functor-derived-functor`, clause (1), is declared in `split_report.tool_uses`. It is a generic Kan-extension identification, not a replacement for a step of the restricted-functor unit. The two other generic nodes are Mathlib leaves. No maintainer-owned `tool_uses` was written.

## Mathlib and duplicate searches

All new Mathlib queries were run through the prescribed `msearch.py` command and were read. There are two semantic phrasings. The geometric phrasing finds ordinary sheaf-module pullback comparisons; the general phrasing finds exact-functor localization infrastructure. The local grep confirms that `leftDerivedFunctorCompIso`, `mapDerivedCategoryCompIso` and `leftDerivedUpperStarComp` do not occur in this pinned Mathlib. The online Loogle index has a newer `mapDerivedCategoryCompIso`, but it is absent from the pinned `ExactFunctor.lean`, which I opened completely. A second grep locates `Functor.mapDerivedCategory` at line 36 and `Functor.mapDerivedCategoryFactors` at line 41; these are already recorded by `lem-weil-pbc-exact-functor-derived-factorization`. None supplies the item by a one-line specialization: one must still prove pullback exactness and identify the chosen total derived pullbacks. The previous item's recorded searches were retained as received; all appended records are actual Q29 queries in `searches.jsonl`.

Whole-DAG searches included exact-derived statements, module pullback exactness, ordinary and derived composition, and `mapDerivedCategory`. Whole-blueprint searches included `derived pullback composition`, `composition isomorphism of derived pullbacks`, `exact functor`, and `localization`. The blueprint helper reports the ancestor as `def-sfb-dc-upper-star-comp`, consistent with the preserved ancestry. The ambient comparison of that node is the place this item serves. Its restricted conclusion does not duplicate the present ambient conclusion. No new node is justified.

## Not duplicates

No new nodes were created. Existing exactness, localization and exact-derived nodes were reused; the existing ordinary composition isomorphism is underived and the ancestor is restricted to bounded constructible objects.

## Review by Q29

I checked B1--B10, C1--C8, D1--D5 and E1--E7 against the actual statements and the sources above. There are no new-node hypotheses or sources to audit. The following is my mathematical reading of each step.

1. `sk-def-sfb-module-derived-pushpull` really defines the full composite pullback's total left derived functor on the unbounded module-object categories. `det-prop-sfb-module-pullback-exact-main` really asserts its additivity and exactness, with no finite-type, finite-coefficient, flatness, boundedness, or constructibility restriction. `def-weil-abstract-derived-category` supplies precisely the cochain localization and universes used. I apply exactness separately to f, g and their composite h. These are all scheme morphisms, so all three applications have their hypotheses.
2. `lem-weil-pbc-exact-functor-derived-factorization` supplies quasi-isomorphism preservation and the correctly oriented isomorphism D_a Q_S -> Q_T C(F_a), for exact additive functors between abelian categories. The module-object categories are the abelian categories in the preceding derived-functor definition. Clause (1) of `lem-weil-pbc-exact-functor-derived-functor` explicitly states that this pair is a *left* derived pair as a right Kan extension; its right-derived and bounded-below clauses are unused. I wrote both canonical maps and both inverse equations, using uniqueness in those universal properties, rather than assuming a compatibility absent from its statement. Thus the resulting comparisons p_a are natural and invertible on every complex. This is a short formal uniqueness calculation from the cited theorem, not a hidden new exact-derived lemma.
3. `def-sfb-module-upper-star-comp` states b in exactly the direction h^* -> f^* g^*. I use that b, with the corrected mate convention already in its current statement. Naturality at the differential is the displayed chain-map equation. The inverse and naturality on complexes are checked degreewise. This step is elementary and does not assert anything about a derived comparison before descent.
4. `lem-weil-pbc-localization-universal-property` clause (2) supplies descent of a natural transformation, the component equation, and preservation of compositions and identities; clause (3) supplies uniqueness. Its hypotheses are fulfilled by the actual cochain localization Q_Z. The composites with Q_Z invert quasi-isomorphisms because Q_Z does, without claiming that derived functors act on unlocalized complexes. I checked all arrows: p_g takes L_g Q_Z K to Q_Y C(F_g)K; L_f(p_g), followed by p_f at C(F_g)K, has source L_f L_g Q_Z K and target Q_X C(F_f)C(F_g)K. Therefore q^{-1} Q_X(B) p_h has source L_h Q_Z K and the required target. Descending its actual inverse proves invertibility. The last equation proves the “induced by the underived composition isomorphism” clause, not merely abstract existence.

The new proof corrects an implicit strict equality of induced functors in the blueprint: composition is represented termwise, while chosen localization functors are related by canonical isomorphisms. No mathematical statement was changed. It avoids the false general assertion that arbitrary total left derived functors commute with composition. Exactness is the explicit hypothesis making this construction work. It uses no assumption that an intermediate pullback preserves K-flat complexes. On identity scheme morphisms the construction reduces to descent of the ordinary identity comparison; on the zero complex and for the zero coefficient ring every displayed map still has the specified type and is invertible. Empty schemes and unbounded complexes remain covered. There is no use of finite-coefficient/stalk identifications, no change of coefficient category and no cycle through the restricted ancestor.

All four non-elementary/elementary steps are under 2000 characters. Each is either a direct cited application or an explicit degreewise/universal-property argument, with no inline subclaim needing another node. The unsplit exactness prerequisite is intentionally cited by its *statement*, not assumed proved or resplit. No definitions or a clause of this item were packaged as new lemmas. No separate reader or agent was started, as required for this direct delivery.

## Remaining work

No mathematical part of this one-level split remains. The referenced unsplit prerequisite is work for its own claimed node. Required server checks and final delivery are performed after this report is written.
