# def-sfb-dc-upper-star-comp — Q108

## Files written

- `dag/nodes/sec-six-functors-basics/def-sfb-dc-upper-star-comp.json`: existing definition, repaired and marked split; statement unchanged.
- `dag/nodes/sec-six-functors-basics/det-prop-sfb-module-pullback-exact-main.json`: new statement node, blueprint exactness lemma; Mathlib searches found only generic exactness infrastructure.
- `dag/nodes/sec-six-functors-basics/prop-sfb-module-left-derived-upper-star-comp.json`: new statement node, blueprint ambient derived-composition lemma; Mathlib searches found only generic derived-category and ordinary sheaf pullback comparisons.
- `citations.json`: eight verbatim full-statement step/node quotations.
- `report.md`: this report. No Lean was written or compiled.

## Attachments

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and `Comparator` for the item id, `boundedConstructibleUpperStarComp`, and the relevant upper-star names. There is no sorry-free project declaration stating this item. The upstream master reference has the similarly named declaration in `SixFunctors/ProEtale/ModuleObject/Derived/BoundedConstructible.lean:142–155`, but its preservation input is sorry and the master checkout is reference material only.

## Wanted sources

WANTED: none.

## Findings and repairs

The released Q108 handoff required re-splitting the imported first proof step because it was 3359 characters and hid several lemmas. I kept the item statement, route, and restriction/uniqueness steps. I replaced the long ambient paragraph by two short steps citing two new statement-only nodes. The first states exactness of module-object pullback, matching the blueprint node `det-prop-sfb-module-pullback-exact-main`; the second states the ambient derived pullback composition isomorphism, matching `prop-sfb-module-left-derived-upper-star-comp`. The item's second step still records the degreewise comparison, localization, component formula, and inverse, so the ambient normalization is explicit. No new node restates the restricted item's conclusion.

I searched the whole DAG and current blueprint before creating both nodes. Neither statement had an existing DAG node or a same-as blueprint node outside its own blueprint record. Both new nodes are statement-only and therefore carry no proof sketch or proof dependencies. They have the required three search kinds plus repeated valid phrasings in the authentic `searches.jsonl` log. The Mathlib candidates are generic (`mapDerivedCategory`, `leftDerivedNatIso`, `SheafOfModules.pullbackComp`, and additive/abelian sheaf instances), so neither node is a Mathlib leaf.

## Review by Q108

I read the item source and proof in `literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-def-sfb-dc-restricted-functors/def-sfb-dc-upper-star-comp.{md,proof.md}`, the restricted-functors unit and chapter, and the released repair note. I read the exact blueprint source statements for both new nodes and the statements of every node cited by every item step. The new exactness node states precisely that `mapMod(f^*_{Ab})` and `Ext_{alpha_f}` are exact and that their composite module pullback is additive and preserves finite limits and colimits. The new ambient node states precisely the natural isomorphism `L(g∘f)^* ≅ Lf^*∘Lg^*` and that it is induced by the underived module comparison.

Step 1 cites those exactness and derived-category statements. The cited derived-category statement says an exact functor has derived functor `D(F)` applied termwise, which supplies the quasi-isomorphism inversion used here. Step 2 cites the ordinary module pullback composition statement, the new ambient statement, and the localization universal-property statement. Those statements provide the ordinary comparison, its ambient derived comparison, and descent of the degreewise chain map together with inverse preservation. I checked the displayed component formula's order: the inverse of the composite comparison is `(L_f ψ_g)^{-1}` followed by `ψ_f^{-1}`, then the localized degreewise `a`, then `ψ_{gf}`. Steps 3–5 cite the stated inclusion comparison and the bounded-constructible full-subcategory statement. The latter explicitly says morphisms, identities, and composition are ambient, which is exactly what the inverse, naturality, and componentwise uniqueness arguments take from it. All hypotheses (the fixed setting, arbitrary commutative condensed ring, and composable morphisms) remain those of the item and its cited definitions.

I checked delivery-errors B–E: each new node is self-contained and statement-only; the item statement is unchanged; there are no duplicate or clause-restatement nodes; every non-elementary fact used by a step is a cited statement; and every citation quote in `citations.json` is a verbatim substring of that statement. The previous overlong step is gone; all five replacement steps are under 2000 characters. I tested identity morphisms, zero complexes, the zero coefficient ring, and empty schemes conceptually: exactness, the degreewise comparison/localization, and the full-subcategory Hom-set argument do not require nonzero or nonempty hypotheses. No statement dispute, SGA citation, Lean edit, compiler, Lake, or direct git command was used.

## Unfinished work

None before the required dry run and delivery. The two new nodes remain unsplit by design and enter the stage-1 queue below this item.

## Dry-run repair

The first dry run rejected the ambient-node quotation because “There is a natural isomorphism” was too short to show the fact used. Rebuilt all eight quotation pairs using the complete statements verbatim. Corrected the two new nodes’ blueprint ancestry to the item; their source files exist in the current blueprint but are not imported DAG records, so neither is marked as an imported node. Their source statements were read directly, and the whole imported blueprint/DAG search found no existing record to cite. The parent’s statement and Lean audit remain byte-for-byte unchanged. Read the actual Mathlib candidates at ExactFunctor.lean:20–145, PullbackContinuous.lean:150–185 and FullyFaithful.lean:365–389; they give generic constructions or ordinary sheaf-module comparisons, not either new geometric statement.
