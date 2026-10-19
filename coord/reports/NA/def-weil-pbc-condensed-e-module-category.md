## Files written

- dag/nodes/sec-proper-base-change/def-weil-pbc-condensed-e-module-category.json: definition, split; no Mathlib match for the combined coefficient/category/exchange construction.
- dag/nodes/sec-proper-base-change/lem-weil-pbc-profinite-point-pullback.json: statement-only well-definedness input, unsplit; no exact Mathlib match.
- citations.json: empty list, because this item is a definition and has no proof steps.

## Attachments

None. Searched the full slopmaster2 WeilConjectures tree for the item tag, condensedRingObj, pointUpperStar, upperStarFromPoint and profiniteToProEt. None occurs. Existing slopmaster2 pro-etale bounded constructible categories use different coefficient constructions and do not attach this item. The master definitions are reference material: Basic.lean has sorried geometric and monoidality inputs, DerivedCategory.lean has sorried ambient module-category instances, and no master declaration is claimed as a finished proof.

## Wanted sources

WANTED: literature/upstream-master-20261014/WeilConjectures/RefactorInstruction.tex, Sections 4 and 5 (lem:XS, prop:pX, eq:triangle, thm:alpha), for lem-weil-pbc-profinite-point-pullback. This file is not in the literature archive; I read it directly in the exact read-only master checkout. No download or archive write was made.
The archived Proper.lean references definitions outside the archive; I read Basic.lean, ConstructibleSheaf/ProEtaleModule/Def.lean and DerivedCategory.lean, and BaseChangeTheorems/MorphismDefs.lean in that same master checkout.

## Corrections and limitations

The imported statement is faithful to the actual definitions. Added explicit universe conventions and the named geometric well-definedness input, and clarified that the last counit belongs to the f-adjunction (the unit belongs to f-prime). No coefficient/category criterion was changed. In particular, no replacement of local finite presentation by lisse finite free modules, no completion, and no claim of automatic preservation for arbitrary schemes was added.

The item is a definition, so its split is its constituent notions in stmt_deps, not a fabricated theorem proof. The new lemma isolates the geometric existence/monoidality required to apply those definitions, independently of E, constructibility, rationalization and proper base change. It does not restate the category or exchange. Its proof is intentionally empty. There is no key-unit realization update: this item is not the proper-base-change unit's key theorem.

## Not duplicates

lem-weil-pbc-profinite-point-pullback vs lem-weil-pbc-profinite-coefficient-inverse-image: the latter concerns inverse limits of finite constant ring sheaves, not the geometric inverse image from the profinite point or its monoidal comparisons; it does not cover a condensed topological field.
lem-weil-pbc-profinite-point-pullback vs lem-weil-pbc-continuous-functor-sheaf-pullback-adjunction: the latter assumes continuity and proves a general Kan-extension adjunction; it does not prove that the locally constant integer spectrum construction is weakly etale, continuous, or monoidal.
lem-weil-pbc-profinite-point-pullback vs lem-weil-pbc-site-pullback-abelian-exact: the latter assumes a morphism of sites and proves exactness, not the particular morphism's existence or tensor/composition comparisons.
lem-weil-pbc-profinite-point-pullback vs def-weil-pbc-site-comparison-morphism: the latter constructs the etale-to-pro-etale comparison, not the profinite-point comparison.
lem-weil-pbc-profinite-point-pullback vs def-weil-pbc-condensed-e-module-category: the item defines categories and a mate for E; the new lemma supplies a geometric inverse image and monoidal comparisons for arbitrary sheaves, without constructing any constructible category or any mate.

## Review by NA

I read RefactorInstruction.tex Sections 4 and 5 in the exact master source, including the finite-test-object argument of lem:XS, the direction and Kan-extension description in prop:pX, and the base-change identity and monoidal comparison in thm:alpha. These are the source of the new statement. I also read Basic.lean's actual declarations pointUpperStar, upperStarFromPoint, upperStarFromPointComp, coefficientPullbackIso and condensedPullbackHom. The underlying abelian functor is left Kan extension followed by sheafification, not precomposition. The monoidal input is explicitly sorried in master, so it must remain open in the DAG. The size convention uses larger-universe sheaves on smaller-universe profinite objects; no unbounded colimit over a purported small category was assumed. Derived pullback composition here means the termwise functor from exact module pullback, so this comparison is the one used in the master square construction, not a separately chosen isomorphism.

For the item's coefficient clause, I checked def-weil-pbc-proetale-site for the site and size conventions, def-weil-proetale-inverse-image for the scheme inverse image, and def-weil-pbc-sheafification for the universal-property sheafification. The new input says precisely that the point inverse image exists and transports tensor/ring structures, so the phrase induced ring-object structure now has an explicit mathematical prerequisite. Continuous functions form a sheaf on finite profinite covers: a finite disjoint union of covering sources maps quotient-surjectively onto the compact Hausdorff target; matching continuous functions descend uniquely. The ring laws hold pointwise, including restrictions by precomposition. This elementary descent is not a new node.

For the internal-module clause, I opened def-pur-sheaf-tensor-product and def-weil-sheaf-of-modules-category. Their statements give sheafification of sectionwise tensor product and sectionwise compatible module actions respectively. An action from the sheaf tensor is equivalent by its universal property to sectionwise bilinear multiplication, and associativity and the unit can be checked sectionwise. I did not cite def-pod-internal-module: its fixed external ring is not this ring object.

For bounded constructibility, I read the actual IsLocallyFinitelyPresented and IsConstructible definitions and boundedConstructible and BoundedConstructible in master, including mem_boundedConstructible_iff. They require finite-rank presentations after a pro-etale cover of each stratum, and bounded cohomology; they impose no completeness. def-constructible-stratification defines precisely finite locally closed strata with immersions. def-weil-abstract-derived-category supplies the unbounded localization and cohomology. The definition is valid for arbitrary T; topological noetherianity occurs only in a separate triangulated-subcategory instance, which is not asserted here.

For the functor and exchange clauses, I opened def-weil-pbc-proetale-operations: its statement explicitly accepts an arbitrary sheaf of commutative rings with a coefficient pullback isomorphism, defines the ordinary uncompleted unbounded functors, and gives their adjunction. It is therefore applicable with the new point-comparison component, without identifying E with a constant discrete sheaf. Restrictions are conditional on preservation, exactly as the item says. I checked MorphismDefs.lean's three actual transformations: insert the f-prime unit, use the composition comparison in the stated direction, then contract the f counit. The middle comparison has source f-prime-star g-star and target g-prime-star f-star. Thus the final source and target are correctly typed. The archived instantiation uses separated finite-type schemes over a field of positive characteristic distinct from ell; this definition does not claim preservation outside that setting, nor invertibility even inside it. No cartesianness or properness is needed to define the mate.

For B through E, the only new node introduces all its objects, has a statement only, no proof or hidden proof sketch, and no dependency on this item or on a realization equivalence. Searches of the whole DAG and blueprint were made for condensed, profinite, point pullback, finite limits, inverse image and the actual declaration names. I opened the close existing statements distinguished above. The source is project-specific, so no unrelated Stacks tag is attached; generic Stacks-based notions are reused through the existing nodes. Mathlib searches ran through msearch.py only and the recorded queries come from searches.jsonl. The hits are generic CondensedMod, LightCondensed monoidal infrastructure and affine limit results, not this construction; LeanSearch returned Internal Server Error and is recorded unavailable. Two semantic phrasings were tried for both the item and the new input.

Small cases: the empty profinite set gives the empty affine scheme and its unique map, a singleton gives Spec Z, finite discrete sets give finite disjoint unions of Spec Z, and identity scheme morphisms give the identity comparison. Finite products and equalizers use the pro-etale-site limits, not products over an unrelated base. The empty scheme allows the empty stratification and the zero complex; zero ranks in a finite presentation are permitted. For the identity square the unit/counit triangle gives the identity exchange. No false unrestricted preservation or local-freeness assertion was imported. The review repaired only the missing named geometric input, universe clarity and counit notation.

## Unfinished work

The new geometric input is intentionally unsplit, as required by the one-level rule. No Lean was written or compiled. A second reader must review and deliver; this worker runs only --no-push.

## Second reading by NA

- Item statement: checked against `Proper.lean` module docstring and the referenced `Basic.lean`, `Def.lean`, `DerivedCategory.lean`, and `MorphismDefs.lean`; coefficient object, internal-module category, bounded constructibility, derived operations, and ordered unit/comparison/counit mate agree clause by clause, including the conditional preservation and arbitrary-square hypotheses.
- `lem-weil-pbc-profinite-point-pullback`: checked against `RefactorInstruction.tex` Sections 4–5 (`lem:XS`, `prop:pX`, `eq:triangle`, `thm:alpha`) and the corresponding master declarations; all objects, universe/site hypotheses, finite-limit and covering assertions, exact monoidality, and composition comparisons are stated explicitly. It is statement-only and has no proof steps to audit.
- New-node form: both nodes are self-contained, statement-only, carry source places, blueprint metadata, and recorded semantic/grep searches; no Mathlib or slopmaster2 declaration matches either construction. The new node is strictly auxiliary and does not restate the item's category or exchange definition.
- Edge cases: checked empty and singleton profinite sets, finite discrete profinite sets, identity morphisms and squares, empty schemes, zero complexes, and zero-rank presentations; no hypothesis or case is silently lost.
- Changes made in this second reading: none; the worker's explicit geometric input, universe convention, and counit typing are correct. Delivery dry-run was rerun after this review.
