## Files written

- dag/nodes/sec-proetale-coefficients/lem-pe-injective-complex-slice-section-model.json: statement, split, no exact Mathlib match. All hypotheses and clauses retained; six proof steps.
- citations.json: a verbatim statement quote for every step/node citation.
- No new nodes and no new Mathlib leaves.

## Attachments

None. Searched WeilConjectures/ in the read-only slopmaster2 checkout by the exact blueprint tag, item id, injective-complex/derived-sections/slice terminology, and localized module restriction. No project declaration states every clause for arbitrary small sites and arbitrary unital rings. The upstream master source is reference only. Existing generic derived-functor declarations are used through existing DAG nodes, not presented as an attachment for this item.

## WANTED

None. Sources used are present in literature/stacks-project/.

## Corrections and route

The item had no proof. Its statement is unchanged. No statement dispute was found. Its source points to 03F3 and 05TA; I read 03F3 in sites-cohomology.tex (lemma-cohomology-of-open and the following equation-restriction-mapping), sites-modules.tex 04IX/03DH and the extension-by-zero lemmas 03DI–03DJ, and derived.tex proposition-enough-acyclics (05TA). For the natural bounded-below comparison I used the more precise existing Mathlib leaf lem-weil-pbc-right-derived-plus-injective, whose statement includes the unit, its invertibility, and the full universal property, sourced to 05TI/05TH/05SA. Its Mathlib RightDerivedFunctorPlus.lean definition and unit at lines 36 and 45 and IsRightDerivedFunctor instance at line 51 were read.

The chapter record sec-proetale-coefficients and unit record sk-prop-sf-comparison were read. The unit JSON still records the older sec-smooth-purity sketch while the current main-20261015 _section.md is the bounded-below comparison theorem. I followed the current blueprint: the ancestor det-sf-comparison-affine-continuity proof Steps 3–4 require a coherent diagram for the derived colimit, and its existing split Step 5 invokes this item precisely for that purpose. This is a generic localization tool below those steps; no unit statement or proof route is changed, and no unit metadata is edited.

Two existing generic nodes are declared in split_report.tool_uses: lem-pur-kinjective-restrict-localized-adjunction supplies exact extension by zero for module sheaves, and lem-weil-pbc-ring-sheaves-grothendieck supplies ambient enough injectives through the existing Grothendieck theorem. The comparison unit has no replacement for either generic categorical input. No SGA source is used.

## Mathlib and duplicate searches

The interrupted sandbox contained only searches.jsonl and brief markers; there was no node, report, or delivery process for this item. I read and retained that search evidence. The recorded LeanFinder queries use two phrasings (bounded-below injective complexes on every slice; derived evaluation natural in a site object). The LeanSearch query concerns derived global sections on localized sites; Loogle uses CategoryTheory.Sheaf, CategoryTheory.Injective. The grep queries concern injective localized restrictions and overPullback/rightDerived/cohomologyPresheaf. They found K-injective infrastructure, right-derived evaluation ingredients and underived sections restriction, not the combined statement. I read Mathlib Sites/SheafCohomology/Basic.lean:35, where even its abelian cohomology localization comparison is TODO, Sites/Over.lean:288 and ModuleCat/Sheaf/PushforwardContinuous.lean:59–90. The last grep was rerun to read its full file/line hits; all records in the JSON correspond to actual msearch log entries. Imported searches belonging to the existing item were preserved.

Searched the whole DAG by 03F3/05TA/08FI, constant ring sheaf, localized restriction, injective complexes and derived-section models; searched the whole blueprint with blueprint_refs.py for the exact item concepts, 03F3, localized, and derived sections. Reused the module extension adjunction rather than the abelian-only lem-weil-pbc-site-restriction-injectives or abelian-only cohomology-over-object node. The scheme-specific EtaleSectionsRestrictionSquare also has the wrong category for this item; its general categorical idea is written out directly from the existing universal-property leaf. No new smaller lemma or duplicate was created.

## Not duplicates

No new nodes, hence no new/existing same-tag pairs. The item is more than lem-weil-pbc-cohomology-over-object-localization: that node states abelian sheaf cohomology in nonnegative degrees; this item gives derived module objects for bounded-below complexes, specified identifications and literal transition maps on arbitrary small diagrams.

## Review by Q143

I checked the unchanged statement against the sources above. In 03F3 the coefficients are a sheaf of rings and the conclusion is injectivity after restriction and equality of the two section-resolution complexes; its proof uses the exact left adjoint. The module formulas in 03DI–03DJ use left scalar multiplication and do not require a commutative ring. 05TA applies to additive functors between abelian categories and bounded-below acyclic complexes. The existing 05TI/05TH leaf gives exactly the natural unit version needed here; I did not infer naturality of the chosen isomorphisms from an objectwise existence statement.

Step 1 uses def-pur-localized-ringed-site for the actual sectionwise functor and relocalization. Its explicit values agree at every test object. lem-pe-constant-left-module-inverse-image states preservation of the constant ring, exactness on left modules, compatibility with restrictions, and preservation of quasi-isomorphisms for arbitrary unital rings; these are exactly its uses, with localization as the geometric inverse image. In particular no finite or commutative coefficient assumption is imported. The identity object is terminal because a map to it is the structure map of the slice object.

Step 2 uses lem-pur-kinjective-restrict-localized-adjunction for the finite-limit/finite-colimit preserving left adjoint, not for an injectivity clause it does not state. The zero-map hypothesis is checked sectionwise. def-weil-sheaf-of-modules-category supplies abelianness; then lem-sp-right-adjoint-preserves-injectives applies in the correct orientation, exact extension G_W on the left and restriction S_W on the right. The lower bound persists by the explicit values. This proves a clause of the item directly rather than moving it into a new node.

Step 3 uses ring-sheaves-grothendieck on the site and every slice in the fixed common universe, then grothendieck-enough-injectives; it uses ring-modules-enough-injectives only for its abelian-category assertion. The module category definition gives sectionwise kernels and addition, so evaluation is additive and left exact. right-derived-plus-injective supplies both the unit and invertibility on S_W L. Its hypotheses (abelian source/target, enough injectives, additive functor) are all checked. The formula alpha_W = RE_W(S_W e) eta explicitly has the required direction Q(L(W)) to RGamma(K|W); it uses the actual evaluation differential.

Step 4 uses the universal property in clause (1) of right-derived-plus-injective. The section map t_a is evaluated on the actual arrow from W'/W to the terminal W/W, so naturality makes it a chain map. Exactness of restriction from Step 1 lets the proposed target functor factor through D+. Applying the stated universal property to Q(t_a) followed by the target unit constructs the derived section pullback and gives the displayed equation. Thus the comparison square is proved by a specific universal-property computation, not assumed as a separate general compatibility theorem. The second citation, localized-ringed-site, supplies exactly the sectionwise relocalization identification; under it t_a is r_a. This is one direct application of a cited universal property followed by evaluation, hence marked elementary.

Step 5 substitutes Step 4 into the naturality equation for rho at e. The second equality follows from the naturality of the cited derived unit at f and the specified equation u e = e' Qf. These compositions prove the asserted equality for the supplied identifications; they are ordinary substitution and functoriality, not an uncited comparison theorem.

Step 6 uses the module-sheaf definition's presheaf laws to obtain strict identities and composition degreewise, and the same sheaf-map naturality for the differentials. The common lower bound comes from the single L, independently of the size of the small diagram. Finally the cited unit theorem applied to J[0] on the slice computes module cohomology by J(W)[0], and its positive-degree terms are zero. This proves module cohomology vanishing without assuming that forgetting scalars preserves injectivity.

Edge cases checked: W terminal gives ordinary global sections; a identity gives identity restriction; two composable arrows satisfy the presheaf composition law on the same complexes. L=0 and J=0 give zero objects and maps. The empty diagram is strict with the original lower bound vacuously. The zero ring has only zero unital modules; a noncommutative ring such as a matrix ring uses only left linearity throughout. A lower bound N different from zero is unchanged by evaluation. No positivity assumption is used for the derived-object comparison. All six steps are under 2000 characters, and none hides a separate comparison lemma.

The B–E checklist was read in full: there are no new-node shape obligations, fabricated searches, unattached exact Lean matches, omitted hypotheses, stronger citations than their statements, or new clauses substituted for the item. All step citations are quoted verbatim in citations.json. No non-elementary fact is sourced only to a tag: the substantive extension adjunction, injective preservation, enough injectives and derived-functor statements are existing cited nodes. No unresolved mathematical work remains in this split.

## Unfinished work

None in the stage-1 split. Delivery remains subject to the required dry run and independent maintainer review.
