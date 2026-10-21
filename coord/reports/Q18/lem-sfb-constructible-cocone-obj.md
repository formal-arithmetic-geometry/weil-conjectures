# Q18: lem-sfb-constructible-cocone-obj

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-constructible-cocone-obj.json`: existing statement, re-split; statement and statement dependencies unchanged.
- `dag/nodes/sec-six-functors-basics/lem-sfb-constructible-cocone-ambient-realization.json`: new statement-only lemma, status `unsplit`; no Mathlib match after five logged searches, including two semantic phrasings, Loogle, LeanSearch, and source grep.
- `citations.json`: fourteen literal statement excerpts for the five assembly steps.

## Attachments

None. The project declaration `AlgebraicGeometry.ProEtale.constructibleCocone_essSurjObj` in `lean/WeilConjectures/SixFunctors/ProEtale/ModuleObject/Colimit/TwoColimit.lean:237` has `sorry` at line 238. Its hypotheses are exactly a prime and a topologically Noetherian scheme. Searches for the blueprint identifier and cocone terminology found no completed declaration giving the item. The ambient realization package is not already a single project declaration either.

## WANTED

None. The source used here is the local current blueprint and the actual project coefficient definitions; no SGA source is used.

## What changed and why

This is the human's explicit re-split, not a request to re-accept a live reviewed split. The live repository has already shortened the originally reported 5686-character proof by using the existing generic finite-truncation devissage lemma. I retained that improvement. The sandbox initially had no node, report or searches to preserve, so I copied the current item and retained all imported metadata, Lean bindings, original statement, and prior Mathlib search records.

The remaining setup combined identification of two coefficient presentations, identification of their constructibility predicates, inherited triangulated structures at finite stages, exact ambient scalar-extension functors, and the match of the actual cocone comparisons. I extracted that setup into a new statement-only ambient-realization lemma. This lemma asserts no descent of objects, no closure of the union of essential images, and no (Obj) clause. The main argument still uses morphism descent to make the union triangulated, proves the degree-zero case using module descent and the exact single-complex comparison, and applies finite Postnikov devissage. None of those arguments is moved into the new node.

The new lemma is the compatibility package for a specific geometric coefficient system, not a generic statement that the inclusion of a triangulated subcategory is triangulated. Its identification of pulled-back rings and local finite presentations, followed by construction of the shift/triangle structures and agreement of the prescribed comparison maps, remains work for its next stage-1 worker. The intended route is: expand the point pullback and coefficient definitions; use the existing finite-model API for finite-stage triangulation and the condensed flat coefficient calculus for exact scalar functors; transport those structures along the ring/predicate identifications; then use the full-subcategory restriction formula for the actual cocone comparison. This paragraph records the route in the report, not as a proof inside the new unsplit node.

## Not duplicates

lem-sfb-constructible-cocone-ambient-realization vs lem-sfb-constructible-cocone-obj: ambient realization is setup for the given scalar cocone; it asserts no object has a finite coefficient model.

lem-sfb-constructible-cocone-ambient-realization vs lem-weil-pbc-condensed-finite-model-proof-api: the latter states triangulation for finite coefficient object properties, but does not identify the blueprint coefficient/presentation conventions or realize its specified cocone comparisons in the ambient category.

lem-sfb-constructible-cocone-ambient-realization vs lem-weil-pbc-condensed-flat-coefficient-calculus: the latter gives ambient exact scalar functors and tensor comparisons in the condensed convention, but not inherited finite-stage constructible triangulation or the realization of this restricted cocone with its chosen comparisons.

lem-sfb-constructible-cocone-ambient-realization vs lem-weil-pbc-directed-triangulated-image: the latter assumes a triangulated cocone and arrow lifting and concludes its union of essential images is triangulated; the new lemma supplies the particular cocone's ambient triangulated realization without any image-closure conclusion.

lem-sfb-constructible-cocone-ambient-realization vs def-sfb-constructible-cocone: the latter defines an ordinary categorical cocone; it does not assert the ambient triangulated realization or identify the alternate condensed constructibility predicate.

lem-sfb-constructible-cocone-ambient-realization vs lem-weil-scalar-extension-exact-triangulated: the latter concerns rationalizations of completed integral coefficients in the global finite-field datum, not ordinary unbounded module-object derived categories on an arbitrary topologically Noetherian scheme, and does not cover the algebraic-closure cocone or its specified comparisons.

lem-sfb-constructible-cocone-ambient-realization vs lem-sf-exact-functor-derived-triangulated: the latter assumes an exact abelian functor and gives its termwise derived triangulation; it does not establish exactness for these coefficients, identify constructibility conventions, or construct the restricted cocone realization.

Whole-DAG searches included the actual cocone names, ambient realization, triangulated cocones and coefficient identifications; whole-blueprint searches included `constructible cocone`, `triangulated image`, `single complex`, `condensed constructible`, `scalar single`, `ambient cocone`, `coefficient comparison`, `triangulated scalar`, and `condensed module category`. The closest results are distinguished above. No new Stacks tag is introduced, so there is no same-tag pair to justify.

## Review by Q18

I read the chapter and unit records, the current main-20261015 item statement and its whole Modules/Complexes proof, and the unit's steps (3) and (4). The item's original statement is correct for the source's local finite-presentation convention and is unchanged. I also read the project TwoColimit definitions at lines 118–145 and 183–225: the restricted comparison is literally formed from the ambient derived scalar comparison by cancelling the full inclusion. For the new lemma I checked the coefficient-ring definitions, the point pullback definition, the condensed-module category definition, the bounded-constructible predicate, the finite-model API and flat coefficient calculus statements. The two pullbacks use the same structure morphism and left Kan extension followed by sheafification; both notions of local finite presentation are cokernels of maps of finite free modules on a pro-etale cover of each stratum. This is ordinary module-object constructibility, with no completeness, finite Tor dimension, finite-dimensional base, invertibility of ell, or standing finite-field datum added.

Step 1 uses the new ambient-realization statement, which explicitly supplies the categories, triangulated functors, termwise exact realization and the comparison maps; it does not take those from the proof of a definition. Its source is precisely the setup used in the Complexes paragraph, with the Modules paragraph's coefficient convention.

Step 2 uses the finite-subextension directed-set statement for nonemptiness, `def-sfb-dcons-qlbar` for fullness, and `lem-sfb-constructible-cocone-hom-surj` for arrow lifting between possibly different finite stages, conjugated by the specified transitivity maps. I read the whole statement of `lem-weil-pbc-directed-triangulated-image`: its index need only be a nonempty preorder; it requires the source pretriangulated structures, additive shifts, triangulated vertex functors and arrow lifting, all supplied here. It concludes precisely triangulation of P. Closure under isomorphisms is just composition of the witnessing isomorphisms. No full individual scalar functor is assumed.

Step 3 uses `lem-weil-pbc-condensed-finite-presentation-descent` for a constructible module model M_E and the tensor isomorphism, with exactly topological Noetherianity and the stratified local-cokernel predicate. The bounded-constructible definition and the finite-presentation definition with R^0=0 justify putting M_E in degree zero. `lem-sf-exact-functor-derived-triangulated` explicitly carries a single complex to the single of its exact image; the new lemma identifies this termwise functor with the actual ambient cocone functor. This proves the degree-zero case rather than assuming a derived object-descent statement.

Step 4 uses `lem-sfb-dc-module-devissage`, whose statement explicitly applies to an arbitrary commutative coefficient ring object, an isomorphism-closed triangulated P, and every constructible degree-zero module. It supplies exactly the finite truncation induction for bounded constructible objects. Step 5 uses the full vertex definition and the (Obj) clause of the filtered two-colimit definition: fullness includes both arrows of the ambient isomorphism, and their inverse equations are unchanged. This last step is elementary.

For the Mathlib audit I read every search result and the triangulated-subcategory infrastructure at `Mathlib/CategoryTheory/Triangulated/Subcategory.lean:725–748`. In particular `isTriangulated_lift` assumes the source structures and exact functor, and the essential-image instance assumes fullness of a single functor; neither supplies this geometric cocone package or replaces common-stage arrow descent. The condensed hits concern ordinary condensed modules, exactness of colimits, or solid/free objects. The Kan-extension cocones are unrelated. The grep for the project's coefficient/cocone identifiers had zero Mathlib hits. All five search records in the new node come from searches.jsonl, without invented queries or verdicts.

I checked B–E: the new lemma is self-contained, statement-only, and names definition dependencies; it contains no disguised proof or induction. It is not a clause of the item, a duplicate, or a one-line specialization of a single existing result. All main-proof uses are actual statements, with literal excerpts checked in citations.json. There are no new circular dependencies through the item, no unexplained source transports, and the off-unit generic inputs are declared in split_report.tool_uses. No proof step exceeds 2000 characters.

Small cases: empty X gives the zero module categories; zero and acyclic objects descend to the base field; a single shifted constructible module is handled by exact scalar extension and shifts; a complex with a nonzero connecting map uses Hom-surjectivity at a common later field, not a false splitting assertion. For E=F the comparisons reduce to the same unit/transitivity normalizations as the given cocone. Nothing uses ell odd, so ell=2 is included. These checks found no statement dispute.

## Unfinished work

No requested stage-1 work is left unfinished. The new helper intentionally remains unsplit for its own stage-1 worker; no Lean has been written and no compiler, Lake or build tool has been run. Server validation and delivery results are recorded by the required delivery tool.
