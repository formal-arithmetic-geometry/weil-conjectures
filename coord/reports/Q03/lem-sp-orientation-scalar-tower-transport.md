# Stage-1 report: lem-sp-orientation-scalar-tower-transport

## Files written

- `dag/nodes/sec-smooth-purity/lem-sp-orientation-scalar-tower-transport.json`: statement, split in six steps; not a Mathlib leaf. Statement unchanged. No new nodes and no new Mathlib leaves.
- `citations.json`: ten entries, one per cited node per proof step, copied verbatim from the current node statements.
- `searches.jsonl`: searches recorded by the prescribed msearch command; the item retains its inherited searches and appends the five searches actually run in this attempt.

## Attachments

None. Searches in `lean/WeilConjectures/` by the exact blueprint tag and by orientation/scalar/tower concepts found no declaration stating both clauses. `OrientationDatum.lean` packages assumed orientation base-change and coefficient compatibility; this is not the theorem here, and contains no full detection assertion for varying-coefficient sheaf towers. The existing Mathlib leaf `lem-weil-pbc-derived-single-fully-faithful` is cited without creating another node or attaching a partial match to the item.

## WANTED

None. The current blueprint and Stacks derived-category source used here are available.

## What needed repair

The imported item was statement-only, with no proof. Its last statement dependency, `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`, was a theorem not mentioned as a notion by the statement. Removed that dependency and used the existing definition `def-sp-constant-scalar-pullback-comparison` for its explicit natural comparison in the proof. The statement and all its hypotheses are unchanged. The scalar normalization equations and mixed square are hypotheses of this interface; no proof of their geometric construction is silently assumed or duplicated.

The blueprint ancestor's proof only briefly says that equality is tested levelwise after removing the shift. The split writes the missing reason: fully faithful singles in the abelian tower category, faithful singles in each finite coefficient category, and componentwise equality of ordinary tower maps. It does not claim faithfulness on arbitrary derived maps. The inherited expanded argument in `coord/reports/Q115/det-sp-purity-bc-factors.md`, Appendix old steps 3-4, was read and retained in the six steps, with the hypotheses already extracted by that delivery left as hypotheses.

## Blueprint and duplicate searches

Read `dag/chapters/sec-smooth-purity.json`, `dag/units/sk-prop-sp-purity-bc.json`, and the current files under `literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-sp-purity-bc/`, including `_section.md` and `sk-prop-sp-purity-bc-factors.proof.md`. This realizes the unit's orientation argument, not its tensor-counit argument. The chapter and unit route are unchanged; the item is not the unit's key statement and does not edit the unit record.

Ran `tools/blueprint_refs.py ancestor lem-sp-orientation-scalar-tower-transport` and whole-blueprint searches for `tower`, `orientation square`, and `fully faithful`. Searched all DAG statements and Lean source for single-functor full faithfulness, jointly injective evaluations, and shifted sheaf towers. Reused the existing full-faithfulness Mathlib leaf rather than creating the otherwise tempting duplicate. No whole-blueprint node states exactly this conditional scalar/tower interface, so `same_as` remains empty. There are no new-node duplicate pairs to list.

## Mathlib searches

The prescribed msearch command ran leanfinder twice with different phrasings, loogle with `DerivedCategory.singleFunctor, CategoryTheory.Functor.Faithful`, a whole-Mathlib orientation/dualizing/scalar/tower regular expression, and leansearch with the full conditional assertion. All five services responded successfully. Read every result. The first semantic search returned Mayer-Vietoris sheaf squares; leansearch returned generic commutative squares and related isomorphisms; these do not state the item. The second semantic search found singles, shifts, and exact-functor/single comparisons, which are ingredients rather than the complete theorem. Loogle found `DerivedCategory.instFaithfulSingleFunctor`, already part of the cited full-faithfulness leaf. The grep's sole hit was about orientation of a complex upper half plane, unrelated to these categories.

Read `lean/.lake/packages/mathlib/Mathlib/Algebra/Homology/DerivedCategory/FullyFaithful.lean`, lines 30-65, especially the faithful instance at line 37 and full instance at line 45. Their abelian-category and derived-category hypotheses apply to the tower category supplied by the cited abelian-towers node and the finite module categories. The item is not a one-line specialization of either instance: its scalar calculation and the assembly through component families are still required. No new node requires a separate search record.

## Review by Q03

I read both copies of delivery-errors B-E, the stage-1 brief and stage document, GOAL.md and SETUP's three levels. I checked the following arguments against the actual source and dependency statements, not the proof text of those dependencies.

Step 1 follows the current blueprint factors proof (1), with the finite scalar calculation expanded from the inherited old step 3. I read the entire statement of `def-sp-constant-scalar-pullback-comparison`: its lambda is the canonical natural isomorphism between scalar-then-pullback and pullback-then-scalar for arbitrary commutative rings. It explicitly imposes no flatness or Tor-amplitude hypothesis. This is exactly the naturality used in the third row of the displayed equality. All other equalities in that calculation are the two normalizations, the mixed square, and the R-orientation equation assumed in the item, together with functoriality. I checked the common source and target and used composition right to left. Thus this is an elementary cancellation calculation from stated hypotheses, not a hidden coefficient theorem. The quote in citations.json includes the comparison's actual definition and its naturality specification.

Step 2 only cancels the invertible pulled-back comparison and composes with the two inverse orientations. Its equations are typed: both sides are maps from the pulled-back A-dualizing object to the primed Tate line, and the final identity has source the primed Tate line and target the primed dualizing object. Functors preserve inverse equations, so no further exactness theorem is used.

Step 3 uses the statements of `det-sp-coefficient-towers-abelian` (Grothendieck abelian tower category, levelwise kernels and cokernels, exact level evaluation), `lem-weil-pbc-derived-single-fully-faithful` (a bijection on Hom sets for singles in any abelian category), and `def-weil-abstract-derived-category` (localization at quasi-isomorphisms and the shift formula). I read these three statements in full and the source for the substantive Hom theorem, Stacks Tag 06XS, `derived.tex`, lemma-negative-exts (2), as well as the matching Mathlib instances. Applied it in the tower category and in each finite module category, not in a category of normalized towers whose abelianness is unavailable. The paragraph spells out why exact evaluation preserves quasi-isomorphisms and evaluates singles and their shifts termwise. In particular exactness alone was not mistaken for faithfulness on all derived maps.

Step 4 uses exactly the family description of tower morphisms in `sk-def-sp-coefficient-towers`. I read its full statement and the current coefficient-towers blueprint section. The component maps already commute with transition maps because they come from actual tower maps in step 3. Equality of every component is equality of the families. Finite-level faithfulness comes from step 3; no lifting of arbitrary levelwise derived morphisms is claimed. This proves the more general clause by an explicit argument, without a new node restating that clause.

Step 5 uses `def-coefficient-twists-detailed` for finite Tate twists being sheaves before the common shift, `det-sp-tower-gamma` for the levelwise twist convention, `det-sp-tower-exceptional-bc` for its actual tower comparison and its stated exact levelwise pullback convention, `prop-weil-pbc-proetale-constant-exact` for finite constant-coefficient exact pullback, and `det-sp-coefficient-towers-abelian` for levelwise kernels and cokernels. I opened and read each full statement. The latter two imply exactness of tower pullback directly by computing those kernels/cokernels levelwise; the ordinary termwise functor therefore sends a single tower sheaf and its shift to the same type of object. The actual orientations and exceptional map are given as actual morphisms in the item's hypotheses, so this step does not reconstruct a derived morphism from its values. Evaluating their composite preserves composition and inverse isomorphisms and gives exactly the displayed h_n identity. Applying step 4 then gives h=1 and the requested equation. I checked that every cited node's quote is a literal substring of its statement; the twist and exact-pullback quotes include the exact part used.

Step 6 is an ideal equality: raising a unit-times-uniformizer expression to the nth power gives the exponent en, not n. The finite ring is therefore A_{E,en}. The detection proof has used neither derived-normalization isomorphisms nor e=1, so it works for ramified fields and non-normalized sheaf towers. No extra arithmetic theorem is hidden in the step.

I tested d=0 and arbitrary integer equal shifts, identity coefficient map R=A, non-flat Z/l^2 -> F_l, the zero ring (if included in the convention), zero towers, empty schemes, and a ramified extension with e=2. The scalar proof uses only functoriality and invertibility, so the non-flat example introduces no new requirement. The tower proof identifies sheaf maps rather than Ext maps, so no assertion about differing degrees or arbitrary complexes is smuggled into these edge cases. Non-normalized towers still have componentwise morphisms, hence need no repair. No statement dispute was found.

For B I checked that no duplicate, elementary fact, or clause of the item was made a new node: there are zero new nodes. For C I read and quoted every cited statement, identified the explicit generic tool uses in split_report, and checked transitive dependencies for cycles back to this item. For D the argument remains in this item; it is not delegated to newly named versions of its two clauses. For E I checked all hypotheses above, especially ordinary uncompleted coefficient categories, arbitrary base change, actual tower morphisms and the equal-shift restriction. Every proof step is shorter than 2000 characters, so there is no long-step lemma to extract. No SGA source is used.

The only off-unit statement tools newly used are the abelian/exact-evaluation theorem and finite constant exact inverse image; these are recorded in split_report.tool_uses. Fully faithful singles is already a Mathlib leaf. The remaining citations are definitions or on the unit's declared smooth-purity/tower route.

## Unfinished work

None in this item's one-level split. All mathematical facts needed are existing nodes. Server validation and the delivery invocation are performed after this report is written; their command output is the authoritative delivery result.
