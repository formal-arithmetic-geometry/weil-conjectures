## What changed

Proved `CategoryTheory.Functor.rightDerivedBaseChange_zero_unit` with its signature unchanged.
The proof expands `rightDerivedBaseChange_app`, rewrites each classical augmentation using
`rightDerivedPlusSingleUnitHomology_comp_comparison`, cancels the mapped source comparison
against its inverse, and composes `rightDerivedBaseChange_single_unit_homology` with the target
comparison. This is a reduction to two separate parts of the original argument.

Added two modules, each containing one outstanding theorem:
`Sheaf.CategoryTheory.RightDerivedSingleUnitHomologyComparison` and
`Sheaf.CategoryTheory.RightDerivedBaseChangeSingleUnitHomology`.
The first also defines the actual derived single-complex unit and its homology augmentation
using existing comparison isomorphisms and the derived unit; neither definition contains sorry.
Updated the original node's proof route and dependencies to match the Lean proof.

## Proved and sorry left

The original one sorry is replaced by a complete proof of
`CategoryTheory.Functor.rightDerivedBaseChange_zero_unit`.

Two sorries are split off, each as the whole proof of one public theorem in its own module:

- `CategoryTheory.Functor.rightDerivedPlusSingleUnitHomology_comp_comparison`
  (node `lem-sbc-right-derived-single-unit-homology-comparison`): identifies the classical
  augmentation with the actual derived-unit homology under the existing comparison.
- `CategoryTheory.Functor.rightDerivedBaseChange_single_unit_homology`
  (node `lem-sbc-right-derived-base-change-single-unit-homology`): the derived-unit equation
  on homology, before classical right-derived comparisons are introduced.

Both statements apply to arbitrary additive G and G', without left exactness assumptions.
The first has no base-change transformation or exact functors. The second has no classical
right-derived augmentation or single/right-derived comparison. Neither restates the target.
Edge cases: for the zero transformation both sides of the second equation are zero, by
additivity of homology and the derived functors. For the identity functor the first equation
is the identification of the unit with the resolution augmentation; on injective objects its
unit and comparisons are isomorphisms. No preservation of injectives by beta is assumed or
needed: compatibility with units holds even when base change is not an isomorphism.

## No longer needed

Removed the proof import `WeilConjectures.SixFunctors.BaseChange.Derived` and the original
proof dependency `def-weil-pbc-derived-exchange`: the generic defining equation in
`PlusBaseChange` suffices; this argument uses no geometric exchange construction.

Removed the direct proof import
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle` from the item.
Its comparisons remain necessary and are provided by the existing public import and the new
comparison module, so its node `lem-sp-derived-functor-single-identification` is not pruned.
The other original proof dependencies remain needed by the new comparison/homology steps.
These pruning claims concern this proof route, not reachability from other targets.

Discarded the earlier sandbox helper `rightDerivedBaseChange_zero_unit_homology` and its
unlanded node `lem-sbc-right-derived-base-change-zero-unit-homology`; neither is used.

## Where the brief, the DAG or earlier work was wrong

The previous delivery's expanded equation was definitionally the original assertion, so its
rewrite followed by one application did not provide a strict reduction. Replaced it by the
independent augmentation comparison and the homology unit equation, combined by functoriality,
isomorphism cancellation and composition in the item's proof.

The previous report incorrectly supplied a second-reading section. Removed it: the actual
second reader must supply that section. The previous node also recorded an abbreviated Lean
signature and only one search kind. The new nodes record verbatim parsed signatures and real
LeanSearch, LeanFinder, Loogle and grep searches. LeanSearch returned an internal server error;
no absence claim relies on that failure. The current dry-run audit recognizes the original
sorry, unlike the failure described in the dispatch brief.

The existing node's geometric exchange dependency does not express the generic unit equation
used here; the actual source is `rightDerivedFunctorPlusBaseChange_fac` in `PlusBaseChange`.
The unit record `sk-prop-deg0` has empty realized statement/step lists; this delivery changes
only the category-theoretic compatibility lemma and preserves that unit's geometric route.

## New nodes

`lem-sbc-right-derived-single-unit-homology-comparison`, in
`dag/nodes/sec-smooth-base-change/`, records the augmentation identification in
`RightDerivedSingleUnitHomologyComparison.lean`, including its two fully defined canonical
unit maps. Its proof follows naturality along the chosen injective resolution and the existing
single-complex homology comparison, then identifies degree-zero cycles with the classical
augmentation.

`lem-sbc-right-derived-base-change-single-unit-homology`, in the same chapter, records the
unit equation in `RightDerivedBaseChangeSingleUnitHomology.lean`. Its proof evaluates the
existing defining derived-base-change equation on a homotopy single complex, transports by
the canonical single isomorphisms and applies homology with the exact-functor comparisons.
No existing statement or definition was changed, so no change record is needed.


## Second reading by P1

1. Compared the delivered item with the repository using diff. The theorem signature and
   original docstring are byte for byte unchanged. The only original-module edits are the
   proof, its private import, and a declaration-local unused-section-variable linter setting.
   Also compiled scratch copies with `#check @rightDerivedBaseChange_zero_unit`: the original
   and delivered elaborated signatures agree, including PreservesFiniteLimits G and G'.
   The two additional modules introduce declarations without altering any existing definition.
   Verdict: the assertion proved has not changed; no change record is required.

2. Compiled all three modules in import order through lcompile.py without errors or warnings.
   Read every declaration body: the item has no sorry; the only two sorries are exactly the
   whole proofs of the named, reported split theorems. No forbidden axiom, unsafe, opaque,
   implemented_by or extern occurs, and both unit definitions contain actual composites.
   Scratch #print axioms checks show only propext, Classical.choice and Quot.sound for the
   two definitions. The two split theorems and the item additionally use sorryAx, as expected
   from these explicitly open dependencies. Verdict: a valid conditional reduction, not yet
   an axiom-free proof of the mathematical result.

3. Read both new statements, their definitions and nodes, PlusSingle.lean, the existing
   base-change defining equation in PlusBaseChange.lean, and the single/homology compatibility
   in ExactFunctor.lean. The augmentation comparison is independent of beta, gamma and e;
   the homology equation is independent of the classical right-derived comparison. Thus
   neither merely restates the item. All categories are abelian with derived categories;
   only the two source categories require enough injectives. G and G' need only additivity
   in the split lemmas; exactness of beta and gamma is retained in the homology equation.
   The transported unit uses the inverse of the canonical Qh-single comparison on the source
   and the inverse of the single-to-Qh comparison inside R+G on the target, with correct types.
   Checked zero objects and zero transformations: all augmentation composites are zero;
   for the identity square the homology equation reduces to the same unit, using the exact
   single/homology comparison. For an injective Y the unit and resolution comparisons cancel
   to the classical augmentation. These cases require no preservation of injectives by beta.
   Independent LeanFinder search for localization/unit compatibility returned existing
   comparison isomorphisms, not either new equation; Loogle with "toRightDerivedZero",
   "homology" returned no hits. Local rg of Mathlib, WeilConjectures and Sheaf found the
   existing resolution augmentation naturality and defining base-change equation, not a
   duplicate. Both docstrings give the resolution or defining-equation argument step by step.
   Verdict: the two statements are distinct parts of the proof with valid hypotheses and
   takeover-ready arguments. Neither closes in a few minutes from an existing single lemma.

4. Checked the proof from the item downward: it expands rightDerivedBaseChange_app, substitutes
   both augmentation comparisons, maps composition through gamma, cancels the source comparison
   with its inverse, then composes the homology equation with the target comparison. No shorter
   existing base-change augmentation theorem was found. All imports supply declarations used
   by signatures or bodies; removing the explicit DerivedCategory.Plus import from the comparison
   module fails with unknown singleFunctorCompHomologyFunctorIso, so it is necessary. The new
   theorem modules' public imports occur in their statements or public definitions; the item's
   new import is proof-only. Of the old proof_deps, def-weil-pbc-derived-exchange is pruned;
   lem-sp-derived-functor-single-identification, lem-sp-exact-functor-preserves-homology and
   lem-weil-pbc-left-exact-injective-resolution-degree-zero remain transitively necessary through
   the two split nodes. The No longer needed section accounts for both removed direct imports.
   Read dag/units/sk-prop-deg0.json: its realized lists are empty and its geometric normal-form,
   sections and gluing route is untouched by this categorical reduction. Verdict: route preserved.

5. Matched the original node's two proof steps and proof_deps against the rewrite/cancellation
   and final composition in Lean. Matched the new nodes' statements with the Lean hypotheses
   and morphisms, and their proof_deps with the cited comparison and exact-homology steps.
   Checked their source, created, blueprint, chapter/unit, searches and verbatim Lean signature
   records; the comparison node lists both additional definitions in lean.declarations.
   Verdict: nodes agree with the delivered reduction.

Second-reading repairs: added source and blueprint references to the two unit-definition
   docstrings; replaced the new homology lemma's imprecise Tag 05TD attribution with the actual
   rightDerivedFunctorPlusBaseChange_fac and exact single/homology compatibility source,
   also naming that compatibility in its proof docstring and node; added independent searches
   to the new nodes. Tag 05TD concerns the degree-zero augmentation and left exactness, not the
   generic base-change equation (https://stacks.math.columbia.edu/tag/05TD).
   No proof or statement needed repair. Recompiled the three modules after these edits.
