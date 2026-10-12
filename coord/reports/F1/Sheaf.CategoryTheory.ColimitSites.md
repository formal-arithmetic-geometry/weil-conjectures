## What changed

Reduced `CategoryTheory.exists_colimit_site_reduced` to three strictly smaller
arguments in new modules:
`Sheaf.CategoryTheory.ColimitSiteCoveringConstruction`,
`Sheaf.CategoryTheory.ColimitSiteSetInverseImage`, and
`Sheaf.CategoryTheory.ColimitSiteAbelianInverseImage`.
The existing theorem signatures, visibility and public imports are unchanged
relative to the landed finite-index correction in `finite-precoverage-closure.md`.
The wrapper `CategoryTheory.exists_colimit_site` is unchanged.

The proof obtains the compatible category and stage functors from
`CategoryTheory.exists_filteredColimit_category`, bundles a strict Cat cocone,
and transports the object and arrow colimit witnesses along explicit cocone
isomorphisms. It uses that theorem's finite-list and finite-functor lifting clauses.
It constructs the image precoverage Q directly as a set of presieves; its defining
criterion is proved by reflexivity. The covering lemma supplies the finite-family
site properties, preserved covering pullbacks, and canonical continuity. Canonical
cover preservation is proved with explicit stage witnesses. The two inverse-image
lemmas supply the set and abelian section data. Finite-colimit preservation is
proved by `sheafAdjunctionContinuous` and
`Adjunction.leftAdjoint_preservesColimits`; the final existential/conjunction
assembly is complete Lean.

All four delivered modules have the module-system header and 100-character lines.
The three new imports and Mathlib's adjunction import are proof-only in the item.
The existing redundant hcat argument is consumed but its arbitrary category
witness is not used as data: the compatible category is obtained from the existing
category-colimit universal-property theorem. A declaration-local unused-variable
linter option accommodates the unchanged `∃ s, True` binder; it changes no typing
or kernel check. There are no new definitions or data chosen from arbitrary
unproved existence. No forced adaptations or interface-change records are needed.

## Proved and sorry left

Original hole closed by decomposition:
`CategoryTheory.exists_colimit_site_reduced`
(node `lem-weil-pbc-colimit-of-sites-reduced`).
The item now has no textual sorry. Its wrapper and `filtered_index_nonempty`
retain their existing proofs.

Exactly three new holes remain, each a public theorem with a whole-proof sorry,
source and complete proof in words, in its own module:

- `CategoryTheory.colimit_site_covering_construction`
  (`lem-weil-pbc-colimit-site-covering-construction`): the finite indexed site axioms,
  preservation of covering pullbacks, and continuity for a fixed V and explicitly
  specified image precoverage Q. It does not construct the category, prove any
  finite lifting clause, or assert inverse-image exactness/section formulas.
- `CategoryTheory.colimit_site_set_inverse_image`
  (`lem-weil-pbc-colimit-site-set-inverse-image`): finite-limit preservation and the
  unit-compatible section colimit formula for set sheaves on a fixed continuous
  site cocone. It assumes the site data, constructs no category/precoverage, and
  does not assert the abelian formula or finite-colimit preservation. Transition
  inverse-image finite-colimit preservation is not needed in its signature.
- `CategoryTheory.colimit_site_abelian_inverse_image`
  (`lem-weil-pbc-colimit-site-abelian-inverse-image`): only the additive section
  colimit formula for a fixed continuous site cocone. It assumes the site data and
  requires no finite-limit/finite-colimit preservation of transition inverse images.

Closed 1 of 1 original holes; added 3 holes; split off 3. This is a decomposition,
not an axiom-free completion or a net reduction in holes (local net is -2).
The parent assembly was compiled repeatedly before the landed finite-index change;
final verification is against the corrected finite-index interfaces.

Edge cases checked against each new statement: J is nonempty by filteredness;
all-empty stage categories give an empty colimit and vacuous objectwise claims;
an individually empty source stage has no section U to evaluate. For set exactness,
its transition finite-limit hypothesis forces the inverse image of its unique
sheaf to be terminal at later stages, so the general-object formula handles this
case. Empty coverings use the empty equalizer (terminal set or zero group).
Repeated finite indices are allowed. Infinite repeated-index composition and
arbitrarily many chosen isomorphic pullbacks are deliberately not asserted.

## No longer needed

No existing imports, nodes or modules are pruned. The category construction,
refinement, filtered finite-limit commutation, adjunction uniqueness, sheaf limits,
and finite-colimit adjunction nodes of the former plan all remain needed, either
by the real parent assembly or the three residual arguments. No unit statement
or realized unit step in `dag/units/sk-thm-p1.json` is bypassed.

Unused imports were removed while minimizing the new modules: the covering module
needs no group-limit/colimit/filtered-colimit or under-category module; the set
module needs no group modules. The abelian module retains group filtered colimits
because removing it makes its statement fail `HasWeakSheafify` synthesis. These
are new-module dependency choices, not a claim of pruned existing work.

## Where the brief, the DAG or earlier work was wrong

The repository initially supplied the unrestricted
`Precoverage.IsStableUnderComposition` and `IsStableUnderBaseChange` formulation.
During work I independently found the infinite-repeated-index obstruction:
finite codiscrete stages with all presieves covering have a countably infinite
codiscrete colimit, whose image covers are exactly finite presieves; infinitely
many repetitions of one identity can be refined by arrows from distinct objects,
giving an infinite composite presieve. This invalidates the unrestricted conclusion.
The F3 correction `coord/changes/finite-precoverage-closure.md` landed during this
session and fixes exactly that issue. The delivered proof and new nodes use its
finite-index classes and preserve the corrected signatures; no stale disputed
statement or false intermediate theorem is delivered.

Mathlib's `isContinuous_toGrothendieck_of_pullbacksPreservedBy` requires the
unrestricted base-change class, so the earlier direct invocation cannot be used
with the corrected classes. Canonical continuity is retained in the smaller
covering-construction argument, with a proof through finite covering equalizers
and the generated topology. The dependent set and abelian formulas explicitly
assume canonical continuity.

LeanSearch returned Internal Server Error on all three attempted semantic queries;
these are recorded as unavailable. LeanFinder, fully qualified Loogle and Mathlib
source grep ran and found only supporting single-site results, not the full
filtered-colimit-site construction. The Stacks source was read from the available
local copy `/home/ubuntu/c1-stacks-review/sites.tex`, at `lemma-colimit-sites` and
`lemma-compute-pullback-to-limit`; the repository's literature directory lacks
that regenerated file. This is the same source named by the existing nodes.

## New nodes

`lem-weil-pbc-colimit-site-covering-construction`, module
`Sheaf.CategoryTheory.ColimitSiteCoveringConstruction`, records the finite-family
covering construction and canonical continuity (09YL and 0A35's opening paragraph).
Q is an input with its exact image criterion, determined by a real construction
in the parent proof. It is strictly the site part of the argument.

`lem-weil-pbc-colimit-site-set-inverse-image`, module
`Sheaf.CategoryTheory.ColimitSiteSetInverseImage`, records the presentation sheaf,
unit-compatible section colimit and objectwise finite-limit argument (0A35).
Its natural-language proof specifies transitions, common refinements, restriction
independence, sheaf equalizers, the inverse adjunction bijections and unit equations.

`lem-weil-pbc-colimit-site-abelian-inverse-image`, module
`Sheaf.CategoryTheory.ColimitSiteAbelianInverseImage`, records the same presentation
and adjunction construction in abelian groups, with only the additive section
formula as conclusion (0A35 and the abelian colimit facts of 03CO).

The existing reduced node's proof, proof_deps and proof_origin now follow the
actual assembly. No node statement or Lean statement record was changed, and
there are no interface-change records in this delivery.

## Second reading by F1

1. I compared the delivered item module with the repository version. Existing declaration signatures and visibility are unchanged; the reduced theorem proof only fills the prior sorry, while the three added modules introduce the split statements documented above.
2. I compiled all four modules with `lcompile.py --all`; compilation succeeds. The only remaining sorries are the three named split-off public theorems, each with a source, proof description, and matching DAG node. No forbidden declarations or sorry in definitions occur.
3. The three split statements are strictly smaller than the parent construction: covering properties, set inverse-image formulas, and abelian formulas are separated. Their hypotheses and conclusions match the Lean declarations and edge cases described in the report; no existing library duplicate was found by the recorded searches.
4. The reduced proof follows the filtered category, cocone, covering construction, and inverse-image steps. Imports used only for proof are plain imports in the item; the added modules expose the types required by their public theorem statements. No further pruning was found.
5. The parent and split nodes' proof, dependencies, and origins agree with the Lean proof and the unit route remains realized in `sk-thm-p1.json`.

I changed only this report section during second reading; no source or node repair was necessary.

Additional second-reader verification: scratch copies with `#print axioms` show
only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx` for the reduced
and wrapper theorems and the three residual statements; `filtered_index_nonempty`
uses no axioms. Independent LeanFinder and Mathlib grep searches for filtered
site inverse-image sections found supporting sheaf/equalizer results, but no
replacement for a residual statement. I also inspected the unit's `realized`
record and the old dependency list: old dependencies remain in the residual
arguments, so none becomes globally unnecessary.
