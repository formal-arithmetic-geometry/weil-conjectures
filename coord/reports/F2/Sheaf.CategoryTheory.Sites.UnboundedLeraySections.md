## What changed

Replaced the body of `CategoryTheory.UnboundedSectionsLocalization.unboundedLeraySections`
by a construction through the universal property of total right derived functors. The
original signature, definitions, public imports, independent derived-category universes,
and normalization equation are unchanged.

The proof uses one new, strictly smaller mathematical step:
`CategoryTheory.UnboundedSectionsLocalization.leraySectionResolution_quasiIso`, in
`Sheaf.CategoryTheory.Sites.LeraySectionResolutionQuasiIso`. This says only that evaluating
a K-injective resolution of the direct image of a K-injective complex yields a
quasi-isomorphism. It gives no natural isomorphism, normalization, uniqueness, or
restriction square.

Private proved helpers express the composite-unit formula, the generic K-injective
derivability criterion, extensionality on K-injective representatives, naturality of
composite derived units, and a general square-compatibility criterion for normalized
derived comparisons. Keeping
the criterion abstract avoids elaborating it repeatedly through concrete site definitions.

The main module uses this step and naturality of the evaluation unit to prove that
unit invertible on the direct image of each K-injective. The K-injective derivability
criterion then makes the composite functor a right derived functor; uniqueness constructs
the comparison. A generic proved helper constructs the unique comparison from the two derived units,
so site-specific elaboration does not unfold its construction. The main proof supplies
its normalization, derives the restriction
square from the two derived-natural-transformation unit equations, and proves uniqueness
using essential surjectivity of K-injectives in the derived category.

The new lemma records precisely the localization and punctual-topos argument of Stacks
Tags 0D6H, 0D6G and 0D6E, with a complete proof in words and matching DAG node. Its
edge cases include the zero complex and identity resolution (evaluation gives an
identity quasi-isomorphism), the identity site map, and arbitrary nonflat ring maps.
No argument asserts that the module direct image preserves K-injectivity.

## Proved and sorry left

Original holes: 1, in
`CategoryTheory.UnboundedSectionsLocalization.unboundedLeraySections`
(node `lem-sfb-ringed-site-unbounded-leray-sections`). Its proof body is now complete,
conditional on the new sectionwise resolution lemma. This is a decomposition, not
a net closed proof: 1 original hole eliminated, 1 lower hole added, net 0.

The only remaining delivered `sorry` is
`CategoryTheory.UnboundedSectionsLocalization.leraySectionResolution_quasiIso`
(node `lem-sfb-leray-section-resolution-quasi-iso`), whose entire body is `by sorry`.
There are no holes in definitions or private helpers. No existing signature changed.
Server compilation passed in 56.0 seconds with a theorem-local 400000-heartbeat budget;
the fixed 60-second wall-time limit is unchanged. The required explanatory comment
addresses the heartbeat-setting linter warning. Delivery performs the final compile and checks.

## No longer needed

The main module no longer directly imports:

- `Sheaf.Paper.LocalizeRingedSiteMorphismGeneral`;
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`;
- `WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalized`;
- `Sheaf.CategoryTheory.FiniteTypeRestrictionExact`;
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`;
- `Mathlib.CategoryTheory.Sites.LeftExact`;
- `Sheaf.ProperBaseChange.SingletonSiteModuleComparison`;
- `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`.

The localization, restriction, punctual-topos and composition dependencies remain
needed by the new resolution lemma, and its module imports the corresponding interfaces.
They are not globally pruned. K-injective resolutions and their hom comparison remain
needed by the main proof through the existing section-functor imports. The independent
site-universe resolution module is unnecessary here: all sites in the statement are
small in the common module universe and their Grothendieck instances already exist.
No module or mathematical node is withdrawn. Thus the pruned-module count is zero.
The parent node's obsolete direct tool-use entries for localization, restriction, singleton comparison and composition are removed;
these uses now belong to the new node, where they are generic tools for the same route.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The proof plan correctly avoids claiming that module
pushforward preserves K-injectives without flatness. The existing universal derived-functor
API supplies the naturality and uniqueness part without explicitly choosing representatives
for every derived morphism. This changes only the formal implementation of steps 5–6,
keeping the localization and punctual-topos argument of steps 2–4.

Searches with LeanSearch, LeanFinder, Loogle and Mathlib grep found the generic universal
property and K-injective machinery, but no theorem giving the required sectionwise
quasi-isomorphism for a general ringed-site morphism. The new node records the three
required searches. A whole-blueprint search for “Leray unbounded” found no imported
blueprint node with this statement. The inherited blueprint ancestry is already null;
the new node preserves that ancestry and records the exact parent proof steps served.

## New nodes

`lem-sfb-leray-section-resolution-quasi-iso` isolates the sectionwise quasi-isomorphism
in steps 2–4 of the original plan. It is in
`dag/nodes/sec-six-functors-basics/lem-sfb-leray-section-resolution-quasi-iso.json`, with
its sole theorem in `lean/Sheaf/CategoryTheory/Sites/LeraySectionResolutionQuasiIso.lean`.
The statement is strictly narrower than the original comparison theorem and has no
canonical-family or naturality assertion. Its dependencies are the existing localization,
exact restriction, K-injective restriction, constant-sheaf adjunction, exact sheafification,
singleton module comparison and ringed-topos composition nodes. The change record
`coord/changes/leray-derived-functor-local-transparency.md` documents the local irreducibility attribute and its downstream users. Existing
statements, definitions and public imports are unchanged.

## Second reading by F2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
