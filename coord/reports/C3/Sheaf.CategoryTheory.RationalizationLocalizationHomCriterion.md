## What changed

Proved `CategoryTheory.Rationalization.localization_hom_criterion` in
`Sheaf.CategoryTheory.RationalizationLocalizationHomCriterion`, preserving its statement
and public imports. Adapted the existing proved private
`rationalization_localization_of_hom` argument from
`Sheaf.UpstreamExtra.WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization`:
the proof now returns the constructed Full, Faithful and EssSurj instances as well as
IsLocalization. It imports neither that large module nor its coefficient-theory dependencies.

The proof follows the nine-step DAG plan. It descends linearity along the localization,
uses the comparison isomorphism to define a linear Hom map, proves bijectivity by scalar
fractions, transports it to arbitrary quotient objects, proves essential surjectivity,
and transfers localization through `G.asEquivalence`.
`Rationalization.map_eq_map_iff` packages the third-denominator cancellation in steps 5–6.
No node route, statement, definition, visibility or consumer changes are needed.

Validation: the final module compiled cleanly through `lcompile.py` in 2.3 seconds.
The only proof dependency outside the existing public imports is the already proved
`WeilConjectures.CategoryTheory.DerivedCategory.RationalizationMap`.
Searches with LeanFinder, Loogle and ripgrep confirmed the existing scalar-fraction
and localization APIs, and the private assembled argument above.

## Proved and sorry left

Closed 1 of 1 holes: `CategoryTheory.Rationalization.localization_hom_criterion`
(node `lem-sfb-rationalization-localization-hom-criterion`).
No sorry remains in the item. Added 0 holes; split off 0 theorems.

## No longer needed

Removed redundant proof imports `Mathlib.CategoryTheory.Equivalence` and
`Mathlib.CategoryTheory.Localization.Linear`; the public rationalization dependency
already exposes the required API. No DAG dependencies, statements or library modules
are pruned: the proof implements the existing plan and uses its scalar-fraction lemma.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface errors found. The stage-2 review's suggestion to reuse the
existing private criterion was sufficient; its assembled proof applies unchanged to the
independent universes of the present theorem after returning the three additional
conjuncts. No new nodes or change records are required.

## Second reading by C3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
