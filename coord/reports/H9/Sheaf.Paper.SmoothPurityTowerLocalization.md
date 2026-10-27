## What changed

Replaced the proof hole of
`AlgebraicGeometry.ProEtale.SpTowerShriek.tower_localization_realization` by the
short-exact-complex construction and explicit transport of all three arrows.
The private helper `derived_sequence` applies the three exact endofunctors to a
complex representative, proves the termwise short complex short exact, applies
`DerivedCategory.triangleOfSES_distinguished`, and transports it using the exact
functor localization comparisons and naturality of `deriveMap`. The theorem then
conjugates by the composition and identity comparison isomorphisms, uses
`Open.counit_termwise`, and maps the resulting very same triangle by exact derived
evaluation. No independent finite connecting morphisms are chosen.

Added the proof import `Sheaf.Paper.SmoothPurityTowerOrdinaryLocalization` and the
Mathlib proof imports for short exact triangles and degreewise short exactness.
The new module isolates the remaining ordinary normalization step: right
exactness of the closed system pushforward and the short exact sequence of the
specified ordinary counit and unit. This is strictly below the original derived
triangle existence statement, with no derived object, representative, or
connecting map in its conclusion. Its docstring and node retain the complete
normalization transport argument from the original node's first step.

The original theorem signature, all definitions, and the public imports of the
item are unchanged. No source-library file is changed. The item node now records
the actual proof. The unit route is unchanged.

## Proved and sorry left

Original hole removed/reduced:
`AlgebraicGeometry.ProEtale.SpTowerShriek.tower_localization_realization`
(node `lem-sp-tower-localization-realization`). Its assembly proof has no sorry.

One hole added and remaining:
`AlgebraicGeometry.ProEtale.SpTowerShriek.tower_ordinary_localization`
in `Sheaf.Paper.SmoothPurityTowerOrdinaryLocalization`
(node `lem-sp-tower-ordinary-localization`).

This is a decomposition: one upper hole closed and one strictly smaller ordinary
hole added, net zero holes. It is not reported as a complete proof of the
geometric localization input. No other theorem, definition, or instance has a
new hole. The private derived transport helper is proved.

Validation: `lcompile.py --all` compiled both modules with exit code zero.
The ordinary module took 46.0 seconds and the item took 50.0 seconds, both below
the 60-second limit. The compiler also built the unpublished current interface
dependency in its private overlay. There are no errors or additional warnings.

## No longer needed

The parent proof no longer uses `lem-weil-pbc-exact-functor-derived-functor`
(`Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`) or
`lem-weil-pbc-dplus-injective-representative`. An arbitrary representative under
`DerivedCategory.Q` suffices: the relevant functors are exact, and their actual
`mapDerivedCategoryFactors` and `Localization.liftNatTrans_app` give all required
comparison squares. Neither an injective representative nor a separate
right-derived-functor identification is used. Their proof-dependency entries
are removed. No import of these dependencies was present to remove.

`lem-sp-semilinear-open-closed-complex-sequence` and
`lem-coef-semilinear-derived-sections` move from the parent's direct proof
requirements to the proof requirements of the remaining ordinary normalization
node; they are still needed. Their source modules and statements are retained.
The item retains its original public import. No module is withdrawn, and no
global pruning is claimed. The SES triangle and exact-derived-triangulated
Mathlib tools remain used. All new imports serve the proof or the new statement.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The original proof plan asked for a bounded-below
injective representative and a separate exact/right-derived comparison, although
its conclusion uses the termwise closed pushforward. Those steps are unnecessary.
The argument constructed here works for any unbounded representative, before
specializing to the bounded-below objects required by the unchanged interface.

The existing `semilinearOpenClosedComplexSequence` concerns actual inverse-image
ring systems and a slice presentation of the open part. It cannot be applied by
`exact` to the fixed constant-coefficient `Geometry` and `Open` interfaces.
The remaining ordinary lemma states precisely the required coefficient/site
transport and adjunction normalization, rather than leaving that work hidden
inside the derived proof. Empty open or closed parts and the zero system cause
no extra hypothesis: the ordinary sequence reduces respectively to the unit
isomorphism or counit isomorphism; the zero system gives the zero sequence.

## New nodes

`lem-sp-tower-ordinary-localization` is the ordinary part of the original first
proof step, in the same chapter and unit. It states finite-colimit preservation
of the closed pushforward and exactness of the actual ordinary counit-unit
sequence. It depends on the already stated semilinear open-closed sequence and
the normalized ordinary geometric calculus. It includes the source, full proof
in words, Mathlib searches, and its exact Lean declaration. No existing
statement or definition changes, so no change record or consumer adaptation is
required.

## Second reading by H9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
