## What changed

Proved `CategoryTheory.exact_localization_inverse_mate` in
`Sheaf.SixFunctors.ExactLocalizationInverseMate`, with its original signature and all universes.
Four proved private helpers compute the localized unit, normalize the Hom bijection,
compute the standard derived square on complexes, and transport the mate unit equation.
The final proof uses Hom-bijection injectivity and localization extensionality.
The node now records this unit-equation version of its original calculation.

Validation: the remote single-file compile passed without warnings. A temporary
`#print axioms CategoryTheory.exact_localization_inverse_mate` reported exactly
`propext`, `Classical.choice`, and `Quot.sound`; the probe was then removed.
No definition, public signature, public import, or consumer was changed.

## Proved and sorry left

Closed 1 of 1 holes: `CategoryTheory.exact_localization_inverse_mate`
(node `lem-sf-exact-localization-inverse-mate`).
Added 0 holes; split off 0 statements. No sorry remains in the delivered module.
All four private helpers are fully proved.

## No longer needed

None. All four declared proof dependencies remain used: exact derived-functor
factorizations, the localization universal property, the specified exact derived
adjunction, and the mates correspondence. No new proof imports were needed;
existing public imports are preserved. No node or module is withdrawn.
Within the calculation, the explicit localized counit formula and three-arrow inverse-mate
expansion are unnecessary: the unit equation and Hom-bijection injectivity suffice.

## Where the brief, the DAG or earlier work was wrong

No statement error. The existing
`Adjunction.mapDerivedCategoryAdjunction_mate` has additional tensor, flat-resolution,
and K-injective-resolution assumptions, so it cannot be applied to the categories here.
The proof instead adapts its factorization calculation directly to the cochain localization,
using the adjunction specified by this item. It follows the same unit route and the same
four stated dependencies, with no extra assumptions. The DAG's steps 4–6 now describe
this calculation accurately. Sources read: Stacks `sites-cohomology.tex`,
`remark-base-change`, and the units/counits compatibility sentence of
`fix-prop-coherence.proof.md` in the current blueprint.

## Second reading by M8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
