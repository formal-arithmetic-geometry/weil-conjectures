## What changed

Implemented `WeilConjectures.NativeDualRealization.dual_realization_comparison`
using the fixed `Presentation`, actual coefficient Hom, exceptional comparison,
and evaluation-transpose realization comparison. All public signatures and definitions
of the item are retained. New proof imports supply the ordinary presentation transport
and permitted pairs for the specified structural exceptional image.

The natural comparison is the explicit three-arrow composite. Private helpers prove
its naturality, the native/presentation evaluation identity, and the evaluation
naturality calculation. Bounded constructibility uses the realization image criterion.
The complete item and both split modules compiled successfully via `lcompile.py --all`;
a final pass checks the removal of an unnecessary alias-module import.

## Proved and sorry left

Closed the original hole in
`WeilConjectures.NativeDualRealization.dual_realization_comparison`.
Two strictly simpler statements are split off:

- `WeilConjectures.NativeDualPresentation.ordinary_closed_presentation`
  (`lem-sf-ordinary-closed-presentation`): closure/section transport of the given ordinary
  tensor and Hom, with evaluation-transpose normalization; no dualizing object is involved.
- `WeilConjectures.NativeDualPresentation.structural_omega_hom_pairs`
  (`lem-sf-structural-omega-hom-pairs`): only the permitted-pair assertion for internal
  Hom into the specified structural exceptional image; no comparison or evaluation
  statement is included.

This is a decomposition: one original hole closed and two added. No sorry remains
in the item module. No definition contains a sorry.

## No longer needed

Removed the direct proof import `Sheaf.SixFunctors.CoefQbarVerdier` from the item;
its use is localized to `StructuralOmegaHomPairs`, where its internal-Hom conclusion
must be compared to the specified exceptional system. The new lemmas use the underlying closure/section functor and realized closed structure
directly, so their unnecessary `NativeSectionClosedForgetful` alias import is also removed.
No mathematical dependency is globally pruned. The unit route and the four original comparison dependencies
are retained, directly or through the new lemmas.

## Where the brief, the DAG or earlier work was wrong

The existing interfaces do not directly supply the presentation for an arbitrary
given compatible closed model N: NativeSectionClosed supplies its own native model.
The new presentation lemma isolates precisely this transport for the given N.
CoefQbarVerdier supplies a dualizing object for its own exceptional system; the item
uses the actual `S.ring.operation c .closed` at `geometricPointOmega`. The permitted
pair lemma retains that system and unit and records the required adjoint/unit comparison.
The original DAG's conceptual argument remains unchanged.

## New nodes

`lem-sf-ordinary-closed-presentation`, module
`Sheaf.WeilSheaf.OrdinaryClosedPresentation`, is the ordinary presentation portion
of step 3, with no native dualizing or constructible-comparison conclusion.

`lem-sf-structural-omega-hom-pairs`, module
`Sheaf.WeilSheaf.StructuralOmegaHomPairs`, is the constructibility portion of step 1,
for the specified structural exceptional image. Edge cases checked in both statements:
empty scheme, zero source and identity transports. Neither imposes global site-perfectness
on constructible objects.

## Second reading by F2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
