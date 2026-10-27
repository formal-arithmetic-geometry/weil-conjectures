## What changed

Proved `completedShriekChoiceIndependence` in
`Sheaf.SixFunctors.CompletedShriekCompositionLaws`. The dense common refinement
makes the two composite refinement arrows equal. The existing reverse-refinement
composition clause then identifies their images, and cancellation of invertible
maps identifies the comparison isomorphisms. Added two proved private helpers:
`completedShriekRefinement_isIso` and `completedShriekCommonSpan`.

Added the private proof import `Sheaf.SixFunctors.SystemProperOpenSupport`, using
its existing proved `systemProperOpenGammaIsIso`. This is essential because the
new common refinement has no assumed `completedShriekDomain`; the supported-counit
argument gives invertibility on all inputs. The dependency is an existing proved
tool from the projection-formula unit, rather than a replacement of the present
unit's composition/refinement route. Updated proof step 2 and proof dependencies
of `lem-sf-completed-shriek-composition-laws` accordingly. No existing public
signature, definition body, attribute or public import changed.

## Proved and sorry left

Closed one of the original eight holes:
`WeilConjectures.IntegralSystemRealization.completedShriekChoiceIndependence`.
No new holes were added and no statements were split off. This proof uses the
composition clause of the already stated `completedShriekRefinementLaws`, whose
proof remains an independent obligation of this same module.

Seven original holes remain, all attached to
`lem-sf-completed-shriek-composition-laws`, in namespace
`WeilConjectures.IntegralSystemRealization`:

- `completedShriekRefinementLaws`
- `completedShriekTowerRefinement`
- `completedShriekAssociativity`
- `completedShriekUnits`
- `completedShriekFiniteEvaluation`
- `completedShriekIntegralComposition`
- `completedShriekSpecifiedIntegral`

The other proofs, including the previous integral-bounds proof, are preserved.

## No longer needed

No existing imports, modules or nodes are pruned: the remaining obligations still
need their original route. The new choice-independence proof does not need a good
domain for the extra dense refinement, a separate equalizer construction, or a
refining composition tower. The experimental new invertibility statement was
removed from the sandbox before delivery in favor of the existing proved theorem;
there is no new module or node in the packet. An experimental private import of
`WeilConjectures.Compactification.Cofiltered` was also removed; the needed common
refinement and uniqueness declarations are already publicly available.

## Where the brief, the DAG or earlier work was wrong

The original choice-independence sketch did not explain how to obtain the domain
bounds needed to invoke its stated refinement-invertibility clause on the extra
common refinement. The existing arbitrary-input proper/open support theorem avoids
that missing hypothesis. Scheme-theoretic density also equalizes both pairs of
arrows at once, so no further equalization or compatible tower is necessary for
this particular declaration. Empty schemes and zero inputs are included by the
same dense-refinement and categorical cancellation argument; no nonemptiness or
nonzero hypothesis is added.

## Second reading by R2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
