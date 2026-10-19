## What changed

Proved both equivalences without changing their statements. A private geometric lemma handles
any property of morphisms stable under precomposition: choose a finite affine cover, apply the
existing global immersed refinement with actual factorization morphisms, and pull back the global
stratification for the converse. The coefficient-sized composition comparisons are constructed
from base-change composition by taking mates of the continuous pushforward adjunctions.

Added Sheaf.CategoryTheory.CoefficientFiniteLocalSystemsPullback, proving preservation of finitely
generated module local systems directly for continuous finite-limit-preserving functors of small
sites. Its proof constructs the localization comparison using the product-preservation square
and adjunction mates, then sends a terminal-object trivializing sieve to the target and restricts
its unchanged constant module values along the factorization arrows. The same result handles
both sites. For pro-etale values, the existing Noetherian-ring theorem and converse instance
identify finite generation with finite presentation.

No definitions, existing public signatures, or consumer modules change. All new helper definitions
are explicit isomorphisms built from already constructed adjunctions; no arbitrary witness is
chosen from an unproved existence theorem. Edge cases: empty schemes and empty covering sieves
remain allowed; R and the model modules can have infinite underlying sets; no separatedness is
assumed and refinement uses actual scheme factorizations.

## Proved and sorry left

Closed the two original holes:
- AlgebraicGeometry.Scheme.etale_noetherian_global_constructibility.
- AlgebraicGeometry.Scheme.proEtale_noetherian_global_constructibility.

Added zero holes. No sorry remains in either delivered Lean module. The new theorem
CategoryTheory.coefficient_finite_local_systems_pullback is proved, not split off as a hole.
Its node is lem-sfb-coefficient-finite-local-systems-pullback. This is a proof, not a decomposition.
On resumption on 2026-10-19, both delivered modules compiled cleanly against the current
project server build using lcompile.py --all (exit code 0). Both existing public theorem
signatures are textually identical to the current shared sources. Both Lean files have
zero sorry and satisfy the 100-character line limit. Earlier attempts encountered
infrastructure checkout timeouts before preflight; the required dry run was restarted
with the unmodified delivery tool in this session. The first completed dry run compiled
both modules and required a change record for the file-level universe/open commands;
that record is now included.

## No longer needed

Removed six direct proof imports:
- Sheaf.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage.
- Sheaf.CategoryTheory.SiteInverseImageTensor.
- Mathlib.AlgebraicGeometry.Sites.MorphismProperty.
- Mathlib.Topology.NoetherianSpace.
- Sheaf.CategoryTheory.ConstantLeftModuleInverseImage.
- Sheaf.SixFunctors.GeometricInverseImageConstantModule.

The proof no longer needs the declared dependencies det-pe-topos-functoriality-inverse-image,
lem-weil-pbc-left-exact-site-inverse-image-tensor, lem-pe-constant-left-module-inverse-image,
lem-sfb-geometric-inverse-image-constant-module, or lem-weil-pbc-etale-covering-base-change as
separate theorem applications: it works directly with fixed-scalar module sheaves and their
constructed sheaf pullback adjunctions, existing continuity, and the proved generic local-model
preservation lemma. Their separate intrinsic-module lifts and tensor structures are unnecessary.

It also no longer needs lem-sc-affine-noetherian-underlying-space,
lem-kun-finite-union-noetherian, lem-sfb-noetherian-space-compact-subsets, or
def-weil-constructible-subset as proof dependencies. Compactness is already supplied by
IsNoetherian X, and the recorded Stratification already has constructible strata, retained by
its existing pullback and global refinement. No node realizes a skipped unit step.

Withdrew the obsolete top-level tool_uses entries for
lem-weil-pbc-left-exact-site-inverse-image-tensor,
lem-weil-pbc-etale-covering-base-change, lem-weil-pbc-etale-base-change-finite-limits,
det-pe-topos-functoriality-inverse-image, and lem-pe-constant-left-module-inverse-image.
The finite-limit leaf remains a proof dependency, proved by the existing instance. The
stratification-pullback tool approval remains. Modules still reachable through other public
imports are not claimed to leave the whole target closure.

## Where the brief, the DAG or earlier work was wrong

The existing plan's general geometric inverse-image statements do not directly identify their
intrinsic-module lift with the fixed-scalar Kan-extension pullbacks appearing in this item's
statements. The direct module-valued adjunction argument proves exactly the needed assertion
without constructing those extra scalar and tensor comparisons. The earlier space argument was
redundant under the actual IsNoetherian hypothesis. No mathematical statement is disputed or
changed; the unit record has no realized step requiring the removed route.

## New nodes

lem-sfb-coefficient-finite-local-systems-pullback records the proved generic site lemma, in
lean/Sheaf/CategoryTheory/CoefficientFiniteLocalSystemsPullback.lean. It assumes finite limits
on the sites, continuity and finite-limit preservation of the site functor, and a commutative
coefficient ring. It has no scheme, stratification, Noetherian-ring or affine-local/global
hypotheses or conclusions, so it is strictly the local-model preservation part of the argument.
Change record: coord/changes/h4-noetherian-global-proof-commands.md documents the file-level
universe/open commands flagged by preflight and the proved generic helper. Existing public
signatures and definitions are unchanged; no consumer requires adaptation.

## Second reading by H4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
