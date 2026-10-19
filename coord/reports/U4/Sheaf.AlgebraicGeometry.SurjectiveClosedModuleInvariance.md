## What changed

Completed `sfbProEtale_surjectiveClosed_module_invariance` without changing its
statement, either finite-local-model definition, or the already proved etale theorem.
Private proved helpers compare the intrinsic and fixed-module encodings, translate
localized models to scheme-site pullbacks, and preserve/reflect arbitrary model
predicates. The proof uses existing closed-immersion counit invertibility and
jointly-surjective zero detection, then transports the equivalence through constant
scalar restriction. Reflection follows the existing cover-refinement theorem.

Added proof imports of ProEtaleConstantModuleConstructibility (including its private
scalar-comparison API), ProEtaleConstantModulePullbackEncoding (including its private
direct-image comparison), the fixed-module ClosedImmersion module, and
ConstantSheafEquivalence. Updated the node proof, dependencies and proof origin.
All new helpers are proved; no new public statements or definitions are introduced.
The finite models and splitting maps are literally retained. Empty covers, empty
schemes, the zero ring, the zero module and rank zero require no extra hypotheses.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.sfbProEtale_surjectiveClosed_module_invariance`
(node `lem-sfb-surjective-closed-module-invariance`).
The etale theorem was already proved by K7 and remains proved.
Holes closed: 1. Holes added: 0. Holes remaining in the item: 0.
No split-off statements. Existing imported results are used as stage 3 permits.
Validation: the complete file compiled through lcompile.py; delivery preflight is
run on the final packet as well.

## No longer needed

Removed these proof imports and their direct planned dependencies:

- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap`
  (`prop-weil-pbc-proetale-constant-ring-map`): the ordinary operations already supply
  the canonical coefficient isomorphism for arbitrary rings.
- `Sheaf.AlgebraicGeometry.ProEtaleSheafTopologicalInvariance`
  (`lem-trf-proetale-topological-invariance`): fixed-module counit invertibility and
  zero detection suffice, so set-valued topological invariance is unnecessary here.
- `Sheaf.CategoryTheory.Adjunction.LiftsGroupRingObjects`
  (`lem-weil-pbc-adjunction-lifts-group-ring-objects`).
- `Sheaf.CategoryTheory.ConstantLeftModuleInverseImage`
  (`lem-pe-constant-left-module-inverse-image`).
- `Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction`
  (`lem-weil-pbc-ringed-topoi-module-adjunction`): the last three generic lifting
  tools are replaced by the proved constant-scalar encoding and canonical pullback
  comparison, for the specified ordinary adjunction.
- `Sheaf.SixFunctors.GeometricInverseImageConstantModule`
  (`lem-sfb-geometric-inverse-image-constant-module`): the fixed-module constant-sheaf
  pullback comparison plus scalar encoding gives the required comparison directly.

The same six entries were removed from top-level tool_uses. Other modules may still
need them; this is pruning from this item's proof. The unchanged etale route and
its dependencies are retained. The pro-etale object-restriction import is retained
for its slice-density API. The universe-local-constancy import supplies the explicit
abelian-coefficient sheafification/locally-bijective instances used by the global
scalar-comparison helper.

## Where the brief, the DAG or earlier work was wrong

The remaining pro-etale plan needlessly routed the equivalence through set-valued
topological invariance and general lifting of algebraic structures. The source
library already proves the fixed-module closed-immersion counit invertible and
jointly-surjective zero detection. These combine with the triangle identity and
balancedness of the abelian category to give the needed equivalence directly.
The cover-refinement declaration is indexed in universe u; Mathlib's smallness of
the quasi-compact weakly-etale precoverage shrinks the given u+1-indexed cover
before applying it. Explicit coefficient universes avoid unresolved max-universe
metavariables in the global scalar-comparison helper.

The existing generic closed-immersion counit theorem belongs to the open/closed
triangle unit; its statement is an independently proved site-theoretic tool and
neither presupposes this item's finite-local-model result nor uses the flat-model
unit. The constant-scalar encoding helpers similarly concern arbitrary modules
and are proved independently. The unit's flat-model route is unchanged. No
statements, definitions, public imports or consumer interfaces changed.

## Second reading by U4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
