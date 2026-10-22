# AlgebraicGeometry.perfectOverlapStageTransport

## Reason

Retire the duplicate Sheaf transport definition in favour of its canonical
WeilConjectures owner, preserving the fixed construction and its dependencies.
Repair the return of bfc856a2d12, whose landing failed after the tail consumer
was quarantined. Its rework row and archive were read and a claim was attempted;
N2 held that item and restored it during this repair, in landing
20261021T225159-L-3789340. The current restored consumer is the basis of the
edits below. The subsequent return at 208cdfa3757 requires preserving E2's
landed simplification 7ef9e5524fd. This repair starts from the current library
file and changes only the transport import and its comparison-API reexport.

## Old

Current Sheaf source, verbatim:

```lean
/- Copyright (c) 2026 The SHEAF contributors. -/
module

public import Sheaf.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreComparisons
public import WeilConjectures.AlgebraicGeometry.PerfectOverlapStageEquivalenceFunctor

/-! # Derived transport with the cartesian stage interfaces -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
attribute [local irreducible] perfectHomComposition
attribute [local instance] Functor.additive_of_preserves_binary_products
attribute [local instance 2000] openComparisonModuleAbelian openComparisonOverModuleAbelian
variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]

/-- The fixed derived transport, with its endpoints expressed by the stage functors.
Source: Stacks Project, Tags 08DW and 0D5S. The forward stage functor is derived
pullback along the inverse cartesian isomorphism, so the explicitly constructed
derived transport has these endpoints directly, without equality transports.
(blueprint: def-pc-perfect-overlap-stage-transport). -/
@[irreducible] noncomputable def perfectOverlapStageTransport
    {X Y K C T S : Scheme.{u}}
    (g : X ⟶ Y) (f : K ⟶ Y)
    (pX : X ⟶ C) (pK : K ⟶ T) (pY : Y ⟶ S)
    (b : C ⟶ S) (q : T ⟶ S)
    (hg : IsPullback g pX pY b) (hf : IsPullback f pK pY q)
    (U V : Y.Opens)
    (r : (g ⁻¹ᵁ (U ⊓ V)).toScheme ⟶ (f ⁻¹ᵁ (U ⊓ V)).toScheme)
    (m : pullback ((U ⊓ V).ι ≫ pY) b ⟶ pullback ((U ⊓ V).ι ≫ pY) q)
    (hmap :
      ((isPullback_morphismRestrict g (U ⊓ V)).paste_vert hg).isoPullback.inv ≫ r =
        m ≫ ((isPullback_morphismRestrict f (U ⊓ V)).paste_vert hf).isoPullback.inv) :
    derivedPullback r ⋙ (perfectOverlapStageEquivalence g pX pY b hg U V).functor ≅
      (perfectOverlapStageEquivalence f pK pY q hf U V).functor ⋙
        derivedPullback m := by
  exact perfectOverlapDerivedPullbackTransport r
    ((isPullback_morphismRestrict g (U ⊓ V)).paste_vert hg).isoPullback
    ((isPullback_morphismRestrict f (U ⊓ V)).paste_vert hf).isoPullback m hmap

end AlgebraicGeometry
```

## New

Withdraw `lean/Sheaf/AlgebraicGeometry/PerfectOverlapStageTransport.lean` through
`deleted.txt`. Attach its node to the unchanged
`WeilConjectures.AlgebraicGeometry.PerfectOverlapStageTransport`, declaration
`AlgebraicGeometry.perfectOverlapStageTransport`. The official definition has
exactly the same signature. It rewrites the two stage functors by their proved
equations before constructing the same `perfectOverlapDerivedPullbackTransport`.
The private scratch compatibility theorem proves equality to the old construction
by `unfold perfectOverlapStageTransport; rfl`; it is not delivered.

For each direct consumer, replace only its public import of the withdrawn
Sheaf transport with the canonical official transport and explicitly public-import
the Sheaf core-comparison API formerly exported by the withdrawn module.
Preserve every other import, declaration, proof body and local command verbatim.
In particular the tail retains E2's direct cartesian projection calculation,
`perfectOverlapCompositeLocalIso_eq_compositionTo_global`, and reduced proof
imports. Its statement, proof and existing dependency plan are unchanged.

The prism's official core-base import has already landed. The three prism-chain
sources in the sandbox are byte-identical to current main and are validation only.
No upstream definition, signature, attribute or public import changes.

## Users

Both current Lean importers of the retired module are adapted in this delivery.
The parent DAG nodes retain their dependency on
`def-pc-perfect-overlap-stage-transport`, now attached to the official definition.
The blueprint unit route is unchanged. The tail rework row and archive were checked before source adaptation.
N2 restored it in landing 20261021T225159-L-3789340; E2's later proof
simplification landed as 7ef9e5524fd. Neither consumer is currently claimed
in the shared claim records.
The adaptation is forced by withdrawal of its public transport import, and keeps
every signature, visibility, proof body, local command and other import intact.
The earlier counterfactual compilation against the empty transport failed with
unknown identifiers `perfectOverlapStageTransport` and
`perfectOverlapStageEquivalence_map_eq`. The two import edits restore
respectively that construction and its reexported component API. The adapted
consumer compiles in 26.7 seconds after this repair.
The restored source is present at its normal library path. Its statement and
attachment are preserved, and its archive is not changed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.PerfectOverlapStageTransport | M5 | Retire duplicate definition; retain node with official attachment. |
| Sheaf.AlgebraicGeometry.PerfectOverlapCompositeCounitFactor | unclaimed | Replace transport import and retain its exported component API; proof unchanged. |
| Sheaf.AlgebraicGeometry.PerfectOverlapTailProjectionComponent | unclaimed (E2's proof landed) | Forced transport-import replacement and component-API preservation; all other lines unchanged. |
| Sheaf.AlgebraicGeometry.PerfectOverlapTransportPrism | unclaimed | Already canonical on main; byte-identical validation source. |
| Sheaf.AlgebraicGeometry.PerfectOverlapTransportPrismHom | unclaimed | Byte-identical validation source. |
| Sheaf.AlgebraicGeometry.PerfectOverlapProjectionCompositeAbstract | unclaimed | Byte-identical validation source. |
| Sheaf.AlgebraicGeometry.PerfectOverlapProjectionCompositionComponent | unclaimed | Same transport declaration through adapted consumers; no source change. |
| WeilConjectures.AlgebraicGeometry.PerfectOverlapStageTransport | upstream, unchanged | Existing canonical owner and construction. |
| WeilConjectures.AlgebraicGeometry.PerfectOverlapCompositeCounitFactor | upstream, unchanged | Already uses official transport; no source change. |

Validation: the two adapted consumers and three unchanged prism-chain modules
compile together with `LCOMPILE_NO_LOCAL=1` on the server. The updated tail
compiles in 26.7 seconds without warnings. Run deliver3.py, which fetches
sheaf-dag and applies the packet before preflight and push. Holes closed: 0; holes added: 0; holes remaining: 0.

## Status

landed 20261022T013427-L-3575231 2026-10-22 (merge of deliver/M5/Sheaf.AlgebraicGeometry.PerfectOverlapStageTransport)
