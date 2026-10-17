# perfectOverlapStageTransport

## Reason

The endpoint forward functors are definitionally the indicated derived pullbacks.
Rewriting their equalities before constructing the transport inserts equality
transports into the definition. Consumers comparing components then reduce these
casts repeatedly. Construct the same fixed derived transport directly. This does
not change its signature, visibility, or mathematical data.

## Old

```lean
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
  rw [perfectOverlapStageEquivalence_functor_eq, perfectOverlapStageEquivalence_functor_eq]
  exact perfectOverlapDerivedPullbackTransport r
    ((isPullback_morphismRestrict g (U ⊓ V)).paste_vert hg).isoPullback
    ((isPullback_morphismRestrict f (U ⊓ V)).paste_vert hf).isoPullback m hmap
```

## New

```lean
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
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.PerfectOverlapStageTransport | unclaimed | definitionally the same transport |
| Sheaf.AlgebraicGeometry.PerfectOverlapCompositeCounitFactor | unclaimed | statement and proof unchanged |
| Sheaf.AlgebraicGeometry.PerfectOverlapProjectionCompositionComponent | unclaimed | statement and proof unchanged |
| Sheaf.AlgebraicGeometry.PerfectOverlapTailProjectionComponent | D3 | component calculation uses the same transport |

| Sheaf.AlgebraicGeometry.PerfectOverlapStageTransportComponent | unclaimed | remove redundant final rfl; public signature unchanged |
| Sheaf.AlgebraicGeometry.PerfectOverlapTailProjectionAt | unclaimed | same fixed derived transport; statement and proof unchanged |
| Sheaf.AlgebraicGeometry.PerfectOverlapTailProjectionFactors | unclaimed | same fixed derived transport; statement and proof unchanged |

The original StageTransportComponent fails at its final `rfl` with
`No goals to be solved`: after the constructor simplification, its preceding rewrite
already closes the goal. Remove only that redundant proof line.

The adapted component and unchanged Factors/At consumers compiled together in import order
in 2.7, 7.1 and 6.9 seconds respectively against the repaired dependencies.

The source-only downstream check found these 7 modules using the declaration.
The unchanged CompositeCounitFactor and ProjectionCompositionComponent consumers
were compiled against the changed overlay (23.2 s and 24.0 s respectively), without
errors or warnings.
The broader import closure has 1073 modules; none acquires different mathematical
objects or target meanings, since both endpoint equalities used by the old
constructor are reflexive. No target statement changes.

## Status

landed 20261017T191956-L-3002698 2026-10-17 (merge of deliver/D3/Sheaf.AlgebraicGeometry.PerfectOverlapTailProjectionComponent)
