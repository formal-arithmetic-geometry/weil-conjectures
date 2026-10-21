# AlgebraicGeometry.perfectOverlapNestedPullbackSquare

## Reason

Restore rework row 141, quarantined after the global build. The archived file fails
compilation at its local irreducibility command for `derivedPullback`, which is now
already irreducible. More fundamentally, the adopted source library already declares
both exported names. Restore the Sheaf path as an adapter to the canonical source,
following the repaired PerfectOverlapStageEquivalence adapter. This removes duplicate
ownership of the declarations and the obsolete local elaboration commands.

## Old

The quarantined declaration block, verbatim:

```lean
/-- The restricted maps form a square over the two nested open inclusions.
Both maps agree after the open immersion of the larger target open.
Source: Stacks Project, Tag 08DW.
(blueprint: lem-pc-perfect-overlap-nested-pullback-square). -/
theorem perfectOverlapNestedRestrictedMaps
    {X Y : Scheme.{u}} (g : X ⟶ Y) {W U : Y.Opens} {T P : X.Opens}
    (iY : W ⟶ U) (iX : T ⟶ P)
    (hP : P ≤ g ⁻¹ᵁ U) (hT : T ≤ g ⁻¹ᵁ W) :
    g.resLE W T hT ≫ Y.homOfLE (leOfHom iY) =
      X.homOfLE (leOfHom iX) ≫ g.resLE U P hP := by
  apply (cancel_mono U.ι).1
  simp only [Category.assoc, Scheme.homOfLE_ι, Scheme.Hom.resLE_comp_ι]
  rw [← Category.assoc, Scheme.homOfLE_ι]

variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]

/-- Compare pullback and exact restriction around the nested restricted square.
This is constructed from the fixed pullback composition comparisons and the
fixed comparison between nested exact restriction and open-inclusion pullback.
Source: Stacks Project, Tags 08DW and 0D5S.
(blueprint: lem-pc-perfect-overlap-nested-pullback-square). -/
@[irreducible] noncomputable def perfectOverlapNestedPullbackSquare
    {X Y : Scheme.{u}} (g : X ⟶ Y) {W U : Y.Opens} {T P : X.Opens}
    (iY : W ⟶ U) (iX : T ⟶ P)
    (hP : P ≤ g ⁻¹ᵁ U) (hT : T ≤ g ⁻¹ᵁ W) :
    derivedPullback (g.resLE U P hP) ⋙
        (schemeOpenOverlapRestriction X iX).mapDerivedCategory ≅
      (schemeOpenOverlapRestriction Y iY).mapDerivedCategory ⋙
        derivedPullback (g.resLE W T hT) :=
  Functor.isoWhiskerLeft _ (overlapOpenInclusionPullbackIso X iX).symm ≪≫
    perfectHomComposition (X.homOfLE (leOfHom iX)) (g.resLE U P hP) ≪≫
    eqToIso (congrArg (fun k ↦ derivedPullback k)
      (perfectOverlapNestedRestrictedMaps g iY iX hP hT).symm) ≪≫
    (perfectHomComposition (g.resLE W T hT) (Y.homOfLE (leOfHom iY))).symm ≪≫
    Functor.isoWhiskerRight (overlapOpenInclusionPullbackIso Y iY) _
```

## New

```lean
public import Sheaf.AlgebraicGeometry.PerfectOverlapStageEquivalence
public import WeilConjectures.AlgebraicGeometry.PerfectOverlapNestedPullbackSquare
```

Both declarations are now reexported from the adopted source module. Its declaration
block is byte-identical to the Old block above, including the theorem proof and the
entire explicit comparison body. No data construction changes, and no declaration is
removed from the source library. The original Sheaf public import is preserved, so its
helper equations remain available to downstream modules. The node's Lean attachment
now points at the source declarations; its statement, proof plan and dependencies stay.
No target statement or definition changes meaning, so no target semantic review reopens.

## Users

The current `tools/downstream.py --allow-missing --uses` query reports zero active
consumers. The quarantined consumers are retained and checked separately; their absence
from the live library is not used as withdrawal authority. The adapter restores the
same path and names, and preserves the definitional five-factor expansion used by
normalization proofs. No consumer needs an adaptation in this delivery.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.PerfectOverlapNestedPullbackSquare | U6 | Restore as canonical-source adapter; zero holes. |
| Sheaf.AlgebraicGeometry.PerfectOverlapCompositeStageMap | quarantined; not adapted | Same public names, types and comparison expansion; no edit. |
| Sheaf.AlgebraicGeometry.PerfectOverlapNestedPullbackNormalization | quarantined; not adapted | Same public names, types and comparison expansion; no edit. |
| Sheaf.AlgebraicGeometry.PerfectOverlapNestedSiteCompatibility | quarantined; not adapted | Same public names, types and comparison expansion; no edit. |
| Sheaf.AlgebraicGeometry.PerfectOverlapProjectionCompositionComponent | quarantined; not adapted | Same public names, types and comparison expansion; no edit. |
| Sheaf.AlgebraicGeometry.PerfectOverlapTailProjectionComponent | quarantined; not adapted | Same public names, types and comparison expansion; no edit. |

The additional quarantined term consumers PerfectOverlapCompositeSiteComponent and
PerfectOverlapCompositeStageTail import the interface transitively; their existing
uses likewise retain the same terms and types. The adopted-source module and all its
consumers are unchanged.

## Status

landed 20261021T171849-L-3166667 2026-10-21 (merge of deliver/U6/Sheaf.AlgebraicGeometry.PerfectOverlapNestedPullbackSquare)
