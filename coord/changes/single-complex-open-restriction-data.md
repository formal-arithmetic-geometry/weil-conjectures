# singleComplexOpenPullbackIso and singleComplexRestrictedCoefficient

## Reason

The new compatibility lemmas need the existing explicit constructions. Importing the old
module would form a cycle with the theorem that combines these lemmas. Relocate the two
constructions verbatim to Sheaf.AlgebraicGeometry.SingleComplexOpenRestrictionData and
publicly re-export that module from the original. Their names, universes, binders,
visibility, bodies, and mathematical meaning stay identical. This is a module-placement
change; no definition is weakened or replaced by a witness of an existence theorem.

## Old

In Sheaf.AlgebraicGeometry.SingleComplexOpenRestrictionComparison:

```lean
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The comparison from pullback along an open immersion to exact restriction,
constructed using the pinned tensor-pullback adjunction and left-derived counit.
Source: Stacks Project, Tag 08DW, restriction of derived pullback.
(blueprint: lem-pc-single-complex-open-restriction-comparison). -/
noncomputable def singleComplexOpenPullbackIso
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (Y : Scheme.{u}) (U : Y.Opens) :
    derivedPullback U.ι ≅ (schemeOpenRestriction Y U).mapDerivedCategory := by
  classical
  let T : SheafOfModules.{u} (moduleRings Y.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace) :=
    Scheme.Modules.tensorPullback U.ι
  have : T.Additive := (Classical.choose exists_derivedPullbackComposition) U.ι
  let ε := (Classical.choose (Classical.choose_spec exists_derivedPullbackComposition)) U.ι
  let W := HomotopyCategory.quasiIso
    (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (.up ℤ)
  have : (derivedPullback U.ι).IsLeftDerivedFunctor ε W :=
    (Classical.choose (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition))) U.ι
  let η : T ≅ Scheme.Modules.restrictFunctor U.ι :=
    (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction U.ι)).leftAdjointUniq
      (Scheme.Modules.pullbackPushforwardAdjunction U.ι) ≪≫
        (Scheme.Modules.restrictFunctorIsoPullback U.ι).symm
  let θ : schemeOpenRestriction Y U ≅ T := Scheme.Modules.overFunctorEquiv U ≪≫ η.symm
  have : PreservesFiniteLimits (schemeOpenRestriction Y U) :=
    schemeOpenRestriction_preservesFiniteLimits Y U
  have : PreservesFiniteColimits (schemeOpenRestriction Y U) :=
    schemeOpenRestriction_preservesFiniteColimits Y U
  have : PreservesFiniteLimits T := preservesFiniteLimits_of_natIso θ
  have : PreservesFiniteColimits T := preservesFiniteColimits_of_natIso θ
  have : T.mapDerivedCategory.IsLeftDerivedFunctor T.mapDerivedCategoryFactorsh.hom W :=
    Functor.isLeftDerivedFunctor_of_inverts _ _ T.mapDerivedCategoryFactorsh
  exact Functor.leftDerivedUnique T.mapDerivedCategory (derivedPullback U.ι) ε
    T.mapDerivedCategoryFactorsh.hom W ≪≫ (Functor.mapDerivedCategoryNatIso θ).symm

/-- Restrict the coefficient morphism using the canonical pullback composition
comparisons and the constructed open-pullback comparisons. Both objects and the
morphism are constructed; no existence theorem supplies arbitrary coefficient data.
Source: Stacks Project, Tag 0DJ9, first paragraph.
(blueprint: lem-pc-single-complex-open-restriction-comparison). -/
noncomputable def singleComplexRestrictedCoefficient
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' : Scheme.{u}} (g' : X' ⟶ X)
    (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X')
    (φ : (derivedPullback g').obj K ⟶ K')
    (U : X.Opens) (U' : X'.Opens) (j : U'.toScheme ⟶ U.toScheme)
    (hj : j ≫ U.ι = U'.ι ≫ g') :
    (derivedPullback j).obj ((schemeOpenRestriction X U).mapDerivedCategory.obj K) ⟶
      (schemeOpenRestriction X' U').mapDerivedCategory.obj K' :=
  (derivedPullback j).map ((singleComplexOpenPullbackIso X U).inv.app K) ≫
  ((Classical.choose (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec exists_derivedPullbackComposition)))) j U.ι).hom.app K ≫
  eqToHom (congrArg (fun k ↦ (derivedPullback k).obj K) hj) ≫
  ((Classical.choose (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec exists_derivedPullbackComposition)))) U'.ι g').inv.app K ≫
  (singleComplexOpenPullbackIso X' U').hom.app ((derivedPullback g').obj K) ≫
  (schemeOpenRestriction X' U').mapDerivedCategory.map φ
```

## New

The exact same declarations above are in
`Sheaf.AlgebraicGeometry.SingleComplexOpenRestrictionData`. The original module adds:

```lean
public import Sheaf.AlgebraicGeometry.SingleComplexOpenRestrictionData
```

The old PointwiseLeftDerived public import is supplied through this new data module,
so its original public availability is preserved. Its existing theorem has exactly the same statement. No target definition changes meaning,
so no target statement review is reopened for a mathematical change.

## Users

The downstream search for both definition names found only the item itself and the
following downstream user (414 modules are transitively downstream, but none of the
others mentions either name). No other module is adapted.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.SingleComplexOpenRestrictionComparison | Q3 | Definitions are re-exported with unchanged names, types and bodies. |
| Sheaf.AlgebraicGeometry.SingleComplexTargetLocality | unclaimed in this checkout | Uses singleComplexRestrictedCoefficient through the same public import; no adaptation or statement change. |

## Status

landed 20261013T115432-L-3360003 2026-10-13 (merge of deliver/Q3/Sheaf.AlgebraicGeometry.SingleComplexOpenRestrictionComparison)
