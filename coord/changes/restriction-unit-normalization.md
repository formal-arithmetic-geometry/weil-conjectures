# AlgebraicGeometry.restriction_unit_normalization

## Reason
The private generic helper uses a nested section with local universes and variables.
The preflight conservatively flags the added variable commands as visible changes.
The section ends before the original variables; the helper is private, and the
original public declaration signature is byte-identical. No public interface or
meaning changes. This record documents the flagged commands as required by preflight.

## Old
No generic section or helper; the existing public theorem had proof `by sorry`.

## New
```lean
section

universe u w
open CategoryTheory CategoryTheory.Limits TopologicalSpace
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
noncomputable section
namespace AlgebraicGeometry

section

universe w₁ w₂ w₃ w₄ v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄
variable {C : Type u₁} {D : Type u₂} {A : Type u₃} {B : Type u₄}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} A] [Category.{v₄} B]
  [Abelian C] [Abelian D] [Abelian A] [Abelian B]
  [HasDerivedCategory.{w₁} C] [HasDerivedCategory.{w₂} D]
  [HasDerivedCategory.{w₃} A] [HasDerivedCategory.{w₄} B]
  [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions D]
  [Abelian.HasKInjectiveResolutions A]
  (F : C ⥤ D) (G : A ⥤ B) (LX : C ⥤ A) (LY : D ⥤ B)
  [F.Additive] [G.Additive] [LX.Additive] [LY.Additive]
  [PreservesFiniteLimits LX] [PreservesFiniteColimits LX]
  [PreservesFiniteLimits LY] [PreservesFiniteColimits LY]
  [LX.PreservesKInjectiveComplexes]
  (e : F ⋙ LY ≅ LX ⋙ G)
  (K : HomotopyCategory C (ComplexShape.up ℤ))
private theorem restriction_unit_normalization :
    LY.mapDerivedCategory.map (F.rightDerivedFunctorUnit.app K) ≫
      ((Functor.rightDerivedFunctorCompMapDerivedCategoryIso F LY).symm ≪≫
        Functor.rightDerivedFunctorNatIso e ≪≫
        Functor.rightDerivedFunctorCompIso LX G ≪≫
        Functor.isoWhiskerRight LX.rightDerivedFunctorIsoMapDerivedCategory
          G.rightDerivedFunctor).hom.app (DerivedCategory.Qh.obj K) ≫
      G.rightDerivedFunctor.map (LX.mapDerivedCategoryFactorsh.hom.app K) =
    LY.mapDerivedCategoryFactorsh.hom.app ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
      DerivedCategory.Qh.map
        ((Functor.mapHomotopyCategoryCompIso e (ComplexShape.up ℤ) ≪≫
          (Functor.mapHomotopyCategoryCompIso (Iso.refl (LX ⋙ G))
            (ComplexShape.up ℤ)).symm).hom.app K) ≫
      G.rightDerivedFunctorUnit.app ((LX.mapHomotopyCategory (ComplexShape.up ℤ)).obj K)
```
The helper is fully proved, and its section closes before the existing public theorem.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.DerivedMayerVietorisOpenRestrictionNormalization | H3 | Uses the private helper in its proof; public signature unchanged. |

No downstream module can refer to this private helper. Existing imports and definitions
are unchanged, so no downstream statement or target needs adaptation or renewed review.

## Status
landed 20261013T211106-L-392735 2026-10-13 (merge of deliver/H3/Sheaf.AlgebraicGeometry.DerivedMayerVietorisOpenRestrictionNormalization)
