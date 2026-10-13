/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.MixedAffineSectionsComplexUnit
public import Sheaf.AlgebraicGeometry.MixedGlobalSectionsDirectImageIso
import Sheaf.AlgebraicGeometry.AffineKFlatPullbackChartComparison
import Sheaf.AlgebraicGeometry.TensorPullbackTilde

/-! # The target affine model and its pullback unit normalization
Source: Stacks Project, Tags 06Z0, 08DW(2) and 0D5T.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w wA
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
variable [∀ (R : Type u) [Ring R], HasDerivedCategory.{wA} (ModuleCat.{u} R)]

/-- The pullback counit and affine sections comparison normalize the target unit.
Source: Stacks Project, Tags 06Z0, 08DW(2), 0D5T.
(blueprint: lem-sc-mixed-affine-pullback-unit-normalization).

Proof: Tilde preserves K-flatness, and exact restriction through the spectrum chart
preserves it, so C=F(P) is K-flat. Its derived pullback counit is invertible.
Termwise tensor-pullback/tilde base change and toSpecΓ naturality identify K(C)
with the affine chart complex of E(P) on T. The affine derived sections comparison
is thus invertible on K(C), with no boundedness restriction. Define b by taking
sections of the pullback counit and then the inverse of that sections comparison.
The pinned derived pullback adjunction unit factors through the counit by
exists_schemeDerivedAdjunction and derivedη_fac_app. Apply sections, move its unit
past the ordinary pullback unit by naturality, and substitute the normalized
mixedGlobalSectionsDirectImageIso derived-unit equation. Naturality of that Leray
isomorphism at the counit produces the displayed equality. Insert the complex to
homotopy quotient factor isomorphisms and the exact scalar restriction factor at
both endpoints. This statement uses neither scalar extension nor any comparison c
or hc; it computes only the pullback side. Empty schemes and P=0 are covered by
the same naturality equations, and no equality of localization universes is used. -/
theorem exists_mixedAffineSections_pullback_unit_normalization
    {S T : Scheme.{u}} [IsAffine S] [IsAffine T] (g : T ⟶ S) :
    let F : ModuleCat.{u} Γ(S, ⊤) ⥤
        SheafOfModules.{u} (moduleRings S.toRingedSpace) :=
      tilde.functor Γ(S, ⊤) ⋙ Scheme.Modules.restrictFunctor S.toSpecΓ
    let H := RingedSpace.globalSectionsFunctor S.toRingedSpace
    let J := RingedSpace.globalSectionsFunctor T.toRingedSpace
    let K : SheafOfModules.{u} (moduleRings S.toRingedSpace) ⥤
        SheafOfModules.{u} (moduleRings T.toRingedSpace) := Scheme.Modules.tensorPullback g
    let R := ModuleCat.restrictScalars.{u} g.appTop.hom
    let d : F ⋙ H ⟶ F ⋙ K ⋙ J ⋙ R :=
      Functor.whiskerRight (Functor.whiskerLeft F
        (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)).unit) H
    ∀ [F.Additive] [H.Additive] [J.Additive] [K.Additive]
      (P : CochainComplex (ModuleCat.{u} Γ(S, ⊤)) ℤ)
      (_hP : (HomologicalComplex.quasiIso (ModuleCat.{u} Γ(S, ⊤)) (.up ℤ)).kFlat P),
    let C := (F.mapHomologicalComplex (.up ℤ)).obj P
    let Q : DerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings S.toRingedSpace)) := DerivedCategory.Q.obj C
    let Y := ((F ⋙ K ⋙ J).mapHomologicalComplex (.up ℤ)).obj P
    ∃ b : (schemeDerivedGlobalSections T).obj ((derivedPullback g).obj Q) ≅
        DerivedCategory.Q.obj Y,
      mixedSectionsComplexUnit S C ≫
        (schemeDerivedGlobalSections S).map ((schemeHomPullbackAdjunction g).unit.app Q) ≫
          (mixedGlobalSectionsDirectImageIso g).hom.app ((derivedPullback g).obj Q) ≫
            (schemeGlobalScalarRestriction g).map b.hom =
      DerivedCategory.Q.map ((d.mapHomologicalComplex (.up ℤ)).app P) ≫
        R.mapDerivedCategoryFactors.inv.app Y := by sorry

end AlgebraicGeometry
