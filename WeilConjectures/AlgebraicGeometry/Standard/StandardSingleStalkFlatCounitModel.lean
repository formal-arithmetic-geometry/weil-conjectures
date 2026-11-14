/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Standard.StandardSingleBaseChangeMap
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic

import WeilConjectures.AlgebraicGeometry.Standard.StandardSingleFlatCounitAffine
import WeilConjectures.AlgebraicGeometry.Standard.StandardSingleFlatCounitUnion
import WeilConjectures.AlgebraicGeometry.Standard.StandardSingleFlatCounitLocalization
import WeilConjectures.AlgebraicGeometry.QuasiCompactOpenInduction

/-! # Flat scalar-extension coordinates for a single-module comparison

Source: Stacks Project, Tags 0A1D and 0DJ9, affine calculation and relative Mayer--Vietoris
induction.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Flat scalar-extension coordinates for the canonical comparison at one base point.

Source: Stacks Project, Tag 0A1D, specialized to the structure sheaf and M[0], and Tag 0DJ9, affine
calculation and relative Mayer--Vietoris induction. -/
theorem exists_standardSingle_stalk_flat_counit_model
    {Y B A : Scheme.{u}} (p : Y ⟶ B) [QuasiCompact p] [QuasiSeparated p]
    (M : Y.Modules) [M.IsQuasicoherent] (hM : M.IsFlatOver p) (g : A ⟶ B) (a : A) :
    letI := fun X : Scheme.{u} ↦ HasDerivedCategory.standard
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))
    let R := B.presheaf.stalk (g a)
    let T := A.presheaf.stalk a
    letI := HasDerivedCategory.standard (ModuleCat.{u} R)
    letI := HasDerivedCategory.standard (ModuleCat.{u} T)
    ∃ (P : CochainComplex (ModuleCat.{u} R) ℤ),
      (∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (P.X i)) ∧
      (∀ i : ℤ, Module.Flat R (P.X i)) ∧
      ∃ (LF : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} T))
        (ε : DerivedCategory.Qh ⋙ LF ⟶
          (ModuleCat.extendScalars (g.stalkMap a).hom).mapHomotopyCategory (.up ℤ) ⋙
            DerivedCategory.Qh),
        LF.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso (ModuleCat.{u} R) (.up ℤ)) ∧
        ∀ n : ℤ,
          ∃ (eL : (RingedSpace.moduleStalkFunctor A.toRingedSpace a).obj
              ((DerivedCategory.homologyFunctor _ n).obj
                ((derivedPullback g).obj ((schemeDerivedDirectImage p).obj
                  ((DerivedCategory.singleFunctor _ 0).obj M)))) ≅
              (DerivedCategory.homologyFunctor _ n).obj
                (LF.obj (DerivedCategory.Qh.obj
                  ((HomotopyCategory.quotient _ (.up ℤ)).obj P))))
            (eR : (DerivedCategory.homologyFunctor _ n).obj
                (DerivedCategory.Qh.obj
                  (((ModuleCat.extendScalars (g.stalkMap a).hom).mapHomotopyCategory
                    (.up ℤ)).obj ((HomotopyCategory.quotient _ (.up ℤ)).obj P))) ≅
              (RingedSpace.moduleStalkFunctor A.toRingedSpace a).obj
                ((DerivedCategory.homologyFunctor _ n).obj
                  ((schemeDerivedDirectImage (pullback.snd p g)).obj
                    ((DerivedCategory.singleFunctor _ 0).obj
                      (Scheme.Modules.tensorPullbackObj (pullback.fst p g) M))))),
            (RingedSpace.moduleStalkFunctor A.toRingedSpace a).map
                ((DerivedCategory.homologyFunctor _ n).map (standardSingleBaseChangeMap p M g)) =
              eL.hom ≫ (DerivedCategory.homologyFunctor _ n).map
                (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≫ eR.hom := by
  apply standardSingleFlatCounit_localization ?_ p M hM g a
  intro Y₀ B₀ A₀ p₀ _ _ _ _ g₀
  let : CompactSpace Y₀ := QuasiCompact.compactSpace_of_compactSpace p₀
  let : QuasiSeparatedSpace Y₀ := quasiSeparatedSpace_of_quasiSeparated p₀
  let P : Y₀.Opens → Prop := StandardSingleFlatCounitOnOpen p₀ g₀
  have h_affine : ∀ U : Y₀.Opens, IsAffineOpen U → P U := by
    intro U hU
    exact standardSingleFlatCounitOnOpen_affine p₀ g₀ U hU
  have h_union : ∀ U V : Y₀.Opens, IsCompact (U : Set Y₀) → IsAffineOpen V →
      P U → P V → P (U ⊓ V) → P (U ⊔ V) := by
    intro U V hU hV hPU hPV hPUV
    exact standardSingleFlatCounitOnOpen_union p₀ g₀ U V hU hV hPU hPV hPUV
  exact quasiCompactOpen_induction Y₀ P h_affine h_union ⊤
    (by simpa using (isCompact_univ : IsCompact (Set.univ : Set Y₀)))

end AlgebraicGeometry
