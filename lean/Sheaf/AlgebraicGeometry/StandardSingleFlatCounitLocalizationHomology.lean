module
public import Sheaf.AlgebraicGeometry.StandardSingleFlatCounitPresentation
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
/-- Homology identifications and counit compatibility for fixed stalk data.
Source: Stacks Project, Tags 0DJ9, 06YB and 0D5S.
The proof applies exact stalk functors and homology to the localized presentation equation.
(blueprint: lem-pc-standard-single-flat-counit-localization-homology). -/
theorem standardSingleFlatCounit_localization_homology
    (h_affine : ∀ {Y₀ B₀ A₀ : Scheme.{u}} (p₀ : Y₀ ⟶ B₀)
      [QuasiCompact p₀] [QuasiSeparated p₀] [IsAffine B₀] [IsAffine A₀]
      (g₀ : A₀ ⟶ B₀), StandardSingleFlatCounitOnOpen p₀ g₀ ⊤)
    {Y B A : Scheme.{u}} (p : Y ⟶ B) [QuasiCompact p] [QuasiSeparated p]
    (M : Y.Modules) [M.IsQuasicoherent] (hM : M.IsFlatOver p) (g : A ⟶ B) (a : A)
    (S : B.Opens) (V : A.Opens) (hS : g a ∈ S) (hV : a ∈ V)
    (hSaff : IsAffine S.toScheme) (hVaff : IsAffine V.toScheme)
    (hVS : V ≤ g ⁻¹ᵁ S)
    (hpres : StandardSingleFlatCounitPresentation (p ∣_ S)
      (M.restrict (p ⁻¹ᵁ S).ι) (g.resLE S V hVS)) :
    letI := fun X : Scheme.{u} ↦ HasDerivedCategory.standard
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))
    let R := B.presheaf.stalk (g a)
    let T := A.presheaf.stalk a
    letI := HasDerivedCategory.standard (ModuleCat.{u} R)
    letI := HasDerivedCategory.standard (ModuleCat.{u} T)
    ∀ (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hPbound : ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (P.X i))
    (hPflat : ∀ i : ℤ, Module.Flat R (P.X i))
    (LF : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} T))
    (ε : DerivedCategory.Qh ⋙ LF ⟶
      (ModuleCat.extendScalars (g.stalkMap a).hom).mapHomotopyCategory (.up ℤ) ⋙
        DerivedCategory.Qh)
    (hLF : LF.IsLeftDerivedFunctor ε
      (HomotopyCategory.quasiIso (ModuleCat.{u} R) (.up ℤ))),
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
                (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≫ eR.hom  := by
  sorry
end AlgebraicGeometry
