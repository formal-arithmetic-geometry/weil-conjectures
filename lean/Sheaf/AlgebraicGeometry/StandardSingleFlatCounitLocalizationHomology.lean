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
Proof: unpack Classical.choose_spec hpres into the upper bound, termwise flatness,
identifications e and t, and presentation equation for K. Take its termwise stalk at xS
and restrict scalars along the inverse open-stalk ring isomorphism. Exact additive stalks
preserve zero terms and the bound; flat stalks and transport along the ring isomorphism
give termwise flatness. Set P′ equal to this constructed P, with equality rfl. Choose a
universal left-derived extension-of-scalars pair for g.stalkMap a. On K-flat resolutions,
the ordinary tensor-pullback stalk isomorphism identifies scalar extension with the stalk
of pullback. Naturality and the pure-tensor formula identify the scalar-extension counit
with the stalk of the sheaf counit; localization descends this identity. Transport e and
t through these comparisons. Derived direct image commutes with restriction to full
inverse-image opens, and derived pullback commutes with open restriction. Their
unit-and-counit mate identities identify the restricted base-change map with the original
map. Transport the stalks from S and V to B and A along the open-stalk isomorphisms.
Exact stalks commute with homology, so applying degree-n homology to the transported
presentation equation supplies eL, eR and the displayed equality for every integer n,
using the same P and derived pair.
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
    let K := Classical.choose hpres
    let xS : S.toScheme := ⟨g a, hS⟩
    let P :=
      ((ModuleCat.restrictScalars (S.stalkIso xS).inv.hom).mapHomologicalComplex
        (.up ℤ)).obj
        (((RingedSpace.moduleStalkFunctor S.toScheme.toRingedSpace xS).mapHomologicalComplex
          (.up ℤ)).obj K)
    ∃ (P' : CochainComplex (ModuleCat.{u} R) ℤ), P' = P ∧
      (∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (P'.X i)) ∧
      (∀ i : ℤ, Module.Flat R (P'.X i)) ∧
      ∃ (LF : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} T))
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
                  ((HomotopyCategory.quotient _ (.up ℤ)).obj P'))))
            (eR : (DerivedCategory.homologyFunctor _ n).obj
                (DerivedCategory.Qh.obj
                  (((ModuleCat.extendScalars (g.stalkMap a).hom).mapHomotopyCategory
                    (.up ℤ)).obj ((HomotopyCategory.quotient _ (.up ℤ)).obj P'))) ≅
              (RingedSpace.moduleStalkFunctor A.toRingedSpace a).obj
                ((DerivedCategory.homologyFunctor _ n).obj
                  ((schemeDerivedDirectImage (pullback.snd p g)).obj
                    ((DerivedCategory.singleFunctor _ 0).obj
                      (Scheme.Modules.tensorPullbackObj (pullback.fst p g) M))))),
            (RingedSpace.moduleStalkFunctor A.toRingedSpace a).map
                ((DerivedCategory.homologyFunctor _ n).map (standardSingleBaseChangeMap p M g)) =
              eL.hom ≫ (DerivedCategory.homologyFunctor _ n).map
                (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P')) ≫ eR.hom  := by
  sorry
end AlgebraicGeometry
