module

public import Sheaf.AlgebraicGeometry.StandardSingleBaseChangeMap

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Source restriction comparison for the top open; see the two-step proof of
`standardSingleBaseChange_topRestriction_comparison`.
Source: Stacks Project, Tags 08HY and 0D5S.
(blueprint: lem-pc-standard-single-base-change-top-restriction-source) -/
theorem standardSingleBaseChange_topRestriction_source
    {Y B A : Scheme.{u}} (p : Y ⟶ B) (M : Y.Modules) (g : A ⟶ B) :
    letI := fun X : Scheme.{u} ↦ HasDerivedCategory.standard
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))
    let j := (⊤ : Y.Opens).ι
    let N := M.restrict j
    Nonempty ((schemeDerivedDirectImage p).obj
          ((DerivedCategory.singleFunctor _ 0).obj M) ≅
        (schemeDerivedDirectImage (j ≫ p)).obj
          ((DerivedCategory.singleFunctor _ 0).obj N)) := by sorry

/-- Compatibility equation after choosing the source restriction comparison.
Source: Stacks Project, Tags 08HY and 0D5S.
(blueprint: lem-pc-standard-single-base-change-top-restriction-compatibility) -/
theorem standardSingleBaseChange_topRestriction_compatibility
    {Y B A : Scheme.{u}} (p : Y ⟶ B) (M : Y.Modules) (g : A ⟶ B) :
    letI := fun X : Scheme.{u} ↦ HasDerivedCategory.standard
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))
    ∀ (e : (schemeDerivedDirectImage p).obj
          ((DerivedCategory.singleFunctor _ 0).obj M) ≅
        (schemeDerivedDirectImage ((⊤ : Y.Opens).ι ≫ p)).obj
          ((DerivedCategory.singleFunctor _ 0).obj (M.restrict (⊤ : Y.Opens).ι))),
      ∃ (t : (schemeDerivedDirectImage
          (pullback.snd ((⊤ : Y.Opens).ι ≫ p) g)).obj
          ((DerivedCategory.singleFunctor _ 0).obj
            (Scheme.Modules.tensorPullbackObj
              (pullback.fst ((⊤ : Y.Opens).ι ≫ p) g)
              (M.restrict (⊤ : Y.Opens).ι))) ≅
        (schemeDerivedDirectImage (pullback.snd p g)).obj
          ((DerivedCategory.singleFunctor _ 0).obj
            (Scheme.Modules.tensorPullbackObj (pullback.fst p g) M))),
      standardSingleBaseChangeMap p M g =
        (derivedPullback g).map e.hom ≫
          standardSingleBaseChangeMap ((⊤ : Y.Opens).ι ≫ p)
            (M.restrict (⊤ : Y.Opens).ι) g ≫ t.hom := by sorry

end AlgebraicGeometry
