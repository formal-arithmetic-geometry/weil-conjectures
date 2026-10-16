/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import Sheaf.SixFunctors.ProEtale.BaseChange.SmoothBaseChangeComparisons
public import Sheaf.AlgebraicGeometry.ComparisonPullbackCoherence

/-! # The two ordinary comparison paths and their common derived endpoints

Source: blueprint comparison-square transport, expanded proof step 4.
(blueprint: stage3-proetale-comparison-square-paths)
-/

@[expose] public section

universe u
open CategoryTheory Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

section Paths

variable {A B B' C P Q Q' R : Type*}
  [Category A] [Category B] [Category B'] [Category C]
  [Category P] [Category Q] [Category Q'] [Category R]

/-- The comparison path passing through the first square.
Source: blueprint comparison-square transport, expanded proof step 4.
(blueprint: stage3-proetale-comparison-square-paths) -/
noncomputable def comparisonSquareEtalePathOfData
    (s : ComparisonSquareData A B B' C P Q Q' R) :
    (s.L₁ ⋙ s.L₂) ⋙ s.K₂ ≅ s.K₀ ⋙ (s.R₁' ⋙ s.R₂') :=
  Functor.isoWhiskerRight s.se s.K₂ ≪≫
    Functor.isoWhiskerLeft s.L₁' s.c₂' ≪≫ Functor.isoWhiskerRight s.c₁' s.R₂'

/-- The comparison path passing through the second square.
Source: blueprint comparison-square transport, expanded proof step 4.
(blueprint: stage3-proetale-comparison-square-paths) -/
noncomputable def comparisonSquareProEtalePathOfData
    (s : ComparisonSquareData A B B' C P Q Q' R) :
    (s.L₁ ⋙ s.L₂) ⋙ s.K₂ ≅ s.K₀ ⋙ (s.R₁' ⋙ s.R₂') :=
  Functor.isoWhiskerLeft s.L₁ s.c₂ ≪≫ Functor.isoWhiskerRight s.c₁ s.R₂ ≪≫
    Functor.isoWhiskerLeft s.K₀ s.sp

/-- Component coherence identifies the two specified ordinary paths.
Source: extensionality of natural transformations; blueprint transport step 4.
(blueprint: stage3-proetale-comparison-square-paths) -/
theorem comparisonSquarePaths_eq (s : ComparisonSquareData A B B' C P Q Q' R)
    (h : ∀ F, ComparisonSquareComponent s F) :
    comparisonSquareEtalePathOfData s = comparisonSquareProEtalePathOfData s := by
  apply Iso.ext
  apply NatTrans.ext
  funext F
  simpa only [comparisonSquareEtalePathOfData, comparisonSquareProEtalePathOfData,
    Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Category.assoc] using (h F).symm

end Paths

variable (Λ : Type (u + 1)) [CommRing Λ]
  {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- The ordinary path through the etale square, followed by its two comparison maps.
Source: blueprint comparison-square transport, step 4.
(blueprint: stage3-proetale-comparison-square-paths) -/
noncomputable def comparisonSquareEtalePath (cs : ChosenCartesianSquare g' f' f g) :
    (Etale.upperStar (ModuleCat.{u + 1} Λ) g ⋙
        Etale.upperStar (ModuleCat.{u + 1} Λ) f') ⋙ ν^*(X')[ModuleCat.{u + 1} Λ] ≅
      ν^*(Y)[ModuleCat.{u + 1} Λ] ⋙
        (upperStar (ModuleCat.{u + 1} Λ) f ⋙ upperStar (ModuleCat.{u + 1} Λ) g') :=
  comparisonSquareEtalePathOfData (comparisonSquareData (ModuleCat.{u + 1} Λ) g' f' f g cs)

/-- The ordinary path through the two comparison maps, followed by the pro-etale square.
Source: blueprint comparison-square transport, step 4.
(blueprint: stage3-proetale-comparison-square-paths) -/
noncomputable def comparisonSquareProEtalePath (cs : ChosenCartesianSquare g' f' f g) :
    (Etale.upperStar (ModuleCat.{u + 1} Λ) g ⋙
        Etale.upperStar (ModuleCat.{u + 1} Λ) f') ⋙ ν^*(X')[ModuleCat.{u + 1} Λ] ≅
      ν^*(Y)[ModuleCat.{u + 1} Λ] ⋙
        (upperStar (ModuleCat.{u + 1} Λ) f ⋙ upperStar (ModuleCat.{u + 1} Λ) g') :=
  comparisonSquareProEtalePathOfData (comparisonSquareData (ModuleCat.{u + 1} Λ) g' f' f g cs)

/-- The common source comparison from derivation of the ordinary triple composite.
Source: exact-functor composition comparisons, blueprint transport step 4.
(blueprint: stage3-proetale-comparison-square-paths) -/
noncomputable def comparisonSquareSourceIso (g : Y' ⟶ Y) (f' : X' ⟶ Y') :
    D((Etale.upperStar (ModuleCat.{u + 1} Λ) g ⋙
        Etale.upperStar (ModuleCat.{u + 1} Λ) f') ⋙ ν^*(X')[ModuleCat.{u + 1} Λ]) ≅
      D(Etale.upperStar (ModuleCat.{u + 1} Λ) g) ⋙
        D(Etale.upperStar (ModuleCat.{u + 1} Λ) f') ⋙ D(ν^*(X')[ModuleCat.{u + 1} Λ]) :=
  Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.isoWhiskerRight (Functor.mapDerivedCategoryCompIso _ _) _

/-- The common target comparison to the two total left derived pullbacks.
Source: exact-functor composition comparisons, blueprint transport step 4.
(blueprint: stage3-proetale-comparison-square-paths) -/
noncomputable def comparisonSquareTargetIso (g' : X' ⟶ X) (f : X ⟶ Y) :
    D(ν^*(Y)[ModuleCat.{u + 1} Λ] ⋙
        (upperStar (ModuleCat.{u + 1} Λ) f ⋙ upperStar (ModuleCat.{u + 1} Λ) g')) ≅
      D(ν^*(Y)[ModuleCat.{u + 1} Λ]) ⋙
        L(upperStar (ModuleCat.{u + 1} Λ) f) ⋙ L(upperStar (ModuleCat.{u + 1} Λ) g') :=
  Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.isoWhiskerLeft _ (Functor.mapDerivedCategoryCompIso _ _) ≪≫
    Functor.isoWhiskerLeft _
      (Functor.isoWhiskerRight
          (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) f).symm _ ≪≫
        Functor.isoWhiskerLeft _
          (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) g').symm)

/-- The exact derived image of one ordinary path with the common endpoint factors.
This is a concrete composite; its arguments retain the entire ordinary isomorphism.
Source: exact derivation and blueprint comparison-square transport, step 4.
(blueprint: stage3-proetale-comparison-square-paths) -/
noncomputable def comparisonSquareDerivedPath
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (e : (Etale.upperStar (ModuleCat.{u + 1} Λ) g ⋙
        Etale.upperStar (ModuleCat.{u + 1} Λ) f') ⋙ ν^*(X')[ModuleCat.{u + 1} Λ] ≅
      ν^*(Y)[ModuleCat.{u + 1} Λ] ⋙
        (upperStar (ModuleCat.{u + 1} Λ) f ⋙ upperStar (ModuleCat.{u + 1} Λ) g'))
    (M : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (DerivedCategory.Plus.ι ⋙ D(ν^*(X')[ModuleCat.{u + 1} Λ])).obj
        (D+(Etale.upperStar (ModuleCat.{u + 1} Λ) f').obj
          (D+(Etale.upperStar (ModuleCat.{u + 1} Λ) g).obj M)) ⟶
      L(upperStar (ModuleCat.{u + 1} Λ) g').obj
        (L(upperStar (ModuleCat.{u + 1} Λ) f).obj
          ((DerivedCategory.Plus.ι ⋙ D(ν^*(Y)[ModuleCat.{u + 1} Λ])).obj M)) :=
  (comparisonSquareSourceIso Λ g f').inv.app M.obj ≫
    (Functor.mapDerivedCategoryNatIso e).hom.app M.obj ≫
    (comparisonSquareTargetIso Λ g' f).hom.app M.obj

end AlgebraicGeometry.ProEtale
