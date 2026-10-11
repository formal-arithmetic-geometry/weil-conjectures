module

public import WeilConjectures.SixFunctors.ProEtale.Derived.UpperStarMonoidal

@[expose] public section

universe v u v' u'

open CategoryTheory Limits MonoidalCategory

variable (C : Type u) [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [SymmetricCategory C]
  [HasDerivedCategory.{v} C] [Abelian.HasFunctorialFlatResolution C]
variable (D : Type u') [Category.{v'} D] [Abelian D] [IsGrothendieckAbelian.{v'} D]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [SymmetricCategory D]
  [HasDerivedCategory.{v'} D] [Abelian.HasFunctorialFlatResolution D]

variable (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

noncomputable example : DerivedCategory C ⥤ DerivedCategory D := F.leftDerivedFunctor
noncomputable example : DerivedCategory C ⥤ DerivedCategory C ⥤ DerivedCategory C := curriedTensor _
