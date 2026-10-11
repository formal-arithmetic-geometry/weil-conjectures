/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import Mathlib.CategoryTheory.Localization.Adjunction
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar

/-!
# Extension by zero along an étale morphism

For an étale morphism `f : V ⟶ U`, not necessarily a monomorphism, the lower shriek
`f_! : Sh(V_ét) ⥤ Sh(U_ét)` is the left adjoint of the restriction along the localization
functor `V_ét ⥤ U_ét`, which computes the pullback `f^*`. Its presheaf-level part is the
pointwise left Kan extension, which at `W` is the direct sum over the lifts of `W` through `f`
(`AlgebraicGeometry.SmallSite.preservesFiniteLimits_op_lan_overMap_of_isGrothendieckAbelian`),
so `f_!` is exact, and it induces a left adjoint of `D(f^*)` on derived categories.

## Main definitions

- `AlgebraicGeometry.Etale.etaleLowerShriek`: the lower shriek `f_!` along an étale `f`.
- `AlgebraicGeometry.Etale.etaleLowerShriekUpperStarAdjunction`: `f_! ⊣ f^*`.
- `AlgebraicGeometry.Etale.derivedEtaleLowerShriekUpperStarAdjunction`: `D(f_!) ⊣ D(f^*)`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]

variable {V U : Scheme.{u}} (f : V ⟶ U) (h : Etale f)

/-- The lower shriek `f_!` along an étale morphism `f : V ⟶ U`: left Kan extension on presheaves
along the localization functor followed by sheafification. -/
noncomputable def Etale.etaleLowerShriek :
    Sheaf V.smallEtaleTopology A ⥤ Sheaf U.smallEtaleTopology A :=
  Functor.sheafPullbackConstruction.sheafPullback (MorphismProperty.Over.map ⊤ h) A
    (V.smallGrothendieckTopology @Etale) (U.smallGrothendieckTopology @Etale)

/-- The lower shriek along an étale morphism is left adjoint to the restriction along the
localization functor. -/
noncomputable def Etale.etaleLowerShriekAdjunction :
    Etale.etaleLowerShriek A f h ⊣ Etale.localizationRestriction A f h :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (MorphismProperty.Over.map ⊤ h)
    A (V.smallGrothendieckTopology @Etale) (U.smallGrothendieckTopology @Etale)

/-- The lower shriek along an étale morphism is left adjoint to the pullback `f^*`. -/
noncomputable def Etale.etaleLowerShriekUpperStarAdjunction :
    Etale.etaleLowerShriek A f h ⊣ (f)^*[A] :=
  (Etale.etaleLowerShriekAdjunction A f h).ofNatIsoRight
    (Etale.upperStarIsoLocalizationRestriction A f h).symm

/-- The lower shriek along an étale morphism is left exact: pointwise on presheaves it is a
direct sum of evaluations, and sheafification is left exact. -/
instance Etale.preservesFiniteLimits_etaleLowerShriek :
    PreservesFiniteLimits (Etale.etaleLowerShriek A f h) := by
  have : PreservesFiniteLimits ((MorphismProperty.Over.map ⊤ h).op.lan :
      (V.Etaleᵒᵖ ⥤ A) ⥤ U.Etaleᵒᵖ ⥤ A) :=
    SmallSite.preservesFiniteLimits_op_lan_overMap_of_isGrothendieckAbelian A h
  unfold Etale.etaleLowerShriek Functor.sheafPullbackConstruction.sheafPullback
  infer_instance

instance : PreservesFiniteColimits (Etale.etaleLowerShriek A f h) :=
  have := (Etale.etaleLowerShriekAdjunction A f h).leftAdjoint_preservesColimits
  inferInstance

instance : (Etale.etaleLowerShriek A f h).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The derived adjunction `D(f_!) ⊣ D(f^*)` for an étale morphism `f`, both functors being
exact. -/
noncomputable def Etale.derivedEtaleLowerShriekUpperStarAdjunction :
    (Etale.etaleLowerShriek A f h).mapDerivedCategory ⊣ D((f)^*[A]) :=
  let _ : CatCommSq ((Etale.etaleLowerShriek A f h).mapHomologicalComplex (ComplexShape.up ℤ))
      DerivedCategory.Q DerivedCategory.Q (Etale.etaleLowerShriek A f h).mapDerivedCategory :=
    ⟨(Etale.etaleLowerShriek A f h).mapDerivedCategoryFactors.symm⟩
  let _ : CatCommSq (((f)^*[A]).mapHomologicalComplex (ComplexShape.up ℤ))
      DerivedCategory.Q DerivedCategory.Q D((f)^*[A]) :=
    ⟨((f)^*[A]).mapDerivedCategoryFactors.symm⟩
  ((Etale.etaleLowerShriekUpperStarAdjunction A f h).mapHomologicalComplex
    (ComplexShape.up ℤ)).localization DerivedCategory.Q (HomologicalComplex.quasiIso _ _)
      DerivedCategory.Q (HomologicalComplex.quasiIso _ _) _ _

end AlgebraicGeometry
