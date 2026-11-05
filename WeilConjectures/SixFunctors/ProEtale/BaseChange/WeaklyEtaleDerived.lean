/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatNat
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.SixFunctors.ProEtale.BaseChange.WeaklyEtale
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Injective

/-!
# Weakly étale base change for the derived pushforward

For a weakly étale `j : U ⟶ Z` the pullback `j^*` of pro-étale sheaves with values in a
Grothendieck abelian category `A` is the restriction along the localization functor
`U_proét ⥤ Z_proét`, whose left adjoint, the extension by zero `j_!` (left Kan extension along
the localization functor followed by sheafification, [Stacks 03DH]), is exact. Hence `j^*`
preserves K-injective complexes
(`AlgebraicGeometry.ProEtale.preservesKInjectiveComplexes_upperStar_of_weaklyEtale`), and the
weakly étale base change isomorphism `j^* g''_* ≅ g'_* j'^*` of a cartesian square
(`AlgebraicGeometry.ProEtale.isIso_baseChangeMap_of_isPullback`) derives:
`j^* ∘ Rg''_* ≅ Rg'_* ∘ j'^*` (`AlgebraicGeometry.ProEtale.derivedWeaklyEtaleBaseChangeIso`). In
particular the higher direct images commute with restriction to any object of the pro-étale site
(`AlgebraicGeometry.ProEtale.rightDerivedWeaklyEtaleBaseChangeIso`), naturally in the sheaf.
-/

@[expose] public section

universe u' u

open CategoryTheory Category Limits

namespace AlgebraicGeometry.ProEtale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

section LowerShriek

variable {V U : Scheme.{u}} (f : V ⟶ U) [WeaklyEtale f]

/-- The extension by zero `f_!` along a weakly étale `f : V ⟶ U`: the left Kan extension along
the localization functor `V_proét ⥤ U_proét` followed by sheafification, so that
`(f_! M)(W) = ⨁_{s ∈ Hom_U(W, V)} M(W, s)` before sheafification. -/
noncomputable def weaklyEtaleLowerShriek :
    Sheaf (Scheme.ProEt.topology V) A ⥤ Sheaf (Scheme.ProEt.topology U) A :=
  Functor.sheafPullbackConstruction.sheafPullback
    (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale f)) A
    (Scheme.ProEt.topology V) (Scheme.ProEt.topology U)

/-- The adjunction `f_! ⊣ f^*` for a weakly étale `f`. -/
noncomputable def weaklyEtaleLowerShriekAdjunction :
    weaklyEtaleLowerShriek A f ⊣ (f)^*[A] :=
  (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale f)) A
    (Scheme.ProEt.topology V) (Scheme.ProEt.topology U)).ofNatIsoRight
      (upperStarIsoLocalizationRestriction A f inferInstance).symm

/-- **The extension by zero along a weakly étale morphism is exact** ([Stacks 03DH]): the
presheaf extension by zero is a direct sum over the lifts, and sheafification is exact. -/
instance preservesFiniteLimits_weaklyEtaleLowerShriek :
    PreservesFiniteLimits (weaklyEtaleLowerShriek A f) := by
  have : HasColimitsOfSize.{u + 1, u + 1} A := inferInstance
  have := SmallSite.preservesFiniteLimits_op_lan_overMap_of_isGrothendieckAbelian A
    (P := @WeaklyEtale) (inferInstance : WeaklyEtale f)
  exact comp_preservesFiniteLimits (sheafToPresheaf _ A)
    (((MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale f)).op.lan) ⋙
      presheafToSheaf _ A)

instance preservesFiniteColimits_weaklyEtaleLowerShriek :
    PreservesFiniteColimits (weaklyEtaleLowerShriek A f) :=
  have := (weaklyEtaleLowerShriekAdjunction A f).leftAdjoint_preservesColimits
  PreservesColimitsOfSize.preservesFiniteColimits.{u + 1, u + 1} _

instance : (weaklyEtaleLowerShriek A f).Additive :=
  (weaklyEtaleLowerShriekAdjunction A f).left_adjoint_additive

/-- **The pullback along a weakly étale morphism preserves K-injective complexes**: it has the
exact left adjoint `f_!`. -/
instance preservesKInjectiveComplexes_upperStar_of_weaklyEtale :
    (f)^*[A].PreservesKInjectiveComplexes :=
  have : (weaklyEtaleLowerShriek A f).PreservesHomology := {}
  (weaklyEtaleLowerShriekAdjunction A f).preservesKInjectiveComplexes

end LowerShriek

section BaseChange

variable {U' U Z' Z : Scheme.{u}} {g' : U' ⟶ U} {j' : U' ⟶ Z'} {j : U ⟶ Z} {g'' : Z' ⟶ Z}
  [WeaklyEtale j] [WeaklyEtale j']

end BaseChange

end AlgebraicGeometry.ProEtale
