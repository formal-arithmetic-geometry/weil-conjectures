/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Coseparator
public import Mathlib.CategoryTheory.Adjunction.AdjointFunctorTheorems
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension
public import WeilConjectures.CategoryTheory.Monoidal.Mod.Cofree
public import WeilConjectures.SixFunctors.ProEtale.Adic.BaseChange
public import WeilConjectures.SixFunctors.ProEtale.Adic.InternalHom

/-!
# Extension by zero along a weakly étale morphism of `ℓ`-adic sheaves

For a weakly étale `j : U ⟶ X`, the pullback `j^*` of pro-étale sheaves is the restriction along
the localization functor `U_proét ⥤ X_proét`. It has a left adjoint `j_!`
(`AlgebraicGeometry.ProEtale.weaklyEtaleLowerShriek`), the left Kan extension on presheaves
followed by sheafification. The left Kan extension is pointwise a direct sum over the
factorizations through `j`, so `j_!` is exact.

On sheaves of `ℚ̄_ℓ,X`-modules, `j^*` preserves limits, hence has a left adjoint
(`AlgebraicGeometry.ProEtale.adicWeaklyEtaleLowerShriek`). Its underlying sheaf is the extension
by zero of the underlying sheaf (`AlgebraicGeometry.ProEtale.adicWeaklyEtaleLowerShriekForgetIso`):
the right adjoints of both composites are the cofree modules followed by `j^*`, and the pullback
of a cofree module is cofree, `j^*` commuting with internal homs. Hence the extension by zero is
exact, so `j^*` preserves K-injective complexes and the base change isomorphism derives:
`j^* ∘ Rg''_* ≅ Rg'_* ∘ j'^*` for weakly étale `j`
(`AlgebraicGeometry.ProEtale.adicDerivedBaseChangeIsoOfWeaklyEtale`).
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale

section Sheaf

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  {U X : Scheme.{u}} (j : U ⟶ X) [WeaklyEtale j]

/-- The extension by zero `j_!` along a weakly étale morphism `j` on sheaves for the small
pro-étale sites: the left Kan extension along the localization functor on presheaves followed by
sheafification. -/
noncomputable def weaklyEtaleLowerShriek :
    Sheaf (Scheme.ProEt.topology U) A ⥤ Sheaf (Scheme.ProEt.topology X) A :=
  Functor.sheafPullbackConstruction.sheafPullback
    (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)) A
    (Scheme.ProEt.topology U) (Scheme.ProEt.topology X)

/-- The adjunction `j_! ⊣ j^*` along a weakly étale morphism `j`. -/
noncomputable def weaklyEtaleLowerShriekUpperStarAdjunction :
    weaklyEtaleLowerShriek A j ⊣ (j)^*[A] :=
  (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)) A
    (Scheme.ProEt.topology U) (Scheme.ProEt.topology X)).ofNatIsoRight
    (upperStarIsoLocalizationRestriction A j inferInstance).symm

/-- **The extension by zero along a weakly étale morphism is left exact**: the left Kan extension
along the localization functor is pointwise a direct sum, and sheafification is left exact. -/
instance preservesFiniteLimits_weaklyEtaleLowerShriek :
    PreservesFiniteLimits (weaklyEtaleLowerShriek A j) := by
  have : PreservesFiniteLimits
      ((MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)).op.lan :
        (U.ProEtᵒᵖ ⥤ A) ⥤ X.ProEtᵒᵖ ⥤ A) :=
    SmallSite.preservesFiniteLimits_op_lan_overMap_of_isGrothendieckAbelian A _
  have : PreservesFiniteLimits
      ((MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)).op.lan ⋙
        presheafToSheaf (Scheme.ProEt.topology X) A) :=
    comp_preservesFiniteLimits _ _
  exact comp_preservesFiniteLimits (sheafToPresheaf _ A) _

instance : PreservesLimits ((j)^*[A]) :=
  (weaklyEtaleLowerShriekUpperStarAdjunction A j).rightAdjoint_preservesLimits

end Sheaf

section Adic

variable {l : ℕ} [Fact l.Prime] {U X : Scheme.{u}} (j : U ⟶ X) [WeaklyEtale j]

instance : PreservesLimits ((j)^*ᵃ[l]) := by
  have : PreservesLimits ((j)^*ᵃ[l] ⋙ AdicSheaf.forget U) :=
    inferInstanceAs (PreservesLimits (AdicSheaf.forget X ⋙ (j)^*[WeilCoefficients.{u} l]))
  exact preservesLimits_of_reflects_of_preserves _ (AdicSheaf.forget U)

instance : (j)^*ᵃ[l].IsRightAdjoint :=
  isRightAdjoint_of_preservesLimits_of_isCoseparating (D := AdicSheaf l X)
    (isCoseparator_coseparator (AdicSheaf l X)) (j)^*ᵃ[l]

variable (l) in
/-- The extension by zero `j_!` of sheaves of modules over the constant `ℓ`-adic sheaves along a
weakly étale morphism `j`: the left adjoint of the pullback `j^*`. -/
noncomputable def adicWeaklyEtaleLowerShriek : AdicSheaf l U ⥤ AdicSheaf l X :=
  (j)^*ᵃ[l].leftAdjoint

variable (l) in
/-- The adjunction `j_! ⊣ j^*` on sheaves of `ℚ̄_ℓ`-modules along a weakly étale morphism. -/
noncomputable def adicWeaklyEtaleLowerShriekAdjunction :
    adicWeaklyEtaleLowerShriek l j ⊣ (j)^*ᵃ[l] :=
  Adjunction.ofIsRightAdjoint _

instance : (adicWeaklyEtaleLowerShriek l j).IsLeftAdjoint :=
  (adicWeaklyEtaleLowerShriekAdjunction l j).isLeftAdjoint

instance : (adicWeaklyEtaleLowerShriek l j).Additive :=
  (adicWeaklyEtaleLowerShriekAdjunction l j).left_adjoint_additive

attribute [local instance] Sheaf.symmetricCategory in
/-- The pullback of a cofree `ℚ̄_ℓ,X`-module along a weakly étale morphism is cofree: `j^*`
commutes with internal homs out of `ℚ̄_ℓ,X`. -/
noncomputable def adicUpperStarCofreeIso :
    Mod.cofree (adicConstantSheaf l X) ⋙ (j)^*ᵃ[l] ≅
      (j)^*[WeilCoefficients.{u} l] ⋙ Mod.cofree (adicConstantSheaf l U) :=
  have := isIso_ihomComparison_upperStar (WeilCoefficients.{u} l) j (adicConstantSheaf l X)
  Adjunction.modLeftCofreeIso (upperStarLowerStarAdjunction (WeilCoefficients.{u} l) j)
    (adicConstantSheafToLowerStar l j)

variable (l) in
/-- The underlying sheaf of the extension by zero `j_! M` of a sheaf of `ℚ̄_ℓ,U`-modules is the
extension by zero of the underlying sheaf of `M`: both functors are left adjoint to the cofree
module functor followed by `j^*`. -/
noncomputable def adicWeaklyEtaleLowerShriekForgetIso :
    adicWeaklyEtaleLowerShriek l j ⋙ AdicSheaf.forget X ≅
      AdicSheaf.forget U ⋙ weaklyEtaleLowerShriek (WeilCoefficients.{u} l) j :=
  ((adicWeaklyEtaleLowerShriekAdjunction l j).comp
      (Mod.forgetCofreeAdjunction (adicConstantSheaf l X))).leftAdjointUniq
    (((Mod.forgetCofreeAdjunction (adicConstantSheaf l U)).comp
      (weaklyEtaleLowerShriekUpperStarAdjunction (WeilCoefficients.{u} l) j)).ofNatIsoRight
      (adicUpperStarCofreeIso j).symm)

/-- **The extension by zero along a weakly étale morphism is exact.** On underlying sheaves it is
the extension by zero of sheaves, which is left exact. -/
instance : PreservesFiniteLimits (adicWeaklyEtaleLowerShriek l j) := by
  have : PreservesFiniteLimits (adicWeaklyEtaleLowerShriek l j ⋙ AdicSheaf.forget X) :=
    preservesFiniteLimits_of_natIso (adicWeaklyEtaleLowerShriekForgetIso l j).symm
  exact preservesFiniteLimits_of_reflects_of_preserves _ (AdicSheaf.forget X)

/-- The pullback along a weakly étale morphism preserves K-injective complexes, its left adjoint,
the extension by zero, being exact. -/
instance preservesKInjectiveComplexes_adicUpperStar : (j)^*ᵃ[l].PreservesKInjectiveComplexes :=
  (adicWeaklyEtaleLowerShriekAdjunction l j).preservesKInjectiveComplexes

end Adic

section BaseChange

variable (l : ℕ) [Fact l.Prime] {U' U Z' Z : Scheme.{u}} {g' : U' ⟶ U} {j' : U' ⟶ Z'}
  {j : U ⟶ Z} {g'' : Z' ⟶ Z} [WeaklyEtale j] [WeaklyEtale j']

/-- **Weakly étale base change for the derived pushforward of `ℓ`-adic sheaves**: for a cartesian
square with `j` (hence `j'`) weakly étale, `j^* ∘ Rg''_* ≅ Rg'_* ∘ j'^*`. -/
noncomputable def adicDerivedBaseChangeIsoOfWeaklyEtale (hsq : IsPullback g' j' j g'') :
    (g'')_*ᵃ[l].rightDerivedFunctor ⋙ (j)^*ᵃ[l].mapDerivedCategory ≅
      (j')^*ᵃ[l].mapDerivedCategory ⋙ (g')_*ᵃ[l].rightDerivedFunctor :=
  have := isIso_adicBaseChangeMap_of_isPullback l hsq
  (Functor.rightDerivedFunctorCompMapDerivedCategoryIso (g'')_*ᵃ[l] (j)^*ᵃ[l]).symm ≪≫
    Functor.rightDerivedFunctorNatIso (asIso (adicBaseChangeMap l hsq.toCommSq)) ≪≫
    Functor.rightDerivedFunctorCompIso (j')^*ᵃ[l] (g')_*ᵃ[l] ≪≫
    Functor.isoWhiskerRight (j')^*ᵃ[l].rightDerivedFunctorIsoMapDerivedCategory
      (g')_*ᵃ[l].rightDerivedFunctor

end BaseChange

end AlgebraicGeometry.ProEtale
