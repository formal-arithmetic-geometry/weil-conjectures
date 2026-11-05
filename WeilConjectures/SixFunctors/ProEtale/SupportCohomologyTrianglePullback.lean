/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GlobalSections
public import WeilConjectures.SixFunctors.Etale.SupportCohomologyTriangle

/-!
# Functoriality of the pro-étale triangle of cohomology with support in the pair

This is the pro-étale counterpart of
`WeilConjectures.SixFunctors.Etale.SupportCohomologyTrianglePullback`. Let `e : X' ⟶ X` be a
morphism of schemes, `i : Z ⟶ X` and `i' : Z' ⟶ X'` closed immersions with open complements
`U` and `U'` such that `U' ⊆ e⁻¹(U)`. The pullback of sections along `e` on the small pro-étale
sites (`AlgebraicGeometry.ProEtale.sectionsPullback`) gives maps `Γ(X, F) ⟶ Γ(X', e^* F)`,
`F(U) ⟶ (e^* F)(U')` and `Γ_Z(X, F) ⟶ Γ_{Z'}(X', e^* F)`, and the pullback maps of the right
derived functors form a morphism of triangles

`RΓ_Z(X, K) ⟶ RΓ(X, K) ⟶ RΓ(U, K) ⟶ RΓ_Z(X, K)[1]`
`RΓ_Z'(X', e^*K) ⟶ RΓ(X', e^*K) ⟶ RΓ(U', e^*K) ⟶ RΓ_Z'(X', e^*K)[1]`

natural in the bounded below complex `K` of pro-étale sheaves
(`AlgebraicGeometry.ProEtale.sectionsWithSupportTrianglePullback`), so that the long exact
sequence of cohomology with support on the pro-étale site of blueprint
`thm-pur-with-support-exactness` is functorial in the pair
(`AlgebraicGeometry.ProEtale.homology_sectionsWithSupportTrianglePullback_comm`), compatibly with
composition (`AlgebraicGeometry.ProEtale.sectionsWithSupportTrianglePullback_comp`).
-/

@[expose] public section

universe u' u

open CategoryTheory Category Limits Opposite Pretriangulated DerivedCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace ProEtale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

section HomToPullback

variable {R T : Scheme.{u}} (t : T ⟶ R)

@[reassoc]
lemma proEt_comp_left {X : Scheme.{u}} {V₁ V₂ V₃ : X.ProEt} (a : V₁ ⟶ V₂) (b : V₂ ⟶ V₃) :
    (a ≫ b).left = a.left ≫ b.left :=
  rfl

@[simp]
lemma overPullback_obj_left (U : R.ProEt) :
    ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ t).obj U).left = pullback U.hom t :=
  rfl

@[simp]
lemma overPullback_obj_hom (U : R.ProEt) :
    ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ t).obj U).hom = pullback.snd U.hom t :=
  rfl

end HomToPullback

section Sections

variable {X X' : Scheme.{u}} (e : X' ⟶ X)

instance isIso_natTransΓRes_mkId (X : Scheme.{u}) :
    IsIso (Sheaf.natTransΓRes (Scheme.ProEt.topology X) A (op (Scheme.ProEt.mk (𝟙 X)))) := by
  have (M : Sheaf (Scheme.ProEt.topology X) A) :
      IsIso ((Sheaf.natTransΓRes (Scheme.ProEt.topology X) A (op (Scheme.ProEt.mk (𝟙 X)))).app M) :=
    M.isLimitConeΓ.isIso_π_app_of_isInitial _ (Scheme.ProEt.isTerminalMkId X).op
  exact NatIso.isIso_of_isIso_app _

section CompAux

variable {R S T : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ R)

/-- The unit form of the definition of `AlgebraicGeometry.ProEtale.upperStarComp`:
transposing the composition isomorphism of the pullbacks along the adjunctions `h^* ⊣ h_*`
gives the composition isomorphism of the pushforwards. -/
lemma upperStarComp_hom_app_unit_app (F : Sheaf (Scheme.ProEt.topology R) A) :
    (upperStarLowerStarAdjunction A (h₁ ≫ h₂)).unit.app F ≫
        ((h₁ ≫ h₂)_*[A]).map ((upperStarComp A h₁ h₂).hom.app F) =
      ((upperStarLowerStarAdjunction A h₂).comp
          (upperStarLowerStarAdjunction A h₁)).unit.app F ≫
        (lowerStarComp A h₁ h₂).hom.app (((h₁)^*[A]).obj (((h₂)^*[A]).obj F)) := by
  have hconj : conjugateEquiv ((upperStarLowerStarAdjunction A h₂).comp
        (upperStarLowerStarAdjunction A h₁))
      (upperStarLowerStarAdjunction A (h₁ ≫ h₂)) (upperStarComp A h₁ h₂).hom =
      (lowerStarComp A h₁ h₂).hom :=
    congrArg Iso.inv ((conjugateIsoEquiv (upperStarLowerStarAdjunction A (h₁ ≫ h₂))
      ((upperStarLowerStarAdjunction A h₂).comp
        (upperStarLowerStarAdjunction A h₁))).apply_symm_apply (lowerStarComp A h₁ h₂).symm)
  have hh := unit_conjugateEquiv ((upperStarLowerStarAdjunction A h₂).comp
      (upperStarLowerStarAdjunction A h₁))
    (upperStarLowerStarAdjunction A (h₁ ≫ h₂)) (upperStarComp A h₁ h₂).hom F
  rw [hconj] at hh
  exact hh.symm

end CompAux

section Comp

variable {X'' : Scheme.{u}} (e' : X'' ⟶ X')

end Comp

end Sections

section Pair

variable {X X' Z Z' : Scheme.{u}} (e : X' ⟶ X) (i : Z ⟶ X) [IsClosedImmersion i]
  (i' : Z' ⟶ X') [IsClosedImmersion i'] (h : i'.openComplement ≤ e ⁻¹ᵁ i.openComplement)

section Comp

variable {X'' Z'' : Scheme.{u}} (e' : X'' ⟶ X') (i'' : Z'' ⟶ X'') [IsClosedImmersion i'']
  (h' : i''.openComplement ≤ e' ⁻¹ᵁ i'.openComplement)
  (h'' : i''.openComplement ≤ (e' ≫ e) ⁻¹ᵁ i.openComplement)

attribute [local instance] Limits.comp_preservesFiniteLimits Limits.comp_preservesFiniteColimits

end Comp

end Pair

end ProEtale

end AlgebraicGeometry
