/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Limits.DescentStalk
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Limits.DescentGeometry
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Limits.DescentColimit
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# The system `pᵢ^* pᵢ_* F` on geometric stalks

Let `X = lim Xᵢ` be a cofiltered limit of quasi-compact quasi-separated schemes with affine
transition maps and `F` an étale sheaf of `Λ`-modules on `X`. At every geometric point `x̄` of
`X`, the stalks of the counits `pᵢ^* pᵢ_* F ⟶ F` exhibit the stalk `F_x̄` as the colimit of the
stalks `(pᵢ^* pᵢ_* F)_x̄` (`AlgebraicGeometry.Etale.isColimitSheafFiberMapCoconeDescentCocone`).
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Etale

open Scheme

section LowerStarComp

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
variable {R S T : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ R)

/-- The components of the inverse of the composition isomorphism `(h₁)_* ⋙ (h₂)_* ≅ (h₁₂)_*`
of étale pushforwards are the restriction maps along the inverse pullback pasting
isomorphisms. -/
lemma lowerStarComp_inv_app_hom_app (h₁₂ : T ⟶ R) (hh₁₂ : h₁₂ = h₁ ≫ h₂)
    (G : Sheaf T.smallEtaleTopology A) (V : R.Etaleᵒᵖ) :
    ((Etale.lowerStarComp A h₁ h₂ h₁₂ hh₁₂).inv.app G).hom.app V =
      G.obj.map ((MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) h₁ h₂ h₁₂
        hh₁₂).inv.app V.unop).op := by
  simp only [Etale.lowerStarComp, Functor.sheafPushforwardContinuousComp']
  exact Category.comp_id _

end LowerStarComp

variable {Λ : Type (u + 1)} [CommRing Λ] {I : Type u} [Category.{u} I] [IsCofiltered I]
  {D : I ⥤ Scheme.{u}} {c : Cone D}

variable (hc : IsLimit c) [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
  [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
  (F : Sheaf c.pt.smallEtaleTopology (ModuleCat.{u + 1} Λ))
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ c.pt)

include hc in
/-- Every element of the stalk `F_x̄` comes from the stalk of some `pᵢ^* pᵢ_* F`. -/
lemma exists_sheafFiber_map_counit_eq (y : (pointSmallEtale x).sheafFiber (A := ModuleCat.{u + 1} Λ) |>.obj F) :
    ∃ (i : I) (z : (pointSmallEtale x).sheafFiber (A := ModuleCat.{u + 1} Λ) |>.obj
        ((c.π.app i)^*[ModuleCat.{u + 1} Λ].obj ((c.π.app i)_*[ModuleCat.{u + 1} Λ].obj F))),
      (pointSmallEtale x).sheafFiber.map
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (c.π.app i)).counit.app F) z = y := by
  obtain ⟨W, w, s, rfl⟩ := (pointSmallEtale x).toPresheafFiber_jointly_surjective y
  obtain ⟨i, V, b, hb, v, hv, φ, hφa, hφw⟩ :=
    exists_etale_descent_of_isLimit hc x W.hom w.left (CategoryTheory.Over.w w)
  let Vε : (D.obj i).Etale := MorphismProperty.Over.mk ⊤ b hb
  let vε : (pointSmallEtale (x ≫ c.π.app i)).fiber.obj Vε := CategoryTheory.Over.homMk v hv
  let φε : (c.π.app i).Etale.obj Vε ⟶ W := MorphismProperty.Over.homMk φ hφa
  have hpt : (pointSmallEtale x).fiber.map φε
      ((pointSmallEtaleFiberEtaleIso (c.π.app i) x).inv.app Vε vε) = w := by
    apply CategoryTheory.Over.OverMorphism.ext
    erw [pointSmallEtale_fiber_map_left]
    rw [pointSmallEtaleFiberEtaleIso_inv_app_left]
    exact hφw
  refine ⟨i, ((upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) (c.π.app i) x).app
    ((c.π.app i)_*[ModuleCat.{u + 1} Λ].obj F)).inv
    ((pointSmallEtale (x ≫ c.π.app i)).toPresheafFiber Vε vε
      ((c.π.app i)_*[ModuleCat.{u + 1} Λ].obj F).obj (F.obj.map φε.op s)), ?_⟩
  have h := ConcreteCategory.congr_hom (toPresheafFiber_comp_sheafFiber_map_counit
    (ModuleCat.{u + 1} Λ) (c.π.app i) x F Vε vε) (F.obj.map φε.op s)
  simp only [ConcreteCategory.comp_apply] at h
  refine h.trans ?_
  rw [← hpt]
  exact GrothendieckTopology.Point.toPresheafFiber_w_apply _ _ _ _ _

end AlgebraicGeometry.Etale
