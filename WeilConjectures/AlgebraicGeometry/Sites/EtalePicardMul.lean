/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import WeilConjectures.AlgebraicGeometry.Modules.HomSection
public import WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula
public import WeilConjectures.AlgebraicGeometry.Sites.EtalePicard
public import WeilConjectures.CategoryTheory.Sites.TorsorGluing

/-!
# Additivity of `L ↦ Isom(𝒪, L)`

The torsor `Isom(𝒪, L)` is trivialised over the Zariski opens where `L` has a generator, with
transition functions those of the generators.
-/

@[expose] public section

universe u

open CategoryTheory Opposite CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (A : modulesPseudofunctor.obj (.mk (op X)))
  [SheafOfModules.IsInvertible.{u, u, u} (A : X.Modules)]

set_option maxHeartbeats 1000000 in
-- the defeq checks through the small étale and pro-étale sites are slow
set_option backward.isDefEq.respectTransparency.types false in
/-- The difference of two trivialisations of `Isom(𝒪, A)` attached to generators `e₁`, `e₂` with
`e₂ = c • e₁` is the pullback of `c`. -/
lemma etaleIsoTorsor_sub_eq {V₁ V₂ Z : X.Etale} (a : Z ⟶ V₁) (b : Z ⟶ V₂) {U₁ U₂ : X.Opens}
    (e₁ : Γ((A : X.Modules), U₁)) (e₂ : Γ((A : X.Modules), U₂)) (he₁ : IsFreeGenerator e₁)
    (c : Γ(X, U₁ ⊓ U₂))
    (h : (A : X.Modules).presheaf.map (homOfLE inf_le_right).op e₂ =
      c • (A : X.Modules).presheaf.map (homOfLE inf_le_left).op e₁)
    (hU₁ : V₁.hom ⁻¹ᵁ U₁ = ⊤) (hU₂ : V₂.hom ⁻¹ᵁ U₂ = ⊤) (hZ₁ : Z.hom ⁻¹ᵁ U₁ = ⊤)
    (hZ₂ : Z.hom ⁻¹ᵁ U₂ = ⊤)
    (φ₁ : (modulesPseudofunctor.map V₁.hom.op.toLoc).toFunctor.obj (unitObj X) ⟶
      (modulesPseudofunctor.map V₁.hom.op.toLoc).toFunctor.obj A) (hφ₁ : IsIso φ₁)
    (hs₁ : homSection V₁.hom φ₁ = genSection V₁.hom e₁ hU₁)
    (φ₂ : (modulesPseudofunctor.map V₂.hom.op.toLoc).toFunctor.obj (unitObj X) ⟶
      (modulesPseudofunctor.map V₂.hom.op.toLoc).toFunctor.obj A) (hφ₂ : IsIso φ₂)
    (hs₂ : homSection V₂.hom φ₂ = genSection V₂.hom e₂ hU₂) :
    ((Additive.toMul ((etaleIsoTorsor A).sub
        ((etaleIsoTorsor A).sheaf.obj.map a.op (etaleIsoTorsorMk A φ₁ hφ₁))
        ((etaleIsoTorsor A).sheaf.obj.map b.op (etaleIsoTorsorMk A φ₂ hφ₂))).down :
          Γ(Z.left, ⊤)ˣ) : Γ(Z.left, ⊤)) =
      Z.hom.appLE (U₁ ⊓ U₂) ⊤ (preimage_inf_eq_top Z.hom hZ₁ hZ₂).ge c := by
  set x₁ := (etaleIsoTorsor A).sheaf.obj.map a.op (etaleIsoTorsorMk A φ₁ hφ₁)
  set x₂ := (etaleIsoTorsor A).sheaf.obj.map b.op (etaleIsoTorsorMk A φ₂ hφ₂)
  have hv := congrArg (etaleIsoTorsorVal A) ((etaleIsoTorsor A).sub_vadd x₁ x₂)
  rw [etaleIsoTorsorVal_vadd] at hv
  change smulMor _ _ ≫ pullHom (F := modulesPseudofunctor) φ₁ a.left Z.hom Z.hom
      (MorphismProperty.Over.w a) (MorphismProperty.Over.w a) =
    pullHom (F := modulesPseudofunctor) φ₂ b.left Z.hom Z.hom
      (MorphismProperty.Over.w b) (MorphismProperty.Over.w b) at hv
  have k := congrArg (homSection Z.hom (A := (A : X.Modules))) hv
  rw [homSection_pullHom V₂.hom b.left Z.hom _ e₂ hU₂ hZ₂ φ₂ hs₂] at k
  erw [homSection_smulHom_comp] at k
  rw [homSection_pullHom V₁.hom a.left Z.hom _ e₁ hU₁ hZ₁ φ₁ hs₁,
    genSection_eq_smul Z.hom e₁ e₂ c h hZ₁ hZ₂] at k
  have hg : IsFreeGenerator (genSection Z.hom e₁ hZ₁) := (he₁.pullback_unit_app Z.hom).map _
  have e := hg.smul_left_injective k
  refine (?_ : _ = _).trans (e.trans ?_)
  · exact (Scheme.presheaf_map_id_apply (X := Z.left) _ _).symm
  · rfl

end AlgebraicGeometry.Scheme.Modules
