/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D4
-/
module

public import Sheaf.Paper.PointAutomorphismRestrictionNatural
import all Sheaf.Paper.PointAutomorphismRestrictionNatural

/-! # The normalized ordinary point-restriction transformation

Restriction is linear after transporting scalars by the inverse canonical coefficient
map. The construction works at finite and completed coefficients without a characteristic
hypothesis and is natural on all module sheaves.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local irreducible] CategoryTheory.constantSheaf

universe t u
open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale

namespace WeilConjectures

attribute [local irreducible] integralCoefficientCommRingSheaf

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Ordinary point restriction has a unique natural linear lift with its prescribed values.
Source: inverse-image restriction coordinates, Stacks 00VE and 00WX
(blueprint: lem-trf-point-restriction-section-transformation).
Proof: scalar normalization says that restriction of a scalar constant equals the
inverse coefficient identification applied to that constant. Module restriction
therefore preserves scalar multiplication for the transported target action, as
well as addition. These linear maps are natural by presheaf-module naturality.
Their section values are precisely pointRestrictionRaw by construction. Any other
transformation with the same values agrees at each module and every element, so
module morphism and natural-transformation extensionality give uniqueness.
This includes the identity automorphism, zero modules and every coefficient index;
no characteristic condition is used. -/
theorem pointRestrictionSectionTransformation_existsUnique
    (k : Type t) [Field k] (g : Spec (.of k) ⟶ Spec (.of k)) [IsIso g] (a : Option ℕ) :
    ∃! σ : pointRestrictionSections l E k a ⟶
        pointRestrictionInverseImage l E g a ⋙ pointRestrictionSections l E k a,
      ∀ (M : SheafOfModules.{max u (t + 1)}
          (pointRestrictionRing l E (Spec (.of k)) a))
        (x : M.val.obj (op (ProEt.mk (𝟙 (Spec (.of k)))))),
        σ.app M x = pointRestrictionRaw l E g a M x := by
  have hn (b : pointRestrictionScalars.{t, u} l E a) :
      (pointRestrictionRing l E (Spec (.of k)) a).obj.map
          (pointRestrictionArrow g).op
          (pointRestrictionScalarAt l E (Spec (.of k)) a (ProEt.mk (𝟙 _)) b) =
        (inv (pointRestrictionCoefficientMap l E g a)).hom.app
          (op (ProEt.mk (𝟙 _)))
          (pointRestrictionScalarAt l E (Spec (.of k)) a (ProEt.mk (𝟙 _)) b) := by
    have h := congrArg
      ((inv (pointRestrictionCoefficientMap l E g a)).hom.app
        (op (ProEt.mk (𝟙 _))))
      (scalar_normalization l E g a b)
    simpa only [← RingCat.comp_apply, ← NatTrans.comp_app,
      ← ObjectProperty.FullSubcategory.comp_hom, IsIso.hom_inv_id,
      ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app, RingCat.id_apply] using h
  let σ : pointRestrictionSections l E k a ⟶
      pointRestrictionInverseImage l E g a ⋙
        pointRestrictionSections l E k a :=
    { app M := ModuleCat.ofHom
        (X := (pointRestrictionSections l E k a).obj M)
        (Y := ((pointRestrictionInverseImage l E g a ⋙
          pointRestrictionSections l E k a).obj M))
        (show (pointRestrictionSections l E k a).obj M →ₗ[
            pointRestrictionScalars.{t, u} l E a]
              ((pointRestrictionInverseImage l E g a ⋙
                pointRestrictionSections l E k a).obj M) from
        { toFun := pointRestrictionRaw l E g a M
          map_add' := (pointRestrictionRaw l E g a M).map_add
          map_smul' b x := by
            change M.val.map (pointRestrictionArrow g).op
              (pointRestrictionScalarAt l E (Spec (.of k)) a (ProEt.mk (𝟙 _)) b •
                (show M.val.obj (op (ProEt.mk (𝟙 _))) from x)) = _
            rw [M.val.map_smul, hn b]
            rfl })
      naturality M N f := by
        ext x
        exact (PresheafOfModules.naturality_apply f.val
          (pointRestrictionArrow g).op x).symm }
  refine ⟨σ, fun _ _ ↦ rfl, ?_⟩
  intro τ hτ
  ext M x
  exact hτ M x

end WeilConjectures
