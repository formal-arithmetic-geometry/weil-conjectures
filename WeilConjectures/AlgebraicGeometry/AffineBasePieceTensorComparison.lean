/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.RingTheory.TensorProduct.Maps

import WeilConjectures.AlgebraicGeometry.AffineBasePieceTensorBaseChange

/-!
# Tensor comparison after one affine base change

Source: Stacks Project, Limits, proof of Tag 01ZO (affine reduction),
Schemes, Tags 01JR and 01I4, and Morphisms, Tag 01T2.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
private theorem specModel {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) [LocallyOfFiniteType f] (R : CommRingCat.{u}) (q : Y ⟶ Spec R) :
    ∃ (aB : R →+* Γ(Y, ⊤)) (aC : R →+* Γ(X, ⊤)),
      let : Algebra R Γ(Y, ⊤) := aB.toAlgebra
      let : Algebra R Γ(X, ⊤) := aC.toAlgebra
      ∃ φ : Γ(Y, ⊤) →ₐ[R] Γ(X, ⊤), φ.FiniteType ∧
        Y.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom aB) = q ∧
        X.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom φ.toRingHom) =
          f ≫ Y.isoSpec.hom := by
  let aB : R →+* Γ(Y, ⊤) := ((Scheme.ΓSpecIso R).inv ≫ q.appTop).hom
  let aC : R →+* Γ(X, ⊤) := f.appTop.hom.comp aB
  let : Algebra R Γ(Y, ⊤) := aB.toAlgebra
  let : Algebra R Γ(X, ⊤) := aC.toAlgebra
  let φ : Γ(Y, ⊤) →ₐ[R] Γ(X, ⊤) :=
    { f.appTop.hom with commutes' := fun _ ↦ rfl }
  refine ⟨aB, aC, φ, ?_, ?_, ?_⟩
  · change f.appTop.hom.FiniteType
    simpa [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE] using
      f.finiteType_appLE (isAffineOpen_top Y) (isAffineOpen_top X)
        (by simp)
  · change Y.isoSpec.hom ≫ Spec.map ((Scheme.ΓSpecIso R).inv ≫ q.appTop) = q
    rw [Spec.map_comp]
    rw [← Category.assoc, Scheme.isoSpec_hom_naturality]
    simp [Scheme.isoSpec]
  · exact Scheme.isoSpec_hom_naturality f


set_option backward.isDefEq.respectTransparency false in
private theorem stageLft {S T : Scheme.{u}} (d : T ⟶ S)
    (X₀ Y₀ : Over S) (f₀ : X₀ ⟶ Y₀) [LocallyOfFiniteType f₀.left] :
    LocallyOfFiniteType (((Over.pullback d).map f₀).left) := by
  have hp : IsPullback (pullback.fst X₀.hom d)
      (((Over.pullback d).map f₀).left) f₀.left (pullback.fst Y₀.hom d) := by
    have hs : IsPullback (pullback.fst X₀.hom d)
        ((((Over.pullback d).map f₀).left) ≫ pullback.snd Y₀.hom d)
        (f₀.left ≫ Y₀.hom) d := by
      simpa [Over.pullback_map_left, Over.w] using
        (IsPullback.of_hasPullback X₀.hom d)
    exact hs.of_bot (by simp [Over.pullback_map_left])
      (IsPullback.of_hasPullback Y₀.hom d)
  exact MorphismProperty.of_isPullback hp inferInstance

/-- An affine finite-type base piece has a single tensor model under further base change.

Source: Stacks Project, Limits, proof of Tag 01ZO (affine reduction),
Schemes, Tags 01JR and 01I4, and Morphisms, Tag 01T2. -/
theorem exists_affine_base_piece_tensor_comparison
    {S T : Scheme.{u}} (d : T ⟶ S) [IsAffineHom d]
    (X₀ Y₀ : Over S) (f₀ : X₀ ⟶ Y₀) [LocallyOfFiniteType f₀.left]
    (haffine : IsAffineHom (((Over.pullback d).map f₀).left))
    (V : Y₀.left.Opens) (hV : IsAffineOpen V)
    (W : S.Opens) (hVW : V ≤ Y₀.hom ⁻¹ᵁ W)
    (R : CommRingCat.{u}) (e0 : (d ⁻¹ᵁ W).toScheme ≅ Spec R) :
    ∃ (B C : CommRingCat.{u}) (aB : R →+* B) (aC : R →+* C),
      letI : Algebra R B := aB.toAlgebra
      letI : Algebra R C := aC.toAlgebra
      ∃ φ : B →ₐ[R] C, φ.FiniteType ∧
        ∀ (L : Scheme.{u}) (t : L ⟶ T) (A : CommRingCat.{u}) (aA : Algebra R A),
          letI := aA
          ∀ (e : (t ⁻¹ᵁ (d ⁻¹ᵁ W)).toScheme ≅ Spec A),
            t.resLE (d ⁻¹ᵁ W) _ le_rfl ≫ e0.hom =
              e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)) →
            Nonempty
              (Arrow.mk ((((Over.pullback (t ≫ d)).map f₀).left) ∣_
                ((pullback.fst Y₀.hom (t ≫ d)) ⁻¹ᵁ V)) ≅
                Arrow.mk (Spec.map (CommRingCat.ofHom
                  (Algebra.TensorProduct.map (AlgHom.id R A) φ).toRingHom)))  := by
  let fT := ((Over.pullback d).map f₀).left
  let VT := (pullback.fst Y₀.hom d) ⁻¹ᵁ V
  let : IsAffineHom fT := haffine
  let : LocallyOfFiniteType fT := stageLft d X₀ Y₀ f₀
  let : IsAffineHom (pullback.fst Y₀.hom d) :=
    MorphismProperty.pullback_fst Y₀.hom d inferInstance
  have hVT : IsAffineOpen VT := hV.preimage (pullback.fst Y₀.hom d)
  have hUT : IsAffineOpen (fT ⁻¹ᵁ VT) := hVT.preimage fT
  let : IsAffine VT.toScheme := hVT
  let : IsAffine (fT ⁻¹ᵁ VT).toScheme := hUT
  have hVW' : VT ≤ (pullback.snd Y₀.hom d) ⁻¹ᵁ (d ⁻¹ᵁ W) := by
    rw [← Scheme.Hom.comp_preimage, ← pullback.condition, Scheme.Hom.comp_preimage]
    exact (pullback.fst Y₀.hom d).preimage_mono hVW
  let q := (pullback.snd Y₀.hom d).resLE (d ⁻¹ᵁ W) VT hVW'
  obtain ⟨aB, aC, φ, hφ, hB, hC⟩ := specModel (fT ∣_ VT) R (q ≫ e0.hom)
  let : Algebra R Γ(VT.toScheme, ⊤) := aB.toAlgebra
  let : Algebra R Γ((fT ⁻¹ᵁ VT).toScheme, ⊤) := aC.toAlgebra
  refine ⟨Γ(VT.toScheme, ⊤), Γ((fT ⁻¹ᵁ VT).toScheme, ⊤), aB, aC, φ, hφ, ?_⟩
  exact affine_base_piece_tensor_base_change_instance d X₀ Y₀ f₀ V W R _ _ aB aC e0 q
    (Scheme.Hom.resLE_comp_ι _ _) VT.toScheme.isoSpec (fT ⁻¹ᵁ VT).toScheme.isoSpec
    φ hB hC

end AlgebraicGeometry
