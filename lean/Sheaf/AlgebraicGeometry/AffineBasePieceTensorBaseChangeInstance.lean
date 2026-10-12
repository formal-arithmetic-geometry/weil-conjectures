module
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.RingTheory.TensorProduct.Maps
@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
/-- The fixed test-object affine tensor base-change construction used in the affine reduction.

Source: Stacks Project, Schemes, Tags 01JR and 01I4; Limits, proof of Tag 01ZO.
(blueprint: lem-weil-pbc-affine-base-piece-tensor-base-change-instance).

The proof pastes the two pullback squares with the open restriction squares, transports
both restricted fibre products through the displayed affine charts, and applies the
universal property of the tensor-product pullback. -/
theorem affine_base_piece_tensor_base_change_instance
    {S T : Scheme.{u}} (d : T ⟶ S)
    (X₀ Y₀ : Over S) (f₀ : X₀ ⟶ Y₀)
    (V : Y₀.left.Opens) (W : S.Opens)
    (R B C : CommRingCat.{u}) (aB : R →+* B) (aC : R →+* C)
    (e0 : (d ⁻¹ᵁ W).toScheme ≅ Spec R)
    (q : ((pullback.fst Y₀.hom d) ⁻¹ᵁ V).toScheme ⟶ (d ⁻¹ᵁ W).toScheme)
    (hq : q ≫ (d ⁻¹ᵁ W).ι =
      ((pullback.fst Y₀.hom d) ⁻¹ᵁ V).ι ≫ pullback.snd Y₀.hom d)
    (eB : ((pullback.fst Y₀.hom d) ⁻¹ᵁ V).toScheme ≅ Spec B)
    (eC : ((((Over.pullback d).map f₀).left) ⁻¹ᵁ
      ((pullback.fst Y₀.hom d) ⁻¹ᵁ V)).toScheme ≅ Spec C)
    : letI : Algebra R B := aB.toAlgebra
      letI : Algebra R C := aC.toAlgebra
      ∀ (φ : B →ₐ[R] C),
        eB.hom ≫ Spec.map (CommRingCat.ofHom aB) = q ≫ e0.hom →
        eC.hom ≫ Spec.map (CommRingCat.ofHom φ.toRingHom) =
          ((((Over.pullback d).map f₀).left) ∣_
            ((pullback.fst Y₀.hom d) ⁻¹ᵁ V)) ≫ eB.hom →
        ∀ (L : Scheme.{u}) (t : L ⟶ T) (A : CommRingCat.{u})
          (aA : Algebra R A) (e : (t ⁻¹ᵁ (d ⁻¹ᵁ W)).toScheme ≅ Spec A),
          t.resLE (d ⁻¹ᵁ W) _ le_rfl ≫ e0.hom =
            e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)) →
          Nonempty
            (Arrow.mk ((((Over.pullback (t ≫ d)).map f₀).left) ∣_
              ((pullback.fst Y₀.hom (t ≫ d)) ⁻¹ᵁ V)) ≅
              Arrow.mk (Spec.map (CommRingCat.ofHom
                (Algebra.TensorProduct.map (AlgHom.id R A) φ).toRingHom))) := by
  sorry
end AlgebraicGeometry
