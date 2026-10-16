/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.RingTheory.TensorProduct.Maps
import WeilConjectures.AlgebraicGeometry.AffineBasePieceTensorBaseChangeInstance

/-!
# Base change of a compatible spectrum model of an affine base piece

Source: Stacks Project, Schemes, Tags 01JR and 01I4; Limits, proof of Tag 01ZO.
(blueprint: lem-weil-pbc-affine-base-piece-tensor-base-change).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Compatible spectrum models remain compatible under arbitrary affine base change.

Source: Stacks Project, Schemes, Tags 01JR and 01I4; Limits, proof of Tag 01ZO,
the affine reduction.
(blueprint: lem-weil-pbc-affine-base-piece-tensor-base-change).

Proof: Put V_T = p_Y⁻¹(V) and U_T = f_T⁻¹(V_T). The equation for q says
that V_T → T factors through W_T = d⁻¹(W). The restriction f_T|V_T gives
the same factorization for U_T. For any t : L → T, paste the two base-change
squares for X₀ and Y₀ with the open restriction squares. The target of the
restricted base change is V_T ×_W_T t⁻¹(W_T), and its source is
U_T ×_W_T t⁻¹(W_T), compatibly with the map f_T|V_T. Indeed first pull
back along V_T → Y_T, then replace T by W_T: both charts already factor
through this open, so the open pullback is unchanged. The isomorphisms e0,
eB, eC and e identify the structure maps with Spec of the specified algebra
maps. The target compatibility is hB; the source compatibility follows from
hφ and the fact that φ commutes with R. Apply pullbackSpecIso R A B and
pullbackSpecIso R A C, in this order, to obtain the spectra of A ⊗ B and
A ⊗ C. Their two projections identify the induced map with Spec(id ⊗ φ):
on the A inclusion it is the identity, and on the B inclusion it is φ.
Equality follows from the pullback universal property. The source and target
isomorphisms therefore form the asserted arrow isomorphism. This construction
uses no finite type or inverse-limit assertion and also covers zero rings. -/
theorem affine_base_piece_tensor_base_change
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
        ∀ (L : Scheme.{u}) (t : L ⟶ T) (A : CommRingCat.{u}) (aA : Algebra R A),
          letI := aA
          ∀ (e : (t ⁻¹ᵁ (d ⁻¹ᵁ W)).toScheme ≅ Spec A),
            t.resLE (d ⁻¹ᵁ W) _ le_rfl ≫ e0.hom =
              e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)) →
            Nonempty
              (Arrow.mk ((((Over.pullback (t ≫ d)).map f₀).left) ∣_
                ((pullback.fst Y₀.hom (t ≫ d)) ⁻¹ᵁ V)) ≅
                Arrow.mk (Spec.map (CommRingCat.ofHom
                  (Algebra.TensorProduct.map (AlgHom.id R A) φ).toRingHom))) := by
      intro φ hB hC L t A aA e he
      exact affine_base_piece_tensor_base_change_instance d X₀ Y₀ f₀ V W R B C aB aC e0 q hq eB eC
        φ hB hC L t A aA e he

end AlgebraicGeometry
