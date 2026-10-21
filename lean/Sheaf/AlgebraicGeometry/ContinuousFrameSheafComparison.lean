/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q11
-/
module

public import Sheaf.AlgebraicGeometry.ContinuousFrameModule
public import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.AlgebraicGeometry.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.Sheafification

/-! # Continuous frames and scalar extension of coefficient sheaves

Source: blueprint, stratified lattice proof, paragraph "Pushing down by the trace".
(blueprint: lem-sfb-continuous-frame-sheaf-comparison)
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v

open CategoryTheory Opposite
open scoped TensorProduct ChangeOfRings

namespace AlgebraicGeometry.ProEtale

/-- Continuous frames give free coefficient sheaves and identify the scalar extension of
 their actual inclusion with the ambient vector-valued sheaf.

Source: blueprint, stratified lattice proof, "Pushing down by the trace".
(blueprint: lem-sfb-continuous-frame-sheaf-comparison)

Proof: (1) The subspace topologies make addition, negation and scalar multiplication
continuous on A and L. Thus the displayed presheaves have their pointwise operations.
(2) Apply lem-cbc-continuous-functions-fpqc-sheaf to A, K and L and restrict from fpqc
to the small pro-etale site. This proves the sheaf conditions, also for finite powers.
(3) Compose continuous tuples with beta = b.equivFun.symm. Composing with its inverse
recovers every coordinate, so these are mutually inverse linear maps. Both commute with
precomposition. They give the sheaf isomorphism from the coordinate power to F_L.
(4) Postcomposition with L into K^r is continuous and injective and commutes with
restrictions. The matrix with columns b_i acts on coordinates by finite sums of constant
multiples. The K-basis c with these same columns gives its continuous inverse.
(5) The balanced bilinear map (a,f) to a times f induces mu. Its inverse sends g to
sum_i (c.equivFun g)_i tensor the constant b_i. The first composite is B B^{-1} g.
For the other, expand f in the continuous A-basis coordinates and use balancing on
pure tensors; finite sums of pure tensors give the general identity.
(6) The coordinate tensor identification J has inverse t to sum_i t_i tensor e_i.
The two inverse identities follow by balancing and the finite coordinate expansion.
Both inverse formulas commute with precomposition. On a tensor of a scalar and a
coordinate vector the result is the stated constant matrix times their coordinate product.
(7) The sectionwise tensor presheaf is isomorphic to the ambient continuous-section
sheaf, hence is a sheaf. Sheafification changes nothing: its unit has an inverse by
the sheafification universal property, whose uniqueness gives both inverse identities.
The sheafified map therefore is an isomorphism and its formula is scalar times inclusion.
(8) In rank zero all sums are empty and all the modules and tensor sources are zero;
the same formulas and inverse identities apply without a nonzero-rank hypothesis. -/
theorem continuous_frame_sheaf_comparison
    (X : Scheme.{u}) (K : Type v) [Field K] [TopologicalSpace K]
    [IsTopologicalDivisionRing K] (A : Subring K) (r : ℕ)
    (L : Submodule A (Fin r → K)) (b : Module.Basis (Fin r) A L)
    (c : Module.Basis (Fin r) K (Fin r → K))
    (hc : ∀ i : Fin r, c i = (b i : Fin r → K))
    (hβ : IsHomeomorph (b.equivFun.symm : (Fin r → A) → L)) :
    ∃ hP : Presheaf.IsSheaf (Scheme.ProEt.topology X)
        (continuousFramePresheaf X A (Fin r → A)).presheaf,
    ∃ hF : Presheaf.IsSheaf (Scheme.ProEt.topology X)
        (continuousFramePresheaf X A L).presheaf,
    ∃ hG : Presheaf.IsSheaf (Scheme.ProEt.topology X)
        (continuousFramePresheaf X K (Fin r → K)).presheaf,
    ∃ e : continuousFrameSheaf X A (Fin r → A) hP ≅ continuousFrameSheaf X A L hF,
    ∃ φ : ∀ U : X.ProEtᵒᵖ,
        (Fin r → (lisseContinuousCommRingSheafUniverses X A).obj.obj U) ≃ₗ[
          (lisseContinuousCommRingSheafUniverses X A).obj.obj U]
            (ULift.{u + 1} C(U.unop.left, L)),
    ∃ ι : continuousFrameSheaf X A L hF ⟶
        (SheafOfModules.restrictScalars
          ((sheafCompose (Scheme.ProEt.topology X)
            (forget₂ CommRingCat.{max (u + 1) v} RingCat.{max (u + 1) v})).map
              (continuousFrameCoefficientInclusion X K A))).obj
                (continuousFrameSheaf X K (Fin r → K) hG),
    ∃ μ : continuousFrameTensorPresheaf X K A (continuousFrameSheaf X A L hF) ≅
        (continuousFrameSheaf X K (Fin r → K) hG).val,
    ∃ d : ∀ U : X.ProEtᵒᵖ, C(U.unop.left, Fin r → K) → Fin r → C(U.unop.left, K),
    ∃ J : ∀ U : X.ProEtᵒᵖ,
        (continuousFrameTensorPresheaf X K A
          (continuousFrameSheaf X A (Fin r → A) hP)).obj U ≃ₗ[
            (lisseContinuousCommRingSheafUniverses X K).obj.obj U]
              (Fin r → (lisseContinuousCommRingSheafUniverses X K).obj.obj U),
    ∃ q : continuousFrameTensorSheaf X K A (continuousFrameSheaf X A L hF) ≅
        continuousFrameSheaf X K (Fin r → K) hG,
      (∀ (U : X.ProEtᵒᵖ) (a : Fin r →
          (lisseContinuousCommRingSheafUniverses X A).obj.obj U) (x : U.unop.left),
        (φ U a).down x = ∑ i : Fin r, (a i).down x • b i) ∧
      (∀ (U : X.ProEtᵒᵖ) (f : ULift.{u + 1} C(U.unop.left, L))
          (i : Fin r) (x : U.unop.left),
        ((φ U).symm f i).down x = b.equivFun (f.down x) i) ∧
      (∀ (U : X.ProEtᵒᵖ) (p : ULift.{u + 1} C(U.unop.left, Fin r → A)),
        e.hom.val.app U p =
          φ U (fun i ↦ ULift.up ((ContinuousMap.eval i).comp p.down))) ∧
      (∀ {U V : X.ProEtᵒᵖ} (h : U ⟶ V)
          (a : Fin r → (lisseContinuousCommRingSheafUniverses X A).obj.obj U),
        φ V (fun i ↦ (lisseContinuousCommRingSheafUniverses X A).obj.map h (a i)) =
          ULift.up ((φ U a).down.comp h.unop.left.base.hom)) ∧
      (∀ {U V : X.ProEtᵒᵖ} (h : U ⟶ V) (f : ULift.{u + 1} C(U.unop.left, L))
          (i : Fin r),
        (φ V).symm (ULift.up (f.down.comp h.unop.left.base.hom)) i =
          (lisseContinuousCommRingSheafUniverses X A).obj.map h ((φ U).symm f i)) ∧
      (∀ (U : X.ProEtᵒᵖ) (f : ULift.{u + 1} C(U.unop.left, L)) (x : U.unop.left),
        (ULift.down (ι.val.app U f)) x = (f.down x : Fin r → K)) ∧
      (∀ U : X.ProEtᵒᵖ, Function.Injective (ι.val.app U)) ∧
      (∀ (U : X.ProEtᵒᵖ)
          (a : (lisseContinuousCommRingSheafUniverses X K).obj.obj U)
          (f : ULift.{u + 1} C(U.unop.left, L)) (x : U.unop.left),
        (ULift.down (μ.hom.app U
          (a ⊗ₜ[(lisseContinuousCommRingSheafUniverses X A).obj.obj U,
            ((continuousFrameCoefficientInclusion X K A).hom.app U).hom] f))) x =
              a.down x • (f.down x : Fin r → K)) ∧
      (∀ (U : X.ProEtᵒᵖ) (g : C(U.unop.left, Fin r → K))
          (i : Fin r) (x : U.unop.left), d U g i x = c.equivFun (g x) i) ∧
      (∀ (U : X.ProEtᵒᵖ) (g : ULift.{u + 1} C(U.unop.left, Fin r → K)),
        μ.inv.app U g = ∑ i : Fin r,
          (ULift.up (d U g.down i) : ULift.{u + 1} C(U.unop.left, K)) ⊗ₜ[
            (lisseContinuousCommRingSheafUniverses X A).obj.obj U,
            ((continuousFrameCoefficientInclusion X K A).hom.app U).hom]
              ULift.up (ContinuousMap.const U.unop.left (b i))) ∧
      (∀ {U V : X.ProEtᵒᵖ} (h : U ⟶ V)
          (g : C(U.unop.left, Fin r → K)) (i : Fin r),
        d V (g.comp h.unop.left.base.hom) i = (d U g i).comp h.unop.left.base.hom) ∧
      (∀ (U : X.ProEtᵒᵖ)
          (a : (lisseContinuousCommRingSheafUniverses X K).obj.obj U)
          (p : ULift.{u + 1} C(U.unop.left, Fin r → A)) (i : Fin r) (x : U.unop.left),
        (J U (a ⊗ₜ[(lisseContinuousCommRingSheafUniverses X A).obj.obj U,
          ((continuousFrameCoefficientInclusion X K A).hom.app U).hom] p) i).down x =
            a.down x * (p.down x i : K)) ∧
      (∀ (U : X.ProEtᵒᵖ)
          (a : (lisseContinuousCommRingSheafUniverses X K).obj.obj U)
          (p : ULift.{u + 1} C(U.unop.left, Fin r → A)) (x : U.unop.left) (j : Fin r),
        (ULift.down (μ.hom.app U
          (a ⊗ₜ[(lisseContinuousCommRingSheafUniverses X A).obj.obj U,
            ((continuousFrameCoefficientInclusion X K A).hom.app U).hom]
              e.hom.val.app U p))) x j =
                ∑ i : Fin r, a.down x * (p.down x i : K) * (b i : Fin r → K) j) ∧
      Presheaf.IsSheaf (Scheme.ProEt.topology X)
        (continuousFrameTensorPresheaf X K A (continuousFrameSheaf X A L hF)).presheaf ∧
      continuousFrameTensorUnit X K A (continuousFrameSheaf X A L hF) ≫ q.hom.val = μ.hom := by
  sorry

end AlgebraicGeometry.ProEtale
