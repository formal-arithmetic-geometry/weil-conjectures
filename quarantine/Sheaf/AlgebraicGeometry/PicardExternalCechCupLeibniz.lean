/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T4
-/
module

public import Sheaf.AlgebraicGeometry.PicardExternalCechCupBidegree
import Sheaf.AlgebraicGeometry.PicardExternalCechCupTransport

/-! # External Alexander--Whitney pure-tensor Leibniz calculation
Source: Stacks Project, Tags 0BED and 07MB.
(blueprint: lem-sc-picard-external-cech-cup-leibniz).
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
variable {k : Type w} [Field k] {X Y : Scheme.{w}}

set_option maxHeartbeats 1800000 in
-- Elaborating the three bidegree transports requires additional heartbeats.
/-- The signed face calculation on a pure tensor, before tensor-total assembly.
Source: Stacks Project, Tag 07MB, calculation after equation 20.25.3.2, coefficients in degree zero;
Tag 0BED, equation-kunneth-on-cech, for the external coordinates.
(blueprint: lem-sc-picard-external-cech-cup-leibniz).
Proof: Identify the scalar and ordinary module Cech complexes after forgetting
scalars. Choose the unique refinement cochain maps along the two projections,
using the inclusions of each product open in the respective inverse image.
The transport theorem identifies h, h₁ and h₂ on pure tensors with the ordinary
cup of the refined factor cochains in their three respective bidegrees.
Apply the injective target scalar identification, which commutes with the
differential, addition, integer scalar multiplication and equal-degree casts.
Apply the ordinary Cech cup Leibniz theorem on the product scheme. The two
composite refinement maps are cochain maps, so their commutation equations
identify the differentials of the refined factors with the refined factor
differentials. Substitution in the two casted summands proves the equality.
No map in any other bidegree or tensor-total inclusion is needed. The ordinary
theorem applies also in degree zero, for empty families, zero coefficients and
in characteristic two. -/
theorem picardExternalCechCupBidegree_leibniz
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    {ι κ : Type w} (U : ι → X.Opens) (V : κ → Y.Opens) (F : X.Modules) (G : Y.Modules)
    (p q : ℕ)
    (h : ((curriedTensor (ModuleCat.{w} k)).obj
        (((picardCechFunctor f U).obj F).X p)).obj (((picardCechFunctor g V).obj G).X q) ⟶
      ((picardCechFunctor (pullback.fst f g ≫ f)
        (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
          pullback.snd f g ⁻¹ᵁ V ij.2)).obj (externalCupCoefficients f g F G)).X (p + q))
    (h₁ : ((curriedTensor (ModuleCat.{w} k)).obj
        (((picardCechFunctor f U).obj F).X (p + 1))).obj (((picardCechFunctor g V).obj G).X q) ⟶
      ((picardCechFunctor (pullback.fst f g ≫ f)
        (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
          pullback.snd f g ⁻¹ᵁ V ij.2)).obj (externalCupCoefficients f g F G)).X ((p + 1) + q))
    (h₂ : ((curriedTensor (ModuleCat.{w} k)).obj
        (((picardCechFunctor f U).obj F).X p)).obj (((picardCechFunctor g V).obj G).X (q + 1)) ⟶
      ((picardCechFunctor (pullback.fst f g ≫ f)
        (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
          pullback.snd f g ⁻¹ᵁ V ij.2)).obj (externalCupCoefficients f g F G)).X (p + (q + 1)))
    (hh : IsPicardExternalCechCupBidegree f g U V F G p q h)
    (hh₁ : IsPicardExternalCechCupBidegree f g U V F G (p + 1) q h₁)
    (hh₂ : IsPicardExternalCechCupBidegree f g U V F G p (q + 1) h₂)
    (a : ((picardCechFunctor f U).obj F).X p)
    (b : ((picardCechFunctor g V).obj G).X q) :
    ((picardCechFunctor (pullback.fst f g ≫ f)
        (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
          pullback.snd f g ⁻¹ᵁ V ij.2)).obj (externalCupCoefficients f g F G)).d
        (p + q) (p + q + 1) (h (a ⊗ₜ[k] b)) =
      (eqToHom (congrArg (fun n ↦
        ((picardCechFunctor (pullback.fst f g ≫ f)
        (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
          pullback.snd f g ⁻¹ᵁ V ij.2)).obj (externalCupCoefficients f g F G)).X n)
        (Nat.add_right_comm p 1 q)))
          (h₁ (((picardCechFunctor f U).obj F).d p (p + 1) a ⊗ₜ[k] b)) +
    (-1 : ℤ) ^ p • (eqToHom (congrArg (fun n ↦
        ((picardCechFunctor (pullback.fst f g ≫ f)
        (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
          pullback.snd f g ⁻¹ᵁ V ij.2)).obj (externalCupCoefficients f g F G)).X n)
        (Nat.add_assoc p q 1).symm))
          (h₂ (a ⊗ₜ[k] ((picardCechFunctor g V).obj G).d q (q + 1) b)) := by
  classical
  let W := fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
    pullback.snd f g ⁻¹ᵁ V ij.2
  let E := externalCupCoefficients f g F G
  let FF := (tensorPullback (pullback.fst f g)).obj F
  let GG := (tensorPullback (pullback.snd f g)).obj G
  have hrefineF : ∀ ij : ι × κ, W ij ≤ pullback.fst f g ⁻¹ᵁ U ij.1 :=
    fun _ ↦ inf_le_left
  have hrefineG : ∀ ij : ι × κ, W ij ≤ pullback.snd f g ⁻¹ᵁ V ij.2 :=
    fun _ ↦ inf_le_right
  obtain ⟨gammaF, hgammaF, _⟩ := exists_unique_cechRefinementMap
    (pullback.fst f g) U W Prod.fst hrefineF F
  obtain ⟨gammaG, hgammaG, _⟩ := exists_unique_cechRefinementMap
    (pullback.snd f g) V W Prod.snd hrefineG G
  let φF := (picardCechScalarIso f U F).hom ≫ gammaF
  let φG := (picardCechScalarIso g V G).hom ≫ gammaG
  let eP := picardCechScalarIso (pullback.fst f g ≫ f) W E
  have ht := picardExternalCechCupBidegree_transport f g F G U V p q h hh
    hrefineF hrefineG gammaF hgammaF gammaG hgammaG a b
  have ht₁ := picardExternalCechCupBidegree_transport f g F G U V (p + 1) q h₁ hh₁
    hrefineF hrefineG gammaF hgammaF gammaG hgammaG
    (((picardCechFunctor f U).obj F).d p (p + 1) a) b
  have ht₂ := picardExternalCechCupBidegree_transport f g F G U V p (q + 1) h₂ hh₂
    hrefineF hrefineG gammaF hgammaF gammaG hgammaG
    a (((picardCechFunctor g V).obj G).d q (q + 1) b)
  have hF := ConcreteCategory.congr_hom (φF.comm p (p + 1)) a
  have hG := ConcreteCategory.congr_hom (φG.comm q (q + 1)) b
  change ((cechComplexFunctor W).obj FF.presheafModuleCat).d p (p + 1) (φF.f p a) =
    φF.f (p + 1) (((picardCechFunctor f U).obj F).d p (p + 1) a) at hF
  change ((cechComplexFunctor W).obj GG.presheafModuleCat).d q (q + 1) (φG.f q b) =
    φG.f (q + 1) (((picardCechFunctor g V).obj G).d q (q + 1) b) at hG
  apply (ConcreteCategory.bijective_of_isIso (eP.hom.f (p + q + 1))).1
  dsimp only [eP]
  rw [map_add, map_zsmul,
    picardCechScalarIso_d (pullback.fst f g ≫ f) W E (p + q),
    picardCechScalarIso_cast (pullback.fst f g ≫ f) W E (Nat.add_right_comm p 1 q),
    picardCechScalarIso_cast (pullback.fst f g ≫ f) W E (Nat.add_assoc p q 1).symm]
  rw [ht, ht₁, ht₂]
  change ((cechComplexFunctor W).obj E.presheafModuleCat).d (p + q) (p + q + 1)
    (cechCupCochain W FF GG p q (φF.f p a) (φG.f q b)) = _
  rw [cechCupCochain_leibniz]
  apply congrArg₂ (fun x y ↦
    eqToHom (congrArg (fun n ↦ ((cechComplexFunctor W).obj E.presheafModuleCat).X n)
      (Nat.add_right_comm p 1 q)) x + (-1 : ℤ) ^ p •
    eqToHom (congrArg (fun n ↦ ((cechComplexFunctor W).obj E.presheafModuleCat).X n)
      (Nat.add_assoc p q 1).symm) y)
  · exact congrArg (fun x ↦ cechCupCochain W FF GG (p + 1) q x (φG.f q b)) hF
  · exact congrArg (fun y ↦ cechCupCochain W FF GG p (q + 1) (φF.f p a) y) hG

end
end AlgebraicGeometry.Scheme.Modules
