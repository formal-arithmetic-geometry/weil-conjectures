/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G3
-/
module

public import Sheaf.AlgebraicGeometry.PicardExternalCechCupBidegree
import Sheaf.AlgebraicGeometry.PicardExternalCechCupDifferentialCoordinate

/-! # External Alexander--Whitney pure-tensor Leibniz calculation
Source: Stacks Project, Tags 0BED and 07MB.
(blueprint: lem-sc-picard-external-cech-cup-leibniz).
-/

@[expose] public section
universe w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
variable {k : Type w} [Field k] {X Y : Scheme.{w}}

/-- The signed face calculation on a pure tensor, before tensor-total assembly.
Source: Stacks Project, Tag 07MB, calculation after equation 20.25.3.2, coefficients in degree zero;
Tag 0BED, equation-kunneth-on-cech, for the external coordinates.
(blueprint: lem-sc-picard-external-cech-cup-leibniz).
Proof: Choose a family of bidegree maps using the bidegree existence theorem.
Their prescribed front/back coordinates uniquely determine each pure-tensor value:
apply injectivity of the target Cech coordinate equivalence and use the two
coordinate equations. The chosen maps therefore agree with h, h₁ and h₂ on the
three pure tensors in the conclusion. Apply the inclusion-level differential
compatibility theorem to this family in degree p+q. The degree-map inclusion
formula recovers the initial bidegree map. Expand the tensor-total differential
with mapBifunctor.d_eq, ι_D₁, ι_D₂, d₁_eq and d₂_eq. Its signs are 1 and (-1)^p.
Evaluate the resulting morphism equality on a pure tensor and use the tensor-map
application formulas. Replace the three chosen pure-tensor values by h, h₁ and h₂.
The degree transports are precisely the arithmetic equalities in the statement.
In degree zero and characteristic two the same formulas hold. Empty index
families give vacuous coordinate equalities; zero coefficients give zero maps. -/
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
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    classical
    let l := fun r s ↦ (picardExternalCechCupBidegree_exists f g U V F G r s).choose
    have hl : ∀ r s, IsPicardExternalCechCupBidegree f g U V F G r s (l r s) :=
      fun r s ↦ (picardExternalCechCupBidegree_exists f g U V F G r s).choose_spec
    have heq (r s : ℕ) (m : _)
        (hm : IsPicardExternalCechCupBidegree f g U V F G r s m)
        (x : ((picardCechFunctor f U).obj F).X r)
        (z : ((picardCechFunctor g V).obj G).X s) :
        l r s (x ⊗ₜ[k] z) = m (x ⊗ₜ[k] z) := by
      apply (TopCat.Presheaf.cechComplexFunctorXAddEquiv
        (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
          pullback.snd f g ⁻¹ᵁ V ij.2)
        (scalarPresheaf (pullback.fst f g ≫ f) (externalCupCoefficients f g F G))
        (r + s)).injective
      funext y
      exact (hl r s x z y).trans (hm x z y).symm
    have hc := picardExternalCechCupDegreeMaps_comm_ι f g U V F G l hl (p + q) p q rfl
    rw [← Category.assoc, picardExternalCechCupDegreeMaps_ι] at hc
    simp only [HomologicalComplex.mapBifunctor.d_eq, Preadditive.add_comp,
      Preadditive.comp_add, HomologicalComplex.mapBifunctor.ι_D₁_assoc,
      HomologicalComplex.mapBifunctor.ι_D₂_assoc] at hc
    rw [HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _ (by rfl) q (p + q + 1)
        (Nat.add_right_comm p 1 q),
      HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ p (by rfl) (p + q + 1)
        (Nat.add_assoc p q 1).symm] at hc
    simp only [Linear.units_smul_comp, Category.assoc] at hc
    dsimp only [picardExternalCechCupDegreeMaps] at hc
    simp only [HomologicalComplex.ι_mapBifunctorDesc] at hc
    have hv := congrArg (fun m ↦ m.hom (a ⊗ₜ[k] b)) hc
    simp only [ComplexShape.ε₁_def, one_smul, ComplexShape.ε₂_def,
      ComplexShape.ε_up_ℕ, curriedTensor_map_app, curriedTensor_obj_map] at hv
    simp only [ModuleCat.hom_add, LinearMap.add_apply, ModuleCat.hom_smul,
      LinearMap.smul_apply, ModuleCat.hom_comp, LinearMap.comp_apply] at hv
    simp only [← tensorHom_id, ← id_tensorHom] at hv
    erw [ModuleCat.MonoidalCategory.tensorHom_tmul,
      ModuleCat.MonoidalCategory.tensorHom_tmul] at hv
    simp only [ConcreteCategory.id_apply] at hv
    rw [heq p q h hh a b,
      heq (p + 1) q h₁ hh₁ _ b, heq p (q + 1) h₂ hh₂ a _] at hv
    exact hv

end
end AlgebraicGeometry.Scheme.Modules
