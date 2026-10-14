/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R4
-/
module

public import Sheaf.AlgebraicGeometry.PicardExternalCechCupBidegree
import Sheaf.AlgebraicGeometry.PicardExternalCechCupRefinement

/-! # The external Alexander--Whitney differential calculation
Source: Stacks Project, Tags 0BED and 07MB.
(blueprint: lem-sc-picard-external-cech-cup-differential).
-/

@[expose] public section
universe w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
variable {k : Type w} [Field k] {X Y : Scheme.{w}}

private lemma additiveCech_comm {K L : CochainComplex AddCommGrpCat.{w} ℕ}
    (γ : K ⟶ L) (n : ℕ) (z : K.X n) :
    γ.f (n + 1) (K.d n (n + 1) z) = L.d n (n + 1) (γ.f n z) :=
  (ConcreteCategory.congr_hom (γ.comm n (n + 1)) z).symm

private lemma additiveCech_cast {R T : Type w} [Ring R] [Ring T]
    {K : CochainComplex (ModuleCat.{w} R) ℕ} {L : CochainComplex (ModuleCat.{w} T) ℕ}
    (γ : ((forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w}).mapHomologicalComplex _).obj K ⟶
      ((forget₂ (ModuleCat.{w} T) AddCommGrpCat.{w}).mapHomologicalComplex _).obj L)
    {n m : ℕ} (h : n = m) (z : K.X n) :
    γ.f m (eqToHom (congrArg K.X h) z) =
      eqToHom (congrArg L.X h) (γ.f n z) := by
  subst m
  rfl

/-- Assemble specified bidegree maps by the tensor-total coproduct universal property.
Source: Stacks Project, Tag 0BED, equation-kunneth-on-cech.
(blueprint: lem-sc-picard-external-cech-cup-differential-coordinate). -/
def picardExternalCechCupDegreeMaps
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    {ι κ : Type w} (U : ι → X.Opens) (V : κ → Y.Opens) (F : X.Modules) (G : Y.Modules)
    (l : ∀ p q : ℕ, ((curriedTensor (ModuleCat.{w} k)).obj
        (((picardCechFunctor f U).obj F).X p)).obj
          (((picardCechFunctor g V).obj G).X q) ⟶
      ((picardCechFunctor (pullback.fst f g ≫ f)
        (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
          pullback.snd f g ⁻¹ᵁ V ij.2)).obj (externalCupCoefficients f g F G)).X (p + q)) :
    ∀ n : ℕ, (HomologicalComplex.mapBifunctor ((picardCechFunctor f U).obj F)
        ((picardCechFunctor g V).obj G) (curriedTensor (ModuleCat.{w} k))
          (ComplexShape.up ℕ)).X n ⟶ ((picardCechFunctor (pullback.fst f g ≫ f)
        (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
          pullback.snd f g ⁻¹ᵁ V ij.2)).obj (externalCupCoefficients f g F G)).X n :=
  fun _n ↦ HomologicalComplex.mapBifunctorDesc
    (fun p q hpq ↦ l p q ≫ eqToHom (congrArg
      (fun j ↦ ((picardCechFunctor (pullback.fst f g ≫ f)
        (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
          pullback.snd f g ⁻¹ᵁ V ij.2)).obj (externalCupCoefficients f g F G)).X j) hpq))

/-- Each specified bidegree map is recovered by its tensor-total inclusion.
Source: the coproduct universal property, Stacks Project Tag 0BED.
(blueprint: lem-sc-picard-external-cech-cup-differential). -/
theorem picardExternalCechCupDegreeMaps_ι
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    {ι κ : Type w} (U : ι → X.Opens) (V : κ → Y.Opens) (F : X.Modules) (G : Y.Modules)
    (l : ∀ p q : ℕ, ((curriedTensor (ModuleCat.{w} k)).obj
        (((picardCechFunctor f U).obj F).X p)).obj
          (((picardCechFunctor g V).obj G).X q) ⟶
      ((picardCechFunctor (pullback.fst f g ≫ f)
        (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
          pullback.snd f g ⁻¹ᵁ V ij.2)).obj (externalCupCoefficients f g F G)).X (p + q))
    (p q : ℕ) :
    HomologicalComplex.ιMapBifunctor ((picardCechFunctor f U).obj F)
      ((picardCechFunctor g V).obj G) (curriedTensor (ModuleCat.{w} k))
        (ComplexShape.up ℕ) p q (p + q) rfl ≫
      picardExternalCechCupDegreeMaps f g U V F G l (p + q) = l p q := by
  dsimp only [picardExternalCechCupDegreeMaps]
  rw [HomologicalComplex.ι_mapBifunctorDesc]
  simp

/- Adjacent differential compatibility. -/
attribute [local irreducible] externalCupScalarCechIso externalCupRefineCech
  tensorPullback tensorPullbackObj in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 1600000 in
-- Coercion transports between three categorical Cech product presentations need extra elaboration.
/-- Coordinate differential compatibility for one tensor-total summand.
Source: Stacks Project, Tag 07MB; this is the inclusion-level calculation
used to assemble the total differential identity.
(blueprint: lem-sc-picard-external-cech-cup-differential-coordinate).
Proof: Substitute hpq to work in degree p+q. Tensor-product extensionality reduces the equality
to a pure tensor a tensor b, and Cech product extensionality reduces it to a tuple y of length
p+q+2. Use the degree-map inclusion equation and hl to identify the target coordinates.
Naturality of each pullback adjunction unit identifies pulling a restricted section with
restricting its pullback; presheaf composition identifies successive restrictions, and tensor
sections commute with restriction. In d(a) cup b, the omitted-front terms indexed j=0,...,p
have coefficient (-1)^j and match target faces j=0,...,p. Its final term has coefficient
(-1)^(p+1). In (-1)^p a cup d(b), the first back term has coefficient (-1)^p and is the same
restricted tensor section as that final front term, so they cancel. The remaining back terms
indexed r=1,...,q+1 have coefficient (-1)^(p+r) and match target faces j=p+1,...,p+q+1. These
exhaust the target alternating differential. The tensor-total inclusion differential has
precisely the d(a) tensor b term and the (-1)^p a tensor d(b) term; its inclusion formulas and
the degree-map inclusion equation therefore give the same coordinates. Tensor and product
extensionality conclude the summand equality. The cancellation also applies when p=0 or q=0 and
in characteristic two. Empty index families give vacuous coordinate equalities; zero
coefficients give zero maps. -/
theorem picardExternalCechCupDegreeMaps_comm_ι
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    {ι κ : Type w} (U : ι → X.Opens) (V : κ → Y.Opens) (F : X.Modules) (G : Y.Modules)
    (l : ∀ p q : ℕ, ((curriedTensor (ModuleCat.{w} k)).obj
        (((picardCechFunctor f U).obj F).X p)).obj
          (((picardCechFunctor g V).obj G).X q) ⟶
      ((picardCechFunctor (pullback.fst f g ≫ f)
        (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
          pullback.snd f g ⁻¹ᵁ V ij.2)).obj (externalCupCoefficients f g F G)).X (p + q))
    (hl : ∀ p q, IsPicardExternalCechCupBidegree f g U V F G p q (l p q))
    (n p q : ℕ) (hpq : p + q = n) :
    HomologicalComplex.ιMapBifunctor ((picardCechFunctor f U).obj F)
      ((picardCechFunctor g V).obj G) (curriedTensor (ModuleCat.{w} k))
        (ComplexShape.up ℕ) p q n hpq ≫
      picardExternalCechCupDegreeMaps f g U V F G l n ≫
      ((picardCechFunctor (pullback.fst f g ≫ f)
        (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
          pullback.snd f g ⁻¹ᵁ V ij.2)).obj (externalCupCoefficients f g F G)).d n (n + 1) =
    HomologicalComplex.ιMapBifunctor ((picardCechFunctor f U).obj F)
      ((picardCechFunctor g V).obj G) (curriedTensor (ModuleCat.{w} k))
        (ComplexShape.up ℕ) p q n hpq ≫
      (HomologicalComplex.mapBifunctor ((picardCechFunctor f U).obj F)
        ((picardCechFunctor g V).obj G) (curriedTensor (ModuleCat.{w} k))
          (ComplexShape.up ℕ)).d n (n + 1) ≫
      picardExternalCechCupDegreeMaps f g U V F G l (n + 1) := by
  subst n
  rw [← Category.assoc, picardExternalCechCupDegreeMaps_ι]
  rw [HomologicalComplex.mapBifunctor.d_eq, Preadditive.add_comp,
    Preadditive.comp_add, HomologicalComplex.mapBifunctor.ι_D₁_assoc,
    HomologicalComplex.mapBifunctor.ι_D₂_assoc]
  rw [HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _ (by rfl : p + 1 = p + 1) q
    (p + q + 1) (by dsimp; omega),
    HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ p (by rfl : q + 1 = q + 1)
      (p + q + 1) (by dsimp; omega)]
  have hs₁ : ComplexShape.ε₁ (ComplexShape.up ℕ) (ComplexShape.up ℕ)
      (ComplexShape.up ℕ) (p, q) = 1 := rfl
  have hs₂ : ComplexShape.ε₂ (ComplexShape.up ℕ) (ComplexShape.up ℕ)
      (ComplexShape.up ℕ) (p, q) = (-1 : ℤˣ) ^ p := rfl
  rw [hs₁, hs₂, one_smul]
  simp only [Linear.units_smul_comp, Category.assoc]
  dsimp only [picardExternalCechCupDegreeMaps]
  rw [HomologicalComplex.ι_mapBifunctorDesc, HomologicalComplex.ι_mapBifunctorDesc]
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro a b
  let A := (picardCechFunctor f U).obj F
  let B := (picardCechFunctor g V).obj G
  let W : ι × κ → (Limits.pullback f g).Opens :=
    fun ij ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓ pullback.snd f g ⁻¹ᵁ V ij.2
  let C := (picardCechFunctor (pullback.fst f g ≫ f) W).obj
    (externalCupCoefficients f g F G)
  change C.d (p + q) (p + q + 1) (l p q (a ⊗ₜ[k] b)) =
    eqToHom (congrArg C.X (by omega : (p + 1) + q = p + q + 1))
      (l (p + 1) q (A.d p (p + 1) a ⊗ₜ[k] b)) +
    (-1 : ℤˣ) ^ p • eqToHom (congrArg C.X (by omega : p + (q + 1) = p + q + 1))
      (l p (q + 1) (a ⊗ₜ[k] B.d q (q + 1) b))
  let S := externalCupScalarCechIso (pullback.fst f g ≫ f) W
    (externalCupCoefficients f g F G)
  apply (ConcreteCategory.bijective_of_isIso (S.hom.f (p + q + 1))).1
  erw [additiveCech_comm S.hom]
  simp only [map_add, Units.smul_def, map_zsmul, Units.val_pow_eq_pow_val, Units.val_neg,
    Units.val_one]
  erw [additiveCech_cast S.hom (by omega : (p + 1) + q = p + q + 1),
    additiveCech_cast S.hom (by omega : p + (q + 1) = p + q + 1)]
  erw [externalCup_bidegree_refinement f g U V F G p q _ (hl p q),
    externalCup_bidegree_refinement f g U V F G (p + 1) q _ (hl (p + 1) q),
    externalCup_bidegree_refinement f g U V F G p (q + 1) _ (hl p (q + 1))]
  erw [additiveCech_comm (externalCupScalarCechIso f U F).hom p,
    additiveCech_comm (externalCupScalarCechIso g V G).hom q]
  erw [additiveCech_comm
      (externalCupRefineCech (pullback.fst f g) U W Prod.fst
        (fun _ ↦ inf_le_left) F) p,
    additiveCech_comm
      (externalCupRefineCech (pullback.snd f g) V W Prod.snd
        (fun _ ↦ inf_le_right) G) q]
  exact cechCupCochain_leibniz W ((tensorPullback (pullback.fst f g)).obj F)
    ((tensorPullback (pullback.snd f g)).obj G) p q _ _

end
end AlgebraicGeometry.Scheme.Modules
