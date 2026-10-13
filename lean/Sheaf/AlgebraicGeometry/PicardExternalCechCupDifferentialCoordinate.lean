/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R4
-/
module

public import Sheaf.AlgebraicGeometry.PicardExternalCechCupBidegree

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

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma coordinate_d {Z : TopCat.{w}} {μ : Type w}
    (A : μ → TopologicalSpace.Opens Z) {R : Type w} [Ring R]
    (P : (TopologicalSpace.Opens Z)ᵒᵖ ⥤ ModuleCat.{w} R) (n : ℕ)
    (a : ((cechComplexFunctor A).obj P).X n) (y : Fin (n + 2) → μ) :
    TopCat.Presheaf.cechComplexFunctorXAddEquiv A P (n + 1)
      (((cechComplexFunctor A).obj P).d n (n + 1) a) y =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
        P.map (homOfLE (TopCat.Presheaf.iInf_le_iInf_comp A y i.succAbove)).op
          (TopCat.Presheaf.cechComplexFunctorXAddEquiv A P n a
            (y ∘ i.succAbove)) := by
  have h := (congrArg (fun f ↦ f a y)
    ((TopCat.Presheaf.cechComplexFunctorIso A P).hom.comm n (n + 1))).symm
  change TopCat.Presheaf.cechComplexFunctorXAddEquiv A P (n + 1)
    (((cechComplexFunctor A).obj P).d n (n + 1) a) y =
      ((TopCat.Presheaf.cechComplex A).obj
        (P ⋙ forget₂ (ModuleCat R) AddCommGrpCat)).d n (n + 1)
          (TopCat.Presheaf.cechComplexFunctorXAddEquiv A P n a) y at h
  rw [TopCat.Presheaf.cechComplex_d_apply] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private def forgetCech {Z : Scheme.{w}} (t : Z ⟶ Spec (CommRingCat.of k))
    {μ : Type w} (A : μ → Z.Opens) (M : Z.Modules) (n : ℕ) :
    ((picardCechFunctor t A).obj M).X n ≃+
      ((cechComplexFunctor A).obj M.presheafModuleCat).X n :=
  (TopCat.Presheaf.cechComplexFunctorXAddEquiv A (scalarPresheaf t M) n).trans
    (TopCat.Presheaf.cechComplexFunctorXAddEquiv A M.presheafModuleCat n).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma forgetCech_d {Z : Scheme.{w}} (t : Z ⟶ Spec (CommRingCat.of k))
    {μ : Type w} (A : μ → Z.Opens) (M : Z.Modules) (n : ℕ)
    (a : ((picardCechFunctor t A).obj M).X n) :
    forgetCech t A M (n + 1) (((picardCechFunctor t A).obj M).d n (n + 1) a) =
      ((cechComplexFunctor A).obj M.presheafModuleCat).d n (n + 1)
        (forgetCech t A M n a) := by
  apply (TopCat.Presheaf.cechComplexFunctorXAddEquiv A M.presheafModuleCat
    (n + 1)).injective
  dsimp only [forgetCech, AddEquiv.trans_apply]
  erw [AddEquiv.apply_symm_apply]
  funext y
  change TopCat.Presheaf.cechComplexFunctorXAddEquiv A (scalarPresheaf t M) (n + 1)
    (((cechComplexFunctor A).obj (scalarPresheaf t M)).d n (n + 1) a) y = _
  erw [coordinate_d, coordinate_d]
  erw [AddEquiv.apply_symm_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma forgetCech_cast {Z : Scheme.{w}} (t : Z ⟶ Spec (CommRingCat.of k))
    {μ : Type w} (A : μ → Z.Opens) (M : Z.Modules) {m n : ℕ} (h : m = n)
    (c : ((picardCechFunctor t A).obj M).X m) :
    forgetCech t A M n
      (eqToHom (congrArg (fun j ↦ ((picardCechFunctor t A).obj M).X j) h) c) =
      eqToHom (congrArg (fun j ↦ ((cechComplexFunctor A).obj M.presheafModuleCat).X j) h)
        (forgetCech t A M m c) := by
  subst n
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private def pullCech {Z T : Scheme.{w}} (t : Z ⟶ Spec (CommRingCat.of k))
    (a : T ⟶ Z) {μ ν : Type w} (A : μ → Z.Opens) (B : ν → T.Opens)
    (r : ν → μ) (hr : ∀ j, B j ≤ a ⁻¹ᵁ A (r j)) (M : Z.Modules) (n : ℕ)
    (c : ((picardCechFunctor t A).obj M).X n) :
    ((cechComplexFunctor B).obj ((tensorPullback a).obj M).presheafModuleCat).X n :=
  (TopCat.Presheaf.cechComplexFunctorXAddEquiv B
    ((tensorPullback a).obj M).presheafModuleCat n).symm (fun y ↦
      ((tensorPullback a).obj M).presheaf.map (homOfLE (show
        (⨅ j, B (y j)) ≤ a ⁻¹ᵁ (⨅ j, A (r (y j))) from by
          intro x hx
          change a.base x ∈ ⨅ j, A (r (y j))
          rw [← SetLike.mem_coe, TopologicalSpace.Opens.coe_iInf, Set.mem_iInter]
          intro j
          exact hr (y j) (iInf_le (fun j ↦ B (y j)) j hx))).op
        (((Classical.choose (exists_tensorPullbackAdjunction a)).unit.app M).val.app
          (op (⨅ j, A (r (y j))))
          (TopCat.Presheaf.cechComplexFunctorXAddEquiv A (scalarPresheaf t M) n c
            (r ∘ y))))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma pullCech_d {Z T : Scheme.{w}} (t : Z ⟶ Spec (CommRingCat.of k))
    (a : T ⟶ Z) {μ ν : Type w} (A : μ → Z.Opens) (B : ν → T.Opens)
    (r : ν → μ) (hr : ∀ j, B j ≤ a ⁻¹ᵁ A (r j)) (M : Z.Modules) (n : ℕ)
    (c : ((picardCechFunctor t A).obj M).X n) :
    pullCech t a A B r hr M (n + 1) (((picardCechFunctor t A).obj M).d n (n + 1) c) =
      ((cechComplexFunctor B).obj ((tensorPullback a).obj M).presheafModuleCat).d
        n (n + 1) (pullCech t a A B r hr M n c) := by
  apply (TopCat.Presheaf.cechComplexFunctorXAddEquiv B
    ((tensorPullback a).obj M).presheafModuleCat (n + 1)).injective
  dsimp only [pullCech]
  erw [AddEquiv.apply_symm_apply]
  funext y
  change ((tensorPullback a).obj M).presheaf.map _
    (((Classical.choose (exists_tensorPullbackAdjunction a)).unit.app M).val.app _
      (TopCat.Presheaf.cechComplexFunctorXAddEquiv A (scalarPresheaf t M) (n + 1)
        (((cechComplexFunctor A).obj (scalarPresheaf t M)).d n (n + 1) c) _)) = _
  erw [coordinate_d, coordinate_d, AddEquiv.apply_symm_apply]
  simp only [map_sum, map_zsmul]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  change ((tensorPullback a).obj M).presheaf.map _
    (((Classical.choose (exists_tensorPullbackAdjunction a)).unit.app M).val.app _
      (M.presheaf.map _ _)) = _
  erw [PresheafOfModules.naturality_apply]
  exact (TopCat.Presheaf.map_homOfLE_map_homOfLE_apply
    ((tensorPullback a).obj M).presheaf _ _ _).trans
      (TopCat.Presheaf.map_homOfLE_map_homOfLE_apply
        ((tensorPullback a).obj M).presheaf _ _ _).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private def frontCech
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    {ι κ : Type w} (U : ι → X.Opens) (V : κ → Y.Opens) (F : X.Modules) (n : ℕ) :=
  pullCech f (pullback.fst f g) U
    (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓ pullback.snd f g ⁻¹ᵁ V ij.2)
    Prod.fst (fun _ ↦ inf_le_left) F n

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private def backCech
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    {ι κ : Type w} (U : ι → X.Opens) (V : κ → Y.Opens) (G : Y.Modules) (n : ℕ) :=
  pullCech g (pullback.snd f g) V
    (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓ pullback.snd f g ⁻¹ᵁ V ij.2)
    Prod.snd (fun _ ↦ inf_le_right) G n

set_option maxHeartbeats 800000 in
-- Comparing the nested scalar and sheaf restrictions requires extra definitional reductions.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma bidegree_eq
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    {ι κ : Type w} (U : ι → X.Opens) (V : κ → Y.Opens) (F : X.Modules) (G : Y.Modules)
    (l : ∀ p q : ℕ, ((curriedTensor (ModuleCat.{w} k)).obj
        (((picardCechFunctor f U).obj F).X p)).obj
          (((picardCechFunctor g V).obj G).X q) ⟶
      ((picardCechFunctor (pullback.fst f g ≫ f)
        (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
          pullback.snd f g ⁻¹ᵁ V ij.2)).obj (externalCupCoefficients f g F G)).X (p + q))
    (hl : ∀ p q, IsPicardExternalCechCupBidegree f g U V F G p q (l p q))
    (p q : ℕ)
    (a : ((picardCechFunctor f U).obj F).X p)
    (b : ((picardCechFunctor g V).obj G).X q) :
    forgetCech (pullback.fst f g ≫ f)
      (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
        pullback.snd f g ⁻¹ᵁ V ij.2) (externalCupCoefficients f g F G) (p + q)
      (l p q (a ⊗ₜ[k] b)) =
      cechCupCochain
        (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
          pullback.snd f g ⁻¹ᵁ V ij.2)
        ((tensorPullback (pullback.fst f g)).obj F)
        ((tensorPullback (pullback.snd f g)).obj G) p q
        (frontCech f g U V F p a) (backCech f g U V G q b) := by
  apply (TopCat.Presheaf.cechComplexFunctorXAddEquiv _
    (externalCupCoefficients f g F G).presheafModuleCat (p + q)).injective
  dsimp only [forgetCech, AddEquiv.trans_apply]
  erw [AddEquiv.apply_symm_apply]
  funext y
  erw [hl p q a b y]
  dsimp only [cechCupCochain]
  erw [AddEquiv.apply_symm_apply]
  dsimp only [frontCech, backCech, pullCech]
  erw [AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  apply congrArg₂ tmulSection
  · exact (TopCat.Presheaf.map_homOfLE_map_homOfLE_apply
      ((tensorPullback (pullback.fst f g)).obj F).presheaf _ _ _).symm
  · exact (TopCat.Presheaf.map_homOfLE_map_homOfLE_apply
      ((tensorPullback (pullback.snd f g)).obj G).presheaf _ _ _).symm

/- Adjacent differential compatibility. -/
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 800000 in
-- Scalar restriction and tensor-total degree transports require extra definitional reductions.
/-- Coordinate differential compatibility for one tensor-total summand.
Source: Stacks Project, Tag 07MB; this is the inclusion-level calculation
used to assemble the total differential identity.
(blueprint: lem-sc-picard-external-cech-cup-differential-coordinate).
Proof: Substitute hpq and use the tensor-total inclusion and differential formulas to reduce
to pure tensors. The first total differential applies d to the first factor, and the second
applies d to the second factor with coefficient (-1)^p; the coproduct descent transports each
result to degree p+q+1. Identify scalar Cech cochains with ordinary module Cech cochains by
their common section coordinates. This additive equivalence commutes with the differential
and with degree transports, since scalar restriction preserves the underlying additive maps.
Pull each factor cochain to the product family: on a tuple, apply the canonical tensor-pullback
adjunction unit to its projected coordinates and restrict to the product intersection.
The alternating-face formula, naturality of the unit, and composition of restrictions show
that these pullback operations commute with d. The prescribed bidegree coordinates identify
l(a tensor b), after forgetting scalars, with the ordinary Cech cup of these pulled cochains:
successive restrictions along the front and back faces compose to the full restriction.
Apply cechCupCochain_leibniz on the product scheme, then the pullback differential identities.
Injectivity of the scalar-forgetting equivalence and tensor-product extensionality conclude.
The argument uses arbitrary open families, including empty families, and does not divide by
any sign or scalar, so degree zero, zero coefficients, and characteristic two are included. -/
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
  let A := (picardCechFunctor f U).obj F
  let B := (picardCechFunctor g V).obj G
  let C := (picardCechFunctor (pullback.fst f g ≫ f)
    (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
      pullback.snd f g ⁻¹ᵁ V ij.2)).obj (externalCupCoefficients f g F G)
  erw [← Category.assoc, picardExternalCechCupDegreeMaps_ι]
  erw [HomologicalComplex.mapBifunctor.d_eq, Preadditive.add_comp,
    Preadditive.comp_add, HomologicalComplex.mapBifunctor.ι_D₁_assoc,
    HomologicalComplex.mapBifunctor.ι_D₂_assoc]
  erw [HomologicalComplex.mapBifunctor.d₁_eq A B (curriedTensor (ModuleCat.{w} k))
    (ComplexShape.up ℕ) (show (ComplexShape.up ℕ).Rel p (p + 1) from rfl) q
    (p + q + 1) (by dsimp [ComplexShape.π]; omega)]
  erw [HomologicalComplex.mapBifunctor.d₂_eq A B (curriedTensor (ModuleCat.{w} k))
    (ComplexShape.up ℕ) p (show (ComplexShape.up ℕ).Rel q (q + 1) from rfl)
    (p + q + 1) (by dsimp [ComplexShape.π]; omega)]
  dsimp only [picardExternalCechCupDegreeMaps]
  erw [Linear.units_smul_comp, Linear.units_smul_comp]
  simp only [Category.assoc]
  erw [HomologicalComplex.ι_mapBifunctorDesc, HomologicalComplex.ι_mapBifunctorDesc]
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro a b
  change C.d (p + q) (p + q + 1) (l p q (a ⊗ₜ[k] b)) = _
  simp only [ModuleCat.hom_add, ModuleCat.hom_smul, ModuleCat.hom_comp,
    LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply]
  change C.d (p + q) (p + q + 1) (l p q (a ⊗ₜ[k] b)) =
    (1 : ℤˣ) • eqToHom (congrArg C.X (Nat.add_right_comm p 1 q))
      (l (p + 1) q ((A.d p (p + 1) a) ⊗ₜ[k] b)) +
    ((-1 : ℤˣ) ^ p) • eqToHom (congrArg C.X (Nat.add_assoc p q 1).symm)
      (l p (q + 1) (a ⊗ₜ[k] (B.d q (q + 1) b)))
  simp only [one_smul, Units.smul_def]
  change C.d (p + q) (p + q + 1) (l p q (a ⊗ₜ[k] b)) =
    eqToHom (congrArg C.X (Nat.add_right_comm p 1 q))
      (l (p + 1) q ((A.d p (p + 1) a) ⊗ₜ[k] b)) +
    (-1 : ℤ) ^ p • eqToHom (congrArg C.X (Nat.add_assoc p q 1).symm)
      (l p (q + 1) (a ⊗ₜ[k] (B.d q (q + 1) b)))
  apply (forgetCech (pullback.fst f g ≫ f)
    (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
      pullback.snd f g ⁻¹ᵁ V ij.2) (externalCupCoefficients f g F G)
    (p + q + 1)).injective
  dsimp only [A, B, C]
  erw [forgetCech_d]
  simp only [map_add, map_zsmul]
  rw [forgetCech_cast (pullback.fst f g ≫ f)
      (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
        pullback.snd f g ⁻¹ᵁ V ij.2) (externalCupCoefficients f g F G)
      (Nat.add_right_comm p 1 q)
      (l (p + 1) q ((((picardCechFunctor f U).obj F).d p (p + 1) a) ⊗ₜ[k] b)),
    forgetCech_cast (pullback.fst f g ≫ f)
      (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
        pullback.snd f g ⁻¹ᵁ V ij.2) (externalCupCoefficients f g F G)
      (Nat.add_assoc p q 1).symm
      (l p (q + 1) (a ⊗ₜ[k] (((picardCechFunctor g V).obj G).d q (q + 1) b)))]
  erw [bidegree_eq f g U V F G l hl, bidegree_eq f g U V F G l hl,
    bidegree_eq f g U V F G l hl]
  erw [cechCupCochain_leibniz]
  dsimp only [frontCech, backCech]
  rw [pullCech_d f (pullback.fst f g) U
      (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
        pullback.snd f g ⁻¹ᵁ V ij.2) Prod.fst (fun _ ↦ inf_le_left) F p a,
    pullCech_d g (pullback.snd f g) V
      (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
        pullback.snd f g ⁻¹ᵁ V ij.2) Prod.snd (fun _ ↦ inf_le_right) G q b]
  rfl

end
end AlgebraicGeometry.Scheme.Modules
