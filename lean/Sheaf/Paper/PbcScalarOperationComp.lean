/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups Q30 and A2
-/
module

public import Sheaf.Paper.PbcScalarOperationIdentity
import all Sheaf.Paper.PbcScalarAmbientOperations

/-! # Composition and coefficient-tower coherence of scalar operations

Source: blueprint proper base change, order 1307; Milne, Section 19.
Existing declarations extracted from `PbcScalarExtension` to bound compilation cost.
(blueprint: lem-pbc-scalar-operation-composition-coherence)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.ProEtale
open scoped TensorProduct
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [local irreducible] AlgebraicGeometry.Scheme.pbcRationalCoefficientEquiv
namespace AlgebraicGeometry.Scheme
section AmbientOperations
variable (l : ℕ) [Fact l.Prime]
    (E F : Type u) [Field E] [Field F] [Algebra ℚ_[l] E] [Algebra ℚ_[l] F]
    [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] F] (i : E →ₐ[ℚ_[l]] F)
variable {X Y : Scheme.{u}} (g : X ⟶ Y)

variable {Z : Scheme.{u}} (h : Z ⟶ X)

/-- The ordinary pullback comparison respects the same canonical pasting.
Source: blueprint order 1307 (blueprint: lem-pbc-scalar-operation-composition-coherence).
Proof: on flat-term K-flat models both paths are the ordinary adjunction conjugate
of the sectionwise coefficient square for the iterated fiber product. Its pasting
is the coefficient square for the composite. Universal derived counits descend
that equality, with the indicated composition comparisons retained. -/
theorem pbcScalarOrdinaryPull_comp
    (K : PbcCompletedDerived Y (pbcIntegralDatum l E)) :
    (pbcActualDerivedPull h (pbcIntegralDatum l F)).map
        ((pbcScalarOrdinaryPullIso l E F i g).hom.app K) ≫
      (pbcScalarOrdinaryPullIso l E F i h).hom.app
        ((pbcActualDerivedPull g (pbcIntegralDatum l E)).obj K) =
    (pbcActualDerivedPullCompIso h g (pbcIntegralDatum l F)).inv.app
        ((pbcEmbeddingAmbientTensor l E F i Y).obj K) ≫
      (pbcScalarOrdinaryPullIso l E F i (h ≫ g)).hom.app K ≫
      (pbcEmbeddingAmbientTensor l E F i Z).map
        ((pbcActualDerivedPullCompIso h g (pbcIntegralDatum l E)).hom.app K) := by
  sorry

private theorem scalarMate_comp
    {C₁ C₂ C₃ D₁ D₂ D₃ : Type*}
    [Category C₁] [Category C₂] [Category C₃]
    [Category D₁] [Category D₂] [Category D₃]
    {L₁ : C₁ ⥤ C₂} {R₁ : C₂ ⥤ C₁} (a₁ : L₁ ⊣ R₁)
    {L₂ : C₂ ⥤ C₃} {R₂ : C₃ ⥤ C₂} (a₂ : L₂ ⊣ R₂)
    {M₁ : D₁ ⥤ D₂} {S₁ : D₂ ⥤ D₁} (b₁ : M₁ ⊣ S₁)
    {M₂ : D₂ ⥤ D₃} {S₂ : D₃ ⥤ D₂} (b₂ : M₂ ⊣ S₂)
    {L : C₁ ⥤ C₃} {R : C₃ ⥤ C₁} (a : L ⊣ R)
    {M : D₁ ⥤ D₃} {S : D₃ ⥤ D₁} (b : M ⊣ S)
    {F : C₁ ⥤ D₁} {G : C₂ ⥤ D₂} {H : C₃ ⥤ D₃}
    (α : TwoSquare F L₁ M₁ G) (β : TwoSquare G L₂ M₂ H)
    (γ : TwoSquare F L M H) (u : L ≅ L₁ ⋙ L₂) (v : M ≅ M₁ ⋙ M₂)
    (ho : ∀ K : C₁, M₂.map (α.natTrans.app K) ≫ β.natTrans.app (L₁.obj K) =
      v.inv.app (F.obj K) ≫ γ.natTrans.app K ≫ H.map (u.hom.app K)) (K : C₃) :
    (mateEquiv a₁ b₁ α).natTrans.app (R₂.obj K) ≫
        S₁.map ((mateEquiv a₂ b₂ β).natTrans.app K) ≫
        (conjugateIsoEquiv (b₁.comp b₂) b v).hom.app (H.obj K) =
      F.map ((conjugateIsoEquiv (a₁.comp a₂) a u).hom.app K) ≫
        (mateEquiv a b γ).natTrans.app K := by
  have hs : (TwoSquare.vComp α β).whiskerLeft u.inv = γ.whiskerRight v.inv := by
    ext T
    have ht := congrArg (fun z ↦ z ≫ H.map (u.inv.app T)) (ho T)
    simp only [Category.assoc] at ht
    rw [← H.map_comp, Iso.hom_inv_id_app, H.map_id] at ht
    have htid := congrArg (fun z ↦ v.inv.app (F.obj T) ≫ z)
      (Category.comp_id (γ.natTrans.app T))
    have ht' := ht.trans htid
    simpa only [TwoSquare.vComp, TwoSquare.whiskerLeft, TwoSquare.whiskerRight,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Category.id_comp, Category.comp_id, Category.assoc] using ht'
  have hm := congrArg (mateEquiv a (b₁.comp b₂)) hs
  rw [conjugateEquiv_mateEquiv_vcomp a (a₁.comp a₂) (b₁.comp b₂),
    mateEquiv_conjugateEquiv_vcomp a b (b₁.comp b₂),
    mateEquiv_hcomp a₁ b₁ a₂ b₂] at hm
  have hc := congrArg (fun z ↦ z.natTrans.app K) hm
  simp only [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.hComp,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id] at hc
  rw [← conjugateIsoEquiv_apply_inv, ← conjugateIsoEquiv_apply_inv] at hc
  apply (cancel_epi (F.map ((conjugateIsoEquiv (a₁.comp a₂) a u).inv.app K))).mp
  have ht := congrArg
    (fun z ↦ z ≫ (conjugateIsoEquiv (b₁.comp b₂) b v).hom.app (H.obj K)) hc
  simp only [Category.assoc] at ht
  rw [Iso.inv_hom_id_app] at ht
  have ht' := ht.trans (Category.comp_id ((mateEquiv a b γ).natTrans.app K))
  simpa only [Category.assoc, ← F.map_comp_assoc,
    Iso.inv_hom_id_app, F.map_id, Category.id_comp] using ht'

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Direct-image comparison respects composition with its canonical adjunction pasting.
Source: blueprint order 1307 (blueprint: lem-pbc-scalar-operation-composition-coherence).
Proof: the counit of a composite adjunction is the composite of its two counits.
Tensoring those counits with one is consequently the same projection mate on
both paths. The canonical balancing comparison identifies their coefficients,
and the derived universal comparisons preserve this equality. -/
theorem pbcScalarDirectImage_comp
    (K : PbcCompletedDerived Z (pbcIntegralDatum l E)) :
    (pbcScalarDirectImageIso l E F i g).hom.app
        ((pbcActualDerivedPush h (pbcIntegralDatum l E)).obj K) ≫
      (pbcActualDerivedPush g (pbcIntegralDatum l F)).map
        ((pbcScalarDirectImageIso l E F i h).hom.app K) ≫
      (pbcActualDerivedDirectCompIso h g (pbcIntegralDatum l F)).hom.app
        ((pbcEmbeddingAmbientTensor l E F i Z).obj K) =
    (pbcEmbeddingAmbientTensor l E F i Y).map
        ((pbcActualDerivedDirectCompIso h g (pbcIntegralDatum l E)).hom.app K) ≫
      (pbcScalarDirectImageIso l E F i (h ≫ g)).hom.app K := by
  have hm := scalarMate_comp
    (pbcActualDerivedAdjunction g (pbcIntegralDatum l E))
    (pbcActualDerivedAdjunction h (pbcIntegralDatum l E))
    (pbcActualDerivedAdjunction g (pbcIntegralDatum l F))
    (pbcActualDerivedAdjunction h (pbcIntegralDatum l F))
    (pbcActualDerivedAdjunction (h ≫ g) (pbcIntegralDatum l E))
    (pbcActualDerivedAdjunction (h ≫ g) (pbcIntegralDatum l F))
    (TwoSquare.mk _ _ _ _ (pbcScalarOrdinaryPullIso l E F i g).hom)
    (TwoSquare.mk _ _ _ _ (pbcScalarOrdinaryPullIso l E F i h).hom)
    (TwoSquare.mk _ _ _ _ (pbcScalarOrdinaryPullIso l E F i (h ≫ g)).hom)
    (pbcActualDerivedPullCompIso h g (pbcIntegralDatum l E))
    (pbcActualDerivedPullCompIso h g (pbcIntegralDatum l F))
    (pbcScalarOrdinaryPull_comp l E F i g h) K
  simpa only [pbcScalarDirectImageIso_hom, pbcScalarDirectImageMap,
    pbcActualScalarDirectImageMap, pbcScalarOrdinaryPullIso,
    pbcActualDerivedDirectCompIso] using hm



variable (G : Type u) [Field G] [Algebra ℚ_[l] G] [FiniteDimensional ℚ_[l] G]
    (j : F →ₐ[ℚ_[l]] G)

/-- Pullback comparison respects successive finite coefficient extensions.
Source: blueprint order 1307 (blueprint: lem-pbc-scalar-operation-composition-coherence).
Proof: on resolving complexes all three coefficient extensions are sheafified
tensor. The two paths multiply exactly the same coefficients in the same order.
Associativity identifies them before localization; the prescribed derived
counits give the displayed equality of derived morphisms. -/
theorem pbcScalarOrdinaryPull_coefficients
    (K : PbcCompletedDerived Y (pbcIntegralDatum l E)) :
    (pbcScalarOrdinaryPullIso l F G j g).hom.app
        ((pbcEmbeddingAmbientTensor l E F i Y).obj K) ≫
      (pbcEmbeddingAmbientTensor l F G j X).map
        ((pbcScalarOrdinaryPullIso l E F i g).hom.app K) ≫
      (pbcAmbientScalarComp l E F G i j X).hom.app
        ((pbcActualDerivedPull g (pbcIntegralDatum l E)).obj K) =
    (pbcActualDerivedPull g (pbcIntegralDatum l G)).map
        ((pbcAmbientScalarComp l E F G i j Y).hom.app K) ≫
      (pbcScalarOrdinaryPullIso l E G (j.comp i) g).hom.app K := by
  sorry

private theorem scalarMate_coefficients
    {C D E C' D' E' : Type*}
    [Category C] [Category D] [Category E]
    [Category C'] [Category D'] [Category E']
    {L₁ : C ⥤ C'} {R₁ : C' ⥤ C} (a₁ : L₁ ⊣ R₁)
    {L₂ : D ⥤ D'} {R₂ : D' ⥤ D} (a₂ : L₂ ⊣ R₂)
    {L₃ : E ⥤ E'} {R₃ : E' ⥤ E} (a₃ : L₃ ⊣ R₃)
    {F : C ⥤ D} {F' : C' ⥤ D'} {G : D ⥤ E} {G' : D' ⥤ E'}
    {H : C ⥤ E} {H' : C' ⥤ E'}
    (α : TwoSquare F L₁ L₂ F') (β : TwoSquare G L₂ L₃ G')
    (γ : TwoSquare H L₁ L₃ H') (u : F ⋙ G ≅ H) (v : F' ⋙ G' ≅ H')
    (ho : ∀ T : C, β.natTrans.app (F.obj T) ≫ G'.map (α.natTrans.app T) ≫
      v.hom.app (L₁.obj T) = L₃.map (u.hom.app T) ≫ γ.natTrans.app T) (K : C') :
    G.map ((mateEquiv a₁ a₂ α).natTrans.app K) ≫
        (mateEquiv a₂ a₃ β).natTrans.app (F'.obj K) ≫ R₃.map (v.hom.app K) =
      u.hom.app (R₁.obj K) ≫ (mateEquiv a₁ a₃ γ).natTrans.app K := by
  have hs : ((TwoSquare.hComp α β).whiskerTop u.inv).whiskerBottom v.hom = γ := by
    ext T
    have ht := congrArg (fun z ↦ L₃.map (u.inv.app T) ≫ z) (ho T)
    simp only [← L₃.map_comp_assoc, Iso.inv_hom_id_app, L₃.map_id,
      Category.id_comp] at ht
    simpa only [TwoSquare.hComp, TwoSquare.whiskerTop, TwoSquare.whiskerBottom,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Category.id_comp, Category.comp_id, Category.assoc] using ht
  have hm := mateEquiv_whiskerTop_whiskerBottom a₁ a₃ (TwoSquare.hComp α β)
    u.inv v.hom
  rw [hs, mateEquiv_vcomp a₁ a₂ a₃] at hm
  have hc := congrArg (fun z ↦ z.natTrans.app K) hm
  apply (cancel_epi (u.inv.app (R₁.obj K))).mp
  change _ = u.inv.app _ ≫ u.hom.app _ ≫ _
  simpa only [TwoSquare.whiskerRight, TwoSquare.whiskerLeft, TwoSquare.vComp,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Category.assoc, Iso.inv_hom_id_app_assoc] using hc.symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Direct-image comparison respects successive finite coefficient extensions.
Source: blueprint order 1307 (blueprint: lem-pbc-scalar-operation-composition-coherence).
Proof: the two composites are projection mates with the same counit tensored
with the product coefficient. Ordinary tensor balancing sends the iterated
coefficient tensor to that product. The universal derived normalizations make
this equality independent of the chosen flat representative. -/
theorem pbcScalarDirectImage_coefficients
    (K : PbcCompletedDerived X (pbcIntegralDatum l E)) :
    (pbcEmbeddingAmbientTensor l F G j Y).map
        ((pbcScalarDirectImageIso l E F i g).hom.app K) ≫
      (pbcScalarDirectImageIso l F G j g).hom.app
        ((pbcEmbeddingAmbientTensor l E F i X).obj K) ≫
      (pbcActualDerivedPush g (pbcIntegralDatum l G)).map
        ((pbcAmbientScalarComp l E F G i j X).hom.app K) =
    (pbcAmbientScalarComp l E F G i j Y).hom.app
        ((pbcActualDerivedPush g (pbcIntegralDatum l E)).obj K) ≫
      (pbcScalarDirectImageIso l E G (j.comp i) g).hom.app K := by
  have hm := scalarMate_coefficients
    (pbcActualDerivedAdjunction g (pbcIntegralDatum l E))
    (pbcActualDerivedAdjunction g (pbcIntegralDatum l F))
    (pbcActualDerivedAdjunction g (pbcIntegralDatum l G))
    (TwoSquare.mk _ _ _ _ (pbcScalarOrdinaryPullIso l E F i g).hom)
    (TwoSquare.mk _ _ _ _ (pbcScalarOrdinaryPullIso l F G j g).hom)
    (TwoSquare.mk _ _ _ _ (pbcScalarOrdinaryPullIso l E G (j.comp i) g).hom)
    (pbcAmbientScalarComp l E F G i j Y) (pbcAmbientScalarComp l E F G i j X)
    (pbcScalarOrdinaryPull_coefficients l E F i g G j) K
  simpa only [pbcScalarDirectImageIso_hom, pbcScalarDirectImageMap,
    pbcActualScalarDirectImageMap, pbcScalarOrdinaryPullIso] using hm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Completion comparison respects successive coefficients with its actual unit.
Source: blueprint order 1307 (blueprint: lem-pbc-scalar-operation-composition-coherence).
Proof: both composites preserve the completion unit, since each comparison and
the balancing associator does. The completion reflector's uniqueness therefore
identifies them. This is also the strict quotient-tower calculation followed by
derived inverse limit, so includes every transition and the augmentation. -/
theorem pbcScalarCompletion_coefficients (W : Scheme.{u})
    (K : PbcCompletedDerived W (pbcIntegralDatum l E)) :
    (pbcScalarCompletionIso l F G j W).hom.app
        ((pbcEmbeddingAmbientTensor l E F i W).obj K) ≫
      (pbcEmbeddingAmbientTensor l F G j W).map
        ((pbcScalarCompletionIso l E F i W).hom.app K) ≫
      (pbcAmbientScalarComp l E F G i j W).hom.app
        ((pbcActualCompletion (pbcIntegralDatum l E) W).obj K) =
    (pbcActualCompletion (pbcIntegralDatum l G) W).map
        ((pbcAmbientScalarComp l E F G i j W).hom.app K) ≫
      (pbcScalarCompletionIso l E G (j.comp i) W).hom.app K := by
  let A := pbcEmbeddingAmbientTensor l E F i W
  let B := pbcEmbeddingAmbientTensor l F G j W
  let C := pbcEmbeddingAmbientTensor l E G (j.comp i) W
  let ηE := pbcActualCompletionUnit (pbcIntegralDatum l E) W
  let ηF := pbcActualCompletionUnit (pbcIntegralDatum l F) W
  let ηG := pbcActualCompletionUnit (pbcIntegralDatum l G) W
  let α := pbcAmbientScalarComp l E F G i j W
  let eEF := pbcScalarCompletionIso l E F i W
  let eFG := pbcScalarCompletionIso l F G j W
  let eEG := pbcScalarCompletionIso l E G (j.comp i) W
  have hEF : ηF.app (A.obj K) ≫ eEF.hom.app K = A.map (ηE.app K) := by
    dsimp only [eEF]
    unfold pbcScalarCompletionIso
    exact (pbcScalarCompletionIso_exists l E F i W).exists.choose_spec K
  have hFG : ηG.app (B.obj (A.obj K)) ≫ eFG.hom.app (A.obj K) =
      B.map (ηF.app (A.obj K)) := by
    dsimp only [eFG]
    unfold pbcScalarCompletionIso
    exact (pbcScalarCompletionIso_exists l F G j W).exists.choose_spec (A.obj K)
  have hEG : ηG.app (C.obj K) ≫ eEG.hom.app K = C.map (ηE.app K) := by
    dsimp only [eEG]
    unfold pbcScalarCompletionIso
    exact (pbcScalarCompletionIso_exists l E G (j.comp i) W).exists.choose_spec K
  have hc : PbcIsIntrinsicallyComplete W (pbcIntegralDatum l E)
      ((pbcActualCompletion (pbcIntegralDatum l E) W).obj K) :=
    ((ObjectProperty.ι (PbcIsIntrinsicallyComplete W (pbcIntegralDatum l E)
      )).leftAdjoint.obj K).property
  apply pbcCompletion_hom_ext W (pbcIntegralDatum l G) _ _
    (pbcScalarPreservesComplete l E G (j.comp i) W ⟨_, hc⟩)
  change ηG.app (B.obj (A.obj K)) ≫
      (eFG.hom.app (A.obj K) ≫ B.map (eEF.hom.app K) ≫
        α.hom.app ((pbcActualCompletion (pbcIntegralDatum l E) W).obj K)) =
    ηG.app (B.obj (A.obj K)) ≫
      ((pbcActualCompletion (pbcIntegralDatum l G) W).map (α.hom.app K) ≫ eEG.hom.app K)
  calc
    _ = B.map (A.map (ηE.app K)) ≫
        α.hom.app ((pbcActualCompletion (pbcIntegralDatum l E) W).obj K) := by
      rw [← Category.assoc, ← Category.assoc, hFG,
        ← CategoryTheory.Functor.map_comp, hEF]
    _ = α.hom.app K ≫ C.map (ηE.app K) := α.hom.naturality (ηE.app K)
    _ = _ := by
      have hn : ηG.app (B.obj (A.obj K)) ≫
          (pbcActualCompletion (pbcIntegralDatum l G) W).map (α.hom.app K) =
          α.hom.app K ≫ ηG.app (C.obj K) := by
        exact (ηG.naturality (α.hom.app K)).symm
      rw [← Category.assoc, hn, Category.assoc, hEG]


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Pullback comparison respects successive finite coefficient extensions.
Source: blueprint order 1307 (blueprint: lem-pbc-scalar-operation-composition-coherence).
Proof: the ordinary comparison is balanced on K-flat models. The three coefficient
extensions are sheafified tensor. The two paths multiply exactly the same
coefficients in the same order.
Associativity identifies them before localization; the prescribed derived
counits give the displayed equality of derived morphisms. -/
theorem pbcScalarCompletedPull_coefficients
    (K : PbcCompletedDerived Y (pbcIntegralDatum l E)) :
    (pbcScalarCompletedPullIso l F G j g).hom.app
        ((pbcEmbeddingAmbientTensor l E F i Y).obj K) ≫
      (pbcEmbeddingAmbientTensor l F G j X).map
        ((pbcScalarCompletedPullIso l E F i g).hom.app K) ≫
      (pbcAmbientScalarComp l E F G i j X).hom.app
        ((pbcActualCompletedPull g (pbcIntegralDatum l E)).obj K) =
    (pbcActualCompletedPull g (pbcIntegralDatum l G)).map
        ((pbcAmbientScalarComp l E F G i j Y).hom.app K) ≫
      (pbcScalarCompletedPullIso l E G (j.comp i) g).hom.app K := by
  let A := pbcEmbeddingAmbientTensor l E F i X
  let B := pbcEmbeddingAmbientTensor l F G j X
  let L := pbcActualDerivedPull g (pbcIntegralDatum l E)
  let M := pbcActualDerivedPull g (pbcIntegralDatum l F)
  let Λ := pbcActualCompletion (pbcIntegralDatum l G) X
  let e := pbcScalarOrdinaryPullIso l E F i g
  let f := pbcScalarOrdinaryPullIso l F G j g
  let d := pbcScalarOrdinaryPullIso l E G (j.comp i) g
  let c := pbcScalarCompletionIso l F G j X
  let b := pbcScalarCompletionIso l E F i X
  let a := pbcScalarCompletionIso l E G (j.comp i) X
  let α := pbcAmbientScalarComp l E F G i j X
  let β := pbcAmbientScalarComp l E F G i j Y
  have hn : c.hom.app ((M.obj
      ((pbcEmbeddingAmbientTensor l E F i Y).obj K))) ≫
      B.map ((pbcActualCompletion (pbcIntegralDatum l F) X).map (e.hom.app K)) =
      Λ.map (B.map (e.hom.app K)) ≫ c.hom.app (A.obj (L.obj K)) :=
    (c.hom.naturality (e.hom.app K)).symm
  have hc : c.hom.app (A.obj (L.obj K)) ≫ B.map (b.hom.app (L.obj K)) ≫
      α.hom.app ((pbcActualCompletion (pbcIntegralDatum l E) X).obj (L.obj K)) =
      Λ.map (α.hom.app (L.obj K)) ≫ a.hom.app (L.obj K) :=
    pbcScalarCompletion_coefficients l E F i G j X (L.obj K)
  have ho : f.hom.app ((pbcEmbeddingAmbientTensor l E F i Y).obj K) ≫
      B.map (e.hom.app K) ≫ α.hom.app (L.obj K) =
      (pbcActualDerivedPull g (pbcIntegralDatum l G)).map (β.hom.app K) ≫
        d.hom.app K := pbcScalarOrdinaryPull_coefficients l E F i g G j K
  rw [pbcScalarCompletedPullIso_hom, pbcScalarCompletedPullIso_hom,
    pbcScalarCompletedPullIso_hom, CategoryTheory.Functor.map_comp]
  change (Λ.map (f.hom.app _) ≫ c.hom.app _) ≫
      (B.map ((pbcActualCompletion (pbcIntegralDatum l F) X).map (e.hom.app K)) ≫
        B.map (b.hom.app (L.obj K))) ≫ α.hom.app _ =
    Λ.map ((pbcActualDerivedPull g (pbcIntegralDatum l G)).map (β.hom.app K)) ≫
      (Λ.map (d.hom.app K) ≫ a.hom.app (L.obj K))
  calc
    _ = Λ.map (f.hom.app _) ≫ Λ.map (B.map (e.hom.app K)) ≫
        (c.hom.app (A.obj (L.obj K)) ≫ B.map (b.hom.app (L.obj K)) ≫
          α.hom.app _) := by
      simp only [Category.assoc]
      rw [← Category.assoc (c.hom.app _) (B.map _) _, hn]
      simp only [Category.assoc]
    _ = _ := by
      rw [hc, ← CategoryTheory.Functor.map_comp_assoc,
        ← CategoryTheory.Functor.map_comp_assoc, Category.assoc, ho,
        CategoryTheory.Functor.map_comp]
      simp only [Category.assoc]


end AmbientOperations


end AlgebraicGeometry.Scheme
