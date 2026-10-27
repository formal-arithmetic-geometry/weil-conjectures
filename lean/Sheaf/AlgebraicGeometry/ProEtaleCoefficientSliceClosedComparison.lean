/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q115
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleCoefficientSliceComparisonData
import Sheaf.AlgebraicGeometry.ProEtaleSliceOrdinaryComparison
import Sheaf.AlgebraicGeometry.ProEtaleSliceMonoidalDescent
import Sheaf.AlgebraicGeometry.ProEtaleSliceClosedMates

/-! # Closed slice comparison with transported coefficients

Source: Hemo--Richarz--Scholbach, Lemma 4.5; Stacks 03CE, 07A4, 08J9, 08JB.
(blueprint: lem-zl-proetale-coefficient-slice-closed-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u u₁ v₁ u₂ v₂
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
namespace AlgebraicGeometry.Scheme

private theorem scalarEvaluation_naturality
    {D : Type*} [Category.{v₁} D] {H : Dᵒᵖ × D ⥤ D}
    (S : CoefficientClosedStructure H) (P Q P' Q' : D)
    (f : P' ⟶ P) (g : Q ⟶ Q') :
    S.tensor.map (Prod.mkHom (H.map (Prod.mkHom f.op g)) (𝟙 P')) ≫
        S.evaluation P' Q' =
      S.tensor.map (Prod.mkHom (𝟙 _) f) ≫ S.evaluation P Q ≫ g := by
  let := S.monoidal
  have he : S.tensor.map (Prod.mkHom (H.map (Prod.mkHom f.op (𝟙 Q))) (𝟙 P')) ≫
      S.evaluation P' Q = S.tensor.map (Prod.mkHom (𝟙 _) f) ≫ S.evaluation P Q := by
    simpa [CoefficientClosedStructure.tensor, CoefficientClosedStructure.evaluation] using
      S.evaluation_naturality P P' Q f
  have hg : S.tensor.map (Prod.mkHom (H.map (Prod.mkHom (𝟙 (op P')) g)) (𝟙 P')) ≫
      S.evaluation P' Q' = S.evaluation P' Q ≫ g := by
    simpa [CoefficientClosedStructure.tensor, CoefficientClosedStructure.evaluation] using
      (S.adjunction P').counit.naturality g
  have hh : H.map (Prod.mkHom f.op g) =
      H.map (Prod.mkHom f.op (𝟙 Q)) ≫ H.map (Prod.mkHom (𝟙 (op P')) g) := by
    rw [← H.map_comp]
    congr 1
    ext <;> simp
  rw [hh]
  have ht : Prod.mkHom
      (H.map (Prod.mkHom f.op (𝟙 Q)) ≫ H.map (Prod.mkHom (𝟙 (op P')) g)) (𝟙 P') =
      Prod.mkHom (H.map (Prod.mkHom f.op (𝟙 Q))) (𝟙 P') ≫
        Prod.mkHom (H.map (Prod.mkHom (𝟙 (op P')) g)) (𝟙 P') := by
    ext <;> simp
  rw [ht, S.tensor.map_comp, Category.assoc, hg, ← Category.assoc, he]
  exact Category.assoc _ _ _

private theorem scalarBaseChangeHom_naturality
    {A : Type*} {B : Type*} [Category.{v₁} A] [Category.{v₂} B]
    {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B}
    (SA : CoefficientClosedStructure HA) (SB : CoefficientClosedStructure HB)
    (F : A ⥤ B) (μ : SA.tensor ⋙ F ≅ F.prod F ⋙ SB.tensor)
    (P Q P' Q' : A) (f : P' ⟶ P) (g : Q ⟶ Q') :
    F.map (HA.map (Prod.mkHom f.op g)) ≫ coefficientClosedPullbackMap SA SB F μ P' Q' =
      coefficientClosedPullbackMap SA SB F μ P Q ≫
        HB.map (Prod.mkHom (F.map f).op (F.map g)) := by
  let := SB.monoidal
  have hu (T P Q : B) (h : T ⟶ HB.obj (op P, Q)) :
      (SB.transpose T P Q).symm h =
        SB.tensor.map (Prod.mkHom h (𝟙 P)) ≫ SB.evaluation P Q := by
    simpa [CoefficientClosedStructure.transpose, CoefficientClosedStructure.tensor,
      CoefficientClosedStructure.evaluation] using! (SB.adjunction P).homEquiv_counit T Q h
  apply (SB.transpose _ (F.obj P') (F.obj Q')).symm.injective
  rw [hu, hu]
  have tc {U V Z R : B} (a : U ⟶ V) (b : V ⟶ Z) :
      SB.tensor.map (Prod.mkHom (a ≫ b) (𝟙 R)) =
        SB.tensor.map (Prod.mkHom a (𝟙 R)) ≫ SB.tensor.map (Prod.mkHom b (𝟙 R)) := by
    rw [← SB.tensor.map_comp]
    congr 1
    ext <;> simp
  simp only [tc, Category.assoc]
  rw [scalarEvaluation_naturality SB _ _ _ _ (F.map f) (F.map g)]
  have beta (U V : A) :
      SB.tensor.map (Prod.mkHom (coefficientClosedPullbackMap SA SB F μ U V) (𝟙 (F.obj U))) ≫
        SB.evaluation (F.obj U) (F.obj V) =
          μ.inv.app (HA.obj (op U, V), U) ≫ F.map (SA.evaluation U V) := by
    rw [← hu, coefficientClosedPullbackMap, Equiv.symm_apply_apply]
    rfl
  rw [beta]
  have hn := μ.inv.naturality (Prod.mkHom (HA.map (Prod.mkHom f.op g)) (𝟙 P'))
  have hn' := μ.inv.naturality (Prod.mkHom (𝟙 (HA.obj (op P, Q))) f)
  dsimp only [Functor.comp_map, Functor.prod_map] at hn hn'
  erw [F.map_id] at hn
  erw [F.map_id] at hn'
  rw [← Category.assoc, hn, Category.assoc, ← F.map_comp, scalarEvaluation_naturality SA]
  rw [F.map_comp, F.map_comp]
  have ht : SB.tensor.map
      (Prod.mkHom (coefficientClosedPullbackMap SA SB F μ P Q) (𝟙 (F.obj P'))) ≫
      SB.tensor.map (Prod.mkHom (𝟙 _) (F.map f)) =
    SB.tensor.map (Prod.mkHom (𝟙 _) (F.map f)) ≫
      SB.tensor.map (Prod.mkHom (coefficientClosedPullbackMap SA SB F μ P Q) (𝟙 (F.obj P))) := by
    rw [← SB.tensor.map_comp, ← SB.tensor.map_comp]
    congr 1
    ext <;> simp
  rw [reassoc_of% ht, reassoc_of% beta P Q, ← reassoc_of% hn']

private theorem scalarUncurry
    {D : Type*} [Category.{v₁} D] {H : Dᵒᵖ × D ⥤ D}
    (S : CoefficientClosedStructure H) (T P Q : D) (h : T ⟶ H.obj (op P, Q)) :
    (S.transpose T P Q).symm h =
      S.tensor.map (Prod.mkHom h (𝟙 P)) ≫ S.evaluation P Q := by
  let := S.monoidal
  simpa [CoefficientClosedStructure.transpose, CoefficientClosedStructure.tensor,
    CoefficientClosedStructure.evaluation] using! (S.adjunction P).homEquiv_counit T Q h

private theorem scalarTensor_comp
    {D : Type*} [Category.{v₁} D] {H : Dᵒᵖ × D ⥤ D}
    (S : CoefficientClosedStructure H) {X Y Z U V W : D}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : U ⟶ V) (k : V ⟶ W) :
    S.tensor.map (Prod.mkHom (f ≫ g) (h ≫ k)) =
      S.tensor.map (Prod.mkHom f h) ≫ S.tensor.map (Prod.mkHom g k) :=
  S.tensor.map_comp (Prod.mkHom f h) (Prod.mkHom g k)

private theorem scalarUncurry_pre
    {D : Type*} [Category.{v₁} D] {H : Dᵒᵖ × D ⥤ D}
    (S : CoefficientClosedStructure H) {T U P Q : D}
    (f : T ⟶ U) (h : U ⟶ H.obj (op P, Q)) :
    (S.transpose T P Q).symm (f ≫ h) =
      S.tensor.map (Prod.mkHom f (𝟙 P)) ≫ (S.transpose U P Q).symm h := by
  rw [scalarUncurry, scalarUncurry]
  simpa only [Category.id_comp, Category.assoc] using
    congrArg (fun k ↦ k ≫ S.evaluation P Q) (scalarTensor_comp S f h (𝟙 P) (𝟙 P))

private theorem scalarUncurry_post
    {D : Type*} [Category.{v₁} D] {H : Dᵒᵖ × D ⥤ D}
    (S : CoefficientClosedStructure H) {T P Q P' Q' : D}
    (h : T ⟶ H.obj (op P, Q)) (f : P' ⟶ P) (g : Q ⟶ Q') :
    (S.transpose T P' Q').symm (h ≫ H.map (Prod.mkHom f.op g)) =
      S.tensor.map (Prod.mkHom (𝟙 T) f) ≫ (S.transpose T P Q).symm h ≫ g := by
  rw [scalarUncurry_pre, scalarUncurry, scalarEvaluation_naturality]
  rw [scalarUncurry]
  simp only [← Category.assoc, ← S.tensor.map_comp]
  congr 2
  congr 1
  ext <;> simp

private theorem scalarBaseChangeHom_beta
    {A : Type*} {B : Type*} [Category.{v₁} A] [Category.{v₂} B]
    {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B}
    (SA : CoefficientClosedStructure HA) (SB : CoefficientClosedStructure HB)
    (F : A ⥤ B) (μ : SA.tensor ⋙ F ≅ F.prod F ⋙ SB.tensor) (P Q : A) :
    (SB.transpose _ (F.obj P) (F.obj Q)).symm (coefficientClosedPullbackMap SA SB F μ P Q) =
      μ.inv.app (HA.obj (op P, Q), P) ≫ F.map (SA.evaluation P Q) :=
  Equiv.symm_apply_apply _ _

private theorem scalarBaseChangeHom_tower
    {A : Type*} {B : Type*} {D : Type u₂}
    [Category.{v₁} A] [Category.{v₂} B] [Category.{u₁} D]
    {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B} {HD : Dᵒᵖ × D ⥤ D}
    (SA : CoefficientClosedStructure HA) (SB : CoefficientClosedStructure HB)
    (SD : CoefficientClosedStructure HD) (F : A ⥤ B) (G : B ⥤ D) (K : A ⥤ D)
    (μ : SA.tensor ⋙ F ≅ F.prod F ⋙ SB.tensor)
    (ν : SB.tensor ⋙ G ≅ G.prod G ⋙ SD.tensor)
    (ξ : SA.tensor ⋙ K ≅ K.prod K ⋙ SD.tensor) (α : F ⋙ G ≅ K)
    (ht : ∀ X Y : A,
      G.map (μ.hom.app (X, Y)) ≫ ν.hom.app (F.obj X, F.obj Y) ≫
          SD.tensor.map (Prod.mkHom (α.hom.app X) (α.hom.app Y)) =
        α.hom.app (SA.tensor.obj (X, Y)) ≫ ξ.hom.app (X, Y)) (P Q : A) :
    G.map (coefficientClosedPullbackMap SA SB F μ P Q) ≫
        coefficientClosedPullbackMap SB SD G ν (F.obj P) (F.obj Q) ≫
        HD.map (Prod.mkHom (α.inv.app P).op (α.hom.app Q)) =
      α.hom.app (HA.obj (op P, Q)) ≫ coefficientClosedPullbackMap SA SD K ξ P Q := by
  have hi (X Y : A) :
      ν.inv.app (F.obj X, F.obj Y) ≫ G.map (μ.inv.app (X, Y)) ≫
          α.hom.app (SA.tensor.obj (X, Y)) =
        SD.tensor.map (Prod.mkHom (α.hom.app X) (α.hom.app Y)) ≫ ξ.inv.app (X, Y) := by
    apply (cancel_mono (ξ.hom.app (X, Y))).1
    simp only [Category.assoc, Iso.inv_hom_id_app]
    rw [← ht]
    simp [← G.map_comp, ← Category.assoc]
  have he : (SD.transpose _ (G.obj (F.obj P)) (G.obj (F.obj Q))).symm
      (G.map (coefficientClosedPullbackMap SA SB F μ P Q) ≫
        coefficientClosedPullbackMap SB SD G ν (F.obj P) (F.obj Q)) =
      ν.inv.app (F.obj (HA.obj (op P, Q)), F.obj P) ≫
        G.map (μ.inv.app (HA.obj (op P, Q), P)) ≫ G.map (F.map (SA.evaluation P Q)) := by
    rw [scalarUncurry_pre, scalarBaseChangeHom_beta]
    have hn := ν.inv.naturality
      (Prod.mkHom (coefficientClosedPullbackMap SA SB F μ P Q) (𝟙 (F.obj P)))
    dsimp only [Functor.comp_map, Functor.prod_map] at hn
    erw [G.map_id] at hn
    rw [← Category.assoc, hn, Category.assoc, ← G.map_comp]
    rw [← scalarUncurry, scalarBaseChangeHom_beta, G.map_comp]
  apply (SD.transpose _ (K.obj P) (K.obj Q)).symm.injective
  rw [← Category.assoc, scalarUncurry_post, he, scalarUncurry_pre,
    scalarBaseChangeHom_beta]
  have hn := α.hom.naturality (SA.evaluation P Q)
  dsimp only [Functor.comp_map] at hn
  simp only [Category.assoc]
  rw [hn, reassoc_of% hi (HA.obj (op P, Q)) P]
  rw [← Category.assoc, ← SD.tensor.map_comp]
  congr 2
  ext <;> simp


private theorem tensor_inverse_square
    {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Category.{v₂} B]
    (H : B × B ⥤ B) (G F : A ⥤ B) (K : A × A ⥤ A) (a : F ≅ G)
    (mu : K ⋙ F ≅ F.prod F ⋙ H) (nu : ∀ L M, G.obj (K.obj (L, M)) ⟶
      H.obj (G.obj L, G.obj M))
    (ht : ∀ L M, mu.hom.app (L, M) ≫
      H.map (Prod.mkHom (a.hom.app L) (a.hom.app M)) =
      a.hom.app (K.obj (L, M)) ≫ nu L M) (L M : A) :
    nu L M ≫ H.map (Prod.mkHom (a.inv.app L) (a.inv.app M)) =
      a.inv.app (K.obj (L, M)) ≫ mu.hom.app (L, M) := by
  apply (cancel_mono (H.mapIso (Iso.prod (a.app L) (a.app M))).hom).mp
  simp only [Functor.mapIso_hom, Iso.prod_hom, Iso.app_hom, Category.assoc]
  rw [← H.map_comp]
  have hi : Prod.mkHom (a.inv.app L) (a.inv.app M) ≫
      Prod.mkHom (a.hom.app L) (a.hom.app M) = 𝟙 _ := by
    ext <;> simp
  rw [hi, H.map_id, Category.comp_id]
  rw [ht]
  simp

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem scalar_equivalence
    {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u₂} RingCat.{u₂})]
    {R B : Sheaf J CommRingCat.{u₂}} (b : R ≅ B) :
    (SheafOfModules.scalarRestriction b.inv).IsEquivalence := by
  let d := (sheafCompose J (forget₂ CommRingCat RingCat)).mapIso b.symm
  have : (CategoryTheory.Equivalence.refl (C := C)).functor.IsContinuous J J :=
    inferInstanceAs (Functor.IsContinuous (𝟭 C) J J)
  have : (CategoryTheory.Equivalence.refl (C := C)).inverse.IsContinuous J J :=
    inferInstanceAs (Functor.IsContinuous (𝟭 C) J J)
  let e : SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ≌
      SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B) :=
    SheafOfModules.pushforwardPushforwardEquivalence
      (CategoryTheory.Equivalence.refl (C := C))
    d.hom d.inv
    (by
      change Functor.whiskerRight (𝟙 (𝟭 Cᵒᵖ))
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj =
          d.inv.hom ≫ d.hom.hom
      rw [Functor.whiskerRight_id']
      exact (congrArg (fun f ↦ f.hom) d.inv_hom_id).symm)
    (by
      change d.hom.hom ≫ d.inv.hom ≫ Functor.whiskerRight (𝟙 (𝟭 Cᵒᵖ))
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B).obj = 𝟙 _
      rw [Functor.whiskerRight_id']
      change d.hom.hom ≫ d.inv.hom ≫
        𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B).obj = 𝟙 _
      rw [Category.comp_id]
      exact congrArg (fun f ↦ f.hom) d.hom_inv_id)
  exact e.isEquivalence_functor

private theorem uncurry_transpose
    {D : Type u₁} [Category.{v₁} D] {H : Dᵒᵖ × D ⥤ D}
    (S : CoefficientClosedStructure H) (A L M : D) (g : S.tensor.obj (A, L) ⟶ M) :
    S.tensor.map (Prod.mkHom (S.transpose A L M g) (𝟙 L)) ≫ S.evaluation L M = g := by
  have h := (S.transpose A L M).symm_apply_apply g
  change ((S.adjunction L).homEquiv A M).symm _ = g at h
  rw [Adjunction.homEquiv_symm_apply] at h
  simpa only [CoefficientClosedStructure.tensor, CoefficientClosedStructure.evaluation,
    MonoidalCategory.tensor_map, MonoidalCategory.tensorRight, Functor.flip,
    MonoidalCategory.curriedTensor, MonoidalCategory.tensorHom_id] using h

private theorem transpose_precomp
    {D : Type u₁} [Category.{v₁} D] {H : Dᵒᵖ × D ⥤ D}
    (S : CoefficientClosedStructure H) {A A' L M : D}
    (a : A' ⟶ A) (g : S.tensor.obj (A, L) ⟶ M) :
    S.transpose A' L M (S.tensor.map (Prod.mkHom a (𝟙 L)) ≫ g) =
      a ≫ S.transpose A L M g := by
  simpa [CoefficientClosedStructure.transpose, CoefficientClosedStructure.tensor,
    Prod.sectR, Functor.comp_obj] using!
    (S.adjunction L).homEquiv_naturality_left a g

private theorem closed_evaluation
    {D : Type u₁} [Category.{v₁} D] {E : Type u₂} [Category.{v₂} E]
    {H : Dᵒᵖ × D ⥤ D} {HB : Eᵒᵖ × E ⥤ E}
    (S : CoefficientClosedStructure H) (SB : CoefficientClosedStructure HB)
    (F : D ⥤ E) (rho : S.tensor ⋙ F ≅ F.prod F ⋙ SB.tensor) (L M : D) :
    SB.tensor.map (Prod.mkHom (coefficientClosedPullbackMap S SB F rho L M)
        (𝟙 (F.obj L))) ≫ SB.evaluation (F.obj L) (F.obj M) =
      (rho.app (H.obj (op L, M), L)).inv ≫ F.map (S.evaluation L M) := by
  exact uncurry_transpose SB _ _ _ _

private theorem closed_transpose
    {D : Type u₁} [Category.{v₁} D] {E : Type u₂} [Category.{v₂} E]
    {H : Dᵒᵖ × D ⥤ D} {HB : Eᵒᵖ × E ⥤ E}
    (S : CoefficientClosedStructure H) (SB : CoefficientClosedStructure HB)
    (F : D ⥤ E) (rho : S.tensor ⋙ F ≅ F.prod F ⋙ SB.tensor)
    (A L M : D) (g : S.tensor.obj (A, L) ⟶ M) :
    SB.transpose _ _ _ ((rho.app (A, L)).inv ≫ F.map g) =
      F.map (S.transpose A L M g) ≫ coefficientClosedPullbackMap S SB F rho L M := by
  unfold coefficientClosedPullbackMap
  rw [← transpose_precomp SB]
  congr 1
  have hn := rho.inv.naturality (Prod.mkHom (S.transpose A L M g) (𝟙 L))
  dsimp only [Functor.comp_map, Functor.prod_map] at hn
  simp only [F.map_id] at hn
  change rho.inv.app (A, L) ≫ F.map g =
    SB.tensor.map (Prod.mkHom (F.map (S.transpose A L M g)) (𝟙 (F.obj L))) ≫
      rho.inv.app (H.obj (op L, M), L) ≫ F.map (S.evaluation L M)
  rw [reassoc_of% hn, ← F.map_comp, uncurry_transpose]

private def closed_iso
    {D : Type u₁} [Category.{v₁} D] {E : Type u₂} [Category.{v₂} E]
    {H : Dᵒᵖ × D ⥤ D} {HB : Eᵒᵖ × E ⥤ E}
    (S : CoefficientClosedStructure H) (SB : CoefficientClosedStructure HB)
    (F : D ⥤ E) (rho : S.tensor ⋙ F ≅ F.prod F ⋙ SB.tensor)
    (h : ∀ L M, IsIso (coefficientClosedPullbackMap S SB F rho L M)) :
    H ⋙ F ≅ (F.op.prod F) ⋙ HB := by
  letI (L M : D) := h L M
  refine NatIso.ofComponents (fun p ↦ asIso
    (coefficientClosedPullbackMap S SB F rho p.1.unop p.2)) ?_
  rintro ⟨L, M⟩ ⟨L', M'⟩ ⟨f, g⟩
  exact scalarBaseChangeHom_naturality S SB F rho
    L.unop M L'.unop M' f.unop g

private theorem closed_equivalence_isIso
    {D : Type u₁} [Category.{v₁} D] {E : Type u₂} [Category.{v₂} E]
    {H : Dᵒᵖ × D ⥤ D} {HB : Eᵒᵖ × E ⥤ E}
    (S : CoefficientClosedStructure H) (SB : CoefficientClosedStructure HB)
    (F : D ⥤ E) [F.IsEquivalence]
    (rho : S.tensor ⋙ F ≅ F.prod F ⋙ SB.tensor) (L M : D) :
    IsIso (coefficientClosedPullbackMap S SB F rho L M) := by
  have hb (A : D) : Function.Bijective
      (fun f : F.obj A ⟶ F.obj (H.obj (op L, M)) ↦
        f ≫ coefficientClosedPullbackMap S SB F rho L M) := by
    let e := ((S.transpose A L M).symm.trans
      (Functor.FullyFaithful.ofFullyFaithful F).homEquiv).trans
      (((Iso.homCongr (rho.app (A, L)) (Iso.refl (F.obj M)))).trans
        (SB.transpose (F.obj A) (F.obj L) (F.obj M)))
    have he (f : A ⟶ H.obj (op L, M)) :
        e f = F.map f ≫ coefficientClosedPullbackMap S SB F rho L M := by
      change SB.transpose _ _ _
        ((rho.app (A, L)).inv ≫ F.map ((S.transpose A L M).symm f) ≫ 𝟙 _) = _
      rw [Category.comp_id, closed_transpose, Equiv.apply_symm_apply]
    have hh : (fun f : A ⟶ H.obj (op L, M) ↦
        F.map f ≫ coefficientClosedPullbackMap S SB F rho L M) = e := by
      funext f
      exact (he f).symm
    have hcomp := hh.symm ▸ e.bijective
    exact (Function.Bijective.of_comp_iff _
      (Functor.FullyFaithful.ofFullyFaithful F).homEquiv.bijective).mp hcomp
  apply isIso_of_yoneda_map_bijective
  intro A
  let e := F.objObjPreimageIso A
  let k := coefficientClosedPullbackMap S SB F rho L M
  have h (T : E) : Function.Bijective
      (fun f : A ⟶ T ↦ e.hom ≫ f) :=
    by simpa [Iso.homCongr] using (Iso.homCongr e.symm (Iso.refl T)).bijective
  have hh : (fun f : A ⟶ F.obj (H.obj (op L, M)) ↦ e.hom ≫ (f ≫ k)) =
      (fun f : F.obj (F.objPreimage A) ⟶ F.obj (H.obj (op L, M)) ↦ f ≫ k) ∘
        (fun f : A ⟶ F.obj (H.obj (op L, M)) ↦ e.hom ≫ f) := by
    funext f
    exact (Category.assoc _ _ _).symm
  have hcomp : Function.Bijective
      ((fun f : A ⟶ HB.obj (op (F.obj L), F.obj M) ↦ e.hom ≫ f) ∘
        (fun f : A ⟶ F.obj (H.obj (op L, M)) ↦ f ≫ k)) := by
    rw [Function.comp_def, hh]
    exact (hb _).comp (h _)
  exact (Function.Bijective.of_comp_iff' (h _) _).mp hcomp

/-- Closed slice comparison for arbitrary commutative pro-etale coefficient sheaves,
with exact inverse image, the scalar transport of canonical slice internal Hom,
and all three identities for the canonical tensor and Koszul comparisons.
The closed structures, tensor models and coherence witnesses are presentations of
those in `ringedDerived_closed_symmetric_monoidal`, not hypotheses on the scheme,
coefficients or complexes.

Source: Hemo--Richarz--Scholbach, Lemma 4.5 proof; Stacks 03CE, 03CZ, 03EL,
07A4, 08J7, 08J9, 08JB and 0FPT
(blueprint: lem-zl-proetale-coefficient-slice-closed-comparison).

Proof:
1. Use `lem-weil-proetale-weakly-etale-localization` to identify sites. Naturality
   of delta from `lem-sfb-proetale-object-inverse-image-restriction`, applied to
   actions and product projections, makes delta semilinear over delta_O. Since
   b delta_O = c, scalar extension followed by delta is balanced; on tensors
   m tensor s it is b inverse(s) delta(m). Its inverse sends n to delta inverse(n)
   tensor 1 (`lem-weil-sheaf-scalar-extension-ring-iso`). Both functors are exact;
   `lem-weil-pbc-exact-functor-derived-factorization` localizes the natural iso.
2. Scalar transport along b inverse leaves abelian sheaves and maps unchanged;
   transport along b is its inverse. Tensor sends pure factors to themselves,
   and the unit sends a to b(a). The two balancing relations agree. Associativity,
   unit and symmetry diagrams hold on local generators, including the Koszul
   sign in total degree (`lem-sf-ringed-derived-closed-symmetric-monoidal`).
   `lem-weil-pbc-ringed-topoi-derived-tensor-pullback` supplies K-flat preservation
   and localization of these tensor comparisons.
3. The ordinary pullback tensor map multiplies the two extension scalars. Under
   delta, multiplication agrees with applying b inverse separately to the two
   factors. The unit equation is b delta_O = c. Local tensor generators and the
   K-flat representative description show that these are the specified derived
   comparisons, giving tensor_compatibility and unit_compatibility.
4. Scalar transport preserves acyclicity, homotopies and K-injectives: translate
   a map out of an acyclic complex using the inverse equivalence, contract it,
   then transport its null homotopy back. On every further slice the R-linear
   maps are exactly the B-linear maps after transport. Thus the Hom families,
   products and differential d_I f - (-1)^n f d_L are unchanged. The ordinary
   unbounded Hom-complex construction (`def-pur-derived-internal-hom`) gives
   the natural scalarHom isomorphism without a boundedness assumption.
5. The tensor-Hom bijections identify scalarHom with the transpose of transported
   evaluation: both evaluate a local family f on x as f(x). The representative
   normalization in `def-coef-ringed-tensor-hom-model` fixes the counit, giving
   scalar_hom_normalization, rather than only an isomorphism of its source objects.
6. Compose the canonical slice Hom comparison
   (`lem-weil-pbc-ringed-internal-hom-exact-restriction`) with scalarHom and
   conjugate by localized delta. This is hom_transport. Apply scalar transport
   to `lem-weil-pbc-ringed-slice-evaluation-transpose`, insert Step 5 and the
   canonical tensor square of Step 3; obtain the evaluation identity for F.
7. Write g as evaluation after transpose(g) tensor 1. Tensor naturality and the
   evaluation identity give the transpose equation after the closed bijection.
   The symmetry equation follows on total-complex summands: both paths swap
   the factors with sign (-1)^(pq). Natural localization extends all equations
   to arbitrary derived inputs, with no geometric finiteness or constancy. -/
theorem proEtaleCoefficientSliceClosedComparison {X : Scheme.{u}} (U : X.ProEt)
    (O : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (B : Sheaf (ProEt.topology U.left) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage U.hom CommRingCat.{u + 1}).obj O ≅ B)
    (delta : ProEtaleObjectRestrictionComparison U CommRingCat.{u + 1})
    (S : CoefficientClosedStructure (proEtaleCoefficientHom X O))
    (SR : CoefficientClosedStructure (proEtaleCoefficientHom U.left (proEtaleSliceRing U O)))
    (SB : CoefficientClosedStructure (proEtaleCoefficientHom U.left B))
    (T : CoefficientTensorModels.{u + 1, u + 1, u} (ProEt.topology X) O S)
    (TR : CoefficientTensorModels.{u + 1, u + 1, u} (ProEt.topology U.left)
      (proEtaleSliceRing U O) SR)
    (TB : CoefficientTensorModels.{u + 1, u + 1, u} (ProEt.topology U.left) B SB)
    (beta : @SymmetricCategory (DerivedCategory (proEtaleRingModules X O)) _ S.monoidal)
    (betaB : @SymmetricCategory (DerivedCategory (proEtaleRingModules U.left B)) _ SB.monoidal)
    (_coherence : RingedDerivedTensorCoherence.{u + 1, u, u + 1}
      (ProEt.topology X) O S T beta)
    (_coherenceB : RingedDerivedTensorCoherence.{u + 1, u, u + 1}
      (ProEt.topology U.left) B SB TB betaB) :
    ∃ d : ProEtaleCoefficientSliceComparison.Data U O B c delta S SR SB T TR TB,
      ProEtaleCoefficientSliceComparison.Normalized U O B c delta S SR SB T TR TB d ∧
      CoefficientClosedComparisonLaws S SB (proEtaleRingDerivedPullback U.hom O B c)
        (ProEtaleCoefficientSliceComparison.rho U O B c S SB T TB)
        d.homComparison beta betaB := by
  obtain ⟨i, hi⟩ := proEtaleSlice_ordinary_comparison.{u} U O B c delta
  obtain ⟨t, _hi, ht, hsym⟩ := proEtaleSlice_monoidal_descent.{u} U O B c delta S SR SB T TR TB
    beta betaB _coherence _coherenceB i hi
  let R : DerivedCategory (proEtaleRingModules X O) ⥤
      DerivedCategory (proEtaleRingModules U.left (proEtaleSliceRing U O)) :=
    proEtaleSliceDerivedRestriction U O
  let E : DerivedCategory (proEtaleRingModules U.left (proEtaleSliceRing U O)) ⥤
      DerivedCategory (proEtaleRingModules U.left B) :=
    proEtaleSliceDerivedScalarTransport U O B (proEtaleSliceCoefficientIso U O B c delta)
  let F := proEtaleRingDerivedPullback U.hom O B c
  let a := proEtaleSliceDerivedComparison.{u} U O B c delta t.ordinary
  let rho := ProEtaleCoefficientSliceComparison.rho.{u} U O B c S SB T TB
  have he : (ProEtaleCoefficientSliceComparison.e U O B c delta).IsEquivalence :=
    scalar_equivalence (proEtaleSliceCoefficientIso U O B c delta)
  let := he
  have hE : E.IsEquivalence :=
    Functor.isEquivalence_mapDerivedCategory (ProEtaleCoefficientSliceComparison.e U O B c delta)
  let := hE
  have hR := proEtaleSlice_closed_maps_isIso.{u} U O B c delta S SR SB T TR TB t ht
  have hscalar (L M) : IsIso (coefficientClosedPullbackMap SR SB E t.scalarTensor.rho L M) :=
    closed_equivalence_isIso SR SB E t.scalarTensor.rho L M
  let rHom := closed_iso S SR R t.restrictionTensor.rho hR
  let eHom := closed_iso SR SB E t.scalarTensor.rho hscalar
  obtain ⟨hsection, hrchain, hechain, hrunit, heunit, hfunit, htensor, hunit, _⟩ := ht
  have htower (L M) :
      E.map (t.restrictionTensor.rho.hom.app (L, M)) ≫
          t.scalarTensor.rho.hom.app (R.obj L, R.obj M) ≫
          SB.tensor.map (Prod.mkHom (a.inv.app L) (a.inv.app M)) =
        a.inv.app (S.tensor.obj (L, M)) ≫ rho.hom.app (L, M) := by
    simpa only [Category.assoc] using tensor_inverse_square SB.tensor (R ⋙ E) F S.tensor a rho
      (fun L M ↦ E.map (t.restrictionTensor.rho.hom.app (L, M)) ≫
        t.scalarTensor.rho.hom.app (R.obj L, R.obj M)) htensor L M
  have htransport (L M) : coefficientClosedPullbackMap S SB F rho L M =
      a.hom.app ((proEtaleCoefficientHom.{u} X O).obj (op L, M)) ≫
        E.map (rHom.hom.app (op L, M)) ≫
        eHom.hom.app (op (R.obj L), R.obj M) ≫
        (proEtaleCoefficientHom.{u} U.left B).map
          (Prod.mkHom (a.hom.app L).op (a.inv.app M)) := by
    have h := scalarBaseChangeHom_tower S SR SB R E F
      t.restrictionTensor.rho t.scalarTensor.rho rho a.symm htower L M
    change E.map (rHom.hom.app (op L, M)) ≫
      eHom.hom.app (op (R.obj L), R.obj M) ≫
      (proEtaleCoefficientHom.{u} U.left B).map
        (Prod.mkHom (a.hom.app L).op (a.inv.app M)) =
      a.inv.app ((proEtaleCoefficientHom.{u} X O).obj (op L, M)) ≫
        coefficientClosedPullbackMap S SB F rho L M at h
    rw [h]
    simp
  have hF (L M) : IsIso (coefficientClosedPullbackMap S SB F rho L M) := by
    rw [htransport]
    have hi : IsIso ((proEtaleCoefficientHom.{u} U.left B).map
        (Prod.mkHom (a.hom.app L).op (a.inv.app M))) := by
      change IsIso (((proEtaleCoefficientHom.{u} U.left B).mapIso
        (Iso.prod (a.app L).op (a.app M).symm)).hom)
      infer_instance
    infer_instance
  let fHom := closed_iso S SB F rho hF
  let d : ProEtaleCoefficientSliceComparison.Data U O B c delta S SR SB T TR TB := {
    ordinary := t.ordinary
    restrictionTensor := t.restrictionTensor
    scalarTensor := t.scalarTensor
    restrictionUnit := t.restrictionUnit
    scalarUnit := t.scalarUnit
    pullbackUnit := t.pullbackUnit
    restrictionHom := rHom
    scalarHom := eHom
    homComparison := fHom }
  refine ⟨d, ?_, ?_⟩
  · exact ⟨he, hE, hsection, hrchain, hechain, hrunit, heunit, hfunit,
      htensor, hunit, (fun _ _ ↦ rfl), (fun _ _ ↦ rfl), (fun _ _ ↦ rfl), htransport⟩
  · intro A L M g
    exact ⟨(closed_evaluation S SB F rho L M).symm,
      closed_transpose S SB F rho A L M g, hsym L M⟩

end AlgebraicGeometry.Scheme
