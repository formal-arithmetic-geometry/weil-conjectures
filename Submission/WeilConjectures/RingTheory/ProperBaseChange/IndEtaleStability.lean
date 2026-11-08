/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.RingTheory.ProperBaseChange.IndPrincipalZariski
public import Submission.WeilConjectures.RingTheory.ProEtale.WeaklyEtale
public import Mathlib.CategoryTheory.Limits.Comma

import Mathlib.RingTheory.Localization.Pi

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Stability of ind-etale and principal ind-Zariski maps

Source: blueprint, proper base change, lemma "Stability and diagonal of an ind-etale algebra"
(blueprint: lem-weil-pbc-ind-etale-stability).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

-- Finite principal-localization blocks and their explicit base changes.
private def blocks (A : Type u) [CommRing A] : ObjectProperty (CommAlgCat.{u} A) :=
  fun B ↦ ∃ (n : ℕ) (f : Fin n → A),
    Nonempty (B ≃ₐ[A] ((j : Fin n) → Localization.Away (f j)))
open TensorProduct in
private noncomputable def tensorBlockEquiv (A S : Type u)
    [CommRing A] [CommRing S] [Algebra A S] (n : ℕ) (f : Fin n → A) :
    S ⊗[A] ((j : Fin n) → Localization.Away (f j)) ≃ₐ[S]
      ((j : Fin n) → Localization.Away (algebraMap A S (f j))) := by
  classical
  refine (Algebra.TensorProduct.piRight A S S _).trans (AlgEquiv.piCongrRight fun j ↦ ?_)
  have : IsLocalization.Away (algebraMap A S (f j)) (S ⊗[A] Localization.Away (f j)) := by
    simpa only [Algebra.algebraMapSubmonoid, Submonoid.map_powers] using
      (inferInstance : IsLocalization
        (Algebra.algebraMapSubmonoid S (Submonoid.powers (f j)))
        (S ⊗[A] Localization.Away (f j)))
  exact IsLocalization.algEquiv (Submonoid.powers (algebraMap A S (f j))) _ _
open TensorProduct in
private theorem block_tensor (A S : Type u) [CommRing A] [CommRing S] [Algebra A S]
    (B : CommAlgCat.{u} A) (hB : blocks A B) :
    blocks S (CommAlgCat.of S (S ⊗[A] B)) := by
  obtain ⟨n, f, ⟨e⟩⟩ := hB
  exact ⟨n, fun j ↦ algebraMap A S (f j),
    ⟨(Algebra.TensorProduct.congr (AlgEquiv.refl : S ≃ₐ[S] S) e).trans
      (tensorBlockEquiv A S n f)⟩⟩
private noncomputable def bc (A S : Type u) [CommRing A] [CommRing S] [Algebra A S] :
    CommAlgCat.{u} A ⥤ CommAlgCat.{u} S :=
  (commAlgCatEquivUnder (.of A)).functor ⋙
    Under.pushout (CommRingCat.ofHom (algebraMap A S)) ⋙
      (commAlgCatEquivUnder (.of S)).inverse
private theorem blocks_of_equiv (A : Type u) [CommRing A] {B C : CommAlgCat.{u} A}
    (e : B ≃ₐ[A] C) (h : blocks A C) : blocks A B := by
  obtain ⟨n, f, ⟨e'⟩⟩ := h
  exact ⟨n, f, ⟨e.trans e'⟩⟩
-- Relate the algebra presentation to the categorical ind-property.
private local instance blocks_closedIso (A : Type u) [CommRing A] :
    (blocks A).IsClosedUnderIsomorphisms where
  of_iso e h := blocks_of_equiv A (CommAlgCat.algEquivOfIso e).symm h
private def blockMaps : MorphismProperty CommRingCat.{u} :=
  fun A B f ↦ let := f.hom.toAlgebra; blocks A (CommAlgCat.of A B)
private local instance blockMaps_baseChange : blockMaps.{u}.IsStableUnderCobaseChange := by
  change (RingHom.toMorphismProperty
    (fun {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) ↦
      let := f.toAlgebra; blocks A (CommAlgCat.of A B))).IsStableUnderCobaseChange
  apply RingHom.isStableUnderCobaseChange_toMorphismProperty_iff.mpr
  intro R S R' S' _ _ _ _ _ _ _ _ _ _ _ hpush h
  rw [toAlgebra_algebraMap] at h ⊢
  have : Algebra.IsPushout R R' S S' := hpush.symm
  exact blocks_of_equiv R' (Algebra.IsPushout.equiv R R' S S').symm
    (block_tensor R R' (CommAlgCat.of R S) h)

-- Localization and finite products preserve the blocks, including empty products.
private theorem block_away (A : Type u) [CommRing A] (B : CommAlgCat.{u} A)
    (hB : blocks A B) (b : B) : blocks A (CommAlgCat.of A (Localization.Away b)) := by
  classical
  obtain ⟨n, f, ⟨e⟩⟩ := hB
  let R (i : Fin n) := Localization.Away (f i)
  let g : (i : Fin n) → R i := e b
  let T (i : Fin n) := Localization.Away (g i)
  have (i : Fin n) : IsLocalization ((Submonoid.powers g).map (Pi.evalRingHom R i))
      (T i) := by
    simp only [Submonoid.map_powers]
    change IsLocalization.Away (g i) (T i)
    infer_instance
  have : IsLocalization.Away g ((i : Fin n) → T i) :=
    (IsLocalization.iff_map_piEvalRingHom R ((i : Fin n) → T i)
      (Submonoid.powers g)).mpr inferInstance
  let e₁ : Localization.Away b ≃ₐ[A] Localization.Away g :=
    IsLocalization.algEquivOfAlgEquiv (M := Submonoid.powers b)
      (T := Submonoid.powers g) _ _ e (by rw [Submonoid.map_powers])
  let e₂ : Localization.Away g ≃ₐ[A] ((i : Fin n) → T i) :=
    (IsLocalization.algEquiv (Submonoid.powers g) _ _).restrictScalars A
  let a (i : Fin n) : A := (IsLocalization.Away.sec (f i) (g i)).1
  have (i : Fin n) : IsLocalization.Away (f i * a i) (T i) :=
    IsLocalization.Away.mul_of_associated (f i) (a i) (g i)
      (IsLocalization.Away.associated_sec_fst (f i) (g i))
  refine ⟨n, fun i ↦ f i * a i, ⟨e₁.trans (e₂.trans ?_)⟩⟩
  exact AlgEquiv.piCongrRight fun i ↦
    IsLocalization.algEquiv (Submonoid.powers (f i * a i)) _ _
private theorem block_pi (A : Type u) [CommRing A] {m : ℕ}
    (B : Fin m → CommAlgCat.{u} A) (hB : ∀ j, blocks A (B j)) :
    blocks A (CommAlgCat.of A ((j : Fin m) → B j)) := by
  classical
  choose n f e using hB
  let J := (j : Fin m) × Fin (n j)
  let fs : J → A := fun p ↦ f p.1 p.2
  let e₁ : ((j : Fin m) → B j) ≃ₐ[A]
      ((p : J) → Localization.Away (fs p)) :=
    { toFun x p := (e p.1).some (x p.1) p.2
      invFun x j := (e j).some.symm (fun k ↦ x ⟨j, k⟩)
      left_inv x := by ext j; exact (e j).some.symm_apply_apply (x j)
      right_inv x := by ext p; exact congrFun ((e p.1).some.apply_symm_apply _) p.2
      map_mul' x y := by ext p; simp
      map_add' x y := by ext p; simp
      commutes' a := by
        ext p
        simpa only [fs, Pi.algebraMap_apply] using congrFun ((e p.1).some.commutes a) p.2 }
  let k := Fintype.card J
  let eqv : Fin k ≃ J := (Fintype.equivFin J).symm
  refine ⟨k, fs ∘ eqv, ⟨e₁.trans ?_⟩⟩
  exact (AlgEquiv.piCongrLeft A (fun p : J ↦ Localization.Away (fs p)) eqv).symm
private theorem block_comp (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
    (hB : blocks A (CommAlgCat.of A B)) (hC : blocks B (CommAlgCat.of B C)) :
    blocks A (CommAlgCat.of A C) := by
  obtain ⟨n, f, ⟨e⟩⟩ := hC
  apply blocks_of_equiv A
    (C := CommAlgCat.of A ((j : Fin n) → Localization.Away (f j))) (e.restrictScalars A)
  apply block_pi A (fun j ↦ CommAlgCat.of A (Localization.Away (f j)))
  intro j
  exact block_away A (CommAlgCat.of A B) hB (f j)

private local instance blockMaps_comp : blockMaps.{u}.IsStableUnderComposition where
  comp_mem {A B C} f g hf hg := by
    let := f.hom.toAlgebra
    let := g.hom.toAlgebra
    let := (g.hom.comp f.hom).toAlgebra
    have : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq' rfl
    exact block_comp A B C hf hg
-- Descend the finite list of denominators to one filtered stage.
private theorem finite_reps {I : Type u} [SmallCategory I] [IsFiltered I]
    (D : I ⥤ CommRingCat.{u}) (c : Cocone D) (hc : IsColimit c)
    (n : ℕ) (x : Fin n → c.pt) :
    ∃ (i : I) (y : Fin n → D.obj i), ∀ j, (c.ι.app i).hom (y j) = x j := by
  classical
  choose i y hy using fun j ↦ Concrete.isColimit_exists_rep D hc (x j)
  let co := IsFiltered.cocone (Discrete.functor i)
  refine ⟨co.pt, fun j ↦ (D.map (co.ι.app ⟨j⟩)).hom (y j), fun j ↦ ?_⟩
  have hw := congrArg (fun k ↦ k.hom (y j)) (c.w (co.ι.app ⟨j⟩))
  exact hw.trans (hy j)
open TensorProduct in
private local instance blockMaps_spreads : MorphismProperty.PreIndSpreads.{u} blockMaps.{u} where
  exists_isPushout {I} _ _ {D} {c} hc {T} f hf := by
    let : Algebra c.pt T := f.hom.toAlgebra
    obtain ⟨n, g, ⟨e⟩⟩ := hf
    obtain ⟨i, gi, hgi⟩ := finite_reps D c hc n g
    let : Algebra (D.obj i) c.pt := (c.ι.app i).hom.toAlgebra
    let Ti := (j : Fin n) → Localization.Away (gi j)
    let e₀ : c.pt ⊗[D.obj i] Ti ≃ₐ[c.pt]
        ((j : Fin n) → Localization.Away (g j)) := by
      refine (tensorBlockEquiv (D.obj i) c.pt n gi).trans
        (AlgEquiv.piCongrRight fun j ↦ ?_)
      have hh : algebraMap (D.obj i) c.pt (gi j) = g j := hgi j
      rw [hh]
    let ebc : c.pt ⊗[D.obj i] Ti ≃ₐ[c.pt] T := e₀.trans e.symm
    let fi : D.obj i ⟶ CommRingCat.of Ti := CommRingCat.ofHom (algebraMap (D.obj i) Ti)
    let v : CommRingCat.of Ti ⟶ T := CommRingCat.ofHom
      (ebc.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)
    refine ⟨i, CommRingCat.of Ti, fi, v, ?_, ?_⟩
    · refine (CommRingCat.isPushout_tensorProduct (D.obj i) c.pt Ti).of_iso
        (Iso.refl _) (Iso.refl _) (Iso.refl _) ebc.toRingEquiv.toCommRingCatIso
        ?_ ?_ ?_ ?_
      · rfl
      · rfl
      · ext x
        exact ebc.commutes x
      · rfl
    · change @blocks (D.obj i) _
        (@CommAlgCat.of (D.obj i) _ Ti _ (algebraMap (D.obj i) Ti).toAlgebra)
      rw [toAlgebra_algebraMap]
      exact ⟨n, gi, ⟨AlgEquiv.refl⟩⟩

-- Push out to a fixed source, then construct the colimit universal property.
-- The remaining clauses use existing ind-etale and weakly etale APIs.
namespace RingHom

end RingHom
