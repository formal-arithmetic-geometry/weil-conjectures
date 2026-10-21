/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.DerivedCategory.Basic

import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Sheaf.Algebra.Homology.SubcategoryLeftResolution

/-!
# Compatible bounded-above resolutions from a quotient-generating class

Source: Stacks Project, Derived Categories, Tag 06XX, derived-lemma-special-direct-system
(statement and proof, including the strictification of the homotopy square and final
epicification).
(blueprint: lem-sfb-subcategory-truncation-resolution-system)

This module states the compatible resolution system for the good truncations of a
cochain complex. The proof follows the eight steps recorded in the node: the initial
resolution, the cone resolution, the shifted cone with split inclusion, the triangle
comparison, strictification, and the two-term identity-complex correction.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

set_option maxHeartbeats 600000 in
-- The explicit three-summand cone isomorphism needs many dependent-index checks.
/-- A resolution of the cone of a map produces a strict relative extension whose
terms are the biproducts of the old terms and the resolving terms.

Source: Stacks Project Tag 06XX, relative cone construction before the final
termwise-surjectivity addition. The explicit coordinate proof follows
`exists_relative_boundedAbove_flat_extension` but retains its term description.
Proof: Write the components of the cone resolution as a degree-one map to E
and a degree-zero map to H. On E^i ⊞ Q^i use the differential with diagonal
entries d_E and d_Q and off-diagonal entry minus the first component.
The cone chain-map equation gives square-zero and a map to H. The inclusion
of E is split by the first projection and its composite to H equals f.
The cones of the new map and the given resolution are isomorphic by permuting
the three summands, so the new map is a quasi-isomorphism. The maximum of the
two bounds bounds the new complex. This works also for zero maps and objects.
(blueprint: lem-sc-relative-biprod-cone-extension). -/
private theorem relativeCone
    {C : Type u} [Category.{v} C] [Abelian C]
    (E H : CochainComplex C ℤ) (f : E ⟶ H)
    (hE : ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (E.X i))
    (Q : CochainComplex C ℤ) (r : Q ⟶ CochainComplex.mappingCone f)
    (hQ : ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (Q.X i)) (hr : QuasiIso r) :
    ∃ (F : CochainComplex C ℤ) (t : E ⟶ F) (g : F ⟶ H),
      (∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (F.X i)) ∧
      QuasiIso g ∧ t ≫ g = f ∧ (∀ i : ℤ, IsSplitMono (t.f i)) ∧
      ∀ i : ℤ, ∃ e : F.X i ≅ E.X i ⊞ Q.X i, t.f i ≫ e.hom = biprod.inl := open CochainComplex in by
  -- Realize the triangle directly: the cone coordinates of r determine the twisted sum.
  let a (i : ℤ) := r.f i ≫ (mappingCone.fst f).1.v i (i + 1) rfl
  let b (i : ℤ) := r.f i ≫ (mappingCone.snd f).v i i (add_zero i)
  have ha (i : ℤ) :
      a i ≫ E.d (i + 1) (i + 1 + 1) + Q.d i (i + 1) ≫ a (i + 1) = 0 := by
    dsimp [a]
    have eq := r.comm i (i + 1)
    simp only [← Category.assoc] at eq ⊢
    rw [← eq]
    simp only [Category.assoc, mappingCone.d_fst_v f i (i + 1) (i + 1 + 1) rfl rfl,
      Preadditive.comp_neg, add_neg_cancel]
  have hb (i : ℤ) : Q.d i (i + 1) ≫ b (i + 1) =
      a i ≫ f.f (i + 1) + b i ≫ H.d i (i + 1) := by
    dsimp [a, b]
    rw [← Category.assoc, ← r.comm, Category.assoc, mappingCone.d_snd_v f i
      (i + 1) rfl]
    simp [Preadditive.comp_add, Category.assoc]
  let d (i : ℤ) : E.X i ⊞ Q.X i ⟶ E.X (i + 1) ⊞ Q.X (i + 1) :=
    biprod.desc (E.d i (i + 1) ≫ biprod.inl)
      (-a i ≫ biprod.inl + Q.d i (i + 1) ≫ biprod.inr)
  have hd (i : ℤ) : d i ≫ d (i + 1) = 0 := by
    apply biprod.hom_ext' <;> apply biprod.hom_ext
    all_goals simp [d, Preadditive.add_comp, Preadditive.comp_add, Category.assoc]
    have eq := ha i
    simpa only [Preadditive.neg_comp, neg_add, neg_zero] using congrArg Neg.neg eq
  let F := CochainComplex.of (fun i ↦ E.X i ⊞ Q.X i) d hd
  let t : E ⟶ F := CochainComplex.ofHom (fun _ ↦ biprod.inl) (by
    intro i
    simp [F, d])
  let g : F ⟶ H := CochainComplex.ofHom (fun i ↦ biprod.desc (f.f i) (b i)) (by
    intro i
    apply biprod.hom_ext'
    · simp [F, d, f.comm]
    · simp [F, d, Preadditive.add_comp, Category.assoc, hb])
  refine ⟨F, t, g, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨e, he⟩ := hE
    obtain ⟨q, hq⟩ := hQ
    refine ⟨max e q, fun i hi ↦ ?_⟩
    exact (biprod_isZero_iff _ _).2
      ⟨he i (lt_of_le_of_lt (le_max_left _ _) hi),
        hq i (lt_of_le_of_lt (le_max_right _ _) hi)⟩
  -- Cone(g) and Cone(r) have the same three summands, in different orders.
  · let e (i : ℤ) : (mappingCone g).X i ≅ (mappingCone r).X i :=
      { hom :=
          ((mappingCone.fst g).1.v i (i + 1) rfl ≫ biprod.snd) ≫
              (mappingCone.inl r).v (i + 1) i (by omega) +
            (((mappingCone.fst g).1.v i (i + 1) rfl ≫ biprod.fst) ≫
                (mappingCone.inl f).v (i + 1) i (by omega) +
              (mappingCone.snd g).v i i (add_zero i) ≫ (mappingCone.inr f).f i) ≫
                (mappingCone.inr r).f i
        inv :=
          biprod.lift
              ((mappingCone.snd r).v i i (add_zero i) ≫
                (mappingCone.fst f).1.v i (i + 1) rfl)
              ((mappingCone.fst r).1.v i (i + 1) rfl) ≫
                (mappingCone.inl g).v (i + 1) i (by omega) +
            ((mappingCone.snd r).v i i (add_zero i) ≫
              (mappingCone.snd f).v i i (add_zero i)) ≫ (mappingCone.inr g).f i
        hom_inv_id := by
          apply mappingCone.ext_from g (i + 1) i rfl
          · apply biprod.hom_ext'
            all_goals
              apply mappingCone.ext_to g i (i + 1) rfl
              · apply biprod.hom_ext
                all_goals simp [F, Category.assoc, Preadditive.add_comp, Preadditive.comp_add]
              · simp [F, Category.assoc, Preadditive.add_comp, Preadditive.comp_add]
          · apply mappingCone.ext_to g i (i + 1) rfl
            · apply biprod.hom_ext
              all_goals simp [F, Category.assoc, Preadditive.add_comp, Preadditive.comp_add]
            · simp [F, Category.assoc, Preadditive.add_comp, Preadditive.comp_add]
        inv_hom_id := by
          apply mappingCone.ext_from r (i + 1) i rfl
          · apply mappingCone.ext_to r i (i + 1) rfl
            · simp [F, Category.assoc, Preadditive.add_comp, Preadditive.comp_add]
            · apply mappingCone.ext_to f i (i + 1) rfl
              all_goals simp [F, Category.assoc, Preadditive.add_comp, Preadditive.comp_add]
          · apply mappingCone.ext_from f (i + 1) i rfl
            all_goals
              apply mappingCone.ext_to r i (i + 1) rfl
              · simp [F, Category.assoc, Preadditive.add_comp, Preadditive.comp_add]
              · apply mappingCone.ext_to f i (i + 1) rfl
                all_goals simp [F, Category.assoc, Preadditive.add_comp, Preadditive.comp_add] }
    have he₁ (i : ℤ) : (e i).hom ≫ (mappingCone.fst r).1.v i (i + 1) rfl =
        (mappingCone.fst g).1.v i (i + 1) rfl ≫ biprod.snd := by
      simp [e, Category.assoc, Preadditive.add_comp]
    have he₂ (i : ℤ) : (e i).hom ≫ (mappingCone.snd r).v i i (add_zero i) ≫
        (mappingCone.fst f).1.v i (i + 1) rfl =
          (mappingCone.fst g).1.v i (i + 1) rfl ≫ biprod.fst := by
      simp [e, Category.assoc, Preadditive.add_comp]
    have he₃ (i : ℤ) : (e i).hom ≫ (mappingCone.snd r).v i i (add_zero i) ≫
        (mappingCone.snd f).v i i (add_zero i) =
          (mappingCone.snd g).v i i (add_zero i) := by
      simp [e, Category.assoc, Preadditive.add_comp]
    have he₁' (i : ℤ) {Z : C}
        (k : Q.X (i + 1) ⟶ Z) :
        (e i).hom ≫ (mappingCone.fst r).1.v i (i + 1) rfl ≫ k =
          (mappingCone.fst g).1.v i (i + 1) rfl ≫ biprod.snd ≫ k := by
      rw [← Category.assoc, he₁, Category.assoc]
    have he₂' (i : ℤ) {Z : C}
        (k : E.X (i + 1) ⟶ Z) :
        (e i).hom ≫ (mappingCone.snd r).v i i (add_zero i) ≫
          (mappingCone.fst f).1.v i (i + 1) rfl ≫ k =
            (mappingCone.fst g).1.v i (i + 1) rfl ≫ biprod.fst ≫ k := by
      simp only [← Category.assoc, he₂]
    have he₃' (i : ℤ) {Z : C}
        (k : H.X i ⟶ Z) :
        (e i).hom ≫ (mappingCone.snd r).v i i (add_zero i) ≫
          (mappingCone.snd f).v i i (add_zero i) ≫ k =
            (mappingCone.snd g).v i i (add_zero i) ≫ k := by
      simp only [← Category.assoc, he₃]
    have hd₁ (i : ℤ) : F.d i (i + 1) ≫ biprod.fst =
        biprod.fst ≫ E.d i (i + 1) - biprod.snd ≫ a i := by
      dsimp only [F]
      rw [of_d]
      apply biprod.hom_ext'
      all_goals simp [d, Preadditive.comp_sub, Preadditive.add_comp, Category.assoc]
    have hd₂ (i : ℤ) : F.d i (i + 1) ≫ biprod.snd =
        biprod.snd ≫ Q.d i (i + 1) := by
      dsimp only [F]
      rw [of_d]
      apply biprod.hom_ext'
      all_goals simp [d, Preadditive.add_comp, Category.assoc]
    have hg (i : ℤ) : g.f i = biprod.fst ≫ f.f i + biprod.snd ≫ b i := by
      change biprod.desc _ _ = _
      exact biprod.desc_eq
    let ec : mappingCone g ≅ mappingCone r :=
      HomologicalComplex.Hom.isoOfComponents e (by
        rintro i _ rfl
        apply mappingCone.ext_to r (i + 1) (i + 1 + 1) rfl
        · simp only [Category.assoc,
            mappingCone.d_fst_v r i (i + 1) (i + 1 + 1) rfl rfl,
            Preadditive.comp_neg, Preadditive.neg_comp, he₁', he₁,
            mappingCone.d_fst_v_assoc g i (i + 1) (i + 1 + 1) rfl rfl,
            hd₂]
        · apply mappingCone.ext_to f (i + 1) (i + 1 + 1) rfl
          · simp only [Category.assoc,
              mappingCone.d_snd_v_assoc r i (i + 1) rfl, Preadditive.comp_add, Preadditive.add_comp,
              mappingCone.d_fst_v f i (i + 1) (i + 1 + 1) rfl rfl,
              Preadditive.comp_neg, Preadditive.neg_comp, he₁', he₂', he₂,
              mappingCone.d_fst_v_assoc g i (i + 1) (i + 1 + 1) rfl rfl,
              hd₁, Preadditive.comp_sub]
            change _ ≫ _ ≫ a (i + 1) + -(_ ≫ _ ≫ _) = -(_ - _)
            abel
          · simp only [Category.assoc,
              mappingCone.d_snd_v_assoc r i (i + 1) rfl, Preadditive.comp_add, Preadditive.add_comp,
              mappingCone.d_snd_v f i (i + 1) rfl,
              he₁', he₂', he₃', he₃,
              mappingCone.d_snd_v g i (i + 1) rfl, hg, Preadditive.comp_add]
            change _ ≫ _ ≫ b (i + 1) + (_ + _) = (_ + _) + _
            abel)
    apply (mappingCone.quasiIso_iff_acyclic g).2
    have hc := (mappingCone.quasiIso_iff_acyclic r).1 hr
    intro i
    apply (HomologicalComplex.exactAt_iff_isZero_homology _ i).2
    exact ((HomologicalComplex.exactAt_iff_isZero_homology _ i).1 (hc i)).of_iso
      ((HomologicalComplex.homologyFunctor _ _ i).mapIso ec)
  · ext i
    simp [t, g]
  · intro i
    exact ⟨⟨biprod.fst, by simp [t]⟩⟩
  · intro i
    exact ⟨Iso.refl _, by simp [t]⟩



/-- Bounded identity disks make an augmentation epic and retain the complementary terms.
Source: Stacks Project, Tag 06XX, the final paragraph, applied in every degree. -/
private theorem epicification
    {C : Type u} [Category.{v} C] [Abelian C]
    (W : C → Prop)
    (hzero : ∀ X : C, IsZero X → W X)
    (hiso : ∀ {X Y : C}, (X ≅ Y) → W X → W Y)
    (hbiprod : ∀ {X Y : C}, W X → W Y → W (X ⊞ Y))
    (hcover : ∀ X : C, ∃ (Y : C) (p : Y ⟶ X), W Y ∧ Epi p)
    (E H : CochainComplex C ℤ) (f : E ⟶ H)
    (hE : ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (E.X i))
    (hH : ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (H.X i))
    (hterms : ∀ i : ℤ, W (E.X i)) :
    ∃ (F : CochainComplex C ℤ) (s : E ⟶ F) (g : F ⟶ H),
      (∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (F.X i)) ∧
      (∀ i : ℤ, W (F.X i)) ∧ QuasiIso s ∧
      (∀ i : ℤ, Epi (g.f i)) ∧ s ≫ g = f ∧
      ∀ i : ℤ, ∃ (D : C) (_ : W D) (e : F.X i ≅ E.X i ⊞ D),
        s.f i ≫ e.hom = biprod.inl := open CochainComplex in by
  classical
  obtain ⟨N, hN⟩ := hH
  choose Q p hQ hp using hcover
  let P : ℤ → C := fun i ↦ if i ≤ N then Q (H.X i) else HasZeroObject.zero.choose
  have hP (i : ℤ) : W (P i) := by
    dsimp [P]
    split_ifs
    · exact hQ _
    · exact hzero _ HasZeroObject.zero.choose_spec
  have hzP (i : ℤ) (hi : N < i) : IsZero (P i) := by
    dsimp [P]
    rw [if_neg (not_le.mpr hi)]
    exact HasZeroObject.zero.choose_spec
  let q (i : ℤ) : P i ⟶ H.X i :=
    if hi : i ≤ N then eqToHom (by simp [P, hi]) ≫ p (H.X i) else 0
  have hq (i : ℤ) : Epi (q i) := by
    by_cases hi : i ≤ N
    · dsimp only [q]
      rw [dif_pos hi]
      have := hp (H.X i)
      infer_instance
    · exact (hN i (lt_of_not_ge hi)).epi _
  let X (i : ℤ) := P i ⊞ P (i - 1)
  let dd (i j : ℤ) : X i ⟶ X j :=
    if hij : i + 1 = j then
      biprod.fst ≫ eqToHom (by congr 1; omega) ≫ biprod.inr
    else 0
  let D : CochainComplex _ ℤ :=
    { X := X
      d := dd
      shape := fun i j hij ↦ dif_neg hij
      d_comp_d' := by
        intro i j k hij hjk
        change i + 1 = j at hij
        change j + 1 = k at hjk
        simp [dd, hij, hjk, Category.assoc] }
  let a : D ⟶ H := CochainComplex.ofHom
    (fun i ↦ biprod.desc (q i) (q (i - 1) ≫ H.d (i - 1) i)) (by
      intro i
      have hi : i + 1 - 1 = i := by omega
      apply biprod.hom_ext'
      · simp only [D, dd, dif_pos rfl, Category.assoc,
          biprod.inl_fst_assoc, biprod.inr_desc]
        simpa using (eqToHom_naturality
          (fun k ↦ q k ≫ H.d k (i + 1)) hi.symm)
      · simp [D, dd, Category.assoc])
  have ha (i : ℤ) : Epi (a.f i) := by
    have := hq i
    exact epi_of_epi_fac (by simp [a] :
      (biprod.inl : P i ⟶ X i) ≫ a.f i = q i)
  let hh (i j : ℤ) : D.X i ⟶ D.X j :=
    if hij : j + 1 = i then
      biprod.snd ≫ eqToHom (by congr 1; omega) ≫ biprod.inl
    else 0
  have hcontract : Homotopy (𝟙 D) 0 := by
    refine { hom := hh, zero := ?_, comm := ?_ }
    · intro i j hij
      exact dif_neg hij
    · intro i
      rw [dNext_eq hh (show (ComplexShape.up ℤ).Rel i (i + 1) by rfl),
        prevD_eq hh (show (ComplexShape.up ℤ).Rel (i - 1) i by change i - 1 + 1 = i; omega)]
      have hi' : i - 1 + 1 = i := by omega
      simp only [D, dd, hh, dif_pos rfl, dif_pos hi', HomologicalComplex.id_f,
        HomologicalComplex.zero_f, Category.assoc, biprod.inr_snd_assoc,
        biprod.inl_fst_assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
        add_zero]
      exact (biprod.total (X := P i) (Y := P (i - 1))).symm
  have hDbound : ∀ i : ℤ, N + 1 < i → IsZero (D.X i) := by
    intro i hi
    exact (biprod_isZero_iff _ _).2 ⟨hzP i (by omega), hzP (i - 1) (by omega)⟩
  let F := E ⊞ D
  let s : E ⟶ F := biprod.inl
  let g : F ⟶ H := biprod.desc f a
  let e : HomotopyEquiv E F :=
    { hom := s
      inv := biprod.fst
      homotopyHomInvId := Homotopy.ofEq (by simp [s])
      homotopyInvHomId := by
        let h₁ := (hcontract.compRight (biprod.inr : D ⟶ F)).compLeft
          (biprod.snd : F ⟶ D)
        let h₂ := (Homotopy.refl (biprod.fst ≫ s)).add h₁
        exact (Homotopy.ofEq (by simp [s])).trans
          (h₂.symm.trans (Homotopy.ofEq (by
            simpa only [s, Category.id_comp] using biprod.total (X := E) (Y := D)))) }
  refine ⟨F, s, g, ?_, ?_, e.quasiIso_hom, ?_, ?_, ?_⟩
  · obtain ⟨b, hb⟩ := hE
    refine ⟨max b (N + 1), fun i hi ↦ ?_⟩
    apply IsZero.of_iso _ (HomologicalComplex.biprodXIso E D i)
    exact (biprod_isZero_iff _ _).2
      ⟨hb i (lt_of_le_of_lt (le_max_left _ _) hi),
        hDbound i (lt_of_le_of_lt (le_max_right _ _) hi)⟩
  · intro i
    exact hiso (HomologicalComplex.biprodXIso E D i).symm
      (hbiprod (hterms i) (hbiprod (hP i) (hP (i - 1))))
  · intro i
    have := ha i
    exact epi_of_epi_fac (HomologicalComplex.biprod_inr_desc_f f a i)
  · simp [s, g]
  · intro i
    refine ⟨D.X i, hbiprod (hP i) (hP (i - 1)),
      HomologicalComplex.biprodXIso E D i, ?_⟩
    dsimp only [s]
    apply (cancel_mono (HomologicalComplex.biprodXIso E D i).inv).1
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id,
      HomologicalComplex.inl_biprodXIso_inv]

/-- The canonical inclusion from the good truncation at `n` to that at `n + 1`.

Source: Stacks Project, Derived Categories, Tag 06XX, derived-lemma-special-direct-system.
(blueprint: lem-sfb-subcategory-truncation-resolution-system)
-/
noncomputable def subcategoryTruncationMap
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : CochainComplex C ℤ) (n : ℤ) :
    K.truncLE n ⟶ K.truncLE (n + 1) := by
  have h : (K.truncLE n).IsStrictlyLE (n + 1) :=
    CochainComplex.isStrictlyLE_of_le _ n (n + 1) (by omega)
  exact inv ((K.truncLE n).ιTruncLE (n + 1)) ≫
    CochainComplex.truncLEMap (K.ιTruncLE n) (n + 1)

/-- A relative cone resolution followed by bounded disk addition gives one strict step.
Source: Stacks Project, Tag 06XX, the induction step. -/
private theorem successor
    {C : Type u} [Category.{v} C] [Abelian C]
    (P : C → Prop)
    (hzero : ∀ X : C, IsZero X → P X)
    (hiso : ∀ {X Y : C}, (X ≅ Y) → P X → P Y)
    (hbiprod : ∀ {X Y : C}, P X → P Y → P (X ⊞ Y))
    (hcover : ∀ X : C, ∃ (Y : C) (p : Y ⟶ X), P Y ∧ Epi p)
    (K : CochainComplex C ℤ) (n : ℤ)
    (E : CochainComplex C ℤ) (e : E ⟶ K.truncLE n)
    (hE : ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (E.X i))
    (hterms : ∀ i : ℤ, P (E.X i)) :
    ∃ (F : CochainComplex C ℤ) (g : F ⟶ K.truncLE (n + 1)) (t : E ⟶ F),
      (∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (F.X i)) ∧
      (∀ i : ℤ, P (F.X i)) ∧ (∀ i : ℤ, Epi (g.f i)) ∧ QuasiIso g ∧
      t ≫ g = e ≫ subcategoryTruncationMap K n ∧
      (∀ i : ℤ, IsSplitMono (t.f i)) ∧ (∀ i : ℤ, P (cokernel (t.f i))) := open CochainComplex in by
  let H := K.truncLE (n + 1)
  let f := e ≫ subcategoryTruncationMap K n
  obtain ⟨b, hb⟩ := hE
  let N := max b (n + 1)
  have hcone : ∀ i : ℤ, N < i → IsZero ((mappingCone f).X i) := by
    intro i hi
    rw [mappingCone.isZero_X_iff]
    exact ⟨hb (i + 1) (by dsimp [N] at hi; omega),
      H.isZero_of_isStrictlyLE (n + 1) i (by dsimp [N] at hi; omega)⟩
  obtain ⟨Q, r, hr, hQterms, _, hQbound⟩ :=
    exists_subcategory_left_resolution P
      ⟨HasZeroObject.zero.choose, hzero _ HasZeroObject.zero.choose_spec,
        HasZeroObject.zero.choose_spec⟩ hcover N (mappingCone f) hcone
  obtain ⟨B, t, g, hBbound, hg, htg, _, hB⟩ :=
    relativeCone E H f ⟨b, hb⟩ Q r ⟨N, hQbound⟩ hr
  have hBterms (i : ℤ) : P (B.X i) := by
    obtain ⟨a, _⟩ := hB i
    exact hiso a.symm (hbiprod (hterms i) (hQterms i))
  obtain ⟨F, s, g', hFbound, hFterms, hs, hg'epi, hsg, hF⟩ :=
    epicification P hzero hiso hbiprod hcover B H g hBbound
      ⟨n + 1, fun i hi ↦ H.isZero_of_isStrictlyLE (n + 1) i hi⟩ hBterms
  have : QuasiIso s := hs
  have : QuasiIso (s ≫ g') := by rw [hsg]; exact hg
  have hgf : QuasiIso g' := quasiIso_of_comp_left s g'
  have hdecomp (i : ℤ) : ∃ (D : C) (_ : P D) (a : F.X i ≅ E.X i ⊞ D),
      (t ≫ s).f i ≫ a.hom = biprod.inl := by
    obtain ⟨a, ha⟩ := hB i
    obtain ⟨D, hD, c, hc⟩ := hF i
    refine ⟨Q.X i ⊞ D, hbiprod (hQterms i) hD,
      c ≪≫ biprod.mapIso a (Iso.refl D) ≪≫ biprod.associator _ _ _, ?_⟩
    simp only [HomologicalComplex.comp_f, Iso.trans_hom, Category.assoc]
    rw [← Category.assoc (s.f i), hc]
    simp only [biprod.mapIso_hom, biprod.inl_map_assoc]
    rw [← Category.assoc, ha]
    apply biprod.hom_ext
    · simp [biprod.associator]
    · apply biprod.hom_ext <;> simp [biprod.associator]
  refine ⟨F, g', t ≫ s, hFbound, hFterms, hg'epi, hgf, ?_, ?_, ?_⟩
  · simpa only [Category.assoc, hsg] using htg
  · intro i
    obtain ⟨D, _, a, ha⟩ := hdecomp i
    exact ⟨⟨a.hom ≫ biprod.fst, by rw [← Category.assoc, ha]; simp⟩⟩
  · intro i
    obtain ⟨D, hD, a, ha⟩ := hdecomp i
    let c := cokernel.mapIso ((t ≫ s).f i) (biprod.inl : E.X i ⟶ E.X i ⊞ D)
      (Iso.refl _) a (by simpa using ha)
    exact hiso (c ≪≫ cokernelBiprodInlIso).symm hD

/--
Compatible bounded-above resolutions of all good truncations by a quotient-generating
subcategory.

Source: Stacks Project, Derived Categories, Tag 06XX, derived-lemma-special-direct-system.
(blueprint: lem-sfb-subcategory-truncation-resolution-system)

Proof:
1. By [lem-pur-homotopy-category-triangulated], the homotopy category is triangulated
   and its derived localization is exact. Use TR2 and TR3 of
   [def-weil-triangulated-category] to compare cone triangles.
2. Apply [lem-sfb-subcategory-left-resolution] to the first good truncation, which
   vanishes above degree 1, to obtain its bounded-above termwise epimorphic resolution.
3. Given the stages through `n`, form the cone of `j_n e_n`. Its terms are the
   biproducts of the next truncation and shifted terms of `E_n`, so it is bounded above.
   Resolve this cone by a bounded-above complex `Q` with terms in `P`, using
   [lem-sfb-subcategory-left-resolution].
4. Form the shifted cone of the composite `Q → Cone(j_n e_n) → E_n[1]`. Its terms are
   biproducts of those of `E_n` and `Q`; rotation gives a triangle whose first arrow
   is a degreewise split inclusion with cokernels isomorphic to the terms of `Q`.
5. TR3 gives a morphism of triangles with outer components the identity and the cone
   resolution. Exact localization and [lem-sf-triangle-morphism-iso] imply that its
   middle component is a quasi-isomorphism. Choose a chain representative `f`.
6. Lift the homotopy between `f u` and `j_n e_n` along the degreewise retraction of `u`.
   Subtract its boundary from `f` to obtain strict equality, preserving the chain-map
   condition and cohomology maps. The resulting map is already epic below degree `n`
   and above degree `n + 1`, where the target is zero.
7. Choose a cover `p : P₀ → K.X n` with `P P₀`. The identity disk on `P₀` in degrees
   `n` and `n + 1` maps to the next truncation by `p` and `d p`. Adding this map to `f`
   makes degree `n` epic. In degree `n + 1` its image contains the boundaries, and the
   image of `f` surjects onto cohomology, so the sum is epic there as well.
8. The disk is acyclic, so adding it preserves the quasi-isomorphism. Extend the
   transition by zero into the disk summand; strict compatibility is retained. Terms
   and transition cokernels remain in `P` by finite biproducts and isomorphism closure,
   and the new bound is the maximum of the preceding bound and `n + 1`. Induction
   constructs all stages. Cones, cohomology and quasi-isomorphisms use
   [def-weil-abstract-derived-category]; the ambient structure is [def-sp-abelian].
-/
theorem subcategory_truncation_resolution_system
    {C : Type u} [Category.{v} C] [Abelian C]
    (P : C → Prop)
    (hzero : ∀ X : C, IsZero X → P X)
    (hiso : ∀ {X : C} {Y : C}, CategoryTheory.Iso X Y → P X → P Y)
    (hbiprod : ∀ {X : C} {Y : C}, P X → P Y → P (X ⊞ Y))
    (hcover : ∀ X : C, ∃ (Y : C) (p : Y ⟶ X), P Y ∧ Epi p)
    (K : CochainComplex C ℤ) :
    ∃ (E : ℤ → CochainComplex C ℤ)
      (e : ∀ n : ℤ, E n ⟶ K.truncLE n)
      (u : ∀ n : ℤ, E n ⟶ E (n + 1)),
      (∀ n : ℤ, 1 ≤ n →
        u n ≫ e (n + 1) = e n ≫ subcategoryTruncationMap K n) ∧
        (∀ n : ℤ, 1 ≤ n →
          (∃ b : ℤ, ∀ i : ℤ, b < i → IsZero ((E n).X i)) ∧
          (∀ i : ℤ, P ((E n).X i)) ∧
          (∀ i : ℤ, Epi ((e n).f i)) ∧
          QuasiIso (e n)) ∧
        (∀ n : ℤ, 1 ≤ n →
          (∀ i : ℤ, IsSplitMono ((u n).f i)) ∧
          (∀ i : ℤ, P (cokernel ((u n).f i)))) := open CochainComplex in by
  classical
  let Stage (n : ℤ) :=
    {p : (Σ E : CochainComplex C ℤ, E ⟶ K.truncLE n) //
      (∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (p.1.X i)) ∧
      (∀ i : ℤ, P (p.1.X i)) ∧ (∀ i : ℤ, Epi (p.2.f i)) ∧ QuasiIso p.2}
  have hstart (n : ℤ) : Nonempty (Stage n) := by
    obtain ⟨E, e, he, hterms, hepi, hbound⟩ :=
      exists_subcategory_left_resolution P
        ⟨HasZeroObject.zero.choose, hzero _ HasZeroObject.zero.choose_spec,
          HasZeroObject.zero.choose_spec⟩ hcover n (K.truncLE n)
        (fun i hi ↦ (K.truncLE n).isZero_of_isStrictlyLE n i hi)
    exact ⟨⟨⟨E, e⟩, ⟨n, hbound⟩, hterms, hepi, he⟩⟩
  have hnext (n : ℤ) (s : Stage n) :
      ∃ s' : Stage (n + 1), ∃ t : s.val.1 ⟶ s'.val.1,
        t ≫ s'.val.2 = s.val.2 ≫ subcategoryTruncationMap K n ∧
        (∀ i : ℤ, IsSplitMono (t.f i)) ∧ (∀ i : ℤ, P (cokernel (t.f i))) := by
    obtain ⟨F, g, t, hbound, hterms, hepi, hg, hcomm, hsplit, hcoker⟩ :=
      successor P hzero hiso hbiprod hcover K n s.val.1 s.val.2
        s.property.1 s.property.2.1
    exact ⟨⟨⟨F, g⟩, hbound, hterms, hepi, hg⟩, t, hcomm, hsplit, hcoker⟩
  let step (n : ℤ) (_ : 1 ≤ n) (s : Stage n) : Stage (n + 1) := (hnext n s).choose
  let stages (n : ℤ) (hn : 1 ≤ n) : Stage n :=
    Int.leInduction (motive := fun n _ ↦ Stage n) (hstart 1).some step n hn
  have hstages (n : ℤ) (hn : 1 ≤ n) :
      stages (n + 1) (by omega) = (hnext n (stages n hn)).choose :=
    Int.leInduction_add_one (motive := fun n _ ↦ Stage n) (hstart 1).some step n hn
  let stage (n : ℤ) : Stage n :=
    if hn : 1 ≤ n then stages n hn else (hstart n).some
  let Transition (n : ℤ) (s : Stage n) (s' : Stage (n + 1)) : Prop :=
    ∃ t : s.val.1 ⟶ s'.val.1,
      t ≫ s'.val.2 = s.val.2 ≫ subcategoryTruncationMap K n ∧
      (∀ i : ℤ, IsSplitMono (t.f i)) ∧ (∀ i : ℤ, P (cokernel (t.f i)))
  have htransition (n : ℤ) (hn : 1 ≤ n) : Transition n (stage n) (stage (n + 1)) := by
    rw [show stage n = stages n hn from dif_pos hn,
      show stage (n + 1) = stages (n + 1) (by omega) from dif_pos (by omega),
      hstages n hn]
    exact (hnext n (stages n hn)).choose_spec
  let u (n : ℤ) : (stage n).val.1 ⟶ (stage (n + 1)).val.1 :=
    if hn : 1 ≤ n then (htransition n hn).choose else 0
  refine ⟨fun n ↦ (stage n).val.1, fun n ↦ (stage n).val.2, u, ?_, ?_, ?_⟩
  · intro n hn
    dsimp only [u]
    rw [dif_pos hn]
    exact (htransition n hn).choose_spec.1
  · exact fun n _ ↦ (stage n).property
  · intro n hn
    simpa only [u, dif_pos hn] using (htransition n hn).choose_spec.2

end CategoryTheory

end
