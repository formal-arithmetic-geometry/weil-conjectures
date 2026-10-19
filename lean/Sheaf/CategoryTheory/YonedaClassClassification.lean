/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C2
-/
module

public import Sheaf.CategoryTheory.YonedaExtensionClass
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.Algebra.Homology.SingleHomology
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Sheaf.CategoryTheory.YonedaClassSplice
import Sheaf.CategoryTheory.YonedaBaerExistence
import Sheaf.CategoryTheory.YonedaClassNaturality

/-! # Classification by the concrete extension class

Source: Stacks Project, Tag 06XU, lemma-yoneda-extension.
(blueprint: lem-coef-yoneda-class-classification)
-/

@[expose] public section

universe u v w

namespace CategoryTheory.YonedaExtension

open Limits Abelian Preadditive

variable {A : Type u} [Category.{v} A] [Abelian A] [HasExt.{w} A]

set_option backward.isDefEq.respectTransparency false in
private theorem exists_mono_comp_eq_zero {X Y : A} (q : ℕ) (hq : 0 < q)
    (x : Ext X Y q) :
    ∃ (I : A) (j : Y ⟶ I), Mono j ∧ x.comp (Ext.mk₀ j) (add_zero q) = 0 := by
  let := HasDerivedCategory.standard A
  let S := (CochainComplex.singleFunctor A 0).obj X
  let T := (CochainComplex.singleFunctor A (-(q : ℤ))).obj Y
  let e := (DerivedCategory.singleFunctors A).shiftIso (q : ℤ) (-(q : ℤ)) 0
    (by omega)
  obtain ⟨L, hL, f, s, hs, hf⟩ :=
    DerivedCategory.left_fac_of_isStrictlyGE (X := S) (Y := T)
      (x.hom ≫ e.hom.app Y) (-(q : ℤ))
  let := hL
  have : QuasiIso s := (DerivedCategory.isIso_Q_map_iff_quasiIso A s).1 hs
  let p := L.pOpcyclesIso (-(q : ℤ) - 1) (-(q : ℤ)) (by simp)
    ((L.isZero_of_isStrictlyGE (-(q : ℤ)) (-(q : ℤ) - 1) (by omega)).eq_of_src _ _)
  let j : Y ⟶ L.X (-(q : ℤ)) :=
    (HomologicalComplex.singleObjHomologySelfIso _ _ _).inv ≫
      HomologicalComplex.homologyMap s (-(q : ℤ)) ≫ L.homologyι (-(q : ℤ)) ≫ p.inv
  have hj : Mono j := by dsimp [j]; infer_instance
  have hs' : s.f (-(q : ℤ)) =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (-(q : ℤ)) Y).hom ≫ j := by
    rw [← cancel_mono p.hom]
    dsimp [j]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    change s.f (-(q : ℤ)) ≫ L.pOpcycles (-(q : ℤ)) = _
    rw [HomologicalComplex.homologyι_naturality]
    dsimp [T, CochainComplex.singleFunctor, CochainComplex.singleFunctors]
    rw [HomologicalComplex.singleObjHomologySelfIso_inv_homologyι_assoc,
      ← HomologicalComplex.pOpcycles_singleObjOpcyclesSelfIso_inv_assoc,
      Iso.inv_hom_id_assoc, HomologicalComplex.p_opcyclesMap]
  let l : L ⟶ (CochainComplex.singleFunctor A (-(q : ℤ))).obj (L.X (-(q : ℤ))) :=
    HomologicalComplex.mkHomToSingle (𝟙 _) (by
      intro k hk
      have hk' : k + 1 = -(q : ℤ) := hk
      apply (L.isZero_of_isStrictlyGE (-(q : ℤ)) k (by omega)).eq_of_src)
  have hsl : s ≫ l = (CochainComplex.singleFunctor A (-(q : ℤ))).map j := by
    apply HomologicalComplex.from_single_hom_ext
    change (s ≫ HomologicalComplex.mkHomToSingle (𝟙 _) _).f (-(q : ℤ)) = _
    simp only [HomologicalComplex.comp_f, HomologicalComplex.mkHomToSingle_f,
      hs', CochainComplex.singleFunctor, CochainComplex.singleFunctors,
      HomologicalComplex.single_map_f_self, Category.assoc, Category.id_comp]
  have hfl : f ≫ l = 0 := by
    apply HomologicalComplex.to_single_hom_ext
    apply (S.isZero_of_isStrictlyGE 0 (-(q : ℤ)) (by omega)).eq_of_src
  refine ⟨_, j, hj, ?_⟩
  apply Ext.ext
  rw [Ext.zero_hom, Ext.comp_hom, Ext.mk₀_hom, ShiftedHom.comp_mk₀]
  apply (cancel_mono (e.hom.app _)).1
  rw [Category.assoc]
  erw [e.hom.naturality j]
  rw [← Category.assoc, hf]
  change (DerivedCategory.Q.map f ≫ inv (DerivedCategory.Q.map s)) ≫
    DerivedCategory.Q.map ((CochainComplex.singleFunctor A (-(q : ℤ))).map j) = _
  rw [← hsl, DerivedCategory.Q.map_comp]
  simp only [Category.assoc, IsIso.inv_hom_id_assoc]
  rw [← DerivedCategory.Q.map_comp, hfl, Functor.map_zero]
  simp

omit [HasExt A] in
set_option backward.isDefEq.respectTransparency false in
private theorem splice_exists (U : A) (n : ℕ) (S : ShortComplex A) (hS : S.ShortExact)
    (F : YonedaExtension A S.X₃ U (n + 1)) :
    ∃ E : YonedaExtension A S.X₁ U (n + 2), Nonempty (Splice S F E) := by
  have : Epi S.g := hS.epi_g
  have : Mono S.f := hS.mono_f
  let q := S.g ≫ F.leftIso.inv
  let d := q ≫ F.sequence.map' 0 1
  have : Epi q := by dsimp [q]; infer_instance
  have hd : S.f ≫ d = 0 := by simp [d, q, ← Category.assoc, S.zero]
  let T := (F.sequence.δ₀.precomp d).precomp S.f
  have hR : (F.sequence.δ₀.precomp d).Exact := by
    apply ComposableArrows.exact_of_δ₀
    · have hz : d ≫ F.sequence.map' 1 2 = 0 := by
        simp [d, Category.assoc, F.exact.toIsComplex.zero 0]
      apply ComposableArrows.exact₂_mk _ hz
      let φ : ShortComplex.mk d (F.sequence.map' 1 2) hz ⟶
          F.sequence.sc F.exact.toIsComplex 0 :=
        { τ₁ := q
          τ₂ := 𝟙 _
          τ₃ := 𝟙 _
          comm₁₂ := by simp [d]
          comm₂₃ := by simp }
      exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2 (F.exact.exact 0)
    · exact F.exact.δ₀
  have hT : T.Exact := by
    apply ComposableArrows.exact_of_δ₀
    · apply ComposableArrows.exact₂_mk _ hd
      have := F.first_mono
      let φ : S ⟶ ShortComplex.mk S.f d hd :=
        { τ₁ := 𝟙 _
          τ₂ := 𝟙 _
          τ₃ := F.leftIso.inv ≫ F.sequence.map' 0 1
          comm₁₂ := by simp
          comm₂₃ := by simp [d, q, Category.assoc] }
      exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).1 hS.exact
    · exact hR
  let E : YonedaExtension A S.X₁ U (n + 2) :=
    { sequence := T
      leftIso := Iso.refl _
      rightIso := F.rightIso
      exact := hT
      first_mono := hS.mono_f
      last_epi := F.last_epi }
  refine ⟨E, ⟨{ firstIso := Iso.refl _
                tailIso := Iso.refl _
                first_comm := by change S.f ≫ 𝟙 _ = (𝟙 _) ≫ S.f; simp
                splice_comm := by
                  change S.g ≫ F.leftIso.inv ≫ F.sequence.map' 0 1 ≫ 𝟙 _ = (𝟙 _) ≫ d
                  simp only [Category.comp_id, Category.id_comp]
                  simp only [d, q, Category.assoc]
                right_comm := by simp [E] }⟩⟩

omit [HasExt A] in
set_option backward.isDefEq.respectTransparency false in
private theorem related_to_splice {V U : A} (n : ℕ)
    (E : YonedaExtension A V U (n + 2)) (S : ShortComplex A)
    (v : V ≅ S.X₁) (b : E.sequence.obj' 1 ⟶ S.X₂)
    (q : E.head.X₃ ⟶ S.X₃)
    (hb : E.leftIso.inv ≫ E.sequence.map' 0 1 ≫ b = v.hom ≫ S.f)
    (hq : E.head.g ≫ q = b ≫ S.g)
    (F : YonedaExtension A S.X₃ U (n + 1))
    (φ : E.tail.sequence ⟶ F.sequence)
    (hl : E.tail.leftMap F φ = q) (hr : E.tail.rightMap F φ = 𝟙 U)
    (G : YonedaExtension A S.X₁ U (n + 2)) (s : Splice S F G) :
    ∃ ψ : E.sequence ⟶ G.sequence,
      E.leftMap G ψ = v.hom ∧ E.rightMap G ψ = 𝟙 U := by
  have hl' : φ.app 0 ≫ F.leftIso.hom = q := by
    change (𝟙 _) ≫ φ.app 0 ≫ F.leftIso.hom = q at hl
    simpa only [Category.id_comp] using hl
  let t := ComposableArrows.δ₀Functor.map φ ≫ s.tailIso.hom
  have hjoin : E.sequence.map' 1 2 ≫ t.app 0 =
      (b ≫ s.firstIso.hom) ≫ G.sequence.map' 1 2 := by
    apply (cancel_epi (𝟙 (E.sequence.obj' 1))).1
    simp only [Category.id_comp]
    have hh := ComposableArrows.naturality' φ 0 1
    have hc : E.sequence.map' 1 2 ≫ φ.app 1 =
        b ≫ S.g ≫ F.leftIso.inv ≫ F.sequence.map' 0 1 := by
      rw [← cokernel.π_desc (E.sequence.map' 0 1) (E.sequence.map' 1 2)
        (E.exact.toIsComplex.zero 0), Category.assoc]
      change E.head.g ≫ E.tail.sequence.map' 0 1 ≫ φ.app 1 = _
      erw [hh]
      have hφ : φ.app 0 = q ≫ F.leftIso.inv := by
        rw [← hl', Category.assoc, Iso.hom_inv_id, Category.comp_id]
      dsimp only [ComposableArrows.app']
      erw [hφ]
      simpa only [Category.assoc] using
        congrArg (fun f ↦ f ≫ F.leftIso.inv ≫ F.sequence.map' 0 1) hq
    change E.sequence.map' 1 2 ≫ φ.app 1 ≫ s.tailIso.hom.app 0 = _
    rw [← Category.assoc, hc]
    simpa only [Category.assoc] using congrArg (fun f ↦ b ≫ f) s.splice_comm
  let ψ : E.sequence ⟶ G.sequence :=
    ComposableArrows.homMkSucc (E.leftIso.hom ≫ v.hom ≫ G.leftIso.inv)
      (ComposableArrows.homMkSucc (b ≫ s.firstIso.hom) t hjoin) (by
        change E.sequence.map' 0 1 ≫ (b ≫ s.firstIso.hom) =
          (E.leftIso.hom ≫ v.hom ≫ G.leftIso.inv) ≫ G.sequence.map' 0 1
        simp only [Category.assoc]
        rw [← s.first_comm]
        have hb' := congrArg (fun f ↦ E.leftIso.hom ≫ f) hb
        simpa only [Category.assoc, Iso.hom_inv_id_assoc] using
          congrArg (fun f ↦ f ≫ s.firstIso.hom) hb')
  refine ⟨ψ, ?_, ?_⟩
  · change E.leftIso.inv ≫ (E.leftIso.hom ≫ v.hom ≫ G.leftIso.inv) ≫
      G.leftIso.hom = v.hom
    simp
  · change E.rightIso.inv ≫
      (φ.app (Fin.last (n + 2)) ≫ s.tailIso.hom.app (Fin.last (n + 1))) ≫
        G.rightIso.hom = 𝟙 U
    rw [Category.assoc, s.right_comm]
    exact hr

omit [HasExt A] in
set_option backward.isDefEq.respectTransparency false in
private theorem splice_related {U : A} (n : ℕ) (S : ShortComplex A)
    (F F' : YonedaExtension A S.X₃ U (n + 1))
    (E E' : YonedaExtension A S.X₁ U (n + 2))
    (s : Splice S F E) (s' : Splice S F' E')
    (φ : F.sequence ⟶ F'.sequence)
    (hl : F.leftMap F' φ = 𝟙 _) (hr : F.rightMap F' φ = 𝟙 U) :
    E.Related E' := by
  have hl' : F.leftIso.inv ≫ φ.app 0 = F'.leftIso.inv := by
    apply (cancel_mono F'.leftIso.hom).1
    simpa only [leftMap, Category.assoc, Iso.inv_hom_id, Category.comp_id] using hl
  let t := s.tailIso.inv ≫ ComposableArrows.δ₀Functor.map φ ≫ s'.tailIso.hom
  have hc : E.sequence.map' 1 2 ≫ t.app 0 =
      (s.firstIso.inv ≫ s'.firstIso.hom) ≫ E'.sequence.map' 1 2 := by
    apply (cancel_epi s.firstIso.hom).1
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc, ← s.splice_comm]
    simp only [Category.assoc]
    change S.g ≫ F.leftIso.inv ≫ F.sequence.map' 0 1 ≫ s.tailIso.hom.app 0 ≫
      (s.tailIso.inv.app 0 ≫ φ.app 1 ≫ s'.tailIso.hom.app 0) = _
    simp only [← Category.assoc, Iso.hom_inv_id_app]
    simp only [Category.assoc]
    erw [Category.id_comp]
    erw [← Category.assoc (F.sequence.map' 0 1), ComposableArrows.naturality' φ 0 1]
    simp only [Category.assoc]
    dsimp only [ComposableArrows.app']
    erw [← Category.assoc F.leftIso.inv, hl']
    simpa only [Category.assoc] using s'.splice_comm
  let ψ : E.sequence ⟶ E'.sequence :=
    ComposableArrows.homMkSucc (E.leftIso.hom ≫ E'.leftIso.inv)
      (ComposableArrows.homMkSucc (s.firstIso.inv ≫ s'.firstIso.hom) t hc) (by
        change E.sequence.map' 0 1 ≫ (s.firstIso.inv ≫ s'.firstIso.hom) =
          (E.leftIso.hom ≫ E'.leftIso.inv) ≫ E'.sequence.map' 0 1
        apply (cancel_epi E.leftIso.inv).1
        rw [← Category.assoc, ← s.first_comm]
        simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc]
        exact s'.first_comm)
  refine ⟨ψ, ?_, ?_⟩
  · change E.leftIso.inv ≫ (E.leftIso.hom ≫ E'.leftIso.inv) ≫ E'.leftIso.hom = 𝟙 _
    simp
  · change E.rightIso.inv ≫
      (s.tailIso.inv.app (Fin.last (n + 1)) ≫ φ.app (Fin.last (n + 2)) ≫
        s'.tailIso.hom.app (Fin.last (n + 1))) ≫ E'.rightIso.hom = 𝟙 U
    rw [Category.assoc, Category.assoc, s'.right_comm]
    have hs : s.tailIso.inv.app (Fin.last (n + 1)) ≫ F.rightIso.hom =
        E.rightIso.hom := by
      rw [← s.right_comm]
      simp
    have hr' : φ.app (Fin.last (n + 2)) ≫ F'.rightIso.hom = F.rightIso.hom := by
      apply (cancel_epi F.rightIso.inv).1
      simpa only [rightMap, Category.assoc, Iso.inv_hom_id] using hr
    rw [hr', hs, Iso.inv_hom_id]

omit [HasExt A] in
private theorem splice_equivalent {U : A} (n : ℕ) (S : ShortComplex A)
    (hS : S.ShortExact) (F F' : YonedaExtension A S.X₃ U (n + 1))
    (E E' : YonedaExtension A S.X₁ U (n + 2))
    (s : Splice S F E) (s' : Splice S F' E') (h : F.Equivalent F') :
    E.Equivalent E' := by
  induction h generalizing E E' with
  | rel F F' h =>
    obtain ⟨φ, hl, hr⟩ := h
    exact Relation.EqvGen.rel _ _ (splice_related n S F F' E E' s s' φ hl hr)
  | refl F =>
    apply Relation.EqvGen.rel
    exact splice_related n S F F E E' s s' (𝟙 _) (by
        change F.leftIso.inv ≫ 𝟙 _ ≫ F.leftIso.hom = 𝟙 _
        simp)
      (by
        change F.rightIso.inv ≫ 𝟙 _ ≫ F.rightIso.hom = 𝟙 _
        simp)
  | symm F F' h ih => exact (ih E' E s' s).symm
  | trans F F' F'' h h' ih ih' =>
    obtain ⟨G, ⟨t⟩⟩ := splice_exists U n S hS F'
    exact Relation.EqvGen.trans _ _ _ (ih E G s t) (ih' G E' t s')

omit [HasExt A] in
set_option backward.isDefEq.respectTransparency false in
private theorem extension_to_head {V U : A} (n : ℕ)
    (E : YonedaExtension A V U (n + 2)) (S : ShortComplex A) (hS : S.ShortExact)
    (hV : S.X₁ = V) (b : E.sequence.obj' 1 ⟶ S.X₂)
    (hb : E.leftIso.inv ≫ E.sequence.map' 0 1 ≫ b = eqToHom hV.symm ≫ S.f) :
    ∃ (F : YonedaExtension A S.X₃ U (n + 1))
      (G : YonedaExtension A S.X₁ U (n + 2)),
      Nonempty (Splice S F G) ∧
      ∃ ψ : E.sequence ⟶ G.sequence,
        E.leftMap G ψ = eqToHom hV.symm ∧ E.rightMap G ψ = 𝟙 U := by
  let q : E.head.X₃ ⟶ S.X₃ :=
    cokernel.desc (E.sequence.map' 0 1) (b ≫ S.g) (by
      have hh := congrArg (fun f ↦ E.leftIso.hom ≫ f ≫ S.g) hb
      simpa only [Category.assoc, Iso.hom_inv_id_assoc, S.zero, comp_zero] using hh)
  have hq : E.head.g ≫ q = b ≫ S.g := by
    exact cokernel.π_desc _ _ _
  obtain ⟨F, φ, hl, hr, _, _⟩ := pushout_extension n E.tail q
  obtain ⟨G, ⟨t⟩⟩ := splice_exists U n S hS F
  obtain ⟨ψ, hψl, hψr⟩ := related_to_splice n E S (eqToIso hV.symm) b q hb hq
    F φ hl hr G t
  exact ⟨F, G, ⟨t⟩, ψ, hψl, hψr⟩

omit [HasExt A] in
set_option backward.isDefEq.respectTransparency false in
private theorem map_head_splice {U : A} (n : ℕ) (S T : ShortComplex A)
    (φ : S ⟶ T)
    (F : YonedaExtension A S.X₃ U (n + 1))
    (G : YonedaExtension A S.X₁ U (n + 2)) (s : Splice S F G)
    (F' : YonedaExtension A T.X₃ U (n + 1)) (p : F.sequence ⟶ F'.sequence)
    (hl : F.leftMap F' p = φ.τ₃) (hr : F.rightMap F' p = 𝟙 U)
    (G' : YonedaExtension A T.X₁ U (n + 2)) (s' : Splice T F' G') :
    ∃ ψ : G.sequence ⟶ G'.sequence,
      G.leftMap G' ψ = φ.τ₁ ∧ G.rightMap G' ψ = 𝟙 U := by
  let t := s.tailIso.inv ≫ ComposableArrows.δ₀Functor.map p ≫ s'.tailIso.hom
  have hl' : F.leftIso.inv ≫ p.app 0 = φ.τ₃ ≫ F'.leftIso.inv := by
    apply (cancel_mono F'.leftIso.hom).1
    simpa only [leftMap, Category.assoc, Iso.inv_hom_id, Category.comp_id,
      Iso.inv_hom_id_assoc] using hl
  have hc : G.sequence.map' 1 2 ≫ t.app 0 =
      (s.firstIso.inv ≫ φ.τ₂ ≫ s'.firstIso.hom) ≫ G'.sequence.map' 1 2 := by
    apply (cancel_epi s.firstIso.hom).1
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc, ← s.splice_comm]
    simp only [Category.assoc]
    change S.g ≫ F.leftIso.inv ≫ F.sequence.map' 0 1 ≫ s.tailIso.hom.app 0 ≫
      (s.tailIso.inv.app 0 ≫ p.app 1 ≫ s'.tailIso.hom.app 0) = _
    simp only [← Category.assoc, Iso.hom_inv_id_app]
    simp only [Category.assoc]
    erw [Category.id_comp]
    erw [← Category.assoc (F.sequence.map' 0 1), ComposableArrows.naturality' p 0 1]
    simp only [Category.assoc]
    dsimp only [ComposableArrows.app']
    erw [← Category.assoc F.leftIso.inv, hl']
    simp only [← Category.assoc]
    rw [← φ.comm₂₃]
    simpa only [Category.assoc] using
      congrArg (fun f ↦ φ.τ₂ ≫ f) s'.splice_comm
  let ψ : G.sequence ⟶ G'.sequence :=
    ComposableArrows.homMkSucc (G.leftIso.hom ≫ φ.τ₁ ≫ G'.leftIso.inv)
      (ComposableArrows.homMkSucc (s.firstIso.inv ≫ φ.τ₂ ≫ s'.firstIso.hom) t hc) (by
        change G.sequence.map' 0 1 ≫ (s.firstIso.inv ≫ φ.τ₂ ≫ s'.firstIso.hom) =
          (G.leftIso.hom ≫ φ.τ₁ ≫ G'.leftIso.inv) ≫ G'.sequence.map' 0 1
        apply (cancel_epi G.leftIso.inv).1
        rw [← Category.assoc, ← s.first_comm]
        simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc]
        rw [← s'.first_comm]
        simpa only [Category.assoc] using
          congrArg (fun f ↦ f ≫ s'.firstIso.hom) φ.comm₁₂.symm)
  refine ⟨ψ, ?_, ?_⟩
  · change G.leftIso.inv ≫ (G.leftIso.hom ≫ φ.τ₁ ≫ G'.leftIso.inv) ≫
      G'.leftIso.hom = φ.τ₁
    simp
  · change G.rightIso.inv ≫
      (s.tailIso.inv.app (Fin.last (n + 1)) ≫ p.app (Fin.last (n + 2)) ≫
        s'.tailIso.hom.app (Fin.last (n + 1))) ≫ G'.rightIso.hom = 𝟙 U
    rw [Category.assoc, Category.assoc, s'.right_comm]
    have hs : s.tailIso.inv.app (Fin.last (n + 1)) ≫ F.rightIso.hom =
        G.rightIso.hom := by
      rw [← s.right_comm]
      simp
    have hr' : p.app (Fin.last (n + 2)) ≫ F'.rightIso.hom = F.rightIso.hom := by
      apply (cancel_epi F.rightIso.inv).1
      simpa only [rightMap, Category.assoc, Iso.inv_hom_id] using hr
    rw [hr', hs, Iso.inv_hom_id]

set_option backward.isDefEq.respectTransparency false in
private theorem shortExact_map_of_extClass {S T : ShortComplex A}
    (hS : S.ShortExact) (hT : T.ShortExact)
    (l : S.X₁ ⟶ T.X₁) (r : S.X₃ ⟶ T.X₃)
    (h : hS.extClass.comp (Ext.mk₀ l) (add_zero 1) =
      (Ext.mk₀ r).comp hT.extClass (zero_add 1)) :
    ∃ φ : S ⟶ T, φ.τ₁ = l ∧ φ.τ₃ = r := by
  have := hT.mono_f
  have hz : (Ext.mk₀ (S.g ≫ r)).comp hT.extClass (zero_add 1) = 0 := by
    rw [← Ext.mk₀_comp_mk₀_assoc, ← h, ← Ext.comp_assoc_of_third_deg_zero,
      hS.comp_extClass, Ext.zero_comp]
  obtain ⟨x, hx⟩ := Ext.covariant_sequence_exact₃ S.X₂ hT (Ext.mk₀ (S.g ≫ r))
    (zero_add 1) hz
  obtain ⟨b, rfl⟩ := (Ext.mk₀_bijective S.X₂ T.X₂).2 x
  have hb : b ≫ T.g = S.g ≫ r := by
    apply (Ext.mk₀_bijective _ _).1
    simpa using hx
  have ha₀ : (S.f ≫ b) ≫ T.g = 0 := by rw [Category.assoc, hb, ← Category.assoc, S.zero]; simp
  let a := hT.exact.lift (S.f ≫ b) ha₀
  have ha : a ≫ T.f = S.f ≫ b := hT.exact.lift_f _ ha₀
  let ψ : S ⟶ T :=
    { τ₁ := a
      τ₂ := b
      τ₃ := r
      comm₁₂ := ha
      comm₂₃ := hb }
  have hd : hS.extClass.comp (Ext.mk₀ (a - l)) (add_zero 1) = 0 := by
    rw [sub_eq_add_neg, Ext.mk₀_add, Ext.mk₀_neg, Ext.comp_add, Ext.comp_neg]
    rw [(hS.extClass_naturality hT ψ).trans h.symm, add_neg_cancel]
  obtain ⟨x, hx⟩ := Ext.contravariant_sequence_exact₁ hS T.X₁ (Ext.mk₀ (a - l))
    (add_zero 1) hd
  obtain ⟨t, rfl⟩ := (Ext.mk₀_bijective S.X₂ T.X₁).2 x
  have ht : S.f ≫ t = a - l := by
    apply (Ext.mk₀_bijective _ _).1
    simpa using hx
  refine ⟨{ τ₁ := l, τ₂ := b - t ≫ T.f, τ₃ := r, comm₁₂ := ?_, comm₂₃ := ?_ }, rfl, rfl⟩
  · rw [comp_sub, ← Category.assoc, ht, sub_comp, ← ha]
    abel
  · simp only [sub_comp, Category.assoc, T.zero, comp_zero, sub_zero, hb]

set_option backward.isDefEq.respectTransparency false in
private theorem equivalent_of_derivedClass_zero_degree {V U : A}
    (E F : YonedaExtension A V U 1) (h : E.derivedClass 0 = F.derivedClass 0) :
    E.Equivalent F := by
  have h₀ := neg_inj.mp (show
    -(((Ext.mk₀ E.rightIso.inv).comp E.shortExact.extClass (zero_add 1)).comp
      (Ext.mk₀ E.leftIso.hom) (add_zero 1)) =
    -(((Ext.mk₀ F.rightIso.inv).comp F.shortExact.extClass (zero_add 1)).comp
      (Ext.mk₀ F.leftIso.hom) (add_zero 1)) from h)
  have h₁ := congrArg (fun x => (Ext.mk₀ E.rightIso.hom).comp
    (x.comp (Ext.mk₀ F.leftIso.inv) (add_zero 1)) (zero_add 1)) h₀
  have hh : E.shortExact.extClass.comp
      (Ext.mk₀ (E.leftIso.hom ≫ F.leftIso.inv)) (add_zero 1) =
      (Ext.mk₀ (E.rightIso.hom ≫ F.rightIso.inv)).comp F.shortExact.extClass
        (zero_add 1) := by
    simpa only [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀,
      Ext.mk₀_comp_mk₀_assoc, Iso.hom_inv_id, Ext.mk₀_id_comp,
      Category.assoc, Iso.inv_hom_id_assoc, Ext.comp_mk₀_id] using h₁
  obtain ⟨φ, hl, hr⟩ := shortExact_map_of_extClass E.shortExact F.shortExact _ _ hh
  let f : E.sequence ⟶ F.sequence :=
    ComposableArrows.homMk₂ φ.τ₁ φ.τ₂ φ.τ₃ φ.comm₁₂.symm φ.comm₂₃.symm
  apply Relation.EqvGen.rel
  refine ⟨f, ?_, ?_⟩
  · change E.leftIso.inv ≫ φ.τ₁ ≫ F.leftIso.hom = 𝟙 V
    rw [hl]
    simp
  · change E.rightIso.inv ≫ φ.τ₃ ≫ F.rightIso.hom = 𝟙 U
    rw [hr]
    simp

set_option backward.isDefEq.respectTransparency false in
private theorem derivedClass_surjective (V U : A) (n : ℕ) :
    Function.Surjective (derivedClass (A := A) (V := V) (U := U) n) := by
  induction n generalizing V with
  | zero =>
    intro x
    obtain ⟨I, j, hj, hx⟩ := exists_mono_comp_eq_zero 1 (by omega) (-x)
    have := hj
    let S := ShortComplex.mk j (cokernel.π j) (cokernel.condition j)
    have hS : S.ShortExact :=
      { exact := ShortComplex.exact_cokernel j
        mono_f := hj
        epi_g := by infer_instance }
    obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁ U hS (-x) hx (zero_add 1)
    obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective U (cokernel j)).2 y
    let E₀ : YonedaExtension A V (cokernel j) 1 :=
      { sequence := ComposableArrows.mk₂ S.f S.g
        leftIso := Iso.refl _
        rightIso := Iso.refl _
        exact := hS.exact.exact_toComposableArrows
        first_mono := hS.mono_f
        last_epi := hS.epi_g }
    obtain ⟨E, b, hl, hr, _, _⟩ := pullback_extension 0 E₀ f
    have hn := derivedClass_naturality _ _ _ _ 0 E E₀ b
    rw [hl, hr, Ext.comp_mk₀_id] at hn
    refine ⟨E, ?_⟩
    have hc : E₀.derivedClass 0 = -hS.extClass := by
      change -(((Ext.mk₀ (𝟙 _)).comp hS.extClass (zero_add 1)).comp
        (Ext.mk₀ (𝟙 _)) (add_zero 1)) = -hS.extClass
      simp only [Ext.mk₀_id_comp, Ext.comp_mk₀_id]
    rw [hn, hc, Ext.comp_neg]
    exact (congrArg (fun t : Ext U V 1 => -t) hy).trans (neg_neg x)
  | succ n ih =>
    intro x
    let z := (-1 : ℤ) ^ n • x
    obtain ⟨I, j, hj, hx⟩ := exists_mono_comp_eq_zero (n + 2) (by omega) z
    have := hj
    let S := ShortComplex.mk j (cokernel.π j) (cokernel.condition j)
    have hS : S.ShortExact :=
      { exact := ShortComplex.exact_cokernel j
        mono_f := hj
        epi_g := by infer_instance }
    obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁ U hS z hx (show (n + 1) + 1 = n + 2 by omega)
    obtain ⟨F, hF⟩ := ih (cokernel j) y
    obtain ⟨E, ⟨s⟩⟩ := splice_exists U n S hS F
    refine ⟨E, ?_⟩
    rw [derivedClass_splice U n S hS F E s, hF, hy]
    dsimp [z]
    rcases neg_one_pow_eq_or ℤ n with h | h <;> simp [h]

set_option backward.isDefEq.respectTransparency false in
private theorem class_eq_of_fixedMap {V U : A} (n : ℕ)
    (E F : YonedaExtension A V U (n + 1)) (φ : E.sequence ⟶ F.sequence)
    (hl : E.leftMap F φ = 𝟙 V) (hr : E.rightMap F φ = 𝟙 U) :
    E.derivedClass n = F.derivedClass n := by
  simpa only [hl, hr, Ext.comp_mk₀_id, Ext.mk₀_id_comp] using
    derivedClass_naturality V U V U n E F φ

set_option backward.isDefEq.respectTransparency false in
private theorem common_splice_equivalent {U : A} (n : ℕ)
    (ih : ∀ (V : A) (E F : YonedaExtension A V U (n + 1)),
      E.derivedClass n = F.derivedClass n → E.Equivalent F)
    (S : ShortComplex A) (hS : S.ShortExact)
    (P Q : YonedaExtension A S.X₃ U (n + 1))
    (G H : YonedaExtension A S.X₁ U (n + 2))
    (s : Splice S P G) (t : Splice S Q H)
    (h : G.derivedClass (n + 1) = H.derivedClass (n + 1)) :
    G.Equivalent H := by
  have he : (P.derivedClass n).comp hS.extClass
      (show (n + 1) + 1 = n + 2 from rfl) =
      (Q.derivedClass n).comp hS.extClass (by omega) := by
    rw [derivedClass_splice U n S hS P G s,
      derivedClass_splice U n S hS Q H t] at h
    rcases neg_one_pow_eq_or ℤ n with hs | hs <;>
      simpa only [hs, one_smul, neg_one_smul, neg_inj] using h
  have hz : (P.derivedClass n - Q.derivedClass n).comp hS.extClass
      (show (n + 1) + 1 = n + 2 from rfl) = 0 := by
    rw [sub_eq_add_neg, Ext.add_comp, Ext.neg_comp, he, add_neg_cancel]
  obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₃ U hS
    (P.derivedClass n - Q.derivedClass n) (show (n + 1) + 1 = n + 2 from rfl) hz
  obtain ⟨J, j, hj, hyj⟩ := exists_mono_comp_eq_zero (n + 1) (by omega) y
  have := hj
  have := hS.mono_f
  have := hS.epi_g
  let a := S.f ≫ j
  let T := ShortComplex.mk a (cokernel.π a) (cokernel.condition a)
  have hT : T.ShortExact :=
    { exact := ShortComplex.exact_cokernel a
      mono_f := by infer_instance
      epi_g := by infer_instance }
  let q : S.X₃ ⟶ T.X₃ := hS.exact.desc (j ≫ T.g) (by simp [T, a, ← Category.assoc])
  have hq : S.g ≫ q = j ≫ T.g := hS.exact.g_desc _ _
  let φ : S ⟶ T :=
    { τ₁ := 𝟙 _
      τ₂ := j
      τ₃ := q
      comm₁₂ := by simp [T, a]
      comm₂₃ := hq.symm }
  obtain ⟨P', p, hpl, hpr, _, _⟩ := pushout_extension n P q
  obtain ⟨Q', r, hql, hqr, _, _⟩ := pushout_extension n Q q
  have hp := derivedClass_naturality _ _ _ _ n P P' p
  have hq' := derivedClass_naturality _ _ _ _ n Q Q' r
  rw [hpl, hpr, Ext.mk₀_id_comp] at hp
  rw [hql, hqr, Ext.mk₀_id_comp] at hq'
  have hPQ : P'.derivedClass n = Q'.derivedClass n := by
    apply sub_eq_zero.mp
    rw [← hp, ← hq', sub_eq_add_neg, ← Ext.neg_comp, ← Ext.add_comp,
      ← sub_eq_add_neg, ← hy, Ext.comp_assoc_of_second_deg_zero,
      Ext.mk₀_comp_mk₀, hq, ← Ext.mk₀_comp_mk₀,
      ← Ext.comp_assoc_of_second_deg_zero, hyj, Ext.zero_comp]
  obtain ⟨G', ⟨s'⟩⟩ := splice_exists U n T hT P'
  obtain ⟨H', ⟨t'⟩⟩ := splice_exists U n T hT Q'
  obtain ⟨g, hgl, hgr⟩ := map_head_splice n S T φ P G s P' p hpl hpr G' s'
  obtain ⟨k, hkl, hkr⟩ := map_head_splice n S T φ Q H t Q' r hql hqr H' t'
  have hG : G.Equivalent G' := Relation.EqvGen.rel _ _ ⟨g, hgl, hgr⟩
  have hH : H.Equivalent H' := Relation.EqvGen.rel _ _ ⟨k, hkl, hkr⟩
  have hGH := splice_equivalent n T hT P' Q' G' H' s' t' (ih T.X₃ P' Q' hPQ)
  exact Relation.EqvGen.trans _ _ _ hG
    (Relation.EqvGen.trans _ _ _ hGH (Relation.EqvGen.symm _ _ hH))

set_option backward.isDefEq.respectTransparency false in
private theorem equivalent_of_derivedClass_eq (V U : A) (n : ℕ)
    (E F : YonedaExtension A V U (n + 1))
    (h : E.derivedClass n = F.derivedClass n) : E.Equivalent F := by
  induction n generalizing V with
  | zero => exact equivalent_of_derivedClass_zero_degree E F h
  | succ n ih =>
    let aE := E.leftIso.inv ≫ E.sequence.map' 0 1
    let aF := F.leftIso.inv ≫ F.sequence.map' 0 1
    have : Mono aE := by have := E.first_mono; dsimp [aE]; infer_instance
    have : Mono aF := by have := F.first_mono; dsimp [aF]; infer_instance
    let a := aE ≫ pushout.inl aE aF
    let S := ShortComplex.mk a (cokernel.π a) (cokernel.condition a)
    have hS : S.ShortExact :=
      { exact := ShortComplex.exact_cokernel a
        mono_f := by infer_instance
        epi_g := by infer_instance }
    obtain ⟨P, G, ⟨s⟩, g, hgl, hgr⟩ :=
      extension_to_head n E S hS rfl (pushout.inl aE aF) (by simp [S, a, aE])
    obtain ⟨Q, H, ⟨t⟩, k, hkl, hkr⟩ :=
      extension_to_head n F S hS rfl (pushout.inr aE aF) (by
        simpa only [S, a, aF, eqToHom_refl, Category.id_comp, Category.assoc] using
          (pushout.condition (f := aE) (g := aF)).symm)
    have hG := class_eq_of_fixedMap (n + 1) E G g hgl hgr
    have hH := class_eq_of_fixedMap (n + 1) F H k hkl hkr
    have hGH : G.derivedClass (n + 1) = H.derivedClass (n + 1) :=
      hG.symm.trans (h.trans hH)
    have he := common_splice_equivalent n ih S hS P Q G H s t hGH
    have hEG : E.Equivalent G := Relation.EqvGen.rel _ _ ⟨g, hgl, hgr⟩
    have hFH : F.Equivalent H := Relation.EqvGen.rel _ _ ⟨k, hkl, hkr⟩
    exact Relation.EqvGen.trans _ _ _ hEG
      (Relation.EqvGen.trans _ _ _ he (Relation.EqvGen.symm _ _ hFH))

/-- Every positive Ext class is represented by an exact sequence, and equality
of the concrete classes is detected by endpoint-fixed zigzags.
Source: Stacks Project, Tag 06XU, lemma-yoneda-extension.
Proof: first efface any positive Ext class by a monomorphism of its second
argument. Use a left fraction with a target complex zero below minus the degree;
the map of the second argument into the lowest term is monic, and projection
from that complex to this term kills the original class. The covariant Ext exact
sequence for this monomorphism and its actual cokernel lowers the degree.
Induction and the signed splice identity give a representing extension; in
degree one pull back the cokernel short exact sequence along the resulting map.
For equality in degree one, the Ext exact sequences construct a short-complex
map with the prescribed endpoint maps: first lift the right endpoint map, then
correct its middle component by a map through the first injection.
For higher degrees, push out the two first injections to a common monomorphism
and re-express both extensions as splices with its cokernel sequence. The signed
splice identity makes the difference of their tail classes lie in the image
of Ext with values in the middle object. Efface that class by a monomorphism of
the middle object. The induced map of cokernels makes the two pushed-out tail
classes equal. Induction gives a tail zigzag; splice this zigzag and adjoin the
comparison maps from the original extensions. All splices and endpoint changes
use actual pushout extensions, and all resulting maps fix both endpoints.
No enough-injectives hypothesis is used.
(blueprint: lem-coef-yoneda-class-classification) -/
theorem derivedClass_classification (V U : A) (n : ℕ) :
    Function.Surjective (derivedClass (A := A) (V := V) (U := U) n) ∧
    ∀ E F : YonedaExtension A V U (n + 1),
      E.derivedClass n = F.derivedClass n → E.Equivalent F := by
  exact ⟨derivedClass_surjective V U n, equivalent_of_derivedClass_eq V U n⟩

end CategoryTheory.YonedaExtension
