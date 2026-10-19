/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G4
-/
module

public import Sheaf.DeligneLaumon.SmoothAffineGeometricFiltration
public import Sheaf.Paper.FiniteFieldFiber
import Sheaf.AlgebraicGeometry.GeometricallyConnectedCheckAfterExtension
import WeilConjectures.AlgebraicGeometry.Morphisms.Finite.LimitBaseChange
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.Mathlib.AlgebraicGeometry.PullbackCarrier
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.FieldTheory.Finiteness
import WeilConjectures.AlgebraicGeometry.FieldExtensionDescent
import WeilConjectures.AlgebraicGeometry.IntermediateFieldLimit
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# Descending a given finite smooth affine filtration

Source: Stacks Project, Limits, Tag 01ZM, Varieties, Tag 0388, and Descent,
Tag 02L5. This is the simultaneous descent step in paragraphs 6--7 of
`thm-zl-real-mixed-by-curves`.
(blueprint: lem-zl-smooth-affine-filtration-finite-field-descent).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace WeilConjectures

open Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem finite_objects_models
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    (c : Cone D) (hc : IsLimit c)
    (A : Type v) [Finite A] (F : A → Over c.pt)
    (hF : ∀ a, LocallyOfFinitePresentation (F a).hom ∧
      QuasiCompact (F a).hom ∧ QuasiSeparated (F a).hom) :
    ∃ (i : Iᵒᵖ) (V : A → Over (D.obj i)),
      (∀ a, LocallyOfFinitePresentation (V a).hom ∧
        QuasiCompact (V a).hom ∧ QuasiSeparated (V a).hom) ∧
      (∀ a, Nonempty ((Over.pullback (c.π.app i)).obj (V a) ≅ F a)) := by
  classical
  have hex (a : A) : ∃ (i : Iᵒᵖ) (V : Over (D.obj i)),
      (LocallyOfFinitePresentation V.hom ∧ QuasiCompact V.hom ∧ QuasiSeparated V.hom) ∧
      Nonempty ((Over.pullback (c.π.app i)).obj V ≅ F a) := by
    have := (hF a).1
    have := (hF a).2.1
    have := (hF a).2.2
    obtain ⟨i, Y, p, hp, hqc, hqs, h, H⟩ :=
      Scheme.exists_isPullback_of_finitePresentation hc (F a).hom
    refine ⟨i, Over.mk p, ⟨hp, hqc, hqs⟩, ⟨?_⟩⟩
    exact (Over.isoMk H.isoPullback (IsPullback.isoPullback_hom_snd H)).symm
  choose i V hV e using hex
  let _ : Fintype A := Fintype.ofFinite A
  obtain ⟨j, hj⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image i)
  let f (a : A) : j ⟶ i a := (hj (Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩)).some
  refine ⟨j, (fun a ↦ (Over.pullback (D.map (f a))).obj (V a)), ?_, ?_⟩
  · intro a
    have := (hV a).1
    have := (hV a).2.1
    have := (hV a).2.2
    exact ⟨inferInstanceAs (LocallyOfFinitePresentation (pullback.snd _ _)),
      inferInstanceAs (QuasiCompact (pullback.snd _ _)),
      inferInstanceAs (QuasiSeparated (pullback.snd _ _))⟩
  · intro a
    let E := (Over.pullbackComp (c.π.app j) (D.map (f a))).symm ≪≫
      eqToIso (congrArg (fun g : c.pt ⟶ D.obj (i a) ↦ Over.pullback g) (c.w (f a)))
    exact ⟨E.app (V a) ≪≫ (e a).some⟩


private theorem closed_ambient {S : Scheme.{u}} {Y : Over S} {n : ℕ}
    (H : WeilConjectures.SmoothAffineFiltration Y n) (a : Fin (n + 1)) :
    IsClosedImmersion (H.intoAmbient a).left := by
  induction a using Fin.induction with
  | zero => rw [H.intoAmbient_zero]; infer_instance
  | succ a ih =>
    rw [H.intoAmbient_succ, Over.comp_left]
    have := H.closed_inclusion a
    infer_instance

private theorem finite_closed_models
    (k K : Type u) [Field k] [Field K] [Algebra k K] [Algebra.IsAlgebraic k K]
    (X₀ : Scheme.{u}) (f : X₀ ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f]
    (A : Type v) [Finite A] (Z : A → Scheme.{u})
    (z : ∀ a, Z a ⟶ pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    (hz : ∀ a, IsClosedImmersion (z a)) :
    ∃ (L : FiniteIntermediateField k K)
      (W : A → Scheme.{u})
      (w : ∀ a, W a ⟶ pullback f
        (Spec.map (CommRingCat.ofHom (algebraMap k L.1))))
      (r : ∀ a, Z a ⟶ W a),
      ∀ a, IsPullback (r a) (z a) (w a)
        (pullback.map f (Spec.map (CommRingCat.ofHom (algebraMap k K))) f
          (Spec.map (CommRingCat.ofHom (algebraMap k L.1)))
          (𝟙 _) (Spec.map (CommRingCat.ofHom (algebraMap L.1 K))) (𝟙 _)
          (by simp) (by simp [← Spec.map_comp, ← CommRingCat.ofHom_comp,
            ← IsScalarTower.algebraMap_eq k L.1 K])) := by
  classical
  let D₀ := FiniteIntermediateField.specDiagram k K
  let c₀ := FiniteIntermediateField.specCone k K
  let q (i : (FiniteIntermediateField k K)ᵒᵖ) : D₀.obj i ⟶ Spec (.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k i.unop.1))
  have hq {i j : (FiniteIntermediateField k K)ᵒᵖ} (h : i ⟶ j) :
      D₀.map h ≫ q j = q i := by
    simp only [q, D₀, FiniteIntermediateField.specDiagram_map,
      FiniteIntermediateField.specMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
  let q₀ := Spec.map (CommRingCat.ofHom (algebraMap k K))
  have hq₀ (i : (FiniteIntermediateField k K)ᵒᵖ) : c₀.π.app i ≫ q i = q₀ := by
    simp [c₀, q, q₀, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← IsScalarTower.algebraMap_eq k i.unop.1 K]
  let D := baseChangeOverFamilyDiagram D₀ q hq f
  let c := baseChangeOverFamilyCone D₀ c₀ q hq q₀ hq₀ f
  have : IsConnected (FiniteIntermediateField k K)ᵒᵖ := IsCofiltered.isConnected _
  have hc : IsLimit c := isLimitBaseChangeOverFamilyCone D₀ c₀ q hq q₀ hq₀ f
    (FiniteIntermediateField.isLimitSpecCone k K)
  have (i : (FiniteIntermediateField k K)ᵒᵖ) : CompactSpace (D.obj i) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd f (q i))
  have (i : (FiniteIntermediateField k K)ᵒᵖ) : QuasiSeparatedSpace (D.obj i) := by
    have : IsLocallyNoetherian (D₀.obj i) := inferInstanceAs
      (IsLocallyNoetherian (Spec (.of i.unop.1)))
    have : IsLocallyNoetherian (D.obj i) :=
      LocallyOfFiniteType.isLocallyNoetherian (pullback.snd f (q i))
    infer_instance
  have (a : A) : IsClosedImmersion (z a) := hz a
  have : IsLocallyNoetherian c.pt :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd f q₀)
  obtain ⟨i, V, hV, e⟩ := finite_objects_models D c hc A
    (fun a ↦ Over.mk (z a)) (fun a ↦ ⟨
      inferInstanceAs (LocallyOfFinitePresentation (z a)),
      inferInstanceAs (QuasiCompact (z a)), inferInstanceAs (QuasiSeparated (z a))⟩)
  refine ⟨i.unop, (fun a ↦ (V a).left), (fun a ↦ (V a).hom),
    (fun a ↦ (e a).some.inv.left ≫ pullback.fst (V a).hom (c.π.app i)), ?_⟩
  intro a
  exact (IsPullback.of_hasPullback (V a).hom (c.π.app i)).of_iso
    ((Over.forget c.pt).mapIso (e a).some) (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp only [Functor.mapIso_hom, Over.forget_map, Iso.refl_hom, Category.comp_id]
        rw [← Category.assoc, ← Over.comp_left, Iso.hom_inv_id, Over.id_left]
        change _ = (𝟙 _) ≫ _
        rw [Category.id_comp])
    (by simpa using (Over.w (e a).some.hom).symm) (by simp) (by rfl)

private theorem reduced_closed_iso {X Y Z : Scheme.{u}}
    [IsReduced X] [IsReduced Y] (f : X ⟶ Z) (g : Y ⟶ Z)
    [IsClosedImmersion f] [IsClosedImmersion g] (h : Set.range f = Set.range g) :
    ∃ e : X ≅ Y, e.hom ≫ g = f := by
  obtain ⟨a, ha, -⟩ := IsClosedImmersion.existsUnique_fac_of_range_subset_range g f h.le
  obtain ⟨b, hb, -⟩ := IsClosedImmersion.existsUnique_fac_of_range_subset_range f g h.ge
  refine ⟨⟨a, b, ?_, ?_⟩, ha⟩
  · apply (cancel_mono f).mp
    simp [Category.assoc, hb, ha]
  · apply (cancel_mono g).mp
    simp [Category.assoc, hb, ha]

private theorem finite_field_eq (D : FiniteFieldDatum.{u})
    (L : FiniteIntermediateField D.k₀ D.k) :
    ∃ (m : ℕ) (hm : 1 ≤ m), L.1.toSubfield = D.extensionSubfield m hm := by
  have : Module.Finite D.k₀ L.1 := L.2
  refine ⟨Module.finrank D.k₀ L.1, Module.finrank_pos, ?_⟩
  apply (FiniteField.exists_unique_subfield_of_closure D.p D.a D.q D.prime
    D.exponent_pos D.cardinality_eq D.k₀ D.card_base D.k
      (Module.finrank D.k₀ L.1) Module.finrank_pos).choose_spec.2.2.1
  exact (Module.natCard_eq_pow_finrank (K := D.k₀) (V := L.1)).trans
    (by rw [D.card_base])

private theorem finite_named_closed_models (D : FiniteFieldDatum.{u})
    (X₀ : Scheme.{u}) (f : X₀ ⟶ Spec (.of D.k₀))
    [LocallyOfFiniteType f] [QuasiCompact f]
    (A : Type v) [Finite A] (Z : A → Scheme.{u})
    (z : ∀ a, Z a ⟶ pullback f (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))
    (hz : ∀ a, IsClosedImmersion (z a)) :
    ∃ (m : ℕ) (hm : 1 ≤ m),
      let km := D.extensionSubfield m hm
      let Xm := pullback f (Spec.map (CommRingCat.ofHom (D.extensionEmbedding m hm)))
      let X := pullback f (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))
      ∃ (χ : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap km D.k)))).obj
          (Over.mk (pullback.snd f
            (Spec.map (CommRingCat.ofHom (D.extensionEmbedding m hm)))) ) ≅
          Over.mk (pullback.snd f
            (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
        (q : X ⟶ Xm),
        IsPullback q (pullback.snd f _ ) (pullback.snd f _)
          (Spec.map (CommRingCat.ofHom (algebraMap km D.k))) ∧
        (∀ W : Over (Spec (.of km)), ∀ w : W ⟶ Over.mk (pullback.snd f _),
          ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap km D.k)))).map w ≫
            χ.hom).left ≫ q =
          pullback.fst W.hom (Spec.map (CommRingCat.ofHom (algebraMap km D.k))) ≫ w.left) ∧
        ∃ (W : A → Scheme.{u}) (w : ∀ a, W a ⟶ Xm) (r : ∀ a, Z a ⟶ W a),
          ∀ a, IsPullback (r a) (z a) (w a) q := by
  classical
  obtain ⟨L, W, w, r, hr⟩ := finite_closed_models D.k₀ D.k X₀ f A Z z hz
  obtain ⟨m, hm, hL⟩ := finite_field_eq D L
  refine ⟨m, hm, ?_⟩
  have hι := (FiniteField.exists_unique_subfield_of_closure D.p D.a D.q D.prime
    D.exponent_pos D.cardinality_eq D.k₀ D.card_base D.k m hm).choose_spec.2.2.2.2.2.2.choose_spec
  change (D.extensionSubfield m hm).subtype.comp (D.extensionEmbedding m hm) =
    algebraMap D.k₀ D.k at hι
  suffices h : ∀ (E : Subfield D.k) (ι : D.k₀ →+* E),
      L.1.toSubfield = E → E.subtype.comp ι = algebraMap D.k₀ D.k →
      let km := E
      let Xm := pullback f (Spec.map (CommRingCat.ofHom (ι)))
      let X := pullback f (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))
      ∃ (χ : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap km D.k)))).obj
          (Over.mk (pullback.snd f
            (Spec.map (CommRingCat.ofHom (ι)))) ) ≅
          Over.mk (pullback.snd f
            (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
        (q : X ⟶ Xm),
        IsPullback q (pullback.snd f _ ) (pullback.snd f _)
          (Spec.map (CommRingCat.ofHom (algebraMap km D.k))) ∧
        (∀ W : Over (Spec (.of km)), ∀ w : W ⟶ Over.mk (pullback.snd f _),
          ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap km D.k)))).map w ≫
            χ.hom).left ≫ q =
          pullback.fst W.hom (Spec.map (CommRingCat.ofHom (algebraMap km D.k))) ≫ w.left) ∧
        ∃ (W : A → Scheme.{u}) (w : ∀ a, W a ⟶ Xm) (r : ∀ a, Z a ⟶ W a),
          ∀ a, IsPullback (r a) (z a) (w a) q by
    exact h _ _ hL hι
  intro E ι hL hι
  subst E
  have hi : ι = algebraMap D.k₀ L.1 := by
    ext x
    exact DFunLike.congr_fun hι x
  subst ι
  let s := Spec.map (CommRingCat.ofHom (algebraMap L.1 D.k))
  let b := Spec.map (CommRingCat.ofHom (algebraMap D.k₀ L.1))
  let a := Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))
  have hba : s ≫ b = a := by
    simp [s, b, a, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← IsScalarTower.algebraMap_eq D.k₀ L.1 D.k]
  let q := pullback.map f a f b (𝟙 _) s (𝟙 _) (by simp) (by simp [hba])
  have hq := isPullback_pullback_map f a b s hba
  let χ : (Over.pullback s).obj (Over.mk (pullback.snd f b)) ≅
      Over.mk (pullback.snd f a) :=
    (Over.isoMk hq.isoPullback (IsPullback.isoPullback_hom_snd hq)).symm
  refine ⟨χ, q, hq, ?_, W, w, r, hr⟩
  intro V v
  rw [Over.comp_left, Category.assoc]
  change ((Over.pullback s).map v).left ≫ hq.isoPullback.inv ≫ q = _
  rw [IsPullback.isoPullback_inv_fst]
  exact pullback.lift_fst _ _ _

private theorem normalize_closed_models
    {S X : Scheme.{u}} (Y : Over S) (q : X ⟶ Y.left)
    [Surjective q] [Flat q] [QuasiCompact q]
    (n : ℕ) (Z : Fin (n + 1) → Scheme.{u})
    (z : ∀ a, Z a ⟶ X) (hz : ∀ a, IsClosedImmersion (z a))
    (hred : ∀ a, IsReduced (Z a)) (hzero : Surjective (z 0))
    (hfinish : IsEmpty (Z (Fin.last n)))
    (W : Fin (n + 1) → Over S) (w : ∀ a, W a ⟶ Y)
    (r : ∀ a, Z a ⟶ (W a).left)
    (hr : ∀ a, IsPullback (r a) (z a) (w a).left q) :
    ∃ (V : Fin (n + 1) → Over S) (v : ∀ a, V a ⟶ Y)
      (p : ∀ a, Z a ⟶ (V a).left),
      (∀ a, IsPullback (p a) (z a) (v a).left q) ∧
      ∃ h0 : V 0 = Over.mk (Y.left.nilradical.subschemeι ≫ Y.hom),
        v 0 = eqToHom h0 ≫ Over.homMk Y.left.nilradical.subschemeι (by rfl) ∧
        (n ≠ 0 → V (Fin.last n) = Over.mk (Scheme.emptyTo S)) := by
  classical
  let Q : MorphismProperty Scheme.{u} := @Surjective ⊓ @Flat ⊓ @QuasiCompact
  have hq : Q q := ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  have hrQ (a : Fin (n + 1)) : Q (r a) := Q.of_isPullback (hr a).flip hq
  have (a : Fin (n + 1)) : Surjective (r a) := (hrQ a).1.1
  have (a : Fin (n + 1)) : Flat (r a) := (hrQ a).1.2
  have (a : Fin (n + 1)) : IsReduced (W a).left := by
    have := hred a
    exact isReduced_of_flat_of_surjective (r a)
  let : MorphismProperty.DescendsAlong
      (@IsClosedImmersion : MorphismProperty Scheme.{u}) Q :=
    IsClosedImmersion.descendsAlong_surjective_inf_flat_inf_quasicompact
  have (a : Fin (n + 1)) : IsClosedImmersion (w a).left :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := @IsClosedImmersion)
      (hr a).flip hq (hz a)
  have hwzero : Function.Surjective (w 0).left := by
    intro y
    obtain ⟨x, rfl⟩ := q.surjective y
    obtain ⟨t, rfl⟩ := hzero.1 x
    exact ⟨r 0 t, congrArg (fun f ↦ f t) (hr 0).w⟩
  have hnil : Set.range Y.left.nilradical.subschemeι = Set.univ := by
    rw [Scheme.IdealSheafData.range_subschemeι, Y.left.support_nilradical]
    rfl
  obtain ⟨e₀, he₀⟩ := reduced_closed_iso Y.left.nilradical.subschemeι (w 0).left
    (hnil.trans (Set.range_eq_univ.mpr hwzero).symm)
  let E₀ : Over.mk (Y.left.nilradical.subschemeι ≫ Y.hom) ≅ W 0 :=
    Over.isoMk e₀ (by rw [← Over.w (w 0), ← Category.assoc, he₀]; rfl)
  have : IsEmpty (W (Fin.last n)).left :=
    ⟨fun y ↦ by obtain ⟨x, -⟩ := (r (Fin.last n)).surjective y; exact hfinish.false x⟩
  let Eₙ : Over.mk (Scheme.emptyTo S) ≅ W (Fin.last n) :=
    Over.isoMk (asIso (Scheme.emptyTo (W (Fin.last n)).left)) (Scheme.empty_ext _ _)
  let V (a : Fin (n + 1)) : Over S :=
    if a = 0 then Over.mk (Y.left.nilradical.subschemeι ≫ Y.hom)
    else if a = Fin.last n then Over.mk (Scheme.emptyTo S) else W a
  let E (a : Fin (n + 1)) : V a ≅ W a := by
    by_cases h0 : a = 0
    · subst a
      simpa only [V, if_pos rfl] using E₀
    · by_cases hn : a = Fin.last n
      · subst a
        simpa only [V, if_neg h0, ite_true] using Eₙ
      · simpa only [V, if_neg h0, if_neg hn] using Iso.refl (W a)
  let v (a : Fin (n + 1)) : V a ⟶ Y := (E a).hom ≫ w a
  let p (a : Fin (n + 1)) : Z a ⟶ (V a).left := r a ≫ (E a).inv.left
  refine ⟨V, v, p, ?_, by simp only [V, if_pos rfl], ?_, ?_⟩
  · intro a
    exact (hr a).of_iso (Iso.refl _) ((Over.forget S).mapIso (E a).symm)
      (Iso.refl _) (Iso.refl _) (by simp [p]) (by simp)
      (by simp [v]) (by simp)
  · ext1
    simpa [v, E, E₀, V] using he₀
  · intro hn
    have hl : Fin.last n ≠ (0 : Fin (n + 1)) := by
      intro h
      exact hn (congrArg Fin.val h)
    simp only [V, if_neg hl, ite_true]

private theorem filtration_of_closed_models
    {l k : Type u} [Field l] [Field k] [Algebra l k]
    (X : Over (Spec (.of k))) (Y : Over (Spec (.of l)))
    (q : X.left ⟶ Y.left)
    (hq : IsPullback q X.hom Y.hom
      (Spec.map (CommRingCat.ofHom (algebraMap l k))))
    (n : ℕ) (H : SmoothAffineFiltration
      (Over.mk (X.left.nilradical.subschemeι ≫ X.hom)) n)
    (W : Fin (n + 1) → Over (Spec (.of l)))
    (w : ∀ a, W a ⟶ Y)
    (r : ∀ a, (H.closed a).left ⟶ (W a).left)
    (hr : ∀ a, IsPullback (r a)
      ((H.intoAmbient a).left ≫ X.left.nilradical.subschemeι) (w a).left q)
    (hW0 : W 0 = Over.mk (Y.left.nilradical.subschemeι ≫ Y.hom))
    (hw0 : w 0 = eqToHom hW0 ≫ Over.homMk Y.left.nilradical.subschemeι (by rfl))
    (hWn : n ≠ 0 → W (Fin.last n) = Over.mk (Scheme.emptyTo (Spec (.of l)))) :
    ∃ M : SmoothAffineFiltration
        (Over.mk (Y.left.nilradical.subschemeι ≫ Y.hom)) n,
      (n ≠ 0 → M.closed (Fin.last n) = Over.mk (Scheme.emptyTo (Spec (.of l)))) ∧
      ∀ a : Fin n, M.dimension a = H.dimension a ∧
        ∃ e : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap l k)))).obj
            (M.piece a) ≅ H.piece a,
          e.hom.left ≫ (H.pieceInclusion a ≫ H.intoAmbient a.castSucc).left ≫
              X.left.nilradical.subschemeι ≫ q =
            pullback.fst (M.piece a).hom
              (Spec.map (CommRingCat.ofHom (algebraMap l k))) ≫
              (M.pieceInclusion a ≫ M.intoAmbient a.castSucc ≫
                Over.homMk Y.left.nilradical.subschemeι (by rfl)).left := by
  classical
  let s := Spec.map (CommRingCat.ofHom (algebraMap l k))
  let Q : MorphismProperty Scheme.{u} := @Surjective ⊓ @Flat ⊓ @QuasiCompact
  have hs : Q s := surjective_inf_flat_inf_quasiCompact_Spec_map_algebraMap l k
  have hqQ : Q q := Q.of_isPullback hq.flip hs
  have : Surjective q := hqQ.1.1
  have : Flat q := hqQ.1.2
  have hQ (a : Fin (n + 1)) : Q (r a) := Q.of_isPullback (hr a).flip hqQ
  have (a : Fin (n + 1)) : Surjective (r a) := (hQ a).1.1
  have (a : Fin (n + 1)) : Flat (r a) := (hQ a).1.2
  have (a : Fin (n + 1)) : IsReduced (W a).left := by
    have := H.reduced a
    exact isReduced_of_flat_of_surjective (r a)
  let : MorphismProperty.DescendsAlong
      (@IsClosedImmersion : MorphismProperty Scheme.{u}) Q :=
    IsClosedImmersion.descendsAlong_surjective_inf_flat_inf_quasicompact
  have (a : Fin (n + 1)) : IsClosedImmersion (w a).left := by
    have := closed_ambient H a
    exact MorphismProperty.of_isPullback_of_descendsAlong (P := @IsClosedImmersion)
      (hr a).flip hqQ inferInstance
  have hchain (a : Fin n) : Set.range (w a.succ).left ⊆ Set.range (w a.castSucc).left := by
    rintro _ ⟨y, rfl⟩
    obtain ⟨x, rfl⟩ := (r a.succ).surjective y
    have h := congrArg (fun f ↦ f x) (hr a.succ).w
    simp only [Scheme.Hom.comp_apply] at h
    rw [h]
    refine ⟨r a.castSucc ((H.inclusion a).left x), ?_⟩
    have he := congrArg Over.Hom.left (H.intoAmbient_succ a)
    have he := congrArg (fun f ↦ f x) he
    simp only [Over.comp_left, Scheme.Hom.comp_apply] at he
    simpa only [Scheme.Hom.comp_apply, he] using
      congrArg (fun f ↦ f ((H.inclusion a).left x)) (hr a.castSucc).w
  choose i hi _ using fun a : Fin n ↦
    IsClosedImmersion.existsUnique_fac_of_range_subset_range
      (w a.castSucc).left (w a.succ).left (hchain a)
  let ι (a : Fin n) : W a.succ ⟶ W a.castSucc := Over.homMk (i a) (by
    rw [← Over.w (w a.castSucc), ← Category.assoc, hi, Over.w])
  have hι (a : Fin n) : ι a ≫ w a.castSucc = w a.succ := by
    ext1
    exact hi a
  have (a : Fin n) : IsClosedImmersion (ι a).left := by
    have : IsClosedImmersion ((ι a).left ≫ (w a.castSucc).left) := by
      change IsClosedImmersion (i a ≫ (w a.castSucc).left)
      rw [hi]
      infer_instance
    exact IsClosedImmersion.of_comp _ (w a.castSucc).left
  let j (a : Fin (n + 1)) : W a ⟶ Over.mk
      (Y.left.nilradical.subschemeι ≫ Y.hom) :=
    Over.homMk (w a).left.liftNilradical (by simp)
  have hj (a : Fin (n + 1)) : j a ≫
      Over.homMk Y.left.nilradical.subschemeι (by rfl) = w a := by
    ext1
    exact Scheme.Hom.liftNilradical_subschemeι _
  let O (a : Fin n) := (ι a).left.openComplement
  let V (a : Fin n) : Over (Spec (.of l)) := Over.mk ((O a).ι ≫ (W a.castSucc).hom)
  let v (a : Fin n) : V a ⟶ W a.castSucc := Over.homMk (O a).ι (by rfl)
  have (a : Fin n) : IsOpenImmersion (v a).left :=
    inferInstanceAs (IsOpenImmersion (O a).ι)
  have hrv (a : Fin n) : Set.range (v a).left = (Set.range (ι a).left)ᶜ := by
    exact Scheme.Opens.range_ι (O a)
  have hri (a : Fin n) : IsPullback (H.inclusion a).left (r a.succ)
      (r a.castSucc) (ι a).left := by
    apply IsPullback.of_right (t := (hr a.castSucc).flip)
    · rw [← Over.comp_left, hι]
      simpa only [H.intoAmbient_succ, Over.comp_left, Category.assoc] using
        (hr a.succ).flip
    · apply (cancel_mono (w a.castSucc).left).mp
      rw [Category.assoc, Category.assoc, ← Over.comp_left, hι,
        (hr a.succ).w, (hr a.castSucc).w]
      simp only [H.intoAmbient_succ, Over.comp_left, Category.assoc]
  have hcomp (a : Fin n) : (r a.castSucc) ⁻¹' Set.range (ι a).left =
      Set.range (H.inclusion a).left := by
    exact (Scheme.range_snd_of_isPullback (hri a).flip).symm
  let p (a : Fin n) : (H.piece a).left ⟶ (V a).left :=
    IsOpenImmersion.lift (v a).left ((H.pieceInclusion a).left ≫ r a.castSucc) (by
      rw [hrv]
      rintro _ ⟨x, rfl⟩
      change r a.castSucc ((H.pieceInclusion a).left x) ∉ _
      rw [← Set.mem_preimage, hcomp]
      have h := Set.mem_range_self (f := (H.pieceInclusion a).left) x
      rw [H.range_piece a] at h
      exact h)
  have hp (a : Fin n) : p a ≫ (v a).left =
      (H.pieceInclusion a).left ≫ r a.castSucc := IsOpenImmersion.lift_fac _ _ _
  have hpB (a : Fin n) : IsPullback (p a) (H.pieceInclusion a).left
      (v a).left (r a.castSucc) := by
    have := H.open_piece a
    apply IsOpenImmersion.isPullback _ _ _ _ (hp a).symm
    apply TopologicalSpace.Opens.ext
    change (r a.castSucc) ⁻¹' Set.range (v a).left = Set.range (H.pieceInclusion a).left
    rw [hrv, Set.preimage_compl, hcomp, H.range_piece]
  have hpfield (a : Fin n) : IsPullback (p a) (H.piece a).hom (V a).hom s := by
    have hclosed : IsPullback (r a.castSucc) (H.closed a.castSucc).hom
        (W a.castSucc).hom s := by
      have h := (hr a.castSucc).paste_vert hq
      simpa only [Category.assoc, ← Over.w (H.intoAmbient a.castSucc),
        ← Over.w (w a.castSucc), Over.mk_left, Over.mk_hom] using h
    simpa only [V, ← Over.comp_left, Over.w] using (hpB a).paste_vert hclosed
  let e (a : Fin n) : (Over.pullback s).obj (V a) ≅ H.piece a :=
    (Over.isoMk (hpfield a).isoPullback (hpfield a).isoPullback_hom_snd).symm
  have hVsm (a : Fin n) : SmoothOfRelativeDimension (H.dimension a) (V a).hom := by
    exact of_isPullback_Spec_map_algebraMap (@SmoothOfRelativeDimension (H.dimension a))
      (hpfield a) (H.smooth_piece a)
  have hVaff (a : Fin n) : IsAffine (V a).left := by
    let : MorphismProperty.DescendsAlong
        (@IsAffineHom : MorphismProperty Scheme.{u}) Q :=
      IsAffineHom.descendsAlong_surjective_inf_flat_inf_quasicompact
    have := H.affine_piece a
    have : IsAffineHom (H.piece a).hom := inferInstance
    have : IsAffineHom (V a).hom :=
      MorphismProperty.of_isPullback_of_descendsAlong (P := @IsAffineHom)
        (hpfield a).flip hs inferInstance
    exact isAffine_of_isAffineHom (V a).hom
  have hVconn (a : Fin n) : GeometricallyConnected (V a).hom := by
    let : (V a).left.Over (Spec (.of l)) := ⟨(V a).hom⟩
    apply (geometricallyConnected_iff_of_fieldExtension (k' := k) (V a).left).mpr
    have he : IsPullback (e a).hom.left (pullback.snd (V a).hom s)
        (H.piece a).hom (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨by simp⟩
    exact MorphismProperty.of_isPullback (P := @GeometricallyConnected) he
      (H.connected_piece a)
  have hVne (a : Fin n) : Nonempty (V a).left :=
    (H.nonempty_piece a).map (p a)
  have hVred (a : Fin n) : IsReduced (V a).left := by
    change IsReduced (O a).toScheme
    infer_instance
  refine ⟨{
    closed := W, reduced := fun _ ↦ inferInstance, start := hW0,
    finish := ?_, inclusion := ι, intoAmbient := j,
    closed_inclusion := fun _ ↦ inferInstance, intoAmbient_zero := ?_,
    intoAmbient_succ := ?_, piece := V, pieceInclusion := v,
    open_piece := fun a ↦ inferInstanceAs (IsOpenImmersion (O a).ι),
    range_piece := hrv, nonempty_piece := hVne, reduced_piece := hVred,
    affine_piece := hVaff, connected_piece := hVconn,
    dimension := H.dimension, smooth_piece := hVsm }, hWn, ?_⟩
  · have : IsEmpty (H.closed (Fin.last n)).left := H.finish
    exact ⟨fun y ↦ by obtain ⟨x, -⟩ := (r (Fin.last n)).surjective y; exact isEmptyElim x⟩
  · apply (cancel_mono (Over.homMk Y.left.nilradical.subschemeι (by rfl))).mp
    rw [hj, hw0]
  · intro a
    apply (cancel_mono (Over.homMk Y.left.nilradical.subschemeι (by rfl))).mp
    rw [Category.assoc, hj, hj, hι]
  · intro a
    refine ⟨rfl, e a, ?_⟩
    dsimp only
    simp only [Over.comp_left, Category.assoc]
    rw [← Category.assoc _ X.left.nilradical.subschemeι q,
      ← (hr a.castSucc).w]
    rw [← Category.assoc _ (r a.castSucc), ← hp]
    change (e a).hom.left ≫ p a ≫ (v a).left ≫ (w a.castSucc).left = _
    have he : (e a).hom.left ≫ p a = pullback.fst (V a).hom s :=
      (hpfield a).isoPullback_inv_fst
    rw [← Category.assoc, he]
    simp only [← Over.comp_left, hj]
    rfl


/-- A given finite geometric filtration, including its affine smooth complements, has a
model over a single finite subfield. Its dimensions and geometric pieces are preserved.
This is a descent assertion about an already constructed filtration; no partition or
existence of a geometric filtration is assumed in its conclusion.

Source: Stacks Project, Limits, Tag 01ZM (objects, maps and equalities of finite
presentation), Varieties, Tag 0388 (descent of quasi-compact opens), Descent, Tag 02L5
(affine morphisms), and the simultaneous descent step of blueprint
`thm-zl-real-mixed-by-curves`, paragraphs 6--7.
(blueprint: lem-zl-smooth-affine-filtration-finite-field-descent).

Proof: Apply finite-presentation object descent to the finitely many closed immersions
into the geometric ambient scheme, over the inverse system of its prescribed finite-field
base changes. Directedness puts their models at one stage. Their projections from the
geometric closed terms are faithfully flat, so these models are reduced closed subschemes.
The first model maps onto the entire ambient space and hence is its reduction, by
uniqueness of a reduced closed subscheme with prescribed image. The final model is empty.
Replace these endpoint models by the literal reduction and, in positive length, by the
canonical empty scheme, transporting the cartesian squares along the unique isomorphisms.
For a length-zero chain keep the empty reduction as the first and last term.

Surjectivity of the projections reflects containment between the closed images. Reducedness
then gives the unique chain inclusions and their commuting triangles. Take their open
complements; their base changes have exactly the images of the prescribed geometric
pieces, so the open-immersion pullback criterion identifies these pieces. Affineness and
smoothness of their specified relative dimensions descend faithfully flatly, geometric
connectedness is tested after field extension, and their geometric points give nonemptiness.
The finite intermediate field has cardinality q^m for its positive degree m. Uniqueness of
the finite subfield in the fixed closure identifies it with extensionSubfield m; its
embedding is the specified extensionEmbedding because both inclusions into the closure
agree. Finally pullback pasting supplies the ambient and piece isomorphisms. Their equations
are checked against both projections of the ambient cartesian square.
-/
theorem exists_smooth_affine_filtration_finite_field_model
    (D : FiniteFieldDatum.{u}) (X₀ : Scheme.{u})
    (a₀ : X₀ ⟶ Spec (CommRingCat.of D.k₀))
    [IsSeparated a₀] [LocallyOfFiniteType (Over.mk a₀).hom]
    [QuasiCompact (Over.mk a₀).hom]
    (n : ℕ)
    (H : SmoothAffineFiltration
      (Over.mk ((D.geometricFiber (Over.mk a₀)).left.nilradical.subschemeι ≫
        (D.geometricFiber (Over.mk a₀)).hom)) n) :
    ∃ (m : ℕ) (hm : 1 ≤ m),
      let km := D.extensionSubfield m hm
      let Sm := Spec (CommRingCat.of km)
      let Xm := (Over.pullback
        (Spec.map (CommRingCat.ofHom (D.extensionEmbedding m hm)))).obj (Over.mk a₀)
      let X := D.geometricFiber (Over.mk a₀)
      let BC := Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap km D.k)))
      ∃ (χ : BC.obj Xm ≅ X)
        (M : SmoothAffineFiltration
          (Over.mk (Xm.left.nilradical.subschemeι ≫ Xm.hom)) n),
        (n ≠ 0 → M.closed (Fin.last n) = Over.mk (Scheme.emptyTo Sm)) ∧
        ∀ a : Fin n, M.dimension a = H.dimension a ∧
          ∃ e : BC.obj (M.piece a) ≅ H.piece a,
            (BC.map (M.pieceInclusion a ≫ M.intoAmbient a.castSucc ≫
              Over.homMk Xm.left.nilradical.subschemeι (by simp)) ≫ χ.hom).left =
              e.hom.left ≫ (H.pieceInclusion a ≫ H.intoAmbient a.castSucc).left ≫
                X.left.nilradical.subschemeι := by
  classical
  have : LocallyOfFiniteType a₀ := inferInstanceAs
    (LocallyOfFiniteType (Over.mk a₀).hom)
  have : QuasiCompact a₀ := inferInstanceAs (QuasiCompact (Over.mk a₀).hom)
  let X := D.geometricFiber (Over.mk a₀)
  let z (a : Fin (n + 1)) := (H.intoAmbient a).left ≫ X.left.nilradical.subschemeι
  have hz (a : Fin (n + 1)) : IsClosedImmersion (z a) := by
    have := closed_ambient H a
    exact inferInstanceAs (IsClosedImmersion
      ((H.intoAmbient a).left ≫ X.left.nilradical.subschemeι))
  obtain ⟨m, hm, χ, q, hq, hχ, W, w, r, hr⟩ :=
    finite_named_closed_models D X₀ a₀ (Fin (n + 1))
      (fun a ↦ (H.closed a).left) z hz
  let km := D.extensionSubfield m hm
  let Xm := (Over.pullback
    (Spec.map (CommRingCat.ofHom (D.extensionEmbedding m hm)))).obj (Over.mk a₀)
  let s := Spec.map (CommRingCat.ofHom (algebraMap km D.k))
  let Q : MorphismProperty Scheme.{u} := @Surjective ⊓ @Flat ⊓ @QuasiCompact
  have hs : Q s := surjective_inf_flat_inf_quasiCompact_Spec_map_algebraMap km D.k
  have hqQ : Q q := Q.of_isPullback hq.flip hs
  have : Surjective q := hqQ.1.1
  have : Flat q := hqQ.1.2
  have : QuasiCompact q := hqQ.2
  let V (a : Fin (n + 1)) : Over (Spec (.of km)) :=
    Over.mk (w a ≫ Xm.hom)
  let v (a : Fin (n + 1)) : V a ⟶ Xm := Over.homMk (w a) (by rfl)
  have hz0 : Surjective (z 0) := by
    dsimp only [z]
    rw [H.intoAmbient_zero]
    have : Surjective X.left.nilradical.subschemeι := by
      constructor
      apply Set.range_eq_univ.mp
      rw [Scheme.IdealSheafData.range_subschemeι, X.left.support_nilradical]
      rfl
    infer_instance
  obtain ⟨V', v', r', hr', h0, hv0, hvn⟩ := normalize_closed_models Xm q n
    (fun a ↦ (H.closed a).left) z hz H.reduced hz0 H.finish V v r hr
  obtain ⟨M, hMn, hM⟩ := filtration_of_closed_models X Xm q hq n H
    V' v' r' hr' h0 hv0 hvn
  refine ⟨m, hm, χ, M, hMn, ?_⟩
  intro a
  obtain ⟨hd, e, he⟩ := hM a
  refine ⟨hd, e, ?_⟩
  apply hq.hom_ext
  · rw [Category.assoc, hχ]
    exact he.symm
  · change ((Over.pullback s).map
        (M.pieceInclusion a ≫ M.intoAmbient a.castSucc ≫
          Over.homMk Xm.left.nilradical.subschemeι (by rfl)) ≫ χ.hom).left ≫ X.hom = _
    have hleft := Over.w ((Over.pullback s).map
      (M.pieceInclusion a ≫ M.intoAmbient a.castSucc ≫
        Over.homMk Xm.left.nilradical.subschemeι (by rfl)) ≫ χ.hom)
    have hright := Over.w (e.hom ≫ H.pieceInclusion a ≫ H.intoAmbient a.castSucc)
    exact hleft.trans (by
      simpa only [Over.comp_left, Category.assoc, Over.mk_hom,
        FiniteFieldDatum.geometricFiber, Over.pullback_obj_hom] using hright.symm)

end WeilConjectures
