/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y9
-/
module

public import Sheaf.CategoryTheory.FiniteFilteredDerivedPresentation
import Sheaf.CategoryTheory.FilteredPresentationTruncationData

/-!
# Universal pure-grade spans in any finite filtered presentation

Source: Varshavsky, §§5.1.1(b)--(e), 5.1.2(a)--(c), and the unary cutoff
argument of Lemma 5.1.4(i), pp.39--41.
(blueprint: lem-trf-filtered-presentation-truncation).
-/

@[expose] public section

set_option autoImplicit false
universe w v u v' u'

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject

namespace CategoryTheory.FiniteFilteredDerived

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  {D : Type u'} [Category.{v'} D] [HasShift D ℤ] [Preadditive D] [HasZeroObject D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [IsTriangulated D]

private theorem localization_zero {J K : Type*} [Category* J] [Category* K]
    (L : J ⥤ K) (W : MorphismProperty J) [L.IsLocalization W]
    (Z : J) (hZ : IsZero Z) : IsZero (L.obj Z) := by
  classical
  let E := Localization.fullyFaithfulWhiskeringLeft L W K
  let t : L ⋙ (Functor.const K).obj (L.obj Z) ⟶ L ⋙ 𝟭 K :=
    { app := fun X ↦ L.map (hZ.to_ X)
      naturality := fun X Y f ↦ by
        dsimp
        rw [Category.id_comp, ← L.map_comp]
        congr 1
        exact hZ.eq_of_src _ _ }
  let a : (Functor.const K).obj (L.obj Z) ⟶ 𝟭 K := E.preimage t
  have ha (X : J) : a.app (L.obj X) = L.map (hZ.to_ X) :=
    congrArg (fun s ↦ s.app X) (E.map_preimage t)
  have haZ : a.app (L.obj Z) = 𝟙 (L.obj Z) := by
    rw [ha, show hZ.to_ Z = 𝟙 Z from hZ.eq_of_src _ _, L.map_id]
  let s : L ⋙ 𝟭 K ⟶ L ⋙ (Functor.const K).obj (L.obj Z) :=
    { app := fun X ↦ L.map (hZ.from_ X)
      naturality := fun X Y f ↦ by
        dsimp
        rw [Category.comp_id, ← L.map_comp]
        congr 1
        exact hZ.eq_of_tgt _ _ }
  let b : 𝟭 K ⟶ (Functor.const K).obj (L.obj Z) := E.preimage s
  have hb (X : J) : b.app (L.obj X) = L.map (hZ.from_ X) :=
    congrArg (fun t ↦ t.app X) (E.map_preimage s)
  have hbZ : b.app (L.obj Z) = 𝟙 (L.obj Z) := by
    rw [hb, show hZ.from_ Z = 𝟙 Z from hZ.eq_of_tgt _ _, L.map_id]
  constructor
  · intro Y
    refine ⟨⟨⟨a.app Y⟩, fun f ↦ ?_⟩⟩
    have h := a.naturality f
    change 𝟙 _ ≫ a.app Y = a.app (L.obj Z) ≫ f at h
    rw [Category.id_comp] at h
    rw [haZ] at h
    exact (h.trans (Category.id_comp f)).symm
  · intro Y
    refine ⟨⟨⟨b.app Y⟩, fun f ↦ ?_⟩⟩
    have h := b.naturality f
    change f ≫ b.app (L.obj Z) = b.app Y ≫ 𝟙 _ at h
    rw [Category.comp_id] at h
    rw [hbZ, Category.comp_id] at h
    exact h

omit [HasDerivedCategory.{w} C] in
private theorem filtered_hom_ext {K L : FilteredObject (CochainComplex C ℤ)}
    (f g : K ⟶ L) (h : f.hom = g.hom) : f = g := by
  cases f
  cases g
  cases h
  rfl

omit [IsTriangulated D] in
private theorem zero_of_grades (P : Presentation (C := C) (D := D))
    (M : D) (hM : ∀ p : ℤ, IsZero ((P.gr p).obj M)) : IsZero M := by
  classical
  let Z : Complexes C :=
    ⟨⟨(0 : CochainComplex C ℤ), ⟨fun _ ↦ ⊥, fun _ ↦ le_rfl⟩⟩, ⟨⟨0, 0, by
      exact (Subobject.subsingleton_of_isZero (isZero_zero (CochainComplex C ℤ))).elim _ _, rfl⟩,
      ⟨0, inferInstance⟩⟩⟩
  have hZ : IsZero Z := by
    constructor
    · intro K
      refine ⟨⟨⟨⟨⟨0, fun p ↦ ⟨0, by simp⟩⟩⟩⟩, fun f ↦ ?_⟩⟩
      apply ObjectProperty.hom_ext
      have hh : f.hom.hom = 0 := (isZero_zero (CochainComplex C ℤ)).eq_of_src _ _
      exact filtered_hom_ext _ _ hh
    · intro K
      refine ⟨⟨⟨⟨⟨0, fun p ↦ ⟨0, by simp⟩⟩⟩⟩, fun f ↦ ?_⟩⟩
      apply ObjectProperty.hom_ext
      have hh : f.hom.hom = 0 := (isZero_zero (CochainComplex C ℤ)).eq_of_tgt _ _
      exact filtered_hom_ext _ _ hh
  have hZg (p : ℤ) : IsZero (Z.obj.filtration.gradedPiece p) := by
    have hs : IsZero (Z.obj.filtration.F p : CochainComplex C ℤ) :=
      IsZero.of_mono (Z.obj.filtration.F p).arrow (isZero_zero _)
    exact IsZero.of_epi (cokernel.π (Subobject.ofLE _ _
      (Z.obj.filtration.F_succ_le p))) hs
  have := Localization.essSurj P.Q (gradedQuasiIso C)
  let K := P.Q.objPreimage M
  let e : P.Q.obj K ≅ M := P.Q.objObjPreimageIso M
  let f : K ⟶ Z := ⟨⟨0, fun p ↦ ⟨0, by simp⟩⟩⟩
  have hf : gradedQuasiIso C f := by
    intro p
    apply (DerivedCategory.isIso_Q_map_iff_quasiIso C _).1
    have hK : IsZero ((P.gr p).obj (P.Q.obj K)) := (hM p).of_iso ((P.gr p).mapIso e)
    have hK' : IsZero (DerivedCategory.Q.obj (K.obj.filtration.gradedPiece p)) :=
      (DerivedCategory.Plus.ι.map_isZero hK).of_iso (P.grComplex p K).symm
    have hZ' := DerivedCategory.Q.map_isZero (hZg p)
    exact hK'.isIso hZ' _
  have hi : IsIso (P.Q.map f) := Localization.inverts P.Q (gradedQuasiIso C) f hf
  exact ((localization_zero P.Q (gradedQuasiIso C) Z hZ).of_iso
    (asIso (P.Q.map f))).of_iso e.symm

omit [IsTriangulated D] in
private theorem iso_of_grades (P : Presentation (C := C) (D := D))
    {X Y : D} (f : X ⟶ Y) (h : ∀ p : ℤ, IsIso ((P.gr p).map f)) : IsIso f := by
  obtain ⟨Z, g, d, hd⟩ := distinguished_cocone_triangle f
  let S := Triangle.mk f g d
  have hZ : IsZero Z := zero_of_grades P Z (fun p ↦
    (Triangle.isZero₃_iff_isIso₁ ((P.gr p).mapTriangle.obj S)
      ((P.gr p).map_distinguished S hd)).2 (h p))
  exact (Triangle.isZero₃_iff_isIso₁ S hd).1 hZ

omit [IsTriangulated D] in
private theorem cutoff_triangle (P : Presentation (C := C) (D := D))
    (T : P.Truncation) (r : ℤ) (M : D) :
    ∃ d, Triangle.mk ((T.inclusion r).app M) ((T.quotient r).app M) d ∈ distTriang D := by
  obtain ⟨Z, g, d, hd⟩ := distinguished_cocone_triangle ((T.inclusion r).app M)
  let S := Triangle.mk ((T.inclusion r).app M) g d
  have hZ (q : ℤ) (hq : r ≤ q) : IsZero ((P.gr q).obj Z) :=
    (Triangle.isZero₃_iff_isIso₁ ((P.gr q).mapTriangle.obj S)
      ((P.gr q).map_distinguished S hd)).2 (T.high_grade r q M hq)
  obtain ⟨k, hk⟩ := (T.low_universal r M Z hZ).2 g
  change (T.quotient r).app M ≫ k = g at hk
  have hi : IsIso k := iso_of_grades P k (by
    intro q
    by_cases hq : q < r
    · have h₁ := T.low_grade r q M hq
      have h₂ : IsIso ((P.gr q).map g) :=
        (Triangle.isZero₁_iff_isIso₂ ((P.gr q).mapTriangle.obj S)
          ((P.gr q).map_distinguished S hd)).1 (T.high_support r q M hq)
      have h₃ : IsIso ((P.gr q).map ((T.quotient r).app M) ≫ (P.gr q).map k) := by
        rw [← Functor.map_comp, hk]
        exact h₂
      exact IsIso.of_isIso_comp_left ((P.gr q).map ((T.quotient r).app M)) _
    · exact (T.low_support r q M (by omega)).isIso (hZ q (by omega)) _)
  refine ⟨k ≫ d, isomorphic_distinguished S hd _ ?_⟩
  refine Triangle.isoMk _ S (Iso.refl _) (Iso.refl _) (asIso k) ?_ ?_ ?_
  · simp [S]
  · simpa [S] using hk
  · simp [S]

omit [HasDerivedCategory.{w} C] in
private theorem ofLE_iso_eq {A : CochainComplex C ℤ} {X Y : Subobject A} (h : X ≤ Y)
    (hEq : X = Y) : IsIso (Subobject.ofLE X Y h) := by
  subst Y
  rw [Subobject.ofLE_refl]
  infer_instance

omit [IsTriangulated D] in
private theorem finite_support (P : Presentation (C := C) (D := D)) (M : D) :
    ∃ a b : ℤ, Supported P a b M := by
  classical
  have := Localization.essSurj P.Q (gradedQuasiIso C)
  let K := P.Q.objPreimage M
  let e : P.Q.obj K ≅ M := P.Q.objObjPreimageIso M
  obtain ⟨a, b, ha, hb⟩ := K.property.1
  refine ⟨a, b, fun p hp ↦ ?_⟩
  have hz : IsZero (K.obj.filtration.gradedPiece p) := by
    rcases hp with hp | hp
    · have h₁ : K.obj.filtration.F p = ⊤ :=
        top_unique (ha ▸ K.obj.filtration.antitone (by omega))
      have h₂ : K.obj.filtration.F (p + 1) = ⊤ :=
        top_unique (ha ▸ K.obj.filtration.antitone (by omega))
      change IsZero (cokernel (Subobject.ofLE _ _ _))
      have hi : IsIso (Subobject.ofLE (K.obj.filtration.F (p + 1))
          (K.obj.filtration.F p) (K.obj.filtration.F_succ_le p)) := by
        exact ofLE_iso_eq _ (h₂.trans h₁.symm)
      exact isZero_cokernel_of_epi _
    · have h : K.obj.filtration.F p = ⊥ :=
        le_bot_iff.mp (hb ▸ K.obj.filtration.antitone (by omega))
      have hs : IsZero (K.obj.filtration.F p : CochainComplex C ℤ) := by
        rw [h]
        exact (isZero_zero _).of_iso Subobject.botCoeIsoZero
      exact IsZero.of_epi (cokernel.π (Subobject.ofLE _ _
        (K.obj.filtration.F_succ_le p))) hs
  have hz' : IsZero ((P.gr p).obj (P.Q.obj K)) := by
    apply IsZero.of_full_of_faithful_of_isZero DerivedCategory.Plus.ι
    exact (DerivedCategory.Q.map_isZero hz).of_iso (P.grComplex p K)
  exact hz'.of_iso (((P.gr p).mapIso e).symm)

/-- The universal span `M → t≤p M ← t[p,p] M`. The low quotient and the
high inclusion have their universal Hom properties, so the objects and maps are
determined up to their unique compatible isomorphisms. An exact functor preserving
finite intervals makes both arrows invertible after taking grade `p`.
Source: Varshavsky 5.1.1(b)--(e), 5.1.2(b,c), Lemma 5.1.4(i).
(blueprint: lem-trf-filtered-presentation-truncation). -/
structure Presentation.GradedSpan (P : Presentation (C := C) (D := D)) (p : ℤ) where
  cut : D ⥤ D
  piece : D ⥤ D
  quotient : 𝟭 D ⟶ cut
  inclusion : piece ⟶ cut
  cut_support : ∀ (M : D) (q : ℤ), p < q → IsZero ((P.gr q).obj (cut.obj M))
  piece_support : ∀ (M : D) (q : ℤ), q ≠ p → IsZero ((P.gr q).obj (piece.obj M))
  cut_pure : ∀ M : D, (∀ q : ℤ, q ≠ p → IsZero ((P.gr q).obj M)) →
    ∀ q : ℤ, q ≠ p → IsZero ((P.gr q).obj (cut.obj M))
  quotient_universal : ∀ (M R : D),
    (∀ q : ℤ, p < q → IsZero ((P.gr q).obj R)) →
    Function.Bijective (fun f : cut.obj M ⟶ R ↦ quotient.app M ≫ f)
  inclusion_universal : ∀ (M L : D),
    (∀ q : ℤ, q < p → IsZero ((P.gr q).obj L)) →
    Function.Bijective (fun f : L ⟶ piece.obj M ↦ f ≫ inclusion.app M)
  map_iso : ∀ {B : Type u} [Category.{v} B] [Abelian B] [HasDerivedCategory.{w} B]
    {E : Type u'} [Category.{v'} E] [HasShift E ℤ] [Preadditive E] [HasZeroObject E]
    [∀ n : ℤ, (shiftFunctor E n).Additive] [Pretriangulated E] [IsTriangulated E]
    (R : Presentation (C := B) (D := E)) (H : D ⥤ E) [H.CommShift ℤ]
    [H.IsTriangulated],
    (∀ (a b : ℤ) (M : D), Supported P a b M → Supported R a b (H.obj M)) →
    ∀ M : D, IsIso ((R.gr p).map (H.map (quotient.app M))) ∧
      IsIso ((R.gr p).map (H.map (inclusion.app M)))

omit [IsTriangulated D] in
private theorem high_preserved {B : Type u} [Category.{v} B] [Abelian B]
    [HasDerivedCategory.{w} B] {E : Type u'} [Category.{v'} E] [HasShift E ℤ]
    [Preadditive E] [HasZeroObject E] [∀ n : ℤ, (shiftFunctor E n).Additive]
    [Pretriangulated E] [IsTriangulated E]
    (P : Presentation (C := C) (D := D)) (R : Presentation (C := B) (D := E))
    (H : D ⥤ E)
    (hH : ∀ (a b : ℤ) (M : D), Supported P a b M → Supported R a b (H.obj M))
    (r : ℤ) (M : D) (hM : ∀ q : ℤ, q < r → IsZero ((P.gr q).obj M)) :
    ∀ q : ℤ, q < r → IsZero ((R.gr q).obj (H.obj M)) := by
  obtain ⟨a, b, h⟩ := finite_support P M
  have hs : Supported P r b M := fun q hq ↦ hq.elim (hM q) (fun hq ↦ h q (.inr hq))
  exact fun q hq ↦ hH r b M hs q (.inl hq)

omit [IsTriangulated D] in
private theorem low_preserved {B : Type u} [Category.{v} B] [Abelian B]
    [HasDerivedCategory.{w} B] {E : Type u'} [Category.{v'} E] [HasShift E ℤ]
    [Preadditive E] [HasZeroObject E] [∀ n : ℤ, (shiftFunctor E n).Additive]
    [Pretriangulated E] [IsTriangulated E]
    (P : Presentation (C := C) (D := D)) (R : Presentation (C := B) (D := E))
    (H : D ⥤ E)
    (hH : ∀ (a b : ℤ) (M : D), Supported P a b M → Supported R a b (H.obj M))
    (r : ℤ) (M : D) (hM : ∀ q : ℤ, r ≤ q → IsZero ((P.gr q).obj M)) :
    ∀ q : ℤ, r ≤ q → IsZero ((R.gr q).obj (H.obj M)) := by
  obtain ⟨a, b, h⟩ := finite_support P M
  have hs : Supported P a (r - 1) M := fun q hq ↦
    hq.elim (fun hq ↦ h q (.inl hq)) (fun hq ↦ hM q (by omega))
  exact fun q hq ↦ hH a (r - 1) M hs q (.inr (by omega))

omit [IsTriangulated D] in
/-- Universal cutoff spans and joint detection of zero objects by the grades.
Source: Varshavsky 5.1.1(b)--(e), 5.1.2(a)--(c), Lemma 5.1.4(i).
(blueprint: lem-trf-filtered-presentation-truncation).

Proof: obtain the universal high and low truncations in the supplied presentation.
Set cut = low(p+1) and piece = cut followed by high(p), with the canonical quotient
and inclusion. The grade formulas show cut has no grades above p and piece is
pure. For a pure input the remaining grades of cut vanish as well. The universal
Hom bijections are those of low and high. Finite support of any object follows
from a representative's uniform filtration bounds. Thus an interval-preserving
functor preserves high and low support, using a finite bound on the other side.
Apply grade p after the exact functor to the cutoff triangles: the discarded
vertex is zero, so the zero-cone criterion proves both grade arrows invertible.
Finally represent an object whose grades all vanish by K. Its map to the zero
complex is a graded quasi-isomorphism and hence inverted by localization. A
localization preserves a zero object by lifting its unique incoming and outgoing
natural transformations, so the represented object is zero.
-/
theorem Presentation.truncationSpans (P : Presentation (C := C) (D := D)) :
    (∀ p : ℤ, Nonempty (P.GradedSpan p)) ∧
    (∀ M : D, (∀ p : ℤ, IsZero ((P.gr p).obj M)) → IsZero M) := by
  classical
  obtain ⟨T⟩ := P.truncationData
  refine ⟨fun p ↦ ⟨?_⟩, zero_of_grades P⟩
  refine
    { cut := T.low (p + 1)
      piece := T.low (p + 1) ⋙ T.high p
      quotient := T.quotient (p + 1)
      inclusion := Functor.whiskerLeft (T.low (p + 1)) (T.inclusion p)
      cut_support := fun M q hq ↦ T.low_support (p + 1) q M (by omega)
      piece_support := ?_
      cut_pure := ?_
      quotient_universal := ?_
      inclusion_universal := ?_
      map_iso := ?_ }
  · intro M q hq
    by_cases h : q < p
    · exact T.high_support p q _ h
    · have hi := T.high_grade p q ((T.low (p + 1)).obj M) (by omega)
      exact (T.low_support (p + 1) q M (by omega)).of_iso
        (asIso ((P.gr q).map ((T.inclusion p).app _)))
  · intro M hM q hq
    by_cases h : p < q
    · exact T.low_support (p + 1) q M (by omega)
    · have hi := T.low_grade (p + 1) q M (by omega)
      exact (hM q hq).of_iso (asIso ((P.gr q).map ((T.quotient (p + 1)).app M))).symm
  · intro M R hR
    exact T.low_universal (p + 1) M R (fun q hq ↦ hR q (by omega))
  · intro M L hL
    exact T.high_universal p L _ hL
  · intro B _ _ _ E _ _ _ _ _ _ _ R H _ _ hH M
    constructor
    · obtain ⟨d, hd⟩ := cutoff_triangle P T (p + 1) M
      let S := Triangle.mk ((T.inclusion (p + 1)).app M)
        ((T.quotient (p + 1)).app M) d
      let G := H ⋙ R.gr p
      have hz : IsZero (G.obj S.obj₁) :=
        high_preserved P R H hH (p + 1) _ (fun q hq ↦
          T.high_support (p + 1) q M hq) p (by omega)
      exact (Triangle.isZero₁_iff_isIso₂ (G.mapTriangle.obj S)
        (G.map_distinguished S hd)).1 hz
    · let N := (T.low (p + 1)).obj M
      obtain ⟨d, hd⟩ := cutoff_triangle P T p N
      let S := Triangle.mk ((T.inclusion p).app N) ((T.quotient p).app N) d
      let G := H ⋙ R.gr p
      have hz : IsZero (G.obj S.obj₃) :=
        low_preserved P R H hH p _ (fun q hq ↦ T.low_support p q N hq) p le_rfl
      exact (Triangle.isZero₃_iff_isIso₁ (G.mapTriangle.obj S)
        (G.map_distinguished S hd)).1 hz

end CategoryTheory.FiniteFilteredDerived
