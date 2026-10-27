/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y9
-/
module

public import Sheaf.CategoryTheory.FiniteFilteredDerivedPresentation
import Sheaf.Algebra.Homology.FilteredTruncationTriangle
import Mathlib.CategoryTheory.Localization.Equivalence

/-!
# Transport of universal filtration truncations to a presentation

Source: Varshavsky, §§5.1.1(b)--(e), 5.1.2(a)--(c), pp.39--40.
(blueprint: lem-trf-filtered-presentation-truncation-data).
-/

@[expose] public section
set_option autoImplicit false
universe w v u v' u'
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory.FiniteFilteredDerived

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  {D : Type u'} [Category.{v'} D] [HasShift D ℤ] [Preadditive D] [HasZeroObject D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [IsTriangulated D]

private noncomputable def sourceEquivalence :
    CochainComplex.FiniteFiltered.Complex C false ≌ Complexes C where
  functor :=
    { obj := fun K ↦ ⟨K.obj, K.property.1, by
        obtain ⟨⟨n, hn⟩, _⟩ := K.property.2
        exact ⟨n, (CochainComplex.isStrictlyGE_iff _ _).2 hn⟩⟩
      map := fun f ↦ ⟨f.hom⟩ }
  inverse :=
    { obj := fun K ↦ ⟨K.obj, K.property.1, by
        obtain ⟨n, hn⟩ := K.property.2
        exact ⟨⟨n, (by
          rw [CochainComplex.isStrictlyGE_iff] at hn
          exact fun i hi ↦ @hn i hi)⟩, Or.inl rfl⟩⟩
      map := fun f ↦ ⟨f.hom⟩ }
  unitIso := NatIso.ofComponents (fun K ↦ ObjectProperty.isoMk _ (Iso.refl _))
    (by
      intro K L f
      apply ObjectProperty.hom_ext
      change f.hom ≫ 𝟙 _ = 𝟙 _ ≫ f.hom
      simp)
  counitIso := NatIso.ofComponents (fun K ↦ ObjectProperty.isoMk _ (Iso.refl _))
    (by
      intro K L f
      apply ObjectProperty.hom_ext
      change f.hom ≫ 𝟙 _ = 𝟙 _ ≫ f.hom
      simp)
  functor_unitIso_comp := by
    intro K
    apply ObjectProperty.hom_ext
    change (𝟙 K.obj) ≫ 𝟙 _ = 𝟙 _
    simp

omit [IsTriangulated D] in
private theorem source_localization (P : Presentation (C := C) (D := D)) :
    ((sourceEquivalence (C := C)).functor ⋙ P.Q).IsLocalization
      (CochainComplex.FiniteFiltered.quasiIso false) := by
  let S := sourceEquivalence (C := C)
  apply Functor.IsLocalization.of_equivalence_source P.Q (gradedQuasiIso C)
    (S.functor ⋙ P.Q) (CochainComplex.FiniteFiltered.quasiIso false) S.symm
  · intro X Y f hf
    exact MorphismProperty.le_isoClosure _ _ hf
  · intro X Y f hf
    exact Localization.inverts P.Q (gradedQuasiIso C) _ hf
  · exact (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight S.counitIso P.Q ≪≫ Functor.leftUnitor _

omit [IsTriangulated D] in
private noncomputable def modelEquivalence (P : Presentation (C := C) (D := D)) :
    CochainComplex.FiniteFiltered.Derived (A := C) false ≌ D := by
  letI := source_localization P
  exact Localization.uniq (CochainComplex.FiniteFiltered.Q false)
    ((sourceEquivalence (C := C)).functor ⋙ P.Q)
    (CochainComplex.FiniteFiltered.quasiIso false)

omit [IsTriangulated D] in
private noncomputable def modelGrComparison (P : Presentation (C := C) (D := D))
    (T : CochainComplex.FiniteFiltered.FilteredTruncationData C) (p : ℤ) :
    (modelEquivalence P).functor ⋙ P.gr p ≅ T.gr p := by
  let S := sourceEquivalence (C := C)
  let e := modelEquivalence P
  let Q := CochainComplex.FiniteFiltered.Q (A := C) false
  let W := CochainComplex.FiniteFiltered.quasiIso (A := C) false
  letI := source_localization P
  let c : Q ⋙ e.functor ≅ S.functor ⋙ P.Q :=
    Localization.compUniqFunctor Q (S.functor ⋙ P.Q) W
  let d : (S.functor ⋙ P.Q) ⋙ P.gr p ⋙ DerivedCategory.Plus.ι ≅
      CochainComplex.FiniteFiltered.graded false p ⋙ DerivedCategory.Q :=
    NatIso.ofComponents (fun K ↦ P.grComplex p (S.functor.obj K)) (by
      intro K L f
      exact P.grNaturality p (S.functor.map f))
  let b : Q ⋙ (e.functor ⋙ P.gr p ⋙ DerivedCategory.Plus.ι) ≅
      Q ⋙ (T.gr p ⋙ DerivedCategory.Plus.ι) :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight c _ ≪≫ d ≪≫ (T.grComparison p).symm
  let a := (Localization.fullyFaithfulWhiskeringLeft Q W _).preimageIso b
  exact ((Functor.FullyFaithful.ofFullyFaithful
    (DerivedCategory.Plus.ι (C := C))).whiskeringRight _).preimageIso a

private theorem model_high_grade
    (T : CochainComplex.FiniteFiltered.FilteredTruncationData C)
    (r q : ℤ) (M : CochainComplex.FiniteFiltered.Derived (A := C) false) (hq : r ≤ q) :
    IsIso ((T.gr q).map ((T.inclusion r).app M)) := by
  let := T.model
  let := T.gr_shift q
  let := T.gr_exact q
  let S := Triangle.mk ((T.inclusion r).app M) ((T.quotient r).app M)
    ((T.connecting r).app M)
  exact (Triangle.isZero₃_iff_isIso₁ ((T.gr q).mapTriangle.obj S)
    ((T.gr q).map_distinguished S (T.distinguished r M))).1 (T.low_support r q M hq)

private theorem model_low_grade
    (T : CochainComplex.FiniteFiltered.FilteredTruncationData C)
    (r q : ℤ) (M : CochainComplex.FiniteFiltered.Derived (A := C) false) (hq : q < r) :
    IsIso ((T.gr q).map ((T.quotient r).app M)) := by
  let := T.model
  let := T.gr_shift q
  let := T.gr_exact q
  let S := Triangle.mk ((T.inclusion r).app M) ((T.quotient r).app M)
    ((T.connecting r).app M)
  exact (Triangle.isZero₁_iff_isIso₂ ((T.gr q).mapTriangle.obj S)
    ((T.gr q).map_distinguished S (T.distinguished r M))).1 (T.high_support r q M hq)

private theorem transfer_high_bijective {E F : Type*} [Category* E] [Category* F]
    (e : E ≌ F) (H : E ⥤ E) (i : H ⟶ 𝟭 E) (L M : F)
    (h : Function.Bijective (fun f : e.inverse.obj L ⟶ H.obj (e.inverse.obj M) ↦
      f ≫ i.app (e.inverse.obj M))) :
    Function.Bijective (fun f : L ⟶ e.functor.obj (H.obj (e.inverse.obj M)) ↦
      f ≫ e.functor.map (i.app (e.inverse.obj M)) ≫ e.counitIso.hom.app M) := by
  let a := e.symm.toAdjunction.homEquiv L (H.obj (e.inverse.obj M))
  let b := e.fullyFaithfulInverse.homEquiv (X := L) (Y := M)
  have key (f : e.inverse.obj L ⟶ H.obj (e.inverse.obj M)) :
      (a f) ≫ e.functor.map (i.app (e.inverse.obj M)) ≫ e.counitIso.hom.app M =
        b.symm (f ≫ i.app (e.inverse.obj M)) := by
    change (e.counitIso.inv.app L ≫ e.functor.map f) ≫
        e.functor.map (i.app (e.inverse.obj M)) ≫ e.counitIso.hom.app M =
      e.counitIso.inv.app L ≫ e.functor.map (f ≫ i.app (e.inverse.obj M)) ≫
        e.counitIso.hom.app M
    simp only [Functor.map_comp, Category.assoc]
  have hh := b.symm.bijective.comp (h.comp a.symm.bijective)
  change Function.Bijective (fun f : L ⟶ e.functor.obj (H.obj (e.inverse.obj M)) ↦
    b.symm (a.symm f ≫ i.app (e.inverse.obj M))) at hh
  have heq : (fun f : L ⟶ e.functor.obj (H.obj (e.inverse.obj M)) ↦
      f ≫ e.functor.map (i.app (e.inverse.obj M)) ≫ e.counitIso.hom.app M) =
      (fun f ↦ b.symm (a.symm f ≫ i.app (e.inverse.obj M))) := by
    funext f
    simpa only [a.apply_symm_apply] using key (a.symm f)
  rw [heq]
  exact hh

private theorem transfer_low_bijective {E F : Type*} [Category* E] [Category* F]
    (e : E ≌ F) (H : E ⥤ E) (i : 𝟭 E ⟶ H) (M R : F)
    (h : Function.Bijective (fun f : H.obj (e.inverse.obj M) ⟶ e.inverse.obj R ↦
      i.app (e.inverse.obj M) ≫ f)) :
    Function.Bijective (fun f : e.functor.obj (H.obj (e.inverse.obj M)) ⟶ R ↦
      e.counitIso.inv.app M ≫ e.functor.map (i.app (e.inverse.obj M)) ≫ f) := by
  let a := e.toAdjunction.homEquiv (H.obj (e.inverse.obj M)) R
  let b := e.fullyFaithfulInverse.homEquiv (X := M) (Y := R)
  have key (f : e.functor.obj (H.obj (e.inverse.obj M)) ⟶ R) :
      e.counitIso.inv.app M ≫ e.functor.map (i.app (e.inverse.obj M)) ≫ f =
        b.symm (i.app (e.inverse.obj M) ≫ a f) := by
    change e.counitIso.inv.app M ≫ e.functor.map (i.app (e.inverse.obj M)) ≫ f =
      e.counitIso.inv.app M ≫ e.functor.map (i.app (e.inverse.obj M) ≫
        (e.unitIso.hom.app _ ≫ e.inverse.map f)) ≫ e.counitIso.hom.app R
    simp only [Functor.map_comp, Category.assoc]
    rw [show e.functor.map (e.inverse.map f) ≫ e.counitIso.hom.app R =
      e.counitIso.hom.app _ ≫ f from e.counit_naturality f]
    rw [← Category.assoc (e.functor.map (e.unitIso.hom.app _)),
      show e.functor.map (e.unitIso.hom.app _) ≫ e.counitIso.hom.app _ = 𝟙 _ from
        e.functor_unitIso_comp _]
    simp
  have hh := b.symm.bijective.comp (h.comp a.bijective)
  change Function.Bijective (fun f : e.functor.obj (H.obj (e.inverse.obj M)) ⟶ R ↦
    b.symm (i.app (e.inverse.obj M) ≫ a f)) at hh
  have heq : (fun f : e.functor.obj (H.obj (e.inverse.obj M)) ⟶ R ↦
      e.counitIso.inv.app M ≫ e.functor.map (i.app (e.inverse.obj M)) ≫ f) =
      (fun f ↦ b.symm (i.app (e.inverse.obj M) ≫ a f)) := funext key
  rw [heq]
  exact hh

/-- Universal high and low filtration truncations, including their canonical grade maps.
The two Hom bijections determine the functors and arrows up to unique compatible
isomorphisms. Thus the following existence theorem determines its data up to the
isomorphisms used in the graded comparison argument.
Source: Varshavsky 5.1.1(b)--(e), 5.1.2(b,c).
(blueprint: lem-trf-filtered-presentation-truncation-data). -/
structure Presentation.Truncation (P : Presentation (C := C) (D := D)) where
  high : ℤ → D ⥤ D
  low : ℤ → D ⥤ D
  inclusion : ∀ r : ℤ, high r ⟶ 𝟭 D
  quotient : ∀ r : ℤ, 𝟭 D ⟶ low r
  high_support : ∀ (r q : ℤ) (M : D), q < r →
    IsZero ((P.gr q).obj ((high r).obj M))
  low_support : ∀ (r q : ℤ) (M : D), r ≤ q →
    IsZero ((P.gr q).obj ((low r).obj M))
  high_grade : ∀ (r q : ℤ) (M : D), r ≤ q →
    IsIso ((P.gr q).map ((inclusion r).app M))
  low_grade : ∀ (r q : ℤ) (M : D), q < r →
    IsIso ((P.gr q).map ((quotient r).app M))
  high_universal : ∀ (r : ℤ) (L M : D),
    (∀ q : ℤ, q < r → IsZero ((P.gr q).obj L)) →
    Function.Bijective (fun f : L ⟶ (high r).obj M ↦ f ≫ (inclusion r).app M)
  low_universal : ∀ (r : ℤ) (M R : D),
    (∀ q : ℤ, r ≤ q → IsZero ((P.gr q).obj R)) →
    Function.Bijective (fun f : (low r).obj M ⟶ R ↦ (quotient r).app M ≫ f)

omit [IsTriangulated D] in
/-- Universal truncation calculus is invariant under the supplied presentation.
Source: Varshavsky 5.1.1(b)--(e), 5.1.2(a)--(c), pp.39--40.
(blueprint: lem-trf-filtered-presentation-truncation-data).

Proof:
1. The category of complexes in `filteredTruncationTriangle` uses the explicit
   condition that all terms below some integer are zero objects. Identify it with
   `Complexes C` using `CochainComplex.isStrictlyGE_iff`. The identity on underlying
   filtered complexes gives inverse functors and preserves each graded map.
2. The uniqueness of localization therefore gives an equivalence between its
   concrete localized category and D. The isomorphisms `P.grComplex` and
   `P.omegaComplex`, with their stated naturality equations, lift to natural
   comparisons on these localizations: first compare after the fully faithful
   inclusion into the ordinary derived category, then lift back to Plus.
3. Transport the high and low functors, their inclusion and quotient, and their
   Hom bijections from `filteredTruncationTriangle` across this equivalence.
   Its representative formulas identify these functors with the actual filtered
   subcomplex and quotient. In grade q these maps are the identity when r ≤ q
   for high, respectively q < r for low; the remaining grades are zero. This
   proves the support assertions and the invertibility assertions, with the
   displayed arrows rather than arbitrary isomorphisms.
4. The universal Hom bijections give uniqueness of all transferred high and low
   functors and arrows up to compatible isomorphism. Distinguished cutoff
   triangles are recovered separately from the exact grades and their joint
   detection of zero objects, so no shift structure is transported here.
-/
theorem Presentation.truncationData (P : Presentation (C := C) (D := D)) :
    Nonempty P.Truncation := by
  classical
  obtain ⟨T⟩ := CochainComplex.FiniteFiltered.filteredTruncationTriangle C
  let e := modelEquivalence P
  let c (q : ℤ) : e.functor ⋙ P.gr q ≅ T.gr q := modelGrComparison P T q
  let h (r : ℤ) := e.inverse ⋙ T.high r ⋙ e.functor
  let l (r : ℤ) := e.inverse ⋙ T.low r ⋙ e.functor
  let i (r : ℤ) : h r ⟶ 𝟭 D :=
    { app := fun M ↦ e.functor.map ((T.inclusion r).app (e.inverse.obj M)) ≫
        e.counitIso.hom.app M
      naturality := by
        intro M N f
        dsimp [h]
        rw [← Category.assoc, ← Functor.map_comp, (T.inclusion r).naturality,
          Functor.map_comp, Functor.id_map, Category.assoc]
        rw [show e.functor.map (e.inverse.map f) ≫ e.counitIso.hom.app N =
          e.counitIso.hom.app M ≫ f from e.counit_naturality f]
        simp only [Category.assoc] }
  let q (r : ℤ) : 𝟭 D ⟶ l r :=
    { app := fun M ↦ e.counitIso.inv.app M ≫
        e.functor.map ((T.quotient r).app (e.inverse.obj M))
      naturality := by
        intro M N f
        dsimp [l]
        rw [← Category.assoc, ← e.counitInv_naturality, Category.assoc,
          ← Functor.map_comp]
        have hn := (T.quotient r).naturality (e.inverse.map f)
        change e.inverse.map f ≫ (T.quotient r).app (e.inverse.obj N) =
          (T.quotient r).app (e.inverse.obj M) ≫ (T.low r).map (e.inverse.map f) at hn
        rw [hn, Functor.map_comp, Category.assoc] }
  refine ⟨{
    high := h
    low := l
    inclusion := i
    quotient := q
    high_support := ?_
    low_support := ?_
    high_grade := ?_
    low_grade := ?_
    high_universal := ?_
    low_universal := ?_ }⟩
  · intro r a M ha
    exact (T.high_support r a (e.inverse.obj M) ha).of_iso ((c a).app _)
  · intro r a M ha
    exact (T.low_support r a (e.inverse.obj M) ha).of_iso ((c a).app _)
  · intro r a M ha
    have hm : IsIso ((P.gr a).map (e.functor.map
        ((T.inclusion r).app (e.inverse.obj M)))) :=
      (NatIso.isIso_map_iff (c a) _).2 (model_high_grade T r a _ ha)
    dsimp [i]
    rw [Functor.map_comp]
    infer_instance
  · intro r a M ha
    have hm : IsIso ((P.gr a).map (e.functor.map
        ((T.quotient r).app (e.inverse.obj M)))) :=
      (NatIso.isIso_map_iff (c a) _).2 (model_low_grade T r a _ ha)
    dsimp [q]
    rw [Functor.map_comp]
    infer_instance
  · intro r L M hL
    apply transfer_high_bijective e (T.high r) (T.inclusion r) L M
    apply T.high_hom_bijective r _ _
    intro a ha
    exact ((hL a ha).of_iso ((P.gr a).mapIso (e.counitIso.app L))).of_iso
      ((c a).app (e.inverse.obj L)).symm
  · intro r M R hR
    change Function.Bijective (fun f ↦
      (e.counitIso.inv.app M ≫ e.functor.map ((T.quotient r).app (e.inverse.obj M))) ≫ f)
    simp only [Category.assoc]
    apply transfer_low_bijective e (T.low r) (T.quotient r) M R
    apply T.low_hom_bijective r _ _
    intro a ha
    exact ((hR a ha).of_iso ((P.gr a).mapIso (e.counitIso.app R))).of_iso
      ((c a).app (e.inverse.obj R)).symm

end CategoryTheory.FiniteFilteredDerived
