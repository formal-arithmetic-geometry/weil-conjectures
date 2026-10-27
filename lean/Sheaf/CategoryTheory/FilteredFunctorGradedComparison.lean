/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q47
-/
module

public import Sheaf.CategoryTheory.FiniteFilteredDerivedPresentation
import Sheaf.CategoryTheory.FilteredPresentationTruncation

/-!
# Graded comparisons for supplied filtered lifts

Source: Varshavsky, Lefschetz--Verdier trace formula, Sections 5.1.3(a),(b),(e)
and Lemma 5.1.4(i)--(iii), pp. 39--41
(blueprint: lem-trf-filtered-functor-graded-comparison).

The family formulation expresses coherence for arbitrary identities and composites,
including a third abelian category. All categories live in a common larger universe;
object, morphism, derived-localization and indexing universes remain independent.
-/

@[expose] public section

set_option autoImplicit false

universe z w v u v' u'

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory.FiniteFilteredDerived

variable {I : Type z} (C : I → Type u) [∀ i : I, Category.{v} (C i)]
  [∀ i : I, Abelian (C i)] [∀ i : I, HasDerivedCategory.{w} (C i)]
  (D : I → Type u') [∀ i : I, Category.{v'} (D i)] [∀ i : I, HasShift (D i) ℤ]
  [∀ i : I, Preadditive (D i)] [∀ i : I, HasZeroObject (D i)]
  [∀ (i : I) (n : ℤ), (shiftFunctor (D i) n).Additive]
  [∀ i : I, Pretriangulated (D i)] [∀ i : I, IsTriangulated (D i)]
  (P : ∀ i : I, Presentation (C := C i) (D := D i))

/-- A supplied exact filtered lift includes its ordinary functor and the specified
forgetful comparison; preservation is required for every finite filtration interval.
Source: Varshavsky 5.1.3(a),(b), covariant unary case
(blueprint: lem-trf-filtered-functor-graded-comparison). -/
structure Lift (i j : I) where
  ordinary : DerivedCategory.Plus (C i) ⥤ DerivedCategory.Plus (C j)
  filtered : D i ⥤ D j
  [ordinaryShift : ordinary.CommShift ℤ]
  [filteredShift : filtered.CommShift ℤ]
  ordinaryExact : ordinary.IsTriangulated
  filteredExact : filtered.IsTriangulated
  interval : ∀ (a b : ℤ) (M : D i),
    Supported (P i) a b M → Supported (P j) a b (filtered.obj M)
  phi : filtered ⋙ (P j).omega ≅ (P i).omega ⋙ ordinary

attribute [instance] Lift.ordinaryShift Lift.filteredShift Lift.ordinaryExact Lift.filteredExact

variable {C D P}

/-- A lift of a supplied transformation is specified by exactly its forgetful square.
No existence of such a lift is assumed or asserted for arbitrary transformations.
Source: Varshavsky 5.1.3(e)
(blueprint: lem-trf-filtered-functor-graded-comparison). -/
def LiftsTransformation {i j : I} (F G : Lift C D P i j)
    (h : F.ordinary ⟶ G.ordinary) (a : F.filtered ⟶ G.filtered) : Prop :=
  ∀ M : D i, (P j).omega.map (a.app M) ≫ G.phi.hom.app M =
    F.phi.hom.app M ≫ h.app ((P i).omega.obj M)

/-- The given lift of the identity uses the identity forgetful comparison.
Source: Varshavsky 5.1.3(b)
(blueprint: lem-trf-filtered-functor-graded-comparison). -/
noncomputable def identityLift (i : I) : Lift C D P i i where
  ordinary := 𝟭 _
  filtered := 𝟭 _
  ordinaryExact := inferInstance
  filteredExact := inferInstance
  interval := fun _ _ _ h ↦ h
  phi := Iso.refl _

/-- Composition uses the specified composite forgetful comparison.
Source: Varshavsky 5.1.3(b),(e)
(blueprint: lem-trf-filtered-functor-graded-comparison). -/
noncomputable def composeLift {i j k : I} (F : Lift C D P i j) (G : Lift C D P j k) :
    Lift C D P i k where
  ordinary := F.ordinary ⋙ G.ordinary
  filtered := F.filtered ⋙ G.filtered
  ordinaryExact := inferInstance
  filteredExact := inferInstance
  interval := fun a b M h ↦ G.interval a b _ (F.interval a b M h)
  phi := (Functor.associator _ _ _) ≪≫ Functor.isoWhiskerLeft F.filtered G.phi ≪≫
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight F.phi G.ordinary ≪≫
    Functor.associator _ _ _

omit [∀ i : I, IsTriangulated (D i)] in
private theorem pure_preserved {i j : I} (F : Lift C D P i j) (p : ℤ) (M : D i)
    (hM : ∀ q : ℤ, q ≠ p → IsZero (((P i).gr q).obj M)) :
    ∀ q : ℤ, q ≠ p → IsZero (((P j).gr q).obj (F.filtered.obj M)) := by
  have h := F.interval p p M (fun q hq ↦ hM q (by omega))
  exact fun q hq ↦ h q (by omega)

private theorem span_iso {i j : I} (F : Lift C D P i j) (p : ℤ)
    (T : (P i).GradedSpan p) (M : D i) :
    IsIso (((P j).gr p).map (F.filtered.map (T.quotient.app M))) ∧
      IsIso (((P j).gr p).map (F.filtered.map (T.inclusion.app M))) :=
  T.map_iso (P j) F.filtered F.interval M

private theorem span_grade_iso {i : I} (p : ℤ) (T : (P i).GradedSpan p) (M : D i) :
    IsIso (((P i).gr p).map (T.quotient.app M)) ∧
      IsIso (((P i).gr p).map (T.inclusion.app M)) :=
  span_iso (identityLift (C := C) (D := D) (P := P) i) p T M

private noncomputable def pureMap {i j : I} (F : Lift C D P i j) (p : ℤ)
    (M : D i) (hM : ∀ q : ℤ, q ≠ p → IsZero (((P i).gr q).obj M)) :
    ((P j).gr p).obj (F.filtered.obj M) ≅ F.ordinary.obj (((P i).gr p).obj M) :=
  (P j).pureComparison p _ (pure_preserved F p M hM) ≪≫ F.phi.app M ≪≫
    F.ordinary.mapIso ((P i).pureComparison p M hM).symm

omit [∀ i : I, IsTriangulated (D i)] in
private theorem pureMap_naturality {i j : I} (F : Lift C D P i j) (p : ℤ)
    {M N : D i} (hM : ∀ q : ℤ, q ≠ p → IsZero (((P i).gr q).obj M))
    (hN : ∀ q : ℤ, q ≠ p → IsZero (((P i).gr q).obj N)) (f : M ⟶ N) :
    ((P j).gr p).map (F.filtered.map f) ≫ (pureMap F p N hN).hom =
      (pureMap F p M hM).hom ≫ F.ordinary.map (((P i).gr p).map f) := by
  have h : (P i).omega.map f ≫ ((P i).pureComparison p N hN).inv =
      ((P i).pureComparison p M hM).inv ≫ ((P i).gr p).map f := by
    apply (cancel_mono ((P i).pureComparison p N hN).hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [(P i).pureNaturality p hM hN f]
    simp
  dsimp [pureMap]
  rw [← Category.assoc, (P j).pureNaturality p (pure_preserved F p M hM) (pure_preserved F p N hN)
    (F.filtered.map f)]
  simp only [Category.assoc]
  have hn := F.phi.hom.naturality f
  dsimp only [Functor.comp_map] at hn
  rw [reassoc_of% hn]
  rw [← F.ordinary.map_comp, h, F.ordinary.map_comp]

private noncomputable def spanComparison {i j : I} (F : Lift C D P i j) (p : ℤ)
    (T : (P i).GradedSpan p) :
    F.filtered ⋙ (P j).gr p ≅ (P i).gr p ⋙ F.ordinary := by
  have hq (M : D i) := (span_iso F p T M).1
  have hi (M : D i) := (span_iso F p T M).2
  have hq' (M : D i) := (span_grade_iso p T M).1
  have hi' (M : D i) := (span_grade_iso p T M).2
  have : ∀ M, IsIso
      ((Functor.whiskerRight T.quotient (F.filtered ⋙ (P j).gr p)).app M) := hq
  have : IsIso (Functor.whiskerRight T.quotient (F.filtered ⋙ (P j).gr p)) :=
    NatIso.isIso_of_isIso_app _
  have : ∀ M, IsIso
      ((Functor.whiskerRight T.inclusion (F.filtered ⋙ (P j).gr p)).app M) := hi
  have : IsIso (Functor.whiskerRight T.inclusion (F.filtered ⋙ (P j).gr p)) :=
    NatIso.isIso_of_isIso_app _
  have : ∀ M, IsIso ((Functor.whiskerRight T.quotient ((P i).gr p)).app M) := hq'
  have : IsIso (Functor.whiskerRight T.quotient ((P i).gr p)) :=
    NatIso.isIso_of_isIso_app _
  have : ∀ M, IsIso ((Functor.whiskerRight T.inclusion ((P i).gr p)).app M) := hi'
  have : IsIso (Functor.whiskerRight T.inclusion ((P i).gr p)) :=
    NatIso.isIso_of_isIso_app _
  let e₁ : F.filtered ⋙ (P j).gr p ≅ T.piece ⋙ F.filtered ⋙ (P j).gr p :=
    asIso (Functor.whiskerRight T.quotient (F.filtered ⋙ (P j).gr p)) ≪≫
      (asIso (Functor.whiskerRight T.inclusion (F.filtered ⋙ (P j).gr p))).symm
  let e₂ : T.piece ⋙ F.filtered ⋙ (P j).gr p ≅ T.piece ⋙ (P i).gr p ⋙ F.ordinary :=
    NatIso.ofComponents (fun M ↦ pureMap F p _ (T.piece_support M))
      (fun f ↦ pureMap_naturality F p _ _ (T.piece.map f))
  let e₃ : (P i).gr p ≅ T.piece ⋙ (P i).gr p :=
    asIso (Functor.whiskerRight T.quotient ((P i).gr p)) ≪≫
      (asIso (Functor.whiskerRight T.inclusion ((P i).gr p))).symm
  exact e₁ ≪≫ e₂ ≪≫ Functor.isoWhiskerRight e₃.symm F.ordinary

private theorem spanComparison_pure {i j : I} (F : Lift C D P i j) (p : ℤ)
    (T : (P i).GradedSpan p) (M : D i)
    (hM : ∀ q : ℤ, q ≠ p → IsZero (((P i).gr q).obj M)) :
    (spanComparison F p T).hom.app M = (pureMap F p M hM).hom := by
  have hq (N : D i) := (span_iso F p T N).1
  have hi (N : D i) := (span_iso F p T N).2
  have hq' (N : D i) := (span_grade_iso p T N).1
  have hi' (N : D i) := (span_grade_iso p T N).2
  have hc := T.cut_pure M hM
  have h₁ := pureMap_naturality F p hM hc (T.quotient.app M)
  have h₂ := pureMap_naturality F p (T.piece_support M) hc (T.inclusion.app M)
  apply (cancel_mono (F.ordinary.map (((P i).gr p).map (T.quotient.app M)))).1
  dsimp only [spanComparison, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, asIso_hom, asIso_inv,
    NatIso.ofComponents_hom_app, Iso.trans_inv, Iso.symm_inv]
  simp only [NatIso.isIso_inv_app, Functor.whiskerRight_app, Functor.comp_map]
  simp only [Functor.map_comp, Category.assoc, Functor.map_inv,
    ]
  rw [← h₁, ← reassoc_of% h₂]
  simp

private theorem pure_ext {i j : I} (F G : Lift C D P i j) (p : ℤ)
    (T : (P i).GradedSpan p)
    (a b : F.filtered ⋙ (P j).gr p ⟶ (P i).gr p ⋙ G.ordinary)
    (h : ∀ (M : D i) (_hM : ∀ q : ℤ, q ≠ p → IsZero (((P i).gr q).obj M)),
      a.app M = b.app M) : a = b := by
  apply NatTrans.ext
  funext M
  have hi := (span_iso F p T M).2
  have hq := (span_grade_iso p T M).1
  apply (cancel_mono (G.ordinary.map (((P i).gr p).map (T.quotient.app M)))).1
  change a.app M ≫ ((P i).gr p ⋙ G.ordinary).map (T.quotient.app M) =
    b.app M ≫ ((P i).gr p ⋙ G.ordinary).map (T.quotient.app M)
  rw [← a.naturality, ← b.naturality]
  congr 1
  apply (cancel_epi (((P j).gr p).map (F.filtered.map (T.inclusion.app M)))).1
  change (F.filtered ⋙ (P j).gr p).map (T.inclusion.app M) ≫ a.app (T.cut.obj M) =
    (F.filtered ⋙ (P j).gr p).map (T.inclusion.app M) ≫ b.app (T.cut.obj M)
  rw [a.naturality, b.naturality, h (T.piece.obj M) (T.piece_support M)]

omit [∀ i : I, IsTriangulated (D i)] in
private theorem pureMap_transformation {i j : I} (F G : Lift C D P i j)
    (h : F.ordinary ⟶ G.ordinary) (a : F.filtered ⟶ G.filtered)
    (ha : LiftsTransformation F G h a) (p : ℤ) (M : D i)
    (hM : ∀ q : ℤ, q ≠ p → IsZero (((P i).gr q).obj M)) :
    ((P j).gr p).map (a.app M) ≫ (pureMap G p M hM).hom =
      (pureMap F p M hM).hom ≫ h.app (((P i).gr p).obj M) := by
  dsimp [pureMap]
  rw [← Category.assoc, (P j).pureNaturality p (pure_preserved F p M hM) (pure_preserved G p M hM)
    (a.app M)]
  simp only [Category.assoc]
  rw [reassoc_of% (ha M)]
  rw [← h.naturality ((P i).pureComparison p M hM).inv]

omit [∀ i : I, IsTriangulated (D i)] in
private theorem pureMap_identity (i : I) (p : ℤ) (M : D i)
    (hM : ∀ q : ℤ, q ≠ p → IsZero (((P i).gr q).obj M)) :
    (pureMap (identityLift (C := C) (D := D) (P := P) i) p M hM).hom = 𝟙 _ := by
  simp [pureMap, identityLift]

omit [∀ i : I, IsTriangulated (D i)] in
private theorem pureMap_compose {i j k : I} (F : Lift C D P i j) (G : Lift C D P j k)
    (p : ℤ) (M : D i)
    (hM : ∀ q : ℤ, q ≠ p → IsZero (((P i).gr q).obj M)) :
    (pureMap (composeLift F G) p M hM).hom =
      (pureMap G p (F.filtered.obj M) (pure_preserved F p M hM)).hom ≫
        G.ordinary.map (pureMap F p M hM).hom := by
  simp [pureMap, composeLift, Functor.map_comp, Category.assoc]

omit [∀ i : I, IsTriangulated (D i)] in
private theorem isIso_of_grades {i : I} {M N : D i} (f : M ⟶ N)
    (hf : ∀ p : ℤ, IsIso (((P i).gr p).map f)) : IsIso f := by
  obtain ⟨Z, g, h, hT⟩ := distinguished_cocone_triangle f
  let T := Triangle.mk f g h
  have hz : IsZero Z := (Presentation.truncationSpans (P i)).2 Z (fun p ↦ by
    exact (Triangle.isZero₃_iff_isIso₁ (((P i).gr p).mapTriangle.obj T)
      (((P i).gr p).map_distinguished T hT)).2 (hf p))
  exact (Triangle.isZero₃_iff_isIso₁ T hT).1 hz

/-- Graded comparisons, normalized on pure filtration objects, commute with supplied
transformations and both kinds of composition, and detect lifted isomorphisms.
Source: Varshavsky 5.1.3(a),(b),(e), Lemma 5.1.4(i)--(iii)
(blueprint: lem-trf-filtered-functor-graded-comparison).

Proof:
1. Choose the canonical span M → low(p+1) M ← high(p)(low(p+1) M).
   Its right-hand object is pure in degree p. After any supplied exact
   interval-preserving functor, both arrows induce isomorphisms on grade p.
   This is the cutoff-triangle calculation in Presentation.truncationSpans.
2. On the pure right-hand object, use the supplied forgetful comparison through
   the canonical pureComparison isomorphisms. Extend it along the two grade
   isomorphisms of the span. Naturality of all factors gives a natural isomorphism.
   On a pure input the pureNaturality equations cancel the span arrows, giving
   exactly the normalization in the statement.
3. Two natural transformations between the relevant graded functors agree if
   they agree on pure objects: apply naturality to the quotient and inclusion,
   then cancel their invertible graded maps. Thus transformation compatibility,
   identity functors, and composite functors reduce to the corresponding pure
   equations. These follow from pureNaturality, the supplied forgetful square,
   and the definitions of the identity and composite forgetful comparisons.
4. An invertible ordinary transformation therefore gives invertible maps on every
   grade. The exact graded functors send a cone triangle to triangles with zero
   third vertex. Joint detection of zero objects by the grades makes the original
   cone zero, so the filtered component is invertible by the zero-cone criterion.
5. The identity-transformation square follows from functoriality. Compose two
   transformation squares and associate the composites to obtain the last clause.
-/
theorem filteredFunctorGradedComparison :
    ∃ theta : ∀ {i j : I} (F : Lift C D P i j) (p : ℤ),
      F.filtered ⋙ (P j).gr p ≅ (P i).gr p ⋙ F.ordinary,
    (∀ {i j : I} (F : Lift C D P i j) (p : ℤ) (M : D i)
      (hM : ∀ q : ℤ, q ≠ p → IsZero (((P i).gr q).obj M))
      (hFM : ∀ q : ℤ, q ≠ p → IsZero (((P j).gr q).obj (F.filtered.obj M))),
      (theta F p).hom.app M =
        ((P j).pureComparison p (F.filtered.obj M) hFM).hom ≫ F.phi.hom.app M ≫
        F.ordinary.map ((P i).pureComparison p M hM).inv) ∧
    (∀ {i j : I} (F G : Lift C D P i j) (h : F.ordinary ⟶ G.ordinary)
      (a : F.filtered ⟶ G.filtered), LiftsTransformation F G h a →
      (∀ (p : ℤ) (M : D i),
        ((P j).gr p).map (a.app M) ≫ (theta G p).hom.app M =
          (theta F p).hom.app M ≫ h.app (((P i).gr p).obj M)) ∧
      (IsIso h → IsIso a)) ∧
    (∀ (i : I) (p : ℤ) (M : D i),
      (theta (identityLift (C := C) (D := D) (P := P) i) p).hom.app M = 𝟙 _) ∧
    (∀ {i j k : I} (F : Lift C D P i j) (G : Lift C D P j k) (p : ℤ) (M : D i),
      (theta (composeLift F G) p).hom.app M =
        (theta G p).hom.app (F.filtered.obj M) ≫
          G.ordinary.map ((theta F p).hom.app M)) ∧
    (∀ {i j : I} (F : Lift C D P i j) (p : ℤ) (M : D i),
      ((P j).gr p).map ((𝟙 F.filtered : F.filtered ⟶ F.filtered).app M) ≫ (theta F p).hom.app M =
        (theta F p).hom.app M ≫ (𝟙 F.ordinary : F.ordinary ⟶ F.ordinary).app (((P i).gr p).obj M)) ∧
    (∀ {i j : I} (F G H : Lift C D P i j)
      (h : F.ordinary ⟶ G.ordinary) (k : G.ordinary ⟶ H.ordinary)
      (a : F.filtered ⟶ G.filtered) (b : G.filtered ⟶ H.filtered),
      LiftsTransformation F G h a → LiftsTransformation G H k b →
      ∀ (p : ℤ) (M : D i),
        ((P j).gr p).map ((a ≫ b).app M) ≫ (theta H p).hom.app M =
          (theta F p).hom.app M ≫ (h ≫ k).app (((P i).gr p).obj M)) := by
  classical
  let T (i : I) (p : ℤ) := Classical.choice ((Presentation.truncationSpans (P i)).1 p)
  let theta {i j : I} (F : Lift C D P i j) (p : ℤ) := spanComparison F p (T i p)
  have hp {i j : I} (F : Lift C D P i j) (p : ℤ) (M : D i)
      (hM : ∀ q : ℤ, q ≠ p → IsZero (((P i).gr q).obj M)) :
      (theta F p).hom.app M = (pureMap F p M hM).hom :=
    spanComparison_pure F p (T i p) M hM
  have ht {i j : I} (F G : Lift C D P i j) (h : F.ordinary ⟶ G.ordinary)
      (a : F.filtered ⟶ G.filtered) (ha : LiftsTransformation F G h a) (p : ℤ) :
      Functor.whiskerRight a ((P j).gr p) ≫ (theta G p).hom =
        (theta F p).hom ≫ Functor.whiskerLeft ((P i).gr p) h := by
    apply pure_ext F G p (T i p)
    intro M hM
    change ((P j).gr p).map (a.app M) ≫ (theta G p).hom.app M =
      (theta F p).hom.app M ≫ h.app (((P i).gr p).obj M)
    rw [hp F p M hM, hp G p M hM]
    exact pureMap_transformation F G h a ha p M hM
  refine ⟨theta, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j F p M hM hFM
    exact hp F p M hM
  · intro i j F G h a ha
    refine ⟨fun p M ↦ congrArg (fun t ↦ t.app M) (ht F G h a ha p), ?_⟩
    intro hh
    have hi (M : D i) : IsIso (a.app M) := by
      apply isIso_of_grades (P := P) (i := j)
      intro p
      have eq := congrArg (fun t ↦ t.app M) (ht F G h a ha p)
      change ((P j).gr p).map (a.app M) ≫ (theta G p).hom.app M =
        (theta F p).hom.app M ≫ h.app (((P i).gr p).obj M) at eq
      have : IsIso (((P j).gr p).map (a.app M) ≫ (theta G p).hom.app M) := by
        rw [eq]
        infer_instance
      exact IsIso.of_isIso_comp_right _ ((theta G p).hom.app M)
    exact NatIso.isIso_of_isIso_app a
  · intro i p M
    have eq : (theta (identityLift (C := C) (D := D) (P := P) i) p).hom =
        (𝟙 ((P i).gr p)) := by
      apply pure_ext (identityLift (C := C) (D := D) (P := P) i)
        (identityLift (C := C) (D := D) (P := P) i) p (T i p)
      intro N hN
      rw [hp _ p N hN, pureMap_identity]
      rfl
    exact congrArg (fun t ↦ t.app M) eq
  · intro i j k F G p M
    have eq : (theta (composeLift F G) p).hom =
        Functor.whiskerLeft F.filtered (theta G p).hom ≫
          Functor.whiskerRight (theta F p).hom G.ordinary := by
      apply pure_ext (composeLift F G) (composeLift F G) p (T i p)
      intro N hN
      change (theta (composeLift F G) p).hom.app N =
        (theta G p).hom.app (F.filtered.obj N) ≫
          G.ordinary.map ((theta F p).hom.app N)
      rw [hp _ p N hN, hp F p N hN,
        hp G p _ (pure_preserved F p N hN)]
      exact pureMap_compose F G p N hN
    exact congrArg (fun t ↦ t.app M) eq
  · intro i j F p M
    simp
  · intro i j F G H h k a b ha hb p M
    have ha' := congrArg (fun t ↦ t.app M) (ht F G h a ha p)
    have hb' := congrArg (fun t ↦ t.app M) (ht G H k b hb p)
    change ((P j).gr p).map (a.app M) ≫ (theta G p).hom.app M =
      (theta F p).hom.app M ≫ h.app (((P i).gr p).obj M) at ha'
    change ((P j).gr p).map (b.app M) ≫ (theta H p).hom.app M =
      (theta G p).hom.app M ≫ k.app (((P i).gr p).obj M) at hb'
    simp only [NatTrans.comp_app, Functor.map_comp, Category.assoc]
    rw [hb', ← Category.assoc, ha', Category.assoc]

end CategoryTheory.FiniteFilteredDerived
