/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N7
-/
module

public import Sheaf.CategoryTheory.Triangulated.CohomologyComparisonPasting
public import Mathlib.Order.Directed
import all Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE

/-! # Coherent truncation triangles and shifted cohomology in a t-exact system

Source: BBD 1.3.3(i),(ii), 1.3.4--1.3.6, 1.1.9--1.1.10; the agent assembly of the
normalized system-coherence argument in old common-stage proof steps 4--5
(blueprint: lem-per-texact-system-triangle-coherence).

The comparisons are the existing normalized `eTruncLTIso`, `eTruncGEIso`, and
`truncationCohomologyComparison`. The integer parameter `n` of `triangleLTGE` is the
cutoff `r + 1`. Cohomology is `truncGELE r r` followed by shift by `r`.
-/

@[expose] public section

set_option autoImplicit false

universe uI uC vC uD vD

namespace CategoryTheory.Triangulated.TStructure

open Limits Pretriangulated

variable {C : Type uC} [Category.{vC} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [IsTriangulated C]
  {D : Type uD} [Category.{vD} D] [Preadditive D] [HasZeroObject D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D] [IsTriangulated D]

omit [Preadditive C] [HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [IsTriangulated C] in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private lemma identity_commShift_of_unit (F : C ⥤ C) [csF : F.CommShift ℤ]
    (hF : F = 𝟭 C) (a : F ⋙ F ≅ F) [NatTrans.CommShift a.hom ℤ]
    (ha : a = Functor.isoWhiskerRight (eqToIso hF) F ≪≫ Functor.leftUnitor F) :
    NatTrans.CommShift (eqToIso hF).hom ℤ := by
  subst F
  refine @NatTrans.CommShift.mk _ _ _ _ _ _ _ _ _ _ _ csF
    (Functor.CommShift.id C) ?_
  intro n
  apply NatTrans.ext
  funext K
  have hh := NatTrans.shift_app_comm a.hom n K
  simp only [ha, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, eqToIso_refl, Iso.refl_hom, NatTrans.id_app,
    Functor.leftUnitor_hom_app, Functor.commShiftIso_comp_hom_app,
    Functor.id_map] at hh
  dsimp only [Functor.id_obj] at hh
  erw [Category.id_comp, Functor.map_id, Category.comp_id, Category.id_comp] at hh
  have hs : (Functor.commShiftIso (𝟭 C) n).hom.app K = 𝟙 _ := by
    apply (cancel_epi ((Functor.commShiftIso (𝟭 C) n).hom.app K)).1
    exact (hh.trans (Category.id_comp _)).trans (Category.comp_id _).symm
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    eqToIso_refl, Iso.refl_hom, NatTrans.id_app, Functor.map_id,
    Functor.commShiftIso_id_hom_app]
  dsimp only [Functor.comp_obj, Functor.id_obj] at hs ⊢
  erw [Category.comp_id, Category.id_comp]
  exact hs

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The single-functor assertion, with all three arrows and all changes of cutoff.
Source: BBD 1.3.3(i),(ii), 1.3.6 and 1.1.9--1.1.10, agent assembly
(blueprint: lem-per-texact-system-triangle-coherence).

Proof: (1) use lem-pod-texact-truncation-comparison for the normalized first and third
components and their naturality. (2) The full-triangle comparison, or the existing
`Functor.eTruncGEδLT_comm`, supplies the boundary square with the specified shift.
(3) The right/left truncation adjunctions in lem-weil-heart-short-exact-triangles
characterize the cutoff maps by their counit/unit factorizations; cancel those maps to
obtain the two cutoff squares. (4) TR3 extends the cutoff pair to a triangle morphism;
the left adjunction identifies its third component. Equality of triangle morphisms is
componentwise, giving the full cutoff square. (5) Apply
lem-a1-cohomology-comparison-pasting to the double truncation and shift by r: this puts
both sides in the heart and gives the displayed formula. (6) For exact eta, truncation
naturality gives components one and three, and eta at the middle object gives component
two. Naturality and eta's shift equation give its triangle lift and the full comparison
square. The same cohomology-pasting lemma gives the final eta equation. -/
theorem texact_triangle_cutoff_coherence
    (tC : TStructure C) (tD : TStructure D)
    (_hC : tC.bounded = ⊤) (_hD : tD.bounded = ⊤)
    (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated] [F.IsTExact tC tD] :
    ∃ e : ∀ n : ℤ, tC.triangleLTGE n ⋙ F.mapTriangle ≅ F ⋙ tD.triangleLTGE n,
      (∀ (n : ℤ) (K : C),
        ((e n).hom.app K).hom₁ = (F.eTruncLTIso tC tD (n : ℤ)).hom.app K ∧
        ((e n).hom.app K).hom₂ = 𝟙 (F.obj K) ∧
        ((e n).hom.app K).hom₃ = (F.eTruncGEIso tC tD (n : ℤ)).hom.app K ∧
        (F.eTruncGEIso tC tD (n : ℤ)).hom.app K ≫
            (tD.truncGEδLT n).app (F.obj K) =
          F.map ((tC.truncGEδLT n).app K) ≫
            (F.commShiftIso (1 : ℤ)).hom.app ((tC.truncLT n).obj K) ≫
            (shiftFunctor D (1 : ℤ)).map
              ((F.eTruncLTIso tC tD (n : ℤ)).hom.app K)) ∧
      (∀ (n m : ℤ) (hnm : n ≤ m),
        Functor.whiskerRight (tC.natTransTriangleLTGEOfLE n m hnm) F.mapTriangle ≫
            (e m).hom =
          (e n).hom ≫ Functor.whiskerLeft F (tD.natTransTriangleLTGEOfLE n m hnm)) ∧
      (∀ (r : ℤ) (K : C),
        tC.heart ((tC.truncGELE r r ⋙ shiftFunctor C r).obj K) ∧
        tD.heart (F.obj ((tC.truncGELE r r ⋙ shiftFunctor C r).obj K)) ∧
        tD.heart ((tD.truncGELE r r ⋙ shiftFunctor D r).obj (F.obj K)) ∧
        (truncationCohomologyComparison tC tD F r).hom.app K =
          (F.commShiftIso r).hom.app ((tC.truncGELE r r).obj K) ≫
            (shiftFunctor D r).map
              ((F.eTruncGEIso tC tD (r : ℤ)).hom.app ((tC.truncLE r).obj K) ≫
                (tD.truncGE r).map
                  ((F.eTruncLTIso tC tD (r + 1 : ℤ)).hom.app K))) ∧
      (∀ (G : C ⥤ D) [G.CommShift ℤ] [G.IsTriangulated] [G.IsTExact tC tD]
        (η : F ⟶ G) [NatTrans.CommShift η ℤ]
        (eG : ∀ n : ℤ, tC.triangleLTGE n ⋙ G.mapTriangle ≅ G ⋙ tD.triangleLTGE n),
        (∀ (n : ℤ) (K : C),
          ((eG n).hom.app K).hom₁ = (G.eTruncLTIso tC tD (n : ℤ)).hom.app K ∧
          ((eG n).hom.app K).hom₂ = 𝟙 (G.obj K) ∧
          ((eG n).hom.app K).hom₃ = (G.eTruncGEIso tC tD (n : ℤ)).hom.app K) →
        (∃ ηT : F.mapTriangle ⟶ G.mapTriangle,
          (∀ A : Triangle C, (ηT.app A).hom₁ = η.app A.obj₁ ∧
            (ηT.app A).hom₂ = η.app A.obj₂ ∧ (ηT.app A).hom₃ = η.app A.obj₃) ∧
          ∀ n : ℤ, Functor.whiskerLeft (tC.triangleLTGE n) ηT ≫ (eG n).hom =
            (e n).hom ≫ Functor.whiskerRight η (tD.triangleLTGE n)) ∧
        (∀ (n : ℤ) (K : C),
          η.app ((tC.truncLT n).obj K) ≫ (G.eTruncLTIso tC tD (n : ℤ)).hom.app K =
            (F.eTruncLTIso tC tD (n : ℤ)).hom.app K ≫ (tD.truncLT n).map (η.app K) ∧
          η.app ((tC.truncGE n).obj K) ≫ (G.eTruncGEIso tC tD (n : ℤ)).hom.app K =
            (F.eTruncGEIso tC tD (n : ℤ)).hom.app K ≫ (tD.truncGE n).map (η.app K)) ∧
        ∀ (r : ℤ) (K : C),
          η.app ((tC.truncGELE r r ⋙ shiftFunctor C r).obj K) ≫
              (truncationCohomologyComparison tC tD G r).hom.app K =
            (truncationCohomologyComparison tC tD F r).hom.app K ≫
              (tD.truncGELE r r ⋙ shiftFunctor D r).map (η.app K)) := by
  let e (n : ℤ) : tC.triangleLTGE n ⋙ F.mapTriangle ≅ F ⋙ tD.triangleLTGE n :=
    NatIso.ofComponents (fun K ↦ Triangle.isoMk _ _
      ((F.eTruncLTIso tC tD (n : ℤ)).app K) (Iso.refl _)
      ((F.eTruncGEIso tC tD (n : ℤ)).app K)
      (by simpa using (F.eTruncLTIsoApp_hom_eTruncLTι_app tC tD n K).symm)
      (by simpa using F.eTruncGEπ_app_eTruncGEIsoApp_hom tC tD n K)
      (by simpa [Category.assoc] using F.eTruncGEδLT_comm tC tD n K))
      (by
        intro K L f
        apply Triangle.hom_ext
        · exact (F.eTruncLTIso tC tD (n : ℤ)).hom.naturality f
        · simp
        · exact (F.eTruncGEIso tC tD (n : ℤ)).hom.naturality f)
  have he (n : ℤ) (K : C) :
      ((e n).hom.app K).hom₁ = (F.eTruncLTIso tC tD (n : ℤ)).hom.app K ∧
      ((e n).hom.app K).hom₂ = 𝟙 (F.obj K) ∧
      ((e n).hom.app K).hom₃ = (F.eTruncGEIso tC tD (n : ℤ)).hom.app K :=
    ⟨rfl, rfl, rfl⟩
  refine ⟨e, ?_, ?_, ?_, ?_⟩
  · intro n K
    exact ⟨(he n K).1, (he n K).2.1, (he n K).2.2,
      (F.eTruncGEδLT_comm tC tD n K).symm⟩
  · intro n m hnm
    apply NatTrans.ext
    funext K
    apply Triangle.hom_ext
    · exact F.eTruncLT_map_app_eTruncLTIso_hom_app tC tD
        (homOfLE (show (n : EInt) ≤ (m : EInt) from WithBotTop.coe_le_coe.mpr hnm)) K
    · change F.map (𝟙 K) ≫ 𝟙 _ = 𝟙 _ ≫ 𝟙 _
      simp
    · exact F.eTruncGE_map_app_eTruncGEIso_hom_app tC tD
        (homOfLE (show (n : EInt) ≤ (m : EInt) from WithBotTop.coe_le_coe.mpr hnm)) K
  · exact cohomology_comparison_pasting tC tD F _hC _hD
  · intro G _ _ _ η _ eG heG
    have hη (n : ℤ) (K : C) :
        η.app ((tC.truncLT n).obj K) ≫ (G.eTruncLTIso tC tD (n : ℤ)).hom.app K =
          (F.eTruncLTIso tC tD (n : ℤ)).hom.app K ≫ (tD.truncLT n).map (η.app K) ∧
        η.app ((tC.truncGE n).obj K) ≫ (G.eTruncGEIso tC tD (n : ℤ)).hom.app K =
          (F.eTruncGEIso tC tD (n : ℤ)).hom.app K ≫ (tD.truncGE n).map (η.app K) := by
      have hLE := ((texact_truncation_comparison.{uC, vC, uD, vD, uD, vD}
        tC tD _hC _hD F (n - 1)).2.2.2.1 G η K).1
      have hGE := ((texact_truncation_comparison.{uC, vC, uD, vD, uD, vD}
        tC tD _hC _hD F n).2.2.2.1 G η K).2
      have hn : n - 1 + 1 = n := by omega
      rw [hn] at hLE
      exact ⟨hLE, hGE⟩
    let ηT : F.mapTriangle ⟶ G.mapTriangle :=
      { app := fun A ↦
          { hom₁ := η.app A.obj₁
            hom₂ := η.app A.obj₂
            hom₃ := η.app A.obj₃
            comm₁ := by simp
            comm₂ := by simp
            comm₃ := by
              dsimp
              rw [Category.assoc, NatTrans.shift_app_comm η (1 : ℤ),
                ← Category.assoc, η.naturality]
              simp only [Category.assoc] }
        naturality := by
          intro A B f
          apply Triangle.hom_ext
          · exact η.naturality f.hom₁
          · exact η.naturality f.hom₂
          · exact η.naturality f.hom₃ }
    refine ⟨⟨ηT, fun A ↦ ⟨rfl, rfl, rfl⟩, ?_⟩, hη, ?_⟩
    · intro n
      apply NatTrans.ext
      funext K
      apply Triangle.hom_ext
      · change η.app ((tC.truncLT n).obj K) ≫ ((eG n).hom.app K).hom₁ =
          ((e n).hom.app K).hom₁ ≫ (tD.truncLT n).map (η.app K)
        rw [(heG n K).1, (he n K).1]
        exact (hη n K).1
      · change η.app K ≫ ((eG n).hom.app K).hom₂ =
          ((e n).hom.app K).hom₂ ≫ η.app K
        rw [(heG n K).2.1, (he n K).2.1]
        simp
      · change η.app ((tC.truncGE n).obj K) ≫ ((eG n).hom.app K).hom₃ =
          ((e n).hom.app K).hom₃ ≫ (tD.truncGE n).map (η.app K)
        rw [(heG n K).2.2, (he n K).2.2]
        exact (hη n K).2
    · exact truncationCohomologyComparison_naturality tC tD F _hC _hD G η

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- System associators intertwine both normalized truncations, whole triangles and
shifted heart cohomology; diagonal transitions have identity comparisons.
Source: BBD 1.3.3(i),(ii), 1.3.6, 1.1.9--1.1.10, agent assembly
(blueprint: lem-per-texact-system-triangle-coherence).

The equality `unit` expresses the literal diagonal identity of the node. Its induced
isomorphism only transports the equations across that equality; no arbitrary unit map is
substituted. The two unit laws and pentagon are imposed on the supplied associators.

Proof: (1) apply the composition and transformation clauses of
lem-pod-texact-truncation-comparison to the two transitions and a; substitution gives
both displayed system equations. The identity clause gives the diagonal equations.
(2) Choose the natural full-triangle comparisons from texact_triangle_cutoff_coherence.
Their three components are fixed. Composition of triangles is componentwise; Step 1
identifies components one and three, and the middle component is a. Exactness of a
ensures its triangle lift uses precisely the specified shifts, proving the whole-triangle
identity and composition equations. (3) Apply lem-a1-cohomology-comparison-pasting:
its composition clause followed by its exact-transformation clause at a gives the
cohomology system equation; its identity clause gives the diagonal equation. The
unit equations and exactness of a force the diagonal shift structure to be the canonical
identity one, so the identity transport lifts to the displayed uT. Cutoff
and single-functor transformation compatibility are the preceding theorem. -/
theorem texact_system_triangle_coherence
    {I : Type uI} [PartialOrder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (C : I → Type uC) [∀ i : I, Category.{vC} (C i)]
    [∀ i : I, Preadditive (C i)] [∀ i : I, HasZeroObject (C i)]
    [∀ i : I, HasShift (C i) ℤ]
    [∀ (i : I) (n : ℤ), (shiftFunctor (C i) n).Additive]
    [∀ i : I, Pretriangulated (C i)] [∀ i : I, IsTriangulated (C i)]
    (t : ∀ i : I, TStructure (C i)) (_bounded : ∀ i : I, (t i).bounded = ⊤)
    (T : ∀ (i j : I), i ≤ j → C i ⥤ C j)
    [∀ (i j : I) (hij : i ≤ j), (T i j hij).CommShift ℤ]
    [∀ (i j : I) (hij : i ≤ j), (T i j hij).IsTriangulated]
    [∀ (i j : I) (hij : i ≤ j), (T i j hij).IsTExact (t i) (t j)]
    (unit : ∀ i : I, T i i le_rfl = 𝟭 (C i))
    (a : ∀ (i j k : I) (hij : i ≤ j) (hjk : j ≤ k),
      T i j hij ⋙ T j k hjk ≅ T i k (hij.trans hjk))
    [∀ (i j k : I) (hij : i ≤ j) (hjk : j ≤ k),
      NatTrans.CommShift (a i j k hij hjk).hom ℤ]
    (_unitLeft : ∀ (i j : I) (hij : i ≤ j),
      a i i j le_rfl hij =
        Functor.isoWhiskerRight (eqToIso (unit i)) (T i j hij) ≪≫
          Functor.leftUnitor (T i j hij))
    (_unitRight : ∀ (i j : I) (hij : i ≤ j),
      a i j j hij le_rfl =
        Functor.isoWhiskerLeft (T i j hij) (eqToIso (unit j)) ≪≫
          Functor.rightUnitor (T i j hij))
    (_pentagon : ∀ (i j k l : I) (hij : i ≤ j) (hjk : j ≤ k) (hkl : k ≤ l) (K : C i),
      (T k l hkl).map ((a i j k hij hjk).hom.app K) ≫
          (a i k l (hij.trans hjk) hkl).hom.app K =
        (a j k l hjk hkl).hom.app ((T i j hij).obj K) ≫
          (a i j l hij (hjk.trans hkl)).hom.app K) :
    (∀ (i j k : I) (hij : i ≤ j) (hjk : j ≤ k) (r : ℤ) (K : C i),
      (a i j k hij hjk).hom.app (((t i).truncLE r).obj K) ≫
          ((T i k (hij.trans hjk)).eTruncLTIso (t i) (t k) (r + 1 : ℤ)).hom.app K =
        (T j k hjk).map (((T i j hij).eTruncLTIso (t i) (t j) (r + 1 : ℤ)).hom.app K) ≫
          ((T j k hjk).eTruncLTIso (t j) (t k) (r + 1 : ℤ)).hom.app ((T i j hij).obj K) ≫
          ((t k).truncLE r).map ((a i j k hij hjk).hom.app K) ∧
      (a i j k hij hjk).hom.app (((t i).truncGE r).obj K) ≫
          ((T i k (hij.trans hjk)).eTruncGEIso (t i) (t k) (r : ℤ)).hom.app K =
        (T j k hjk).map (((T i j hij).eTruncGEIso (t i) (t j) (r : ℤ)).hom.app K) ≫
          ((T j k hjk).eTruncGEIso (t j) (t k) (r : ℤ)).hom.app ((T i j hij).obj K) ≫
          ((t k).truncGE r).map ((a i j k hij hjk).hom.app K)) ∧
    (∀ (i : I) (r : ℤ) (K : C i),
      ((T i i le_rfl).eTruncLTIso (t i) (t i) (r + 1 : ℤ)).hom.app K ≫
          ((t i).truncLE r).map ((eqToIso (unit i)).hom.app K) =
        (eqToIso (unit i)).hom.app (((t i).truncLE r).obj K) ∧
      ((T i i le_rfl).eTruncGEIso (t i) (t i) (r : ℤ)).hom.app K ≫
          ((t i).truncGE r).map ((eqToIso (unit i)).hom.app K) =
        (eqToIso (unit i)).hom.app (((t i).truncGE r).obj K)) ∧
    (∃ e : ∀ (i j : I) (hij : i ≤ j) (n : ℤ),
        (t i).triangleLTGE n ⋙ (T i j hij).mapTriangle ≅ T i j hij ⋙ (t j).triangleLTGE n,
      (∀ (i j : I) (hij : i ≤ j) (n : ℤ) (K : C i),
        ((e i j hij n).hom.app K).hom₁ =
            ((T i j hij).eTruncLTIso (t i) (t j) (n : ℤ)).hom.app K ∧
        ((e i j hij n).hom.app K).hom₂ = 𝟙 ((T i j hij).obj K) ∧
        ((e i j hij n).hom.app K).hom₃ =
            ((T i j hij).eTruncGEIso (t i) (t j) (n : ℤ)).hom.app K) ∧
      (∀ (i j : I) (hij : i ≤ j) (n m : ℤ) (hnm : n ≤ m),
        Functor.whiskerRight ((t i).natTransTriangleLTGEOfLE n m hnm)
            (T i j hij).mapTriangle ≫ (e i j hij m).hom =
          (e i j hij n).hom ≫
            Functor.whiskerLeft (T i j hij) ((t j).natTransTriangleLTGEOfLE n m hnm)) ∧
      (∀ i : I, ∃ uT : (T i i le_rfl).mapTriangle ≅ 𝟭 (Triangle (C i)),
        (∀ A : Triangle (C i),
          (uT.hom.app A).hom₁ = (eqToIso (unit i)).hom.app A.obj₁ ∧
          (uT.hom.app A).hom₂ = (eqToIso (unit i)).hom.app A.obj₂ ∧
          (uT.hom.app A).hom₃ = (eqToIso (unit i)).hom.app A.obj₃) ∧
        ∀ (n : ℤ) (K : C i),
          uT.hom.app (((t i).triangleLTGE n).obj K) =
            (e i i le_rfl n).hom.app K ≫
              ((t i).triangleLTGE n).map ((eqToIso (unit i)).hom.app K)) ∧
      ∀ (i j k : I) (hij : i ≤ j) (hjk : j ≤ k) (n : ℤ) (K : C i),
        (Functor.mapTriangleIso (a i j k hij hjk)).hom.app
            (((t i).triangleLTGE n).obj K) ≫ (e i k (hij.trans hjk) n).hom.app K =
          (Functor.mapTriangleCompIso (T i j hij) (T j k hjk)).hom.app
              (((t i).triangleLTGE n).obj K) ≫
            (T j k hjk).mapTriangle.map ((e i j hij n).hom.app K) ≫
            (e j k hjk n).hom.app ((T i j hij).obj K) ≫
            ((t k).triangleLTGE n).map ((a i j k hij hjk).hom.app K)) ∧
    (∀ (i j k : I) (hij : i ≤ j) (hjk : j ≤ k) (r : ℤ) (K : C i),
      (a i j k hij hjk).hom.app (((t i).truncGELE r r ⋙ shiftFunctor (C i) r).obj K) ≫
          (truncationCohomologyComparison (t i) (t k) (T i k (hij.trans hjk)) r).hom.app K =
        (T j k hjk).map
            ((truncationCohomologyComparison (t i) (t j) (T i j hij) r).hom.app K) ≫
          (truncationCohomologyComparison (t j) (t k) (T j k hjk) r).hom.app
            ((T i j hij).obj K) ≫
          ((t k).truncGELE r r ⋙ shiftFunctor (C k) r).map
            ((a i j k hij hjk).hom.app K)) ∧
    (∀ (i : I) (r : ℤ) (K : C i),
      (truncationCohomologyComparison (t i) (t i) (T i i le_rfl) r).hom.app K ≫
          ((t i).truncGELE r r ⋙ shiftFunctor (C i) r).map
            ((eqToIso (unit i)).hom.app K) =
        (eqToIso (unit i)).hom.app (((t i).truncGELE r r ⋙ shiftFunctor (C i) r).obj K)) := by
  classical
  have hcomp (i j k : I) (hij : i ≤ j) (hjk : j ≤ k) (m : ℤ) (K : C i) := by
    let := cohomologyComparison_compTExact (t i) (t j) (t k) (T i j hij) (T j k hjk)
    have hc := ((texact_truncation_comparison.{uC, vC, uC, vC, uC, vC}
      (t i) (t j) (_bounded i) (_bounded j) (T i j hij) m).2.2.2.2.2
      (C k) (t k) (_bounded k) (T j k hjk)
      ((T i j hij ⋙ T j k hjk).eTruncLTIso (t i) (t k) (m + 1 : ℤ))
      ((T i j hij ⋙ T j k hjk).eTruncGEIso (t i) (t k) (m : ℤ))
      (fun X ↦ (T i j hij ⋙ T j k hjk).eTruncLTIsoApp_hom_eTruncLTι_app
        (t i) (t k) (m + 1 : ℤ) X)
      (fun X ↦ (T i j hij ⋙ T j k hjk).eTruncGEπ_app_eTruncGEIsoApp_hom
        (t i) (t k) m X) K)
    have hn := (texact_truncation_comparison.{uC, vC, uC, vC, uC, vC}
      (t i) (t k) (_bounded i) (_bounded k) (T i j hij ⋙ T j k hjk) m).2.2.2.1
        (T i k (hij.trans hjk)) (a i j k hij hjk).hom K
    rw [hc.1, hc.2] at hn
    exact hn
  have hdiag (i : I) (m : ℤ) (K : C i) := by
    let := cohomologyComparison_idTExact (t i)
    have hn := (texact_truncation_comparison.{uC, vC, uC, vC, uC, vC}
      (t i) (t i) (_bounded i) (_bounded i) (T i i le_rfl) m).2.2.2.1
        (𝟭 (C i)) (eqToIso (unit i)).hom K
    have hid := (texact_truncation_comparison.{uC, vC, uC, vC, uC, vC}
      (t i) (t i) (_bounded i) (_bounded i) (𝟭 (C i)) m).2.2.2.2.1
      ((𝟭 (C i)).eTruncLTIso (t i) (t i) (m + 1 : ℤ))
      ((𝟭 (C i)).eTruncGEIso (t i) (t i) (m : ℤ))
      (fun X ↦ (𝟭 (C i)).eTruncLTIsoApp_hom_eTruncLTι_app
        (t i) (t i) (m + 1 : ℤ) X)
      (fun X ↦ (𝟭 (C i)).eTruncGEπ_app_eTruncGEIsoApp_hom (t i) (t i) m X) K
    simp only [eTruncLT_obj_coe, eTruncGE_obj_coe, Functor.comp_obj,
      Functor.id_obj] at hid hn
    rw [hid.1, hid.2] at hn
    simp only [Category.comp_id] at hn
    exact And.intro hn.1.symm hn.2.symm
  have hunitShift (i : I) : NatTrans.CommShift (eqToIso (unit i)).hom ℤ :=
    identity_commShift_of_unit (T i i le_rfl) (unit i) (a i i i le_rfl le_rfl)
      (_unitLeft i i le_rfl)
  choose e he hcut hheart heta using fun (i j : I) (hij : i ≤ j) ↦
    texact_triangle_cutoff_coherence (t i) (t j) (_bounded i) (_bounded j) (T i j hij)
  refine ⟨?_, ?_, ⟨e, ?_, hcut, ?_, ?_⟩, ?_, ?_⟩
  · intro i j k hij hjk r K
    simpa only [truncLE, Category.assoc] using hcomp i j k hij hjk r K
  · intro i r K
    simpa only [truncLE] using hdiag i r K
  · intro i j hij n K
    exact ⟨(he i j hij n K).1, (he i j hij n K).2.1, (he i j hij n K).2.2.1⟩
  · intro i
    let := hunitShift i
    let uT := Functor.mapTriangleIso (eqToIso (unit i)) ≪≫ Functor.mapTriangleIdIso (C i)
    have hu (A : Triangle (C i)) :
        (uT.hom.app A).hom₁ = (eqToIso (unit i)).hom.app A.obj₁ ∧
        (uT.hom.app A).hom₂ = (eqToIso (unit i)).hom.app A.obj₂ ∧
        (uT.hom.app A).hom₃ = (eqToIso (unit i)).hom.app A.obj₃ := by
      simp [uT]
    refine ⟨uT, hu, ?_⟩
    intro n K
    apply Triangle.hom_ext
    · rw [comp_hom₁, (hu _).1, (he i i le_rfl n K).1]
      have hh := (hdiag i (n - 1) K).1
      have hn : n - 1 + 1 = n := by omega
      rw [hn] at hh
      exact hh.symm
    · rw [comp_hom₂, (hu _).2.1, (he i i le_rfl n K).2.1]
      simp
    · rw [comp_hom₃, (hu _).2.2, (he i i le_rfl n K).2.2.1]
      exact (hdiag i n K).2.symm
  · intro i j k hij hjk n K
    apply Triangle.hom_ext
    · simp only [comp_hom₁, Functor.mapTriangleIso_hom_app_hom₁,
        Functor.mapTriangleCompIso_hom_app_hom₁,
        Functor.mapTriangle_map_hom₁, triangleLTGE_map_hom₁,
        (he i k (hij.trans hjk) n K).1, (he i j hij n K).1,
        (he j k hjk n ((T i j hij).obj K)).1]
      have hh := (hcomp i j k hij hjk (n - 1) K).1
      have hn : n - 1 + 1 = n := by omega
      rw [hn] at hh
      dsimp only [triangleLTGE, Triangle.functorMk_obj, Triangle.mk_obj₁,
        Functor.comp_obj, Functor.id_obj]
      erw [Category.id_comp]
      simpa only [Category.assoc] using hh
    · simp [(he i k (hij.trans hjk) n K).2.1,
        (he i j hij n K).2.1, (he j k hjk n ((T i j hij).obj K)).2.1]
    · simp only [comp_hom₃, Functor.mapTriangleIso_hom_app_hom₃,
        Functor.mapTriangleCompIso_hom_app_hom₃,
        Functor.mapTriangle_map_hom₃, triangleLTGE_map_hom₃,
        (he i k (hij.trans hjk) n K).2.2.1, (he i j hij n K).2.2.1,
        (he j k hjk n ((T i j hij).obj K)).2.2.1]
      dsimp only [triangleLTGE, Triangle.functorMk_obj, Triangle.mk_obj₃,
        Functor.comp_obj, Functor.id_obj]
      erw [Category.id_comp]
      simpa only [Category.assoc] using (hcomp i j k hij hjk n K).2
  · intro i j k hij hjk r K
    let := cohomologyComparison_compTExact (t i) (t j) (t k) (T i j hij) (T j k hjk)
    have hn := truncationCohomologyComparison_naturality (t i) (t k)
      (T i j hij ⋙ T j k hjk) (_bounded i) (_bounded k)
      (T i k (hij.trans hjk)) (a i j k hij hjk).hom r K
    rw [truncationCohomologyComparison_comp (t i) (t j) (T i j hij)
      (_bounded i) (_bounded j) (t k) (_bounded k) (T j k hjk)] at hn
    simpa only [Category.assoc] using hn
  · intro i r K
    let := hunitShift i
    let := cohomologyComparison_idTExact (t i)
    have hn := truncationCohomologyComparison_naturality (t i) (t i) (T i i le_rfl)
      (_bounded i) (_bounded i) (𝟭 (C i)) (eqToIso (unit i)).hom r K
    rw [truncationCohomologyComparison_id (t i) (_bounded i)] at hn
    simpa only [Functor.comp_obj, Functor.id_obj, Category.comp_id] using hn.symm

end CategoryTheory.Triangulated.TStructure
