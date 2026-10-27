/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NW
-/
module

public import Sheaf.CategoryTheory.RingedConstantTowerPushforwardNormalization
public import Sheaf.CategoryTheory.DerivedTowerCounitProjections
public import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import all Sheaf.CategoryTheory.RingedConstantTowerPushforwardNormalization
import all Sheaf.CategoryTheory.TowerDerivedEvaluationNormalization
import Mathlib.CategoryTheory.Localization.Predicate

/-!
# Exact tower functors and augmented counit evaluations

Source: blueprint main-20261015, sec-smooth-purity, prop-sf-localization-all-stages,
returned Step 6 / immersion comparison Step 5; Stacks Derived Categories, Tags 015F,
04VG and 09T5, and Cohomology on Sites, Tag 0941
(blueprint: lem-sf-exact-tower-augmented-counit-evaluation).

The four auxiliary maps are the displayed composites a, b, q and p of the node.
All comparisons and transitions reuse the existing exact-localization constructions.
The natural index n denotes positive level n + 1. Composition below is left to right.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe uA vA uB vB wA wB wTA wTB uC vC uD vD rA rB

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.ExactTowerAugmentedCounit

section TransitionLaws

variable (A : Type uA) [Category.{vA} A] [Abelian A]
  [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wTA} (ℕᵒᵖ ⥤ A)]

private theorem transition_id (n : ℕᵒᵖ) :
    towerDerivedEvaluationTransition A (𝟙 n) = 𝟙 _ := by
  simp only [towerDerivedEvaluationTransition, Functor.map_id,
    NatTrans.mapHomologicalComplex_id, Functor.whiskerRight_id', Localization.liftNatTrans_id]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem constant_transition {m n : ℕᵒᵖ} (t : m ⟶ n)
    (K : DerivedCategory A) :
    (ringedConstantTowerEvaluation A m).inv.app K ≫
        (towerDerivedEvaluationTransition A t).app
          ((Functor.const ℕᵒᵖ : A ⥤ _).mapDerivedCategory.obj K) =
      (ringedConstantTowerEvaluation A n).inv.app K := by
  let DA := (Functor.const ℕᵒᵖ : A ⥤ _)
  let d := towerDerivedEvaluationTransition A t
  have heq : Functor.whiskerLeft DA.mapDerivedCategory d ≫
      (ringedConstantTowerEvaluation A n).hom =
        (ringedConstantTowerEvaluation A m).hom := by
    apply Localization.natTrans_ext DerivedCategory.Q (HomologicalComplex.quasiIso A (.up ℤ))
    intro I
    dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app]
    let DC := (DA.mapHomologicalComplex (.up ℤ)).obj I
    let x := DA.mapDerivedCategoryFactors.hom.app I
    let EM := ((evaluation ℕᵒᵖ A).obj m).mapDerivedCategory
    let EN := ((evaluation ℕᵒᵖ A).obj n).mapDerivedCategory
    have hm : (ringedConstantTowerEvaluation A m).hom.app (DerivedCategory.Q.obj I) =
        EM.map x ≫ ((evaluation ℕᵒᵖ A).obj m).mapDerivedCategoryFactors.hom.app DC :=
      (rct_eval_fac A m I).symm
    have hn : (ringedConstantTowerEvaluation A n).hom.app (DerivedCategory.Q.obj I) =
        EN.map x ≫ ((evaluation ℕᵒᵖ A).obj n).mapDerivedCategoryFactors.hom.app DC :=
      (rct_eval_fac A n I).symm
    have hd := d.naturality x
    change EM.map x ≫ d.app (DerivedCategory.Q.obj DC) =
      d.app (DA.mapDerivedCategory.obj (DerivedCategory.Q.obj I)) ≫ EN.map x at hd
    have hf : d.app (DerivedCategory.Q.obj DC) ≫
        ((evaluation ℕᵒᵖ A).obj n).mapDerivedCategoryFactors.hom.app DC =
      ((evaluation ℕᵒᵖ A).obj m).mapDerivedCategoryFactors.hom.app DC := by
      have h := towerTransition_fac A t DC
      have hid : (NatTrans.mapHomologicalComplex ((evaluation ℕᵒᵖ A).map t)
          (.up ℤ)).app DC = 𝟙 I := rfl
      rw [hid] at h
      erw [DerivedCategory.Q.map_id, Category.comp_id] at h
      exact h
    rw [hn, ← Category.assoc, ← hd, Category.assoc, hf, ← hm]
  have h := NatTrans.congr_app heq K
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app] at h
  apply (cancel_mono ((ringedConstantTowerEvaluation A n).hom.app K)).mp
  rw [Category.assoc, h, Iso.inv_hom_id_app, Iso.inv_hom_id_app]

end TransitionLaws

section Maps

variable {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]
  [Abelian A] [Abelian B]
  [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
  [HasDerivedCategory.{wTA} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{wTB} (ℕᵒᵖ ⥤ B)]
  (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- The transported augmentation a = H̃(i) j⁻¹, with the specified canonical j.
Source: blueprint localization Step 6; Stacks 015F
(blueprint: lem-sf-exact-tower-augmented-counit-evaluation). -/
def augmentation {K : DerivedCategory A} {M : DerivedCategory (ℕᵒᵖ ⥤ A)}
    (i : (Functor.const ℕᵒᵖ : A ⥤ _).mapDerivedCategory.obj K ⟶ M) :
    (Functor.const ℕᵒᵖ : B ⥤ _).mapDerivedCategory.obj (F.mapDerivedCategory.obj K) ⟶
      ((Functor.whiskeringRight ℕᵒᵖ A B).obj F).mapDerivedCategory.obj M :=
  (ringedConstantTowerPullback F).inv.app K ≫
    ((Functor.whiskeringRight ℕᵒᵖ A B).obj F).mapDerivedCategory.map i

/-- The actual adjunction transpose b = L'(a) v', without assuming b invertible.
Source: blueprint localization Step 6; Stacks 09T5
(blueprint: lem-sf-exact-tower-augmented-counit-evaluation). -/
def transpose
    {L : DerivedCategory (ℕᵒᵖ ⥤ B) ⥤ DerivedCategory B}
    (adj : (Functor.const ℕᵒᵖ : B ⥤ _).mapDerivedCategory ⊣ L)
    {K : DerivedCategory A} {M : DerivedCategory (ℕᵒᵖ ⥤ A)}
    (i : (Functor.const ℕᵒᵖ : A ⥤ _).mapDerivedCategory.obj K ⟶ M) :
    F.mapDerivedCategory.obj K ⟶
      L.obj (((Functor.whiskeringRight ℕᵒᵖ A B).obj F).mapDerivedCategory.obj M) :=
  adj.unit.app (F.mapDerivedCategory.obj K) ≫ L.map (augmentation F i)

/-- The level map qₙ = eₙ(i) sₙ⁻¹ for an arbitrary derived augmentation.
Source: blueprint localization Step 6; Stacks 015F
(blueprint: lem-sf-exact-tower-augmented-counit-evaluation). -/
def level {K : DerivedCategory A} {M : DerivedCategory (ℕᵒᵖ ⥤ A)}
    (i : (Functor.const ℕᵒᵖ : A ⥤ _).mapDerivedCategory.obj K ⟶ M) (n : ℕ) :
    K ⟶ ((evaluation ℕᵒᵖ A).obj (op n)).mapDerivedCategory.obj M :=
  (ringedConstantTowerEvaluation A (op n)).inv.app K ≫
    ((evaluation ℕᵒᵖ A).obj (op n)).mapDerivedCategory.map i

/-- The normalized target projection pₙ = tₙ π'ₙ for the exact tower functor.
Source: blueprint localization Step 6; Stacks 09T5 and 0941
(blueprint: lem-sf-exact-tower-augmented-counit-evaluation). -/
def projection
    {L : DerivedCategory (ℕᵒᵖ ⥤ B) ⥤ DerivedCategory B}
    (π : ∀ n : ℕ, L ⟶ ((evaluation ℕᵒᵖ B).obj (op n)).mapDerivedCategory)
    (n : ℕ) (M : DerivedCategory (ℕᵒᵖ ⥤ A)) :
    L.obj (((Functor.whiskeringRight ℕᵒᵖ A B).obj F).mapDerivedCategory.obj M) ⟶
      F.mapDerivedCategory.obj (((evaluation ℕᵒᵖ A).obj (op n)).mapDerivedCategory.obj M) :=
  (π n).app (((Functor.whiskeringRight ℕᵒᵖ A B).obj F).mapDerivedCategory.obj M) ≫
    (towerDerivedEvaluationInterchange F (op n)).hom.app M


set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem constant_coherence (n : ℕᵒᵖ) (K : DerivedCategory A) :
    (ringedConstantTowerEvaluation B n).inv.app (F.mapDerivedCategory.obj K) ≫
      ((evaluation ℕᵒᵖ B).obj n).mapDerivedCategory.map
        ((ringedConstantTowerPullback F).inv.app K) ≫
      (towerDerivedEvaluationInterchange F n).hom.app
        ((Functor.const ℕᵒᵖ : A ⥤ _).mapDerivedCategory.obj K) =
    F.mapDerivedCategory.map ((ringedConstantTowerEvaluation A n).inv.app K) := by
  let DA := (Functor.const ℕᵒᵖ : A ⥤ _)
  let EB := (evaluation ℕᵒᵖ B).obj n
  have heq :
      Functor.whiskerRight (ringedConstantTowerPullback F).hom EB.mapDerivedCategory ≫
          Functor.whiskerLeft F.mapDerivedCategory (ringedConstantTowerEvaluation B n).hom =
        Functor.whiskerLeft DA.mapDerivedCategory
            (towerDerivedEvaluationInterchange F n).hom ≫
          Functor.whiskerRight (ringedConstantTowerEvaluation A n).hom
            F.mapDerivedCategory := by
    apply Localization.natTrans_ext DerivedCategory.Q (HomologicalComplex.quasiIso A (.up ℤ))
    intro I
    dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
    let DC := (DA.mapHomologicalComplex (.up ℤ)).obj I
    let FI := (F.mapHomologicalComplex (.up ℤ)).obj I
    let FT := (Functor.whiskeringRight ℕᵒᵖ A B).obj F
    let EA := (evaluation ℕᵒᵖ A).obj n
    let x := DA.mapDerivedCategoryFactors.hom.app I
    let y := F.mapDerivedCategoryFactors.hom.app I
    let z := FT.mapDerivedCategoryFactors.hom.app DC
    let eA := EA.mapDerivedCategoryFactors.hom.app DC
    let TC := (FT.mapHomologicalComplex (.up ℤ)).obj DC
    let BC := ((Functor.const ℕᵒᵖ : B ⥤ _).mapHomologicalComplex (.up ℤ)).obj FI
    let c : TC ⟶ BC :=
      (NatIso.mapHomologicalComplex (Functor.compConstIso ℕᵒᵖ F) (.up ℤ)).inv.app I
    let eB := EB.mapDerivedCategoryFactors.hom.app TC
    let eBC := EB.mapDerivedCategoryFactors.hom.app BC
    let dB := (Functor.const ℕᵒᵖ : B ⥤ _).mapDerivedCategoryFactors.hom.app FI
    have hj : (ringedConstantTowerPullback F).hom.app (DerivedCategory.Q.obj I) ≫
        (Functor.const ℕᵒᵖ : B ⥤ _).mapDerivedCategory.map y ≫ dB =
          FT.mapDerivedCategory.map x ≫ z ≫ DerivedCategory.Q.map c := rct_pull_fac F I
    have hc : EB.mapDerivedCategory.map (DerivedCategory.Q.map c) ≫ eBC = eB := by
      have h := EB.mapDerivedCategoryFactors_hom_naturality c
      have hid : (EB.mapHomologicalComplex (.up ℤ)).map c = 𝟙 FI := rfl
      rw [hid] at h
      erw [DerivedCategory.Q.map_id, Category.comp_id] at h
      exact h
    have hsA : (ringedConstantTowerEvaluation A n).hom.app (DerivedCategory.Q.obj I) =
        EA.mapDerivedCategory.map x ≫ eA := (rct_eval_fac A n I).symm
    have hsB : (ringedConstantTowerEvaluation B n).hom.app
        (F.mapDerivedCategory.obj (DerivedCategory.Q.obj I)) ≫ y =
          EB.mapDerivedCategory.map
            ((Functor.const ℕᵒᵖ : B ⥤ _).mapDerivedCategory.map y) ≫
          EB.mapDerivedCategory.map dB ≫ eBC := by
      have hn := (ringedConstantTowerEvaluation B n).hom.naturality y
      change EB.mapDerivedCategory.map
          ((Functor.const ℕᵒᵖ : B ⥤ _).mapDerivedCategory.map y) ≫
          (ringedConstantTowerEvaluation B n).hom.app (DerivedCategory.Q.obj FI) =
        (ringedConstantTowerEvaluation B n).hom.app
          (F.mapDerivedCategory.obj (DerivedCategory.Q.obj I)) ≫ y at hn
      exact hn.symm.trans (congrArg (fun g ↦ EB.mapDerivedCategory.map
        ((Functor.const ℕᵒᵖ : B ⥤ _).mapDerivedCategory.map y) ≫ g)
          (rct_eval_fac B n FI).symm)
    have ht : (towerDerivedEvaluationInterchange F n).hom.app (DerivedCategory.Q.obj DC) ≫
        F.mapDerivedCategory.map eA ≫ y = EB.mapDerivedCategory.map z ≫ eB :=
      towerInterchange_fac F n DC
    have hn := (towerDerivedEvaluationInterchange F n).hom.naturality x
    change EB.mapDerivedCategory.map (FT.mapDerivedCategory.map x) ≫
        (towerDerivedEvaluationInterchange F n).hom.app (DerivedCategory.Q.obj DC) =
      (towerDerivedEvaluationInterchange F n).hom.app
        (DA.mapDerivedCategory.obj (DerivedCategory.Q.obj I)) ≫
          F.mapDerivedCategory.map (EA.mapDerivedCategory.map x) at hn
    apply (cancel_mono y).mp
    calc
      _ = EB.mapDerivedCategory.map
          ((ringedConstantTowerPullback F).hom.app (DerivedCategory.Q.obj I) ≫
            (Functor.const ℕᵒᵖ : B ⥤ _).mapDerivedCategory.map y ≫ dB) ≫ eBC := by
        simp only [Functor.map_comp, Category.assoc, hsB]
      _ = EB.mapDerivedCategory.map (FT.mapDerivedCategory.map x) ≫
          EB.mapDerivedCategory.map z ≫ eB := by
        rw [hj]
        simp only [Functor.map_comp, Category.assoc, hc]
      _ = EB.mapDerivedCategory.map (FT.mapDerivedCategory.map x) ≫
          (towerDerivedEvaluationInterchange F n).hom.app (DerivedCategory.Q.obj DC) ≫
            F.mapDerivedCategory.map eA ≫ y := by rw [ht]
      _ = _ := by
        rw [← Category.assoc, ← Category.assoc, hn, Category.assoc]
        rw [hsA, F.mapDerivedCategory.map_comp]
        simp only [Category.assoc]
  have h := NatTrans.congr_app heq K
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at h
  apply (cancel_epi ((ringedConstantTowerEvaluation B n).hom.app
    (F.mapDerivedCategory.obj K))).mp
  simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
  apply (cancel_epi (EB.mapDerivedCategory.map
    ((ringedConstantTowerPullback F).hom.app K))).mp
  rw [← Category.assoc, ← Category.assoc, ← EB.mapDerivedCategory.map_comp,
    Iso.hom_inv_id_app, EB.mapDerivedCategory.map_id, Category.id_comp]
  rw [h, Category.assoc, ← F.mapDerivedCategory.map_comp,
    Iso.hom_inv_id_app, F.mapDerivedCategory.map_id]
  erw [Category.comp_id]


set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Exact termwise functors commute with every derived evaluation transition.
 The localization factor equations and naturality determine this square.
 Source: Stacks Tags 015F and 0941
 (blueprint: lem-sf-exact-tower-augmented-counit-evaluation). -/
theorem interchange_transition {m n : ℕᵒᵖ} (t : m ⟶ n)
    (M : DerivedCategory (ℕᵒᵖ ⥤ A)) :
    (towerDerivedEvaluationTransition B t).app
        (((Functor.whiskeringRight ℕᵒᵖ A B).obj F).mapDerivedCategory.obj M) ≫
      (towerDerivedEvaluationInterchange F n).hom.app M =
    (towerDerivedEvaluationInterchange F m).hom.app M ≫
      F.mapDerivedCategory.map ((towerDerivedEvaluationTransition A t).app M) := by
  let FT := (Functor.whiskeringRight ℕᵒᵖ A B).obj F
  let EA (n : ℕᵒᵖ) := (evaluation ℕᵒᵖ A).obj n
  let EB (n : ℕᵒᵖ) := (evaluation ℕᵒᵖ B).obj n
  let dA := towerDerivedEvaluationTransition A t
  let dB := towerDerivedEvaluationTransition B t
  have heq : Functor.whiskerLeft FT.mapDerivedCategory dB ≫
      (towerDerivedEvaluationInterchange F n).hom =
        (towerDerivedEvaluationInterchange F m).hom ≫
          Functor.whiskerRight dA F.mapDerivedCategory := by
    apply Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (.up ℤ))
    intro I
    dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
    let TI := (FT.mapHomologicalComplex (.up ℤ)).obj I
    let z := FT.mapDerivedCategoryFactors.hom.app I
    let am := (EA m).mapDerivedCategoryFactors.hom.app I
    let an := (EA n).mapDerivedCategoryFactors.hom.app I
    let bm := (EB m).mapDerivedCategoryFactors.hom.app TI
    let bn := (EB n).mapDerivedCategoryFactors.hom.app TI
    let fm := F.mapDerivedCategoryFactors.hom.app
      (((EA m).mapHomologicalComplex (.up ℤ)).obj I)
    let fn := F.mapDerivedCategoryFactors.hom.app
      (((EA n).mapHomologicalComplex (.up ℤ)).obj I)
    let q := DerivedCategory.Q.map
      ((NatTrans.mapHomologicalComplex ((evaluation ℕᵒᵖ A).map t) (.up ℤ)).app I)
    have hdn : (EB m).mapDerivedCategory.map z ≫ dB.app (DerivedCategory.Q.obj TI) =
        dB.app (FT.mapDerivedCategory.obj (DerivedCategory.Q.obj I)) ≫
          (EB n).mapDerivedCategory.map z := dB.naturality z
    have hdb : dB.app (DerivedCategory.Q.obj TI) ≫ bn =
        bm ≫ DerivedCategory.Q.map
          ((F.mapHomologicalComplex (.up ℤ)).map
            ((NatTrans.mapHomologicalComplex ((evaluation ℕᵒᵖ A).map t) (.up ℤ)).app I)) :=
      towerTransition_fac B t TI
    have hda : dA.app (DerivedCategory.Q.obj I) ≫ an = am ≫ q :=
      towerTransition_fac A t I
    have hf : F.mapDerivedCategory.map q ≫ fn = fm ≫ DerivedCategory.Q.map
        ((F.mapHomologicalComplex (.up ℤ)).map
          ((NatTrans.mapHomologicalComplex ((evaluation ℕᵒᵖ A).map t) (.up ℤ)).app I)) :=
      F.mapDerivedCategoryFactors_hom_naturality _
    have htm : (towerDerivedEvaluationInterchange F m).hom.app (DerivedCategory.Q.obj I) ≫
        F.mapDerivedCategory.map am ≫ fm = (EB m).mapDerivedCategory.map z ≫ bm :=
      towerInterchange_fac F m I
    have htn : (towerDerivedEvaluationInterchange F n).hom.app (DerivedCategory.Q.obj I) ≫
        F.mapDerivedCategory.map an ≫ fn = (EB n).mapDerivedCategory.map z ≫ bn :=
      towerInterchange_fac F n I
    apply (cancel_mono (F.mapDerivedCategory.map an ≫ fn)).mp
    simp only [Category.assoc]
    rw [htn, ← Category.assoc, ← hdn, Category.assoc, hdb]
    rw [← F.mapDerivedCategory.map_comp_assoc, hda, F.mapDerivedCategory.map_comp]
    rw [Category.assoc, hf]
    have htm' := congrArg (fun g ↦ g ≫ DerivedCategory.Q.map
      ((F.mapHomologicalComplex (.up ℤ)).map
        ((NatTrans.mapHomologicalComplex ((evaluation ℕᵒᵖ A).map t) (.up ℤ)).app I))) htm
    simpa only [Category.assoc] using htm'.symm
  exact NatTrans.congr_app heq M

end Maps

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Simultaneous constant/evaluation coherence, augmented counit identities, all tower
transitions, composite and identity indices, and naturality of b, q and p.

Source: blueprint main-20261015, sec-smooth-purity, prop-sf-localization-all-stages,
returned Step 6 / immersion comparison Step 5; Stacks 015F, 04VG, 09T5 and 0941
(blueprint: lem-sf-exact-tower-augmented-counit-evaluation).

`L, κ` present the specified total derived limit; `_hκ` is its K-injective computation.
`_hadj` fixes the actual canonical counit on K-injective towers, as in
lem-coef-derived-tower-counit-projections. `hπ` identifies the specified natural limit
projections with evaluation of this counit using the canonical constant evaluation.
These are normalizations of the objects fixed in the node, not hypotheses about F.
Site, coefficient and all four derived morphism universes are independent. The
sheafification hypotheses express the small-site abelian module convention.

Proof plan (the nine steps of the DAG):
1. Constants, evaluations and termwise F are exact by levelwise abelianity. Use
   lem-weil-pbc-exact-functor-derived-factorization for their canonical comparisons.
2. On Q of a complex, substitute the iterated localization factorizations into the
   constant/evaluation comparison. Cancel adjacent inverse factors. The result is
   H(s⁻¹). Extend by lem-weil-pbc-localization-universal-property, clauses 2 and 3.
   The same argument identifies the transitions on a constant tower with identities.
3. Localize the ordinary evaluation/termwise-F identity on index arrows. This gives
   tₙ d' = H(d) tₘ. Localizing the index functor laws gives composition and identities.
4. Naturality of the actual counit and the left triangle identity give Δ'(b) ε' = a.
5. Naturality of t at the arbitrary derived arrow i and step 2 give the level formula
   s'⁻¹ e'(a) t = H(q). No strict representative for i is selected.
6. By lem-coef-derived-tower-counit-projections, π' = s'⁻¹ e'(ε'). Naturality of s'
   at b and step 4 identify b π' with s'⁻¹ e'(a). Step 5 gives b p = H(q).
7. Naturality of d' at ε' and its constant-tower identity give π'ₘ d' = π'ₙ.
   Step 3 then gives pₘ H(d) = pₙ, without assuming faithful derived evaluations.
8. Functoriality of H and the index composition and identity laws give the two
   composite-index equalities and the identity-index formula.
9. If i u = Δ(f) i', naturality of j gives aᵢ H̃(u) = Δ'H(f) aᵢ'. Naturality
   of the unit gives the b square. Naturality of s gives the q square; naturality
   of the specified π' and t gives the p square. Products need not be preserved. -/
theorem exact_tower_augmented_counit_evaluation
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{rA} C]
    {D : Type uD} [Category.{vD} D] [EssentiallySmall.{rB} D]
    {J : GrothendieckTopology C} {J' : GrothendieckTopology D}
    [HasSheafify J AddCommGrpCat.{rA}] [J.WEqualsLocallyBijective AddCommGrpCat.{rA}]
    [HasSheafify J' AddCommGrpCat.{rB}] [J'.WEqualsLocallyBijective AddCommGrpCat.{rB}]
    (R : Sheaf J RingCat.{rA}) (S : Sheaf J' RingCat.{rB})
    (_hR : ∀ (U : Cᵒᵖ) (a b : R.obj.obj U), a * b = b * a)
    (_hS : ∀ (U : Dᵒᵖ) (a b : S.obj.obj U), a * b = b * a)
    [HasDerivedCategory.{wA} (ringedSiteModules.{rA} R)]
    [HasDerivedCategory.{wB} (ringedSiteModules.{rB} S)]
    [HasDerivedCategory.{wTA} (ℕᵒᵖ ⥤ ringedSiteModules.{rA} R)]
    [HasDerivedCategory.{wTB} (ℕᵒᵖ ⥤ ringedSiteModules.{rB} S)]
    (F : ringedSiteModules.{rA} R ⥤ ringedSiteModules.{rB} S)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [HasLimitsOfShape ℕᵒᵖ (ringedSiteModules.{rB} S)]
    (L : DerivedCategory (ℕᵒᵖ ⥤ ringedSiteModules.{rB} S) ⥤
      DerivedCategory (ringedSiteModules.{rB} S))
    (κ : (lim :
        (ℕᵒᵖ ⥤ ringedSiteModules.{rB} S) ⥤ ringedSiteModules.{rB} S).mapHomologicalComplex
        (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ L)
    [L.IsRightDerivedFunctor κ
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ ringedSiteModules.{rB} S) (.up ℤ))]
    (_hκ : ∀ I : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{rB} S) ℤ,
      I.IsKInjective → IsIso (κ.app I))
    (adj : (Functor.const ℕᵒᵖ : ringedSiteModules.{rB} S ⥤ _).mapDerivedCategory ⊣ L)
    (_hadj : ∀ I : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{rB} S) ℤ,
      I.IsKInjective →
      (Functor.const ℕᵒᵖ : ringedSiteModules.{rB} S ⥤ _).mapDerivedCategory.map
          (κ.app I) ≫ adj.counit.app (DerivedCategory.Q.obj I) =
        (Functor.const ℕᵒᵖ : ringedSiteModules.{rB} S ⥤ _).mapDerivedCategoryFactors.hom.app
          (((lim :
            (ℕᵒᵖ ⥤ ringedSiteModules.{rB} S) ⥤ ringedSiteModules.{rB} S).mapHomologicalComplex
            (.up ℤ)).obj I) ≫
          DerivedCategory.Q.map
            (((constLimAdj :
              (Functor.const ℕᵒᵖ : ringedSiteModules.{rB} S ⥤ _) ⊣ lim).mapHomologicalComplex
              (.up ℤ)).counit.app I))
    (π : ∀ n : ℕ, L ⟶
      ((evaluation ℕᵒᵖ (ringedSiteModules.{rB} S)).obj (op n)).mapDerivedCategory)
    (hπ : ∀ (n : ℕ) (N : DerivedCategory (ℕᵒᵖ ⥤ ringedSiteModules.{rB} S)),
      ((evaluation ℕᵒᵖ (ringedSiteModules.{rB} S)).obj (op n)).mapDerivedCategory.map
          (adj.counit.app N) =
        (ringedConstantTowerEvaluation (ringedSiteModules.{rB} S) (op n)).hom.app (L.obj N) ≫
          (π n).app N) :
    (∀ (n : ℕ) (K : DerivedCategory (ringedSiteModules.{rA} R)),
      (ringedConstantTowerEvaluation (ringedSiteModules.{rB} S) (op n)).inv.app
          (F.mapDerivedCategory.obj K) ≫
        ((evaluation ℕᵒᵖ (ringedSiteModules.{rB} S)).obj (op n)).mapDerivedCategory.map
          ((ringedConstantTowerPullback F).inv.app K) ≫
        (towerDerivedEvaluationInterchange F (op n)).hom.app
          ((Functor.const ℕᵒᵖ : ringedSiteModules.{rA} R ⥤ _).mapDerivedCategory.obj K) =
      F.mapDerivedCategory.map
        ((ringedConstantTowerEvaluation (ringedSiteModules.{rA} R) (op n)).inv.app K)) ∧
    (∀ (m n : ℕ) (h : n ≤ m)
      (M : DerivedCategory (ℕᵒᵖ ⥤ ringedSiteModules.{rA} R)),
      (towerDerivedEvaluationTransition (ringedSiteModules.{rB} S) (homOfLE h).op).app
          (((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapDerivedCategory.obj M) ≫
        (towerDerivedEvaluationInterchange F (op n)).hom.app M =
      (towerDerivedEvaluationInterchange F (op m)).hom.app M ≫
        F.mapDerivedCategory.map
          ((towerDerivedEvaluationTransition (ringedSiteModules.{rA} R) (homOfLE h).op).app M)) ∧
    (∀ (K : DerivedCategory (ringedSiteModules.{rA} R))
      (M : DerivedCategory (ℕᵒᵖ ⥤ ringedSiteModules.{rA} R))
      (i : (Functor.const ℕᵒᵖ : ringedSiteModules.{rA} R ⥤ _).mapDerivedCategory.obj K ⟶ M),
      ((Functor.const ℕᵒᵖ : ringedSiteModules.{rB} S ⥤ _).mapDerivedCategory.map
          (transpose F adj i) ≫ adj.counit.app
          (((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapDerivedCategory.obj M) =
        augmentation F i) ∧
      (∀ n : ℕ,
        (ringedConstantTowerEvaluation (ringedSiteModules.{rB} S) (op n)).inv.app
            (F.mapDerivedCategory.obj K) ≫
          ((evaluation ℕᵒᵖ (ringedSiteModules.{rB} S)).obj (op n)).mapDerivedCategory.map
            (augmentation F i) ≫
          (towerDerivedEvaluationInterchange F (op n)).hom.app M =
        F.mapDerivedCategory.map (level i n)) ∧
      (∀ n : ℕ, transpose F adj i ≫ projection F π n M =
        F.mapDerivedCategory.map (level i n))) ∧
    (∀ (m n : ℕ) (h : n ≤ m)
      (M : DerivedCategory (ℕᵒᵖ ⥤ ringedSiteModules.{rA} R)),
      projection F π m M ≫ F.mapDerivedCategory.map
          ((towerDerivedEvaluationTransition (ringedSiteModules.{rA} R) (homOfLE h).op).app M) =
        projection F π n M) ∧
    (∀ (m n r : ℕ) (hnm : n ≤ m) (hrn : r ≤ n)
      (M : DerivedCategory (ℕᵒᵖ ⥤ ringedSiteModules.{rA} R)),
      (projection F π m M ≫ F.mapDerivedCategory.map
          ((towerDerivedEvaluationTransition (ringedSiteModules.{rA} R) (homOfLE hnm).op).app M) ≫
        F.mapDerivedCategory.map
          ((towerDerivedEvaluationTransition (ringedSiteModules.{rA} R) (homOfLE hrn).op).app M) =
        projection F π m M ≫ F.mapDerivedCategory.map
          ((towerDerivedEvaluationTransition (ringedSiteModules.{rA} R)
            (homOfLE (hrn.trans hnm)).op).app M)) ∧
      (projection F π m M ≫ F.mapDerivedCategory.map
          ((towerDerivedEvaluationTransition (ringedSiteModules.{rA} R)
            (homOfLE (hrn.trans hnm)).op).app M) = projection F π r M)) ∧
    (∀ (n : ℕ) (M : DerivedCategory (ℕᵒᵖ ⥤ ringedSiteModules.{rA} R)),
      ((towerDerivedEvaluationTransition (ringedSiteModules.{rA} R) (𝟙 (op n))).app M =
        𝟙 _) ∧
      (projection F π n M ≫ F.mapDerivedCategory.map
          ((towerDerivedEvaluationTransition (ringedSiteModules.{rA} R) (𝟙 (op n))).app M) =
        projection F π n M)) ∧
    (∀ (K K' : DerivedCategory (ringedSiteModules.{rA} R))
      (M M' : DerivedCategory (ℕᵒᵖ ⥤ ringedSiteModules.{rA} R))
      (f : K ⟶ K') (u : M ⟶ M')
      (i : (Functor.const ℕᵒᵖ : ringedSiteModules.{rA} R ⥤ _).mapDerivedCategory.obj K ⟶ M)
      (i' : (Functor.const ℕᵒᵖ : ringedSiteModules.{rA} R ⥤ _).mapDerivedCategory.obj K' ⟶ M')
      (_hu : i ≫ u =
        (Functor.const ℕᵒᵖ : ringedSiteModules.{rA} R ⥤ _).mapDerivedCategory.map f ≫ i'),
      (transpose F adj i ≫
          L.map (((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapDerivedCategory.map u) =
        F.mapDerivedCategory.map f ≫ transpose F adj i') ∧
      (∀ n : ℕ, level i n ≫
          ((evaluation ℕᵒᵖ (ringedSiteModules.{rA} R)).obj (op n)).mapDerivedCategory.map u =
        f ≫ level i' n) ∧
      (∀ n : ℕ, projection F π n M ≫ F.mapDerivedCategory.map
          (((evaluation ℕᵒᵖ (ringedSiteModules.{rA} R)).obj (op n)).mapDerivedCategory.map u) =
        L.map (((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapDerivedCategory.map u) ≫
          projection F π n M')) := by
  let A := ringedSiteModules.{rA} R
  let B := ringedSiteModules.{rB} S
  let H := F.mapDerivedCategory
  let T := ((Functor.whiskeringRight ℕᵒᵖ A B).obj F).mapDerivedCategory
  let DA := (Functor.const ℕᵒᵖ : A ⥤ _).mapDerivedCategory
  let DB := (Functor.const ℕᵒᵖ : B ⥤ _).mapDerivedCategory
  let EA (n : ℕ) := ((evaluation ℕᵒᵖ A).obj (op n)).mapDerivedCategory
  let EB (n : ℕ) := ((evaluation ℕᵒᵖ B).obj (op n)).mapDerivedCategory
  let sA (n : ℕ) := ringedConstantTowerEvaluation A (op n)
  let sB (n : ℕ) := ringedConstantTowerEvaluation B (op n)
  let t (n : ℕ) := towerDerivedEvaluationInterchange F (op n)
  have hε (K : DerivedCategory A) (M : DerivedCategory (ℕᵒᵖ ⥤ A))
      (i : DA.obj K ⟶ M) :
      DB.map (transpose F adj i) ≫ adj.counit.app (T.obj M) = augmentation F i := by
    exact (adj.homEquiv _ _).symm_apply_apply (augmentation F i)
  have hl (K : DerivedCategory A) (M : DerivedCategory (ℕᵒᵖ ⥤ A))
      (i : DA.obj K ⟶ M) (n : ℕ) :
      (sB n).inv.app (H.obj K) ≫ (EB n).map (augmentation F i) ≫
        (t n).hom.app M = H.map (level i n) := by
    dsimp only [augmentation, level]
    rw [(EB n).map_comp, Category.assoc]
    have hn := (t n).hom.naturality i
    change (EB n).map (T.map i) ≫ (t n).hom.app M =
      (t n).hom.app (DA.obj K) ≫ H.map ((EA n).map i) at hn
    rw [hn]
    have hc := congrArg (fun g ↦ g ≫ H.map ((EA n).map i))
      (constant_coherence F (op n) K)
    simpa only [Category.assoc, H.map_comp] using hc
  have hp (n : ℕ) (N : DerivedCategory (ℕᵒᵖ ⥤ B)) :
      (π n).app N = (sB n).inv.app (L.obj N) ≫ (EB n).map (adj.counit.app N) := by
    have hn := congrArg (fun g ↦ (sB n).inv.app (L.obj N) ≫ g) (hπ n N)
    dsimp only [sB, B] at hn ⊢
    simpa only [Category.assoc, Iso.inv_hom_id_app_assoc] using hn.symm
  have hbp (K : DerivedCategory A) (M : DerivedCategory (ℕᵒᵖ ⥤ A))
      (i : DA.obj K ⟶ M) (n : ℕ) :
      transpose F adj i ≫ projection F π n M = H.map (level i n) := by
    dsimp only [projection]
    rw [hp, ← Category.assoc, ← Category.assoc]
    have hn := (sB n).inv.naturality (transpose F adj i)
    change transpose F adj i ≫ (sB n).inv.app (L.obj (T.obj M)) =
      (sB n).inv.app (H.obj K) ≫ (EB n).map (DB.map (transpose F adj i)) at hn
    rw [hn, Category.assoc, Category.assoc, ← (EB n).map_comp_assoc, hε]
    exact hl K M i n
  have hπt (m n : ℕ) (h : n ≤ m) (N : DerivedCategory (ℕᵒᵖ ⥤ B)) :
      (π m).app N ≫ (towerDerivedEvaluationTransition B (homOfLE h).op).app N =
        (π n).app N := by
    rw [hp, hp, Category.assoc]
    have hn := (towerDerivedEvaluationTransition B (homOfLE h).op).naturality
      (adj.counit.app N)
    dsimp only [Functor.id_obj, Functor.comp_obj] at hn
    rw [hn, ← Category.assoc, constant_transition]
  have hpt (m n : ℕ) (h : n ≤ m) (M : DerivedCategory (ℕᵒᵖ ⥤ A)) :
      projection F π m M ≫ H.map
          ((towerDerivedEvaluationTransition A (homOfLE h).op).app M) =
        projection F π n M := by
    dsimp only [projection]
    rw [Category.assoc, ← interchange_transition F, ← Category.assoc, hπt]
  refine ⟨fun n K ↦ constant_coherence F (op n) K,
    fun m n h M ↦ interchange_transition F (homOfLE h).op M,
    fun K M i ↦ ⟨hε K M i, hl K M i, hbp K M i⟩, hpt, ?_, ?_, ?_⟩
  · intro m n r hnm hrn M
    constructor
    · calc
        _ = projection F π n M ≫ F.mapDerivedCategory.map
            ((towerDerivedEvaluationTransition A (homOfLE hrn).op).app M) := by
          erw [← Category.assoc, hpt m n hnm]
        _ = projection F π r M := hpt n r hrn M
        _ = _ := (hpt m r (hrn.trans hnm) M).symm
    · exact hpt m r (hrn.trans hnm) M
  · intro n M
    have hid : (towerDerivedEvaluationTransition A (𝟙 (op n))).app M = 𝟙 _ :=
      NatTrans.congr_app (transition_id A (op n)) M
    refine ⟨hid, ?_⟩
    change projection F π n M ≫ H.map
      ((towerDerivedEvaluationTransition A (𝟙 (op n))).app M) = _
    rw [hid, H.map_id, Category.comp_id]
  · intro K K' M M' f u i i' hu
    have ha : augmentation F i ≫ T.map u =
        DB.map (H.map f) ≫ augmentation F i' := by
      dsimp only [augmentation]
      rw [Category.assoc, ← T.map_comp, hu, T.map_comp, ← Category.assoc]
      have hn := (ringedConstantTowerPullback F).inv.naturality f
      change DB.map (H.map f) ≫ (ringedConstantTowerPullback F).inv.app K' =
        (ringedConstantTowerPullback F).inv.app K ≫ T.map (DA.map f) at hn
      rw [← hn, Category.assoc]
    refine ⟨?_, ?_, ?_⟩
    · dsimp only [transpose]
      rw [Category.assoc, ← L.map_comp, ha, L.map_comp, ← Category.assoc]
      have hn := adj.unit.naturality (H.map f)
      change H.map f ≫ adj.unit.app (H.obj K') =
        adj.unit.app (H.obj K) ≫ L.map (DB.map (H.map f)) at hn
      rw [← hn, Category.assoc]
    · intro n
      dsimp only [level]
      rw [Category.assoc, ← (EA n).map_comp, hu, (EA n).map_comp, ← Category.assoc]
      have hn := (sA n).inv.naturality f
      change f ≫ (sA n).inv.app K' =
        (sA n).inv.app K ≫ (EA n).map (DA.map f) at hn
      rw [← hn, Category.assoc]
    · intro n
      dsimp only [projection]
      have hn := (t n).hom.naturality u
      change (EB n).map (T.map u) ≫ (t n).hom.app M' =
        (t n).hom.app M ≫ H.map ((EA n).map u) at hn
      rw [Category.assoc, ← hn, ← Category.assoc, ← (π n).naturality,
        Category.assoc]

end CategoryTheory.ExactTowerAugmentedCounit
