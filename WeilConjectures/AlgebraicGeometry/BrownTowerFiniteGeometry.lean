/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Brown.EtaleBrownGeometricComparisons
import all WeilConjectures.AlgebraicGeometry.Etale.Brown.EtaleBrownLevelComparisons
import all WeilConjectures.AlgebraicGeometry.Etale.Brown.EtaleBrownGeometricComparisons

/-! # Finite coefficient geometry over arbitrary schemes

Source: Zheng, Constructions 4.1 and 5.14--5.15, Lemmas 5.13 and 5.16.
The finite-field datum in the earlier wrapper is unused by this construction.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite SheafOfModules
namespace AlgebraicGeometry
attribute [local instance 5000] strictEtaleSystemDerived strictEtaleLevelDerived
attribute [local instance] CoefficientSystemOrdinaryImage.inverseAdditive
  CoefficientSystemOrdinaryImage.rightAdditive
  CoefficientSystemOrdinaryImage.systemInverseAdditive
  CoefficientSystemOrdinaryImage.systemRightAdditive

private theorem finiteLevelComparisons
    (O : Type (u + 1)) [CommRing O] (t : O)
    (hfinite : ∀ n : ℕ, Finite (strictEtaleBrownRing O t n))
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (S : StrictEtaleCompactSupport O t c) :
    ∃ (realizationX : StrictEtaleBrownRealization O t X S.PX)
      (realizationZ : StrictEtaleBrownRealization O t c.Z S.PZ)
      (realizationY : StrictEtaleBrownRealization O t Y S.PY)
      (properRealization : ∀ n, StrictEtaleBrownImageRealization O t c.g n
    S.properImage (S.properDerived.level n) realizationZ realizationY)
      (openRealization : ∀ n, StrictEtaleBrownImageRealization O t c.i n
    S.openImage (S.openDerived.level n) realizationX realizationZ)
      (openComparison : ∀ n, S.levelDerivedOpen n ⋙ realizationZ.derived n ≅
    realizationX.derived n ⋙
      (Etale.openImmersionLowerShriek
        (ModuleCat.{u + 1} (strictEtaleBrownRing O t n)) c.i).mapDerivedCategory)
      (openProjection : ∀ {m n : ℕ} (h : m ≤ n),
    (S.PX.scalar h).derived ⋙ S.levelDerivedOpen m ≅
      S.levelDerivedOpen n ⋙ (S.PZ.scalar h).derived)
      (properProjection : ∀ {m n : ℕ} (h : m ≤ n),
    (S.PZ.scalar h).derived ⋙ (S.properDerived.level m).direct ≅
      (S.properDerived.level n).direct ⋙ (S.PY.scalar h).derived),
      (∀ n,
    (mateEquiv (S.levelDerivedOpenAdjunction n)
      (((Etale.openImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} (strictEtaleBrownRing O t n))
        c.i).mapDerivedCategoryRightDerivedAdjunction).ofNatIsoRight
          (Etale.upperStar (ModuleCat.{u + 1} (strictEtaleBrownRing O t n))
            c.i).rightDerivedFunctorIsoMapDerivedCategory)
      (.mk _ _ _ _ (openComparison n).inv)).natTrans = (openRealization n).inverse.inv) ∧
      (∀ {m n : ℕ} (h : m ≤ n),
    (mateEquiv (S.levelDerivedOpenAdjunction n) (S.levelDerivedOpenAdjunction m)
      (.mk _ _ _ _ (openProjection h).hom)).natTrans = (S.openDerived.derivedTensor h).inv) ∧
      (∀ {m n : ℕ} (h : m ≤ n),
    (properProjection h).inv =
      (mateEquiv (S.properDerived.level n).adjunction (S.properDerived.level m).adjunction
        (.mk _ _ _ _ (S.properDerived.derivedTensor h).hom)).natTrans) ∧
      (let levelComparison (n : ℕ) :
          S.levelFunctor n ⋙ realizationY.derived n ≅
            realizationX.derived n ⋙ Etale.rightDerivedLowerShriekOfCompactification
              (ModuleCat.{u + 1} (strictEtaleBrownRing O t n)) c :=
        Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ (properRealization n).right ≪≫
          (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight (openComparison n) _ ≪≫
          Functor.associator _ _ _
      let projection {m n : ℕ} (h : m ≤ n) :
          (S.PX.scalar h).derived ⋙ S.levelFunctor m ≅
            S.levelFunctor n ⋙ (S.PY.scalar h).derived :=
        (Functor.associator _ _ _).symm ≪≫
          isoWhiskerRight (openProjection h) _ ≪≫ Functor.associator _ _ _ ≪≫
          isoWhiskerLeft _ (properProjection h) ≪≫ (Functor.associator _ _ _).symm
      ∀ {m n : ℕ} (h : m ≤ n)
    (P : DerivedCategory (strictEtaleLevel X O t n)),
    (Etale.scalarExtension (strictEtaleBrownRingMap O t h) Y).map
        ((levelComparison n).inv.app P) ≫
      (realizationY.scalar h).inv.app ((S.levelFunctor n).obj P) ≫
      (realizationY.derived m).map ((projection h).inv.app P) ≫
      (levelComparison m).hom.app ((S.PX.scalar h).derived.obj P) ≫
      (Etale.rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} (strictEtaleBrownRing O t m)) c).map
          ((realizationX.scalar h).hom.app P) =
    (Etale.compactScalarMap (strictEtaleBrownRingMap O t h) c).app
      ((realizationX.derived n).obj P)) := by
  classical
  obtain ⟨RX⟩ := etaleBrownLevelRealization_exists O t X S.PX
  obtain ⟨RZ⟩ := etaleBrownLevelRealization_exists O t c.Z S.PZ
  obtain ⟨RY⟩ := etaleBrownLevelRealization_exists O t Y S.PY
  let rp (n : ℕ) := (etaleBrownImageRealization_exists O t c.g n S.properImage
    (S.properDerived.level n) RZ RY).some
  let ro (n : ℕ) := (etaleBrownImageRealization_exists O t c.i n S.openImage
    (S.openDerived.level n) RX RZ).some
  let : ∀ n, (RX.derived n).IsEquivalence := RX.val.equivalence
  let : ∀ n, (RZ.derived n).IsEquivalence := RZ.val.equivalence
  let a (n : ℕ) :=
    ((Etale.openImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} (strictEtaleBrownRing O t n))
      c.i).mapDerivedCategoryRightDerivedAdjunction).ofNatIsoRight
      (Etale.upperStar (ModuleCat.{u + 1} (strictEtaleBrownRing O t n))
        c.i).rightDerivedFunctorIsoMapDerivedCategory
  let jo (n : ℕ) := inverseMateIso (S.levelDerivedOpenAdjunction n) (a n)
    (ro n).inverse.symm
  have hjo (n : ℕ) :
      (mateEquiv (S.levelDerivedOpenAdjunction n) (a n)
        (.mk _ _ _ _ (jo n).inv)).natTrans = (ro n).inverse.inv :=
    inverseMateIso_mate _ _ _
  have hp {m n : ℕ} (h : m ≤ n) :=
    letI := hfinite n
    etaleBrownProperScalarTransport O t c.g S.properImage S.PY S.PZ
      S.properDerived RZ RY rp h
  let pp {m n : ℕ} (h : m ≤ n) := (hp h).choose
  have hpp {m n : ℕ} (h : m ≤ n) := (hp h).choose_spec.1
  have hproper {m n : ℕ} (h : m ≤ n) := (hp h).choose_spec.2
  have ho {m n : ℕ} (h : m ≤ n) :=
    etaleBrownOpenScalarTransport O t c S RX RZ ro jo hjo h
  let op {m n : ℕ} (h : m ≤ n) := (ho h).choose
  have hop {m n : ℕ} (h : m ≤ n) := (ho h).choose_spec.1
  have hopen {m n : ℕ} (h : m ≤ n) := (ho h).choose_spec.2
  refine ⟨RX, RZ, RY, rp, ro, jo, @op, @pp, hjo, @hop, @hpp, ?_⟩
  let lc (n : ℕ) : S.levelFunctor n ⋙ RY.derived n ≅
      RX.derived n ⋙ Etale.rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} (strictEtaleBrownRing O t n)) c :=
    Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ (rp n).right ≪≫
      (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight (jo n) _ ≪≫
      Functor.associator _ _ _
  let q {m n : ℕ} (h : m ≤ n) : (S.PX.scalar h).derived ⋙ S.levelFunctor m ≅
      S.levelFunctor n ⋙ (S.PY.scalar h).derived :=
    (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight (op h) _ ≪≫
      Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ (pp h) ≪≫
      (Functor.associator _ _ _).symm
  change ∀ {m n : ℕ} (h : m ≤ n)
    (P : DerivedCategory (strictEtaleLevel X O t n)),
    (Etale.scalarExtension (strictEtaleBrownRingMap O t h) Y).map ((lc n).inv.app P) ≫
      (RY.scalar h).inv.app ((S.levelFunctor n).obj P) ≫
      (RY.derived m).map ((q h).inv.app P) ≫
      (lc m).hom.app ((S.PX.scalar h).derived.obj P) ≫
      (Etale.rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} (strictEtaleBrownRing O t m)) c).map
        ((RX.scalar h).hom.app P) =
      (Etale.compactScalarMap (strictEtaleBrownRingMap O t h) c).app
        ((RX.derived n).obj P)
  intro m n h P
  have hsquare :
      (RY.derived m).map ((q h).inv.app P) ≫
        (lc m).hom.app ((S.PX.scalar h).derived.obj P) ≫
        (Etale.rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} (strictEtaleBrownRing O t m)) c).map
          ((RX.scalar h).hom.app P) =
      (RY.scalar h).hom.app ((S.levelFunctor n).obj P) ≫
        (Etale.scalarExtension (strictEtaleBrownRingMap O t h) Y).map
          ((lc n).hom.app P) ≫
        (Etale.compactScalarMap (strictEtaleBrownRingMap O t h) c).app
          ((RX.derived n).obj P) := by
    have hn := (rp m).right.hom.naturality ((op h).inv.app P)
    have ht := (Etale.scalarMate (strictEtaleBrownRingMap O t h) c.g).naturality
      ((jo n).hom.app P)
    -- Expose the subtype interfaces before expanding their projections.
    unfold StrictEtaleCompactSupport at S
    unfold StrictEtaleBrownRealization at RX RZ RY
    unfold StrictEtaleBrownImageRealization at rp ro
    dsimp +instances only [Functor.comp_map, Functor.comp_obj] at hn ht
    dsimp +instances only [q, lc, StrictEtaleCompactSupport.levelFunctor,
      Etale.compactScalarMap,
      Etale.ExceptionalCoefficients.compactSupportMap,
      Etale.rightDerivedLowerShriekOfCompactification]
    simp +instances only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
      NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
      Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Functor.map_comp,
      Category.id_comp, Category.comp_id, Functor.comp_map,
      Functor.comp_obj, Category.assoc]
    rw [reassoc_of% hn]
    simp +instances only [← Functor.map_comp]
    rw [hopen h P]
    simp only [Functor.map_comp]
    rw [reassoc_of% (hproper h ((S.val.levelDerivedOpen n).obj P))]
    rw [← reassoc_of% ht]
  rw [hsquare]
  simp only [Iso.inv_hom_id_app_assoc]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app,
    _root_.CategoryTheory.Functor.map_id, Category.id_comp]


/-- Finite coefficient geometry for the given compact-support presentation.
Source: Zheng, Constructions 4.1 and 5.14--5.15, Lemmas 5.13 and 5.16.
(blueprint: lem-route-brown-tower-finite-geometry).

Proof: choose the normalized constant-scalar realizations and image comparisons.
Take the inverse mate of open inverse image, and the proper and open scalar mates.
Finiteness makes the proper scalar mate invertible. Paste these comparisons.
Conjugate the inverse-image evaluation squares to construct singleton insertion.
The proper singleton mate is invertible below its index by the proper projection,
and above its index because both evaluations vanish; evaluations jointly detect
isomorphisms. Paste with open insertion. The two singleton evaluation formulas
and naturality give the stated below-index formula. These arguments use only
finite quotient coefficients and a compactification, with no base-field datum. -/
theorem brownTowerFiniteGeometry_exists
    (O : Type (u + 1)) [CommRing O] (t : O)
    (hfinite : ∀ n : ℕ, Finite (strictEtaleBrownRing O t n))
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (S : StrictEtaleCompactSupport O t c) :
    Nonempty (StrictEtaleBrownGeometry O t c S) := by
  obtain ⟨RX, RZ, RY, rp, ro, jo, op, pp, hjo, hop, hpp, hrecord⟩ :=
    finiteLevelComparisons O t hfinite c S
  let lc (n : ℕ) : S.levelFunctor n ⋙ RY.derived n ≅
      RX.derived n ⋙ Etale.rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} (strictEtaleBrownRing O t n)) c :=
    Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ (rp n).right ≪≫
      (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight (jo n) _ ≪≫
      Functor.associator _ _ _
  let q {m n : ℕ} (h : m ≤ n) : (S.PX.scalar h).derived ⋙ S.levelFunctor m ≅
      S.levelFunctor n ⋙ (S.PY.scalar h).derived :=
    (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (op h) _ ≪≫ Functor.associator _ _ _ ≪≫
      isoWhiskerLeft _ (pp h) ≪≫ (Functor.associator _ _ _).symm
  have hproper {m n : ℕ} (h : m ≤ n)
      (P : DerivedCategory (strictEtaleLevel c.Z O t n)) :
      (S.PY.evaluation m).map ((strictEtaleBrownProperInsertionMap O t c S n).app P) ≫
        (S.properDerived.directEvaluation m).hom.app ((S.PZ.derivedExtension n).obj P) ≫
        (S.properDerived.level m).direct.map ((S.PZ.derivedBelow h).hom.app P) =
      (S.PY.derivedBelow h).hom.app ((S.properDerived.level n).direct.obj P) ≫
        (pp h).inv.app P := by
    exact etaleBrownProperSingletonEvaluation O t c S h (pp h) (hpp h) P
  have hbelow (n m : ℕ) (h : m ≤ n)
      (P : DerivedCategory (strictEtaleLevel c.Z O t n)) :
      IsIso ((S.PY.evaluation m).map
        ((strictEtaleBrownProperInsertionMap O t c S n).app P)) := by
    have hi : IsIso
        ((S.PY.evaluation m).map ((strictEtaleBrownProperInsertionMap O t c S n).app P) ≫
          (S.properDerived.directEvaluation m).hom.app ((S.PZ.derivedExtension n).obj P) ≫
          (S.properDerived.level m).direct.map ((S.PZ.derivedBelow h).hom.app P)) := by
      rw [hproper h P]
      infer_instance
    simpa only [isIso_comp_right_iff] using hi
  have hproperInv {m n : ℕ} (h : m ≤ n)
      (P : DerivedCategory (strictEtaleLevel c.Z O t n)) :
      (S.PY.evaluation m).map
          ((strictEtaleBrownProperInsertionMate O t c S hbelow n).inv.app P) ≫
        (S.PY.derivedBelow h).hom.app ((S.properDerived.level n).direct.obj P) =
      (S.properDerived.directEvaluation m).hom.app ((S.PZ.derivedExtension n).obj P) ≫
        (S.properDerived.level m).direct.map ((S.PZ.derivedBelow h).hom.app P) ≫
        (pp h).hom.app P := by
    let a := (strictEtaleBrownProperInsertionMate O t c S hbelow n).app P
    have ha : (S.PY.evaluation m).map a.hom ≫
        (S.properDerived.directEvaluation m).hom.app ((S.PZ.derivedExtension n).obj P) ≫
        (S.properDerived.level m).direct.map ((S.PZ.derivedBelow h).hom.app P) =
        (S.PY.derivedBelow h).hom.app ((S.properDerived.level n).direct.obj P) ≫
          (pp h).inv.app P := by
      simpa only [a, Iso.app_hom, properInsertionMate_hom] using hproper h P
    exact (inverse_square (S.PY.evaluation m) a
      ((S.PY.derivedBelow h).hom.app ((S.properDerived.level n).direct.obj P))
      ((S.properDerived.directEvaluation m).hom.app ((S.PZ.derivedExtension n).obj P) ≫
        (S.properDerived.level m).direct.map ((S.PZ.derivedBelow h).hom.app P))
      ((pp h).app P).symm ha).trans (Category.assoc _ _ _)
  have hopen {m n : ℕ} (h : m ≤ n)
      (P : DerivedCategory (strictEtaleLevel X O t n)) :
      (S.PZ.evaluation m).map ((strictEtaleBrownOpenInsertion O t c S n).hom.app P) ≫
        (S.PZ.derivedBelow h).hom.app ((S.levelDerivedOpen n).obj P) =
      (S.openDerivedEvaluation m).hom.app ((S.PX.derivedExtension n).obj P) ≫
        (S.levelDerivedOpen m).map ((S.PX.derivedBelow h).hom.app P) ≫ (op h).hom.app P := by
    exact etaleBrownOpenSingletonEvaluation O t c S h (op h) (hop h) P
  refine ⟨{
    realizationX := RX
    realizationZ := RZ
    realizationY := RY
    properRealization := rp
    openRealization := ro
    openComparison := jo
    openComparison_mate := hjo
    levelComparison := lc
    levelComparison_def := fun _ ↦ rfl
    openProjection := op
    openMate := hop
    properProjection := pp
    properMate := hpp
    projection := q
    projection_def := fun _ ↦ rfl
    projection_recorded_q := hrecord
    properInsertionBelow := hbelow
    leftExtension_below := ?_ }⟩
  intro m n h P
  have he := paste_evaluation_square (S.properDerived.directEvaluation m)
    ((strictEtaleBrownOpenInsertion O t c S n).hom.app P)
    ((S.PY.evaluation m).map
        ((strictEtaleBrownProperInsertionMate O t c S hbelow n).inv.app
          ((S.levelDerivedOpen n).obj P)) ≫
      (S.PY.derivedBelow h).hom.app ((S.levelFunctor n).obj P))
    ((S.PZ.derivedBelow h).hom.app ((S.levelDerivedOpen n).obj P))
    ((pp h).hom.app ((S.levelDerivedOpen n).obj P))
    (hproperInv h ((S.levelDerivedOpen n).obj P))
  have ho := congrArg
    (fun z ↦ (S.properDerived.directEvaluation m).hom.app
        (S.derivedOpen.obj ((S.PX.derivedExtension n).obj P)) ≫
      (S.properDerived.level m).direct.map z ≫
        (pp h).hom.app ((S.levelDerivedOpen n).obj P)) (hopen h P)
  have hp := he.trans ho
  simp only [strictEtaleBrownLeftExtension, q, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.associator_hom_app, Functor.associator_inv_app,
    isoWhiskerRight_hom, isoWhiskerLeft_hom, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, CategoryTheory.Functor.map_comp, Functor.comp_map,
    Category.id_comp, Category.comp_id, Category.assoc,
    StrictEtaleCompactSupport.evaluation,
    StrictEtaleCompactSupport.levelFunctor]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.id_comp]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc] at hp
  dsimp only [StrictEtaleCompactSupport.functor, StrictEtaleCompactSupport.levelFunctor,
    Functor.comp_obj, Functor.comp_map] at hp ⊢
  exact hp


end AlgebraicGeometry
