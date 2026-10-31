/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Open.EtaleOpenTensorDefs
public import WeilConjectures.SmoothPurity.Finite.FiniteTorAmplitudeSites
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
import all WeilConjectures.AlgebraicGeometry.Etale.Open.EtaleOpenTensorDefs
import all WeilConjectures.AlgebraicGeometry.Etale.ProEtale.EtaleProEtaleScalarMate
import WeilConjectures.AlgebraicGeometry.Etale.Scalar.EtaleScalarFlatModel
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.BoundedConstructible
import WeilConjectures.SixFunctors.Etale.Derived.Stability.FlatModelGeneration
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison

/-! # Open coefficient tensor, evaluation, and finite Tor bounds

Source: blueprint main-20261015, sec-smooth-purity/sk-lem-sp-tower,
lem-coef-finite-dualizing.proof.md, paragraphs 2-3; Stacks Tags 03DI, 03DJ,
03S6, 03TT, 0GKB, 06YY, 0E8I and 0GL1
(blueprint: lem-coef-dualizing-open-tensor).

The comparison is the existing B-linear `openScalarExtension`, with the existing
`openScalarRestrictionMap` mate in its evaluation equation. The ordinary
composite is applied to complexes before localization. No faithfulness of derived
stalk functors on morphisms is asserted.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory Limits AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

/-- The ordinary open tensor/evaluation composite, using the fixed ordinary scalar
comparisons and the actual open adjunction counit. Its degreewise application is
the direct-sum total tensor comparison with B in degree zero.
Source: Stacks 03DI, 0E8I (blueprint: lem-coef-dualizing-open-tensor). -/
def openTensorEvaluationZero
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {U Y : Scheme.{u}} (j : U ⟶ Y) [IsOpenImmersion j] :
    upperStar (ModuleCat.{u + 1} A) j ⋙
        openImmersionLowerShriek (ModuleCat.{u + 1} A) j ⋙
        ProEtale.etaleSheafExtendScalars φ Y ⟶ ProEtale.etaleSheafExtendScalars φ Y :=
  Functor.whiskerLeft (upperStar (ModuleCat.{u + 1} A) j)
      (openScalarExtensionZero φ j).hom ≫
    Functor.whiskerRight (openScalarRestrictionZero φ j).hom
      (openImmersionLowerShriek (ModuleCat.{u + 1} B) j) ≫
    Functor.whiskerLeft (ProEtale.etaleSheafExtendScalars φ Y)
      (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j).counit

/-- All clauses of the open coefficient assertion, expressed using published
functors and canonical comparisons. The stratifications simultaneously work in all
degrees and for both coefficients; the final stratum is the closed complement.
Source: blueprint lem-coef-finite-dualizing.proof.md, paragraphs 2-3;
Stacks 03S6, 03TT, 0E8I, 0GL1 (blueprint: lem-coef-dualizing-open-tensor). -/
structure DualizingOpenTensorProperties
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {U Y : Scheme.{u}} (j : U ⟶ Y) [IsOpenImmersion j]
    (W : DerivedCategoryModule A Y) : Prop where
  evaluation :
    (openScalarExtension φ j).hom.app ((derivedRestriction (A := A) j).obj W) ≫
        (derivedExtension (A := B) j).map ((openScalarRestrictionMap φ j).app W) ≫
        (derivedOpenImmersionLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} B) j).counit.app ((scalarExtension φ Y).obj W) =
      (scalarExtension φ Y).map
        ((derivedOpenImmersionLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} A) j).counit.app W)
  evaluation_before_localization :
    ∀ P : CochainComplex (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ,
      etaleKFlat Y A P → Nonempty (_root_.DerivedCategory.Q.obj P ≅ W) →
      ((openTensorEvaluationZero φ j).mapHomologicalComplex (.up ℤ)).app P =
        ((Functor.whiskerRight
          (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j).counit
          (ProEtale.etaleSheafExtendScalars φ Y)).mapHomologicalComplex (.up ℤ)).app P
  bounded_constructible_A : DerivedCategory.isBoundedConstructible A Y
    ((derivedExtension (A := A) j).obj ((derivedRestriction (A := A) j).obj W))
  bounded_constructible_B : DerivedCategory.isBoundedConstructible B Y
    ((derivedExtension (A := B) j).obj
      ((scalarExtension φ U).obj ((derivedRestriction (A := A) j).obj W)))
  finite_tor : ∃ a b : ℤ, a ≤ b ∧
    DerivedCategory.hasTorAmplitudeIn A Y a b
        ((derivedExtension (A := A) j).obj ((derivedRestriction (A := A) j).obj W)) ∧
      DerivedCategory.hasTorAmplitudeIn B Y a b
        ((derivedExtension (A := B) j).obj
          ((scalarExtension φ U).obj ((derivedRestriction (A := A) j).obj W)))
  tor_bounds : ∀ a b : ℤ, a ≤ b →
    DerivedCategory.hasTorAmplitudeIn A U a b ((derivedRestriction (A := A) j).obj W) →
    DerivedCategory.hasTorAmplitudeIn A Y a b
        ((derivedExtension (A := A) j).obj ((derivedRestriction (A := A) j).obj W)) ∧
      DerivedCategory.hasTorAmplitudeIn B Y a b
        ((derivedExtension (A := B) j).obj
          ((scalarExtension φ U).obj ((derivedRestriction (A := A) j).obj W)))
  stratifications : ∃ (S : Scheme.Stratification U) (SY : Scheme.Stratification Y)
      (e : Fin S.n ↪ Fin SY.n) (z : Fin SY.n),
    Set.range e = {z}ᶜ ∧
    (∀ i : Fin S.n, SY.stratum (e i) = j '' S.stratum i) ∧
    SY.stratum z = (Set.range j)ᶜ ∧
    (∀ (q : ℤ) (i : Fin S.n),
      Scheme.IsFiniteLocallyConstantSheaf
        ((upperStar (ModuleCat.{u + 1} A) (S.immersion i)).obj
          ((_root_.DerivedCategory.homologyFunctor _ q).obj
            ((derivedRestriction (A := A) j).obj W))) ∧
      Scheme.IsFiniteLocallyConstantSheaf
        ((upperStar (ModuleCat.{u + 1} B) (S.immersion i)).obj
          ((_root_.DerivedCategory.homologyFunctor _ q).obj
            ((scalarExtension φ U).obj ((derivedRestriction (A := A) j).obj W))))) ∧
    (∀ (q : ℤ) (i : Fin SY.n),
      Scheme.IsFiniteLocallyConstantSheaf
        ((upperStar (ModuleCat.{u + 1} A) (SY.immersion i)).obj
          ((_root_.DerivedCategory.homologyFunctor _ q).obj
            ((derivedExtension (A := A) j).obj ((derivedRestriction (A := A) j).obj W)))) ∧
      Scheme.IsFiniteLocallyConstantSheaf
        ((upperStar (ModuleCat.{u + 1} B) (SY.immersion i)).obj
          ((_root_.DerivedCategory.homologyFunctor _ q).obj
            ((derivedExtension (A := B) j).obj
              ((scalarExtension φ U).obj ((derivedRestriction (A := A) j).obj W)))))) ∧
    (∀ q : ℤ,
      IsZero ((upperStar (ModuleCat.{u + 1} A) (SY.immersion z)).obj
        ((_root_.DerivedCategory.homologyFunctor _ q).obj
          ((derivedExtension (A := A) j).obj ((derivedRestriction (A := A) j).obj W)))) ∧
      IsZero ((upperStar (ModuleCat.{u + 1} B) (SY.immersion z)).obj
        ((_root_.DerivedCategory.homologyFunctor _ q).obj
          ((derivedExtension (A := B) j).obj
            ((scalarExtension φ U).obj ((derivedRestriction (A := A) j).obj W))))))

private theorem uniq_eq_conjugate
    {C D : Type*} [Category C] [Category D]
    {F F' : C ⥤ D} {G G' : D ⥤ C}
    (a : F ⊣ G) (b : F' ⊣ G') (e : G' ≅ G) :
    a.leftAdjointUniq (b.ofNatIsoRight e) = (conjugateIsoEquiv b a).symm e := by
  ext X
  simp [Adjunction.leftAdjointUniq, conjugateEquiv_symm_apply_app]

private theorem scalarOpenInverseMate
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {LA : C ⥤ D} {JA : D ⥤ C} {LB : E ⥤ F} {JB : F ⥤ E}
    {SX : D ⥤ F} {RX : F ⥤ D} {SU : C ⥤ E} {RU : E ⥤ C}
    (a : LA ⊣ JA) (b : LB ⊣ JB) (x : SX ⊣ RX) (u : SU ⊣ RU)
    (q : JB ⋙ RU ≅ RX ⋙ JA) :
    ((mateEquiv a b).symm
      ((mateEquiv x u).symm (TwoSquare.mk _ _ _ _ q.inv))).natTrans =
      ((a.comp x).leftAdjointUniq ((u.comp b).ofNatIsoRight q)).inv := by
  rw [uniq_eq_conjugate]
  exact congrArg TwoSquare.natTrans
    (iterated_mateEquiv_conjugateEquiv_symm a b u x (TwoSquare.mk _ _ _ _ q.inv))

private theorem derivedEvaluation
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (T : DerivedCategoryModule A X) :
    (openScalarExtension φ j).hom.app ((derivedRestriction (A := A) j).obj T) ≫
        (derivedExtension (A := B) j).map ((openScalarRestrictionMap φ j).app T) ≫
        (derivedOpenImmersionLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} B) j).counit.app ((scalarExtension φ X).obj T) =
      (scalarExtension φ X).map
        ((derivedOpenImmersionLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} A) j).counit.app T) := by
  let a := derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j
  let b := derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j
  let x := Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ)
  let u := Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars U.smallEtaleTopology φ)
  let α := (mateEquiv x u).symm
    (TwoSquare.mk _ _ _ _ (openDerivedRestrictScalarsIso φ j).inv)
  have h := mateEquiv_counit_symm a b α T
  have hm : ((mateEquiv a b).symm α).natTrans = (openScalarExtension φ j).inv :=
    scalarOpenInverseMate a b x u (openDerivedRestrictScalarsIso φ j)
  change _ = ((mateEquiv a b).symm α).natTrans.app _ ≫ _ at h
  rw [hm] at h
  change (derivedExtension (A := B) j).map ((openScalarRestrictionMap φ j).app T) ≫
      (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j).counit.app
        ((scalarExtension φ X).obj T) =
    (openScalarExtension φ j).inv.app ((derivedRestriction (A := A) j).obj T) ≫
      (scalarExtension φ X).map
        ((derivedOpenImmersionLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} A) j).counit.app T) at h
  simpa only [Category.assoc, Iso.hom_inv_id_app_assoc] using
    congrArg (fun t ↦ (openScalarExtension φ j).hom.app
      ((derivedRestriction (A := A) j).obj T) ≫ t) h


private theorem ordinaryEvaluation
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {U Y : Scheme.{u}} (j : U ⟶ Y) [IsOpenImmersion j] :
    openTensorEvaluationZero φ j = Functor.whiskerRight
      (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j).counit
      (ProEtale.etaleSheafExtendScalars φ Y) := by
  let a := openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j
  let b := openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j
  let x := ProEtale.etaleSheafExtendScalarsAdjunction φ Y
  let u := ProEtale.etaleSheafExtendScalarsAdjunction φ U
  let α := (mateEquiv x u).symm
    (TwoSquare.mk _ _ _ _ (openRestrictScalarsIso φ j).inv)
  have hr : α.natTrans = (openScalarRestrictionZero φ j).hom := by
    dsimp only [α]
    rw [openRestrictScalarsIso_inv_eq, ordinary_reverse_eq]
    have hh := uniq_eq_conjugate
      (x.comp (upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) j))
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) j).comp u) (Iso.refl _)
    exact congrArg Iso.inv hh.symm
  have hm : ((mateEquiv a b).symm α).natTrans = (openScalarExtensionZero φ j).inv :=
    scalarOpenInverseMate a b x u (openRestrictScalarsIso φ j)
  apply NatTrans.ext
  funext T
  have h := mateEquiv_counit_symm a b α T
  change _ = ((mateEquiv a b).symm α).natTrans.app _ ≫ _ at h
  rw [hm] at h
  change (openImmersionLowerShriek (ModuleCat.{u + 1} B) j).map
      (α.natTrans.app T) ≫ _ = _ at h
  rw [hr] at h
  change (openImmersionLowerShriek (ModuleCat.{u + 1} B) j).map
      ((openScalarRestrictionZero φ j).hom.app T) ≫ b.counit.app
        ((ProEtale.etaleSheafExtendScalars φ Y).obj T) =
    (openScalarExtensionZero φ j).inv.app ((upperStar (ModuleCat.{u + 1} A) j).obj T) ≫
      (ProEtale.etaleSheafExtendScalars φ Y).map (a.counit.app T) at h
  simpa only [openTensorEvaluationZero, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Category.assoc, Iso.hom_inv_id_app_assoc] using
    congrArg (fun t ↦ (openScalarExtensionZero φ j).hom.app
      ((upperStar (ModuleCat.{u + 1} A) j).obj T) ≫ t) h

private theorem finiteFamilyStratification
    {A : Type (u + 1)} [CommRing A] {X : Scheme.{u}}
    (F : ℤ → Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
    (hc : ∀ q, Scheme.IsConstructibleSheaf (F q)) (s : Finset ℤ) :
    ∃ S : Scheme.Stratification X, ∀ q ∈ s, ∀ i : Fin S.n,
      Scheme.IsFiniteLocallyConstantSheaf
        ((upperStar (ModuleCat.{u + 1} A) (S.immersion i)).obj (F q)) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨Scheme.Stratification.trivial X, by simp⟩
  | @insert q s _ ih =>
    obtain ⟨S, hS⟩ := ih
    obtain ⟨T, hT⟩ := (hc q).exists_stratification
    refine ⟨T.inter S, ?_⟩
    intro r hr i
    rcases Finset.mem_insert.mp hr with rfl | hr
    · exact (T.inter_refines_left S).isFiniteLocallyConstantSheaf_upperStar (F r) hT i
    · exact (T.inter_refines_right S).isFiniteLocallyConstantSheaf_upperStar
        (F r) (hS r hr) i

private theorem boundedStratification
    {A : Type (u + 1)} [CommRing A] [Finite A] {X : Scheme.{u}}
    (K : DerivedCategoryModule A X) (hK : DerivedCategory.isBoundedConstructible A X K) :
    ∃ S : Scheme.Stratification X, ∀ (q : ℤ) (i : Fin S.n),
      Scheme.IsFiniteLocallyConstantSheaf
        ((upperStar (ModuleCat.{u + 1} A) (S.immersion i)).obj
          ((_root_.DerivedCategory.homologyFunctor _ q).obj K)) := by
  classical
  obtain ⟨a, b, _, hz⟩ := hK.2
  obtain ⟨S, hS⟩ := finiteFamilyStratification
    (fun q ↦ (_root_.DerivedCategory.homologyFunctor _ q).obj K)
    (fun q ↦ (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).1 (hK.1 q))
    (Finset.Icc a b)
  refine ⟨S, fun q i ↦ ?_⟩
  by_cases hq : q ∈ Finset.Icc a b
  · exact hS q hq i
  · have hzero := hz q (by simpa only [Finset.mem_Icc, not_and_or, not_le] using hq)
    exact Scheme.IsFiniteLocallyConstantSheaf.of_isZero
      ((upperStar (ModuleCat.{u + 1} A) (S.immersion i)).map_isZero hzero)

private theorem openHomologyStratum
    {A : Type (u + 1)} [CommRing A] {U Y : Scheme.{u}}
    (j : U ⟶ Y) [IsOpenImmersion j] (K : DerivedCategoryModule A U)
    (S : Scheme.Stratification U) (i : Fin S.n) (q : ℤ)
    (h : Scheme.IsFiniteLocallyConstantSheaf
      ((upperStar (ModuleCat.{u + 1} A) (S.immersion i)).obj
        ((_root_.DerivedCategory.homologyFunctor _ q).obj K))) :
    Scheme.IsFiniteLocallyConstantSheaf
      ((upperStar (ModuleCat.{u + 1} A) (S.immersion i ≫ j)).obj
        ((_root_.DerivedCategory.homologyFunctor _ q).obj
          ((derivedExtension (A := A) j).obj K))) := by
  let J := openImmersionLowerShriek (ModuleCat.{u + 1} A) j
  let F := (_root_.DerivedCategory.homologyFunctor _ q).obj K
  let e := (upperStar (ModuleCat.{u + 1} A) (S.immersion i ≫ j)).mapIso
      ((J.mapDerivedCategoryHomologyFunctorIso q).symm.app K) ≪≫
    (upperStarComp (ModuleCat.{u + 1} A) (S.immersion i) j).app (J.obj F) ≪≫
    (upperStar (ModuleCat.{u + 1} A) (S.immersion i)).mapIso
      (asIso ((openImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} A) j).unit.app F)).symm
  have hsource : Scheme.IsFiniteLocallyConstantSheaf
      ((upperStar (ModuleCat.{u + 1} A) (S.immersion i)).obj
        ((𝟭 (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A))).obj F)) := by
    change Scheme.IsFiniteLocallyConstantSheaf
      ((upperStar (ModuleCat.{u + 1} A) (S.immersion i)).obj F)
    exact h
  exact Scheme.IsFiniteLocallyConstantSheaf.of_iso e.symm

private theorem openHomologyComplement
    {A : Type (u + 1)} [CommRing A] {U Y Z : Scheme.{u}}
    (j : U ⟶ Y) [IsOpenImmersion j] (i : Z ⟶ Y)
    (hi : Disjoint (Set.range j) (Set.range i))
    (K : DerivedCategoryModule A U) (q : ℤ) :
    IsZero ((upperStar (ModuleCat.{u + 1} A) i).obj
      ((_root_.DerivedCategory.homologyFunctor _ q).obj
        ((derivedExtension (A := A) j).obj K))) := by
  let J := openImmersionLowerShriek (ModuleCat.{u + 1} A) j
  exact (isZero_upperStar_openImmersionLowerShriek_of_disjoint_range
    (ModuleCat.{u + 1} A) j i hi ((_root_.DerivedCategory.homologyFunctor _ q).obj K)).of_iso
    ((upperStar (ModuleCat.{u + 1} A) i).mapIso
      ((J.mapDerivedCategoryHomologyFunctorIso q).symm.app K))

private theorem sourceBoundedConstructible
    {A : Type (u + 1)} [CommRing A] [Finite A] {X : Scheme.{u}}
    {K : DerivedCategoryModule A X} (hK : DerivedCategory.isBoundedConstructible A X K) :
    DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) X K := by
  obtain ⟨c, d, -, hz⟩ := hK.2
  refine ⟨⟨⟨c, ?_⟩, ⟨d, ?_⟩⟩, fun q ↦ ?_⟩
  · exact (_root_.DerivedCategory.isGE_iff _ c).2 fun q hq ↦ hz q (.inl hq)
  · exact (_root_.DerivedCategory.isLE_iff _ d).2 fun q hq ↦ hz q (.inr hq)
  · exact (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).1 (hK.1 q)

private theorem finiteValueBoundedConstructible
    {A : Type (u + 1)} [CommRing A] [Finite A] {X : Scheme.{u}}
    {K : DerivedCategoryModule A X}
    (hK : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) X K) :
    DerivedCategory.isBoundedConstructible A X K := by
  obtain ⟨⟨⟨c, hc⟩, ⟨d, hd⟩⟩, hcons⟩ := hK
  refine ⟨fun q ↦ (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).2
    (hcons q), min c d, d, min_le_right _ _, ?_⟩
  intro q hq
  rcases hq with hq | hq
  · exact (_root_.DerivedCategory.isGE_iff _ c).1 hc q
      (lt_of_lt_of_le hq (min_le_left _ _))
  · exact (_root_.DerivedCategory.isLE_iff _ d).1 hd q hq

private theorem exactFlatFunctor_tor
    {A B : Type (u + 1)} [CommRing A] [CommRing B] {X Y : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A) ⥤
      Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} B))
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (hf : ∀ P, ObjectProperty.flat P → ObjectProperty.flat (F.obj P))
    {K : DerivedCategoryModule A X} {a b : ℤ}
    (ht : DerivedCategory.hasTorAmplitudeIn A X a b K) :
    DerivedCategory.hasTorAmplitudeIn B Y a b (F.mapDerivedCategory.obj K) := by
  rw [DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn] at ht ⊢
  obtain ⟨P, _, _, hP, ⟨e⟩⟩ :=
    _root_.DerivedCategory.exists_iso_Q_obj_flat_of_torAmplitudeIn ht
  exact (_root_.DerivedCategory.torAmplitudeIn _ a b).prop_of_iso
    ((F.mapDerivedCategoryFactors.app P).symm ≪≫ F.mapDerivedCategory.mapIso e)
    (_root_.DerivedCategory.torAmplitudeIn_Q_obj_of_flat _ a b fun q ↦ hf _ (hP q))

private theorem scalarBoundedConstructibleTor
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (X : Scheme.{u}) [IsNoetherian X]
    (K : DerivedCategoryModule A X) (hK : DerivedCategory.isBoundedConstructible A X K)
    (a b : ℤ) (hab : a ≤ b) (ht : DerivedCategory.hasTorAmplitudeIn A X a b K) :
    DerivedCategory.isBoundedConstructible B X ((scalarExtension φ X).obj K) ∧
      DerivedCategory.hasTorAmplitudeIn B X a b ((scalarExtension φ X).obj K) := by
  let Kb : _root_.DerivedCategory.Bounded
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
    ⟨K, (sourceBoundedConstructible hK).1⟩
  have hs := exists_etaleScalarFlatModel X A B φ a b hab Kb hK.1 ht
  have ht' := hs.2.2.2.2
  have hh := _root_.DerivedCategory.homologyConcentratedIn_of_torAmplitudeIn
    (DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.1 ht')
  refine ⟨⟨hs.2.2.2.1, a, b, hab, ?_⟩, ht'⟩
  intro q hq
  exact hq.elim
    (fun h ↦ (_root_.DerivedCategory.isGE_iff _ a).1 hh.1 q h)
    (fun h ↦ (_root_.DerivedCategory.isLE_iff _ b).1 hh.2 q h)

/-- Canonical open coefficient tensor preserves evaluation and finite Tor bounds.
The coefficient rings and quotient map are the recorded O_E/(varpi^n) to O_E/(varpi^m),
with their common coefficient-universe lift. No flatness of that map is required.
Source: blueprint main-20261015, lem-coef-finite-dualizing.proof.md, paragraphs 2-3
(blueprint: lem-coef-dualizing-open-tensor).

Proof: (1) Restrict a flat constructible representative of W, supplied by
lem-sp-etale-scalar-flat-model for A to A. Exact inverse image restricts cohomology
and stratifications. K-flat flat-term pullback and lem-kun-flat-bounded-tor-amplitude
show that L=j^*W is bounded constructible of finite Tor amplitude.
(2) Resolve W by a K-flat flat-term complex (lem-pc-kflat-resolution). Its restriction
and open extension are K-flat (lem-coef-etale-open-tensor). On these representatives,
the B-linear comparison sends (j_!x) tensor b to j_!(x tensor b); its inverse is also
B-linear. The normalization and uniqueness of lem-coef-etale-open-scalar-coherence
identify its localization with the fixed openScalarExtension.
(3) The counit of lem-weil-pbc-extension-by-zero-adjunction sends each extension
summand to the original section and sends an empty summand to zero. Both composites
therefore agree on tensor generators in each degree. Sheafification preserves this
identity. The maps preserve total-tensor summands and their differential signs, so
the equality holds as chain maps before localization, giving evaluation afterwards.
(4) For any Tor interval [a,b] of L, use lem-sp-etale-scalar-flat-model on U and A to B.
The model and its scalar extension have flat constructible terms in [a,b]. Exact
extension by zero preserves flatness and quasi-isomorphisms; the bounded-flat Tor
lemma gives the same interval over A and B, without assuming B flat over A.
(5) Exact extension commutes with cohomology. Refine the finitely many cohomology
stratifications on U, simultaneously for both coefficients. Their strata remain
locally closed constructible in the Noetherian Y. Base change of extension by zero
(Stacks 03S6) identifies the sheaves on these strata with the original finite locally
constant sheaves and makes their restriction to the closed complement zero. Adjoin
that complement as the final stratum, including when it is empty. -/
theorem coefficientDualizingOpenTensor
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hdifferent : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (m n : ℕ) (hm : 1 ≤ m) (hmn : m ≤ n)
    {U Y : Scheme.{u}} [Y.Over (Spec (.of D.k))]
    [IsSeparated (Y ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [IsLocallyNoetherian Y] [CompactSpace Y]
    (j : U ⟶ Y) [IsOpenImmersion j] [QuasiCompact j]
    (W : DerivedCategoryModule
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) Y)
    (_hW : WeilConjectures.finiteTorConstructibleEtale l E n (hm.trans hmn) Y W) :
    @DualizingOpenTensorProperties _ _ _ _
      (Equiv.ulift.finite_iff.mpr (Padic.finite_coefficientExtensionRing l E n (hm.trans hmn)))
      (Equiv.ulift.finite_iff.mpr (Padic.finite_coefficientExtensionRing l E m hm))
      (RingHom.ulift.{u + 1, u + 1} (Ideal.Quotient.factor
        (S := Padic.coefficientExtensionIdeal l E n)
        (T := Padic.coefficientExtensionIdeal l E m) (Ideal.pow_le_pow_right hmn)))
      U Y j inferInstance W := by
  let A := ULift.{u + 1} (Padic.coefficientExtensionRing l E n)
  let B := ULift.{u + 1} (Padic.coefficientExtensionRing l E m)
  let φ : A →+* B := RingHom.ulift.{u + 1, u + 1} (Ideal.Quotient.factor
    (S := Padic.coefficientExtensionIdeal l E n)
    (T := Padic.coefficientExtensionIdeal l E m) (Ideal.pow_le_pow_right hmn))
  let : Finite A := Equiv.ulift.finite_iff.mpr
    (Padic.finite_coefficientExtensionRing l E n (hm.trans hmn))
  let : Finite B := Equiv.ulift.finite_iff.mpr
    (Padic.finite_coefficientExtensionRing l E m hm)
  have : IsLocallyNoetherian U := LocallyOfFiniteType.isLocallyNoetherian j
  have : CompactSpace U := QuasiCompact.compactSpace_of_compactSpace j
  have : IsNoetherian U := {}
  let L := (derivedRestriction (A := A) j).obj W
  have hL : DerivedCategory.isBoundedConstructible A U L :=
    finiteValueBoundedConstructible
      ((sourceBoundedConstructible _hW.1).mapDerivedCategory_upperStar j)
  have htor (a b : ℤ) (ht : DerivedCategory.hasTorAmplitudeIn A Y a b W) :
      DerivedCategory.hasTorAmplitudeIn A U a b L :=
    exactFlatFunctor_tor (upperStar (ModuleCat.{u + 1} A) j)
      (fun _ h ↦ Functor.PreservesFlat.flat_obj h) ht
  have hopen (R : Type (u + 1)) [CommRing R] [Finite R]
      (K : DerivedCategoryModule R U) (hK : DerivedCategory.isBoundedConstructible R U K) :
      DerivedCategory.isBoundedConstructible R Y ((derivedExtension (A := R) j).obj K) :=
    finiteValueBoundedConstructible
      (boundedConstructible_mapDerivedCategory_openImmersionLowerShriek R j
        (sourceBoundedConstructible hK))
  have hopenTor (R : Type (u + 1)) [CommRing R] (K : DerivedCategoryModule R U)
      (a b : ℤ) (ht : DerivedCategory.hasTorAmplitudeIn R U a b K) :
      DerivedCategory.hasTorAmplitudeIn R Y a b ((derivedExtension (A := R) j).obj K) :=
    exactFlatFunctor_tor (openImmersionLowerShriek (ModuleCat.{u + 1} R) j)
      (fun _ h ↦ flat_openImmersionLowerShriek_obj j h) ht
  obtain ⟨a, b, hab, ht⟩ := _hW.2
  have hLt := htor a b ht
  have hB := scalarBoundedConstructibleTor φ U L hL a b hab hLt
  refine
    { evaluation := derivedEvaluation φ j W
      evaluation_before_localization := ?_
      bounded_constructible_A := hopen A L hL
      bounded_constructible_B := hopen B _ hB.1
      finite_tor := ⟨a, b, hab, hopenTor A L a b hLt, hopenTor B _ a b hB.2⟩
      tor_bounds := ?_
      stratifications := ?_ }
  · intro P _ _
    exact NatTrans.congr_app
      (congrArg (fun t ↦ t.mapHomologicalComplex (.up ℤ)) (ordinaryEvaluation φ j)) P
  · intro c d hcd hLcd
    exact ⟨hopenTor A L c d hLcd, hopenTor B _ c d
      (scalarBoundedConstructibleTor φ U L hL c d hcd hLcd).2⟩
  · classical
    obtain ⟨SA, hSA⟩ := boundedStratification L hL
    obtain ⟨SB, hSB⟩ := boundedStratification ((scalarExtension φ U).obj L) hB.1
    let S := SA.inter SB
    have hS (q : ℤ) (i : Fin S.n) :
        Scheme.IsFiniteLocallyConstantSheaf
          ((upperStar (ModuleCat.{u + 1} A) (S.immersion i)).obj
            ((_root_.DerivedCategory.homologyFunctor _ q).obj L)) ∧
        Scheme.IsFiniteLocallyConstantSheaf
          ((upperStar (ModuleCat.{u + 1} B) (S.immersion i)).obj
            ((_root_.DerivedCategory.homologyFunctor _ q).obj ((scalarExtension φ U).obj L))) :=
      ⟨(SA.inter_refines_left SB).isFiniteLocallyConstantSheaf_upperStar _ (hSA q) i,
        (SA.inter_refines_right SB).isFiniteLocallyConstantSheaf_upperStar _ (hSB q) i⟩
    let Z := Scheme.Stratification.trivial (CategoryTheory.Arrow.mk j.closedComplement).left
    let SY := Scheme.Stratification.openClosed j j.closedComplement
      j.range_closedComplement S Z
    let e : Fin S.n ↪ Fin SY.n :=
      ⟨fun i ↦ finSumFinEquiv (Sum.inl i), fun _ _ h ↦
        Sum.inl_injective (finSumFinEquiv.injective h)⟩
    let z : Fin SY.n := finSumFinEquiv (Sum.inr (0 : Fin 1))
    have hz : SY.stratum z = (Set.range j)ᶜ := by
      simpa [SY, z, Z, Scheme.Stratification.openClosed, Scheme.Stratification.trivial]
        using j.range_closedComplement
    have hr : Set.range e = {z}ᶜ := by
      ext k
      constructor
      · rintro ⟨i, rfl⟩ h
        have he : Sum.inl i = Sum.inr (0 : Fin 1) :=
          finSumFinEquiv.injective (Set.mem_singleton_iff.mp h)
        cases he
      · intro hk
        obtain ⟨v, rfl⟩ := finSumFinEquiv.surjective k
        rcases v with i | i
        · exact ⟨i, rfl⟩
        · change Fin 1 at i
          have : i = 0 := Subsingleton.elim _ _
          subst i
          exact False.elim (hk rfl)
    have hclosed : Set.range (SY.immersion z) = (Set.range j)ᶜ :=
      (SY.range_immersion z).trans hz
    have hdis : Disjoint (Set.range j) (Set.range (SY.immersion z)) := by
      rw [hclosed]
      exact disjoint_compl_right
    refine ⟨S, SY, e, z, hr, ?_, hz, hS, ?_, ?_⟩
    · intro i
      simp [SY, e, Scheme.Stratification.openClosed]
    · intro q k
      change Scheme.IsFiniteLocallyConstantSheaf
          ((upperStar (ModuleCat.{u + 1} A)
            (Sum.rec (motive := fun v ↦ Sum.elim S.domain Z.domain v ⟶ Y)
              (fun i ↦ S.immersion i ≫ j) (fun i ↦ Z.immersion i ≫ j.closedComplement)
              (finSumFinEquiv.symm k))).obj
            ((_root_.DerivedCategory.homologyFunctor _ q).obj
              ((derivedExtension (A := A) j).obj L))) ∧
        Scheme.IsFiniteLocallyConstantSheaf
          ((upperStar (ModuleCat.{u + 1} B)
            (Sum.rec (motive := fun v ↦ Sum.elim S.domain Z.domain v ⟶ Y)
              (fun i ↦ S.immersion i ≫ j) (fun i ↦ Z.immersion i ≫ j.closedComplement)
              (finSumFinEquiv.symm k))).obj
            ((_root_.DerivedCategory.homologyFunctor _ q).obj
              ((derivedExtension (A := B) j).obj ((scalarExtension φ U).obj L))))
      generalize finSumFinEquiv.symm k = v
      rcases v with i | i
      · exact ⟨openHomologyStratum j L S i q (hS q i).1,
          openHomologyStratum j ((scalarExtension φ U).obj L) S i q (hS q i).2⟩
      · have hi : Disjoint (Set.range j)
            (Set.range (Z.immersion i ≫ j.closedComplement)) := by
          rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
          apply disjoint_compl_right.mono_right
          rw [← j.range_closedComplement]
          exact Set.image_subset_range _ _
        exact ⟨Scheme.IsFiniteLocallyConstantSheaf.of_isZero
          (openHomologyComplement j (Z.immersion i ≫ j.closedComplement) hi L q),
          Scheme.IsFiniteLocallyConstantSheaf.of_isZero
          (openHomologyComplement j (Z.immersion i ≫ j.closedComplement) hi
            ((scalarExtension φ U).obj L) q)⟩
    · intro q
      exact ⟨openHomologyComplement j (SY.immersion z) hdis L q,
        openHomologyComplement j (SY.immersion z) hdis ((scalarExtension φ U).obj L) q⟩


end AlgebraicGeometry.Etale
