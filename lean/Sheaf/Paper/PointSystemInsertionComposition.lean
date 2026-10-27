/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups Q22 and R1
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Paper.SemilinearDerivedSections
public import Sheaf.Paper.CoefDerivedSystemEvaluationCalculus
public import Sheaf.Paper.IntegralFinitePullbackComposition
public import Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage
public import Sheaf.Paper.InverseImagePullbackComparisonDerived
public import Sheaf.Paper.CoefTowerCoaugmentation
public import Sheaf.Paper.PointProEtaleSectionsExact
public import Sheaf.SixFunctors.FrobeniusPointTransport
public import Sheaf.AlgebraicGeometry.PointSheafInsertionCalculus
public import Sheaf.Paper.PointAutomorphismRestrictionNatural
public import Sheaf.Paper.CoefficientRingedSequenceSite
public import Sheaf.Paper.ProEtaleCoefficientModulePullbackComposition
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryCocycle

public import Sheaf.Paper.PointSystemInsertionData
import Sheaf.Paper.PointSystemNormalizedComparisons
import Sheaf.Paper.PointSystemStrictInsertions
import Mathlib.CategoryTheory.Localization.Predicate

/-! # Composition of normalized point insertions

Source: Stacks Tags 03CB, 0H7J and 015F
(blueprint: lem-trf-point-system-insertion-composition).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
attribute [local irreducible] HasDerivedCategory.standard
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
namespace WeilConjectures.PointSystemInsertion
variable (k : Type t) [Field k] (h : Aut (Spec (.of k)))
  (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
attribute [local irreducible] G sections

private theorem constant_composition
    (A : CommRingCat.{max u (t + 1)}) (m : ℕ) :
    (ringCompositor.{t, u} k h m).hom.app
        ((sheafCompose (ProEt.topology (Spec (.of k)))
          (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
            ((constantSheaf (ProEt.topology (Spec (.of k)))
              CommRingCat.{max u (t + 1)}).obj A)) ≫
      isoSectionwiseConstantMap (h ^ ((m + 1) + 1)).hom A =
    (ringF.{t, u} k h 0).map
        (isoSectionwiseConstantMap (h ^ (m + 1)).hom A) ≫
      isoSectionwiseConstantMap (h ^ (0 + 1)).hom A := by
  let D := (sheafCompose (ProEt.topology (Spec (.of k)))
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
      ((constantSheaf (ProEt.topology (Spec (.of k)))
        CommRingCat.{max u (t + 1)}).obj A)
  let e := (ringCompositor.{t, u} k h m).app D
  apply (cancel_epi e.inv).mp
  change e.inv ≫ e.hom ≫ _ = _
  rw [← Category.assoc, e.inv_hom_id, Category.id_comp]
  symm
  apply (isoSectionwiseConstantMap_existsUnique (h ^ ((m + 1) + 1)).hom A).unique
  · intro U a
    change (isoSectionwiseConstantMap (h ^ (0 + 1)).hom A).hom.app (op U)
      ((isoSectionwiseConstantMap (h ^ (m + 1)).hom A).hom.app
        (op ((proEtaleIsoPostcompose (h ^ (0 + 1)).hom).obj U))
          (D.obj.map ((pointSheafReindexCompositor h m).inv.app U).op
            ((toSheafify (ProEt.topology (Spec (.of k)))
              ((Functor.const (Spec (.of k)).ProEtᵒᵖ).obj A)).app
                (op ((proEtaleIsoPostcompose (h ^ ((m + 1) + 1)).hom).obj U)) a))) = _
    have hn := ConcreteCategory.congr_hom
      ((toSheafify (ProEt.topology (Spec (.of k)))
        ((Functor.const (Spec (.of k)).ProEtᵒᵖ).obj A)).naturality
          ((pointSheafReindexCompositor h m).inv.app U).op) a
    change _ = D.obj.map _ _ at hn
    have hm := (isoSectionwiseConstantMap_existsUnique (h ^ (m + 1)).hom A).exists
      |>.choose_spec ((proEtaleIsoPostcompose (h ^ (0 + 1)).hom).obj U) a
    have h0 := (isoSectionwiseConstantMap_existsUnique (h ^ (0 + 1)).hom A).exists
      |>.choose_spec U a
    exact (congrArg (fun z ↦
      (isoSectionwiseConstantMap (h ^ (0 + 1)).hom A).hom.app (op U)
        ((isoSectionwiseConstantMap (h ^ (m + 1)).hom A).hom.app
          (op ((proEtaleIsoPostcompose (h ^ (0 + 1)).hom).obj U)) z)) hn.symm).trans
      ((congrArg (fun z ↦
        (isoSectionwiseConstantMap (h ^ (0 + 1)).hom A).hom.app (op U) z) hm).trans h0)
  · exact (isoSectionwiseConstantMap_existsUnique
      (h ^ ((m + 1) + 1)).hom A).exists.choose_spec

private theorem coefficient_projection (r n : ℕ) :
    c k h l E r none ≫
        limit.π (integralCoefficientSheafSystem l E (Spec (.of k))) (op n) =
      (ringF.{t, u} k h r).map
          (limit.π (integralCoefficientSheafSystem l E (Spec (.of k))) (op n)) ≫
        c k h l E r (some n) := by
  simp only [c, pointRestrictionCoefficientMap, inverseImageCompletedCoefficientMap,
    limit.lift_π, inverseImageCompletedCoefficientComponent]

private theorem coefficient_laws [IsAlgClosed k] : CoefficientLaws k h l E := by
  have hf (m n : ℕ) :
      (ringCompositor.{t, u} k h m).hom.app
          (pointRestrictionRing l E (Spec (.of k)) (some n)) ≫
            c k h l E (m + 1) (some n) =
        (ringF.{t, u} k h 0).map (c k h l E m (some n)) ≫
          c k h l E 0 (some n) :=
    constant_composition k h
      (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1)))) m
  refine ⟨?_, coefficient_projection k h l E⟩
  intro m a
  cases a with
  | some n => exact hf m n
  | none =>
    apply limit.hom_ext
    intro n
    let p := limit.π (integralCoefficientSheafSystem l E (Spec (.of k))) n
    change ((ringCompositor.{t, u} k h m).hom.app _ ≫ c k h l E (m + 1) none) ≫ p =
      ((ringF.{t, u} k h 0).map (c k h l E m none) ≫ c k h l E 0 none) ≫ p
    have hp (r : ℕ) : c k h l E r none ≫ p =
        (ringF.{t, u} k h r).map p ≫ c k h l E r (some n.unop) :=
      coefficient_projection k h l E r n.unop
    simp only [Category.assoc]
    rw [hp, hp, ← Functor.map_comp_assoc, hp]
    simp only [Functor.map_comp, Category.assoc]
    rw [← NatTrans.naturality_assoc]
    exact congrArg (fun f ↦ (ringF.{t, u} k h 0).map
      ((ringF.{t, u} k h m).map p) ≫ f) (hf m n.unop)

private theorem complexInsertion_f [IsAlgClosed k] (r : ℕ)
    (u : sections k l E ⟶ G k h l E r ⋙ sections k l E)
    (M : CochainComplex (coefficientSequenceModules l E (Spec (.of k))) ℤ) (i : ℤ) :
    ((complexInsertion k h l E r u).app M).f i = u.app (M.X i) := by
  change u.app (M.X i) ≫ 𝟙 _ = _
  exact Category.comp_id _

private def derivedInsertionFactors [IsAlgClosed k] (r : ℕ) :
    DerivedCategory.Q ⋙
        ((G k h l E r).mapDerivedCategory ⋙ (sections k l E).mapDerivedCategory) ≅
      ((G k h l E r).mapHomologicalComplex (.up ℤ) ⋙
        (sections k l E).mapHomologicalComplex (.up ℤ)) ⋙ DerivedCategory.Q :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (G k h l E r).mapDerivedCategoryFactors
      (sections k l E).mapDerivedCategory ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft ((G k h l E r).mapHomologicalComplex (.up ℤ))
      (sections k l E).mapDerivedCategoryFactors ≪≫
    (Functor.associator _ _ _).symm

private theorem derivedInsertionFactors_hom_app [IsAlgClosed k] (r : ℕ)
    (M : CochainComplex (coefficientSequenceModules l E (Spec (.of k))) ℤ) :
    (derivedInsertionFactors k h l E r).hom.app M =
      (sections k l E).mapDerivedCategory.map
          ((G k h l E r).mapDerivedCategoryFactors.hom.app M) ≫
        (sections k l E).mapDerivedCategoryFactors.hom.app
          (((G k h l E r).mapHomologicalComplex (.up ℤ)).obj M) := by
  simp only [derivedInsertionFactors, Iso.trans_hom, Iso.symm_hom,
    Functor.associator_inv_app, Functor.associator_hom_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    NatTrans.comp_app, Category.id_comp, Category.comp_id]

private def derivedInsertion [IsAlgClosed k] (P : Maps k h l E) (r : ℕ) :
    (sections k l E).mapDerivedCategory ⟶
      (G k h l E r).mapDerivedCategory ⋙ (sections k l E).mapDerivedCategory := by
  let : Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso _ (.up ℤ))
      (((G k h l E r).mapHomologicalComplex (.up ℤ) ⋙
        (sections k l E).mapHomologicalComplex (.up ℤ)) ⋙ DerivedCategory.Q)
      ((G k h l E r).mapDerivedCategory ⋙ (sections k l E).mapDerivedCategory) :=
    ⟨derivedInsertionFactors k h l E r⟩
  exact Localization.liftNatTrans DerivedCategory.Q
    (HomologicalComplex.quasiIso _ (.up ℤ)) _ _ _ _
    (Functor.whiskerRight (complexInsertion k h l E r (P.u r)) DerivedCategory.Q)

private theorem derivedInsertion_fac [IsAlgClosed k] (P : Maps k h l E) (r : ℕ)
    (M : CochainComplex (coefficientSequenceModules l E (Spec (.of k))) ℤ) :
    (derivedInsertion k h l E P r).app (DerivedCategory.Q.obj M) ≫
        (sections k l E).mapDerivedCategory.map
          ((G k h l E r).mapDerivedCategoryFactors.hom.app M) ≫
        (sections k l E).mapDerivedCategoryFactors.hom.app
          (((G k h l E r).mapHomologicalComplex (.up ℤ)).obj M) =
      (sections k l E).mapDerivedCategoryFactors.hom.app M ≫
        DerivedCategory.Q.map ((complexInsertion k h l E r (P.u r)).app M) := by
  rw [← derivedInsertionFactors_hom_app]
  simp only [derivedInsertion, Localization.liftNatTrans_app]
  change (_ ≫ _ ≫ (derivedInsertionFactors k h l E r).inv.app M) ≫
    (derivedInsertionFactors k h l E r).hom.app M = _
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  rfl

private theorem derivedInsertion_laws [IsAlgClosed k] (P : Maps k h l E)
    (hs : StrictInsertionLaws k h l E P) :
    DerivedInsertionLaws k h l E { P with I := derivedInsertion k h l E P } := by
  refine ⟨derivedInsertion_fac k h l E P, ?_⟩
  intro m C
  suffices he : derivedInsertion k h l E P (m + 1) =
      derivedInsertion k h l E P m ≫
        Functor.whiskerLeft (G k h l E m).mapDerivedCategory
          (derivedInsertion k h l E P 0) ≫
        Functor.whiskerRight (Functor.mapDerivedCategoryCompNatIso (P.t m)).hom
          (sections k l E).mapDerivedCategory from congr_app he C
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso _ (.up ℤ))
  intro M
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  have ht : Functor.mapHomologicalComplexCompIsoHomOfIso (P.t m) M =
      (Functor.mapHomologicalComplexCompIso (P.t m) (.up ℤ)).hom.app M := by
    apply HomologicalComplex.hom_ext
    intro i
    simp only [Functor.mapHomologicalComplexCompIsoHomOfIso,
      HomologicalComplex.comp_f, Functor.mapHomologicalComplexCompIso_hom_app_f,
      NatTrans.mapHomologicalComplex_app_f, Iso.refl_hom, NatTrans.id_app]
    exact Category.id_comp _
  apply (cancel_mono ((derivedInsertionFactors k h l E (m + 1)).hom.app M)).mp
  simp only [derivedInsertionFactors_hom_app, Category.assoc]
  rw [derivedInsertion_fac, ← Functor.map_comp_assoc,
    Functor.mapDerivedCategoryCompNatIso_hom_app_Q, ht]
  simp only [Functor.map_comp, Category.assoc]
  have hn := (sections k l E).mapDerivedCategoryFactors.hom.naturality
    ((Functor.mapHomologicalComplexCompIso (P.t m) (.up ℤ)).hom.app M)
  simp only [Functor.comp_map] at hn
  rw [hn]
  simp only [Functor.comp_obj]
  have hu := (derivedInsertion k h l E P 0).naturality
    ((G k h l E m).mapDerivedCategoryFactors.hom.app M)
  simp only [Functor.comp_map] at hu
  rw [← reassoc_of% hu,
    reassoc_of% (derivedInsertion_fac k h l E P 0
      (((G k h l E m).mapHomologicalComplex (.up ℤ)).obj M)),
    reassoc_of% (derivedInsertion_fac k h l E P m M)]
  rw [hs.2.2 m M]
  simp only [Functor.map_comp]

/-- Canonical point insertions compose on entire strict systems and their ordinary
unbounded derived categories, with the finite and completed coefficient normalizations.
No normalization, cartesianness, boundedness, constructibility or Tor bound is assumed.
Source: Stacks Tags 03CB and 0H7J; blueprint Global powers
(blueprint: lem-trf-point-system-insertion-composition).

Proof: first prove the finite coefficient composition by uniqueness of the
constant-normalized sectionwise map. The completed identity follows by projecting
its defining limit lift to every finite coefficient ring. Obtain the normalized
module, tower, scalar-restriction and tensor comparisons from
pointSystemNormalizedComparisons. Obtain the strict natural tower insertions and
their composition from pointSystemStrictInsertions. Degreewise extensionality of
the actual complexInsertion construction proves composition on chain complexes.
Finally, exactness of G and sections permits localization on ordinary unbounded
derived categories. Lift the chain insertions using Localization.liftNatTrans and
the specified exact-functor factorization isomorphisms. Its component formula proves
the required factorization. Compare the two composite natural transformations
after precomposition with Q: the specified derived compositor formula, naturality
and the chain composition identity give equality. Localization.natTrans_ext gives
the identity on all derived objects, without evaluation faithfulness. -/
theorem pointSystemInsertionComposition [IsAlgClosed k] (_hl : IsUnit (l : k)) :
    CoefficientLaws k h l E ∧
      ∃ P : Maps k h l E,
        SectionLaws k h l E P ∧ RestrictionCompositionLaws k h l E P ∧
          TensorLaws k h l E P ∧ TransitionLaws k h l E P ∧
          StrictInsertionLaws k h l E P ∧ DerivedInsertionLaws k h l E P := by
  have hc := coefficient_laws k h l E
  obtain ⟨P, hsec, hres, htensor, htrans⟩ :=
    pointSystemNormalizedComparisons k h l E hc
  obtain ⟨u, hu⟩ := pointSystemStrictInsertions k h l E P hsec
  let Q : Maps k h l E := { P with u := u }
  have hstrict : StrictInsertionLaws k h l E Q := by
    refine ⟨hu.1, hu.2, ?_⟩
    intro m M
    apply HomologicalComplex.hom_ext
    intro i
    simp only [HomologicalComplex.comp_f, complexInsertion_f,
      Functor.mapHomologicalComplex_map_f,
      Functor.mapHomologicalComplexCompIso_hom_app_f]
    change (u (m + 1)).app (M.X i) = (u m).app (M.X i) ≫
      (u 0).app ((G k h l E m).obj (M.X i)) ≫
        (sections k l E).map ((P.t m).hom.app (M.X i))
    exact hu.2 m (M.X i)
  let T : Maps k h l E := { Q with I := derivedInsertion k h l E Q }
  refine ⟨hc, T, ?_, ?_, ?_, ?_, ?_, derivedInsertion_laws k h l E Q hstrict⟩
  · simpa only [SectionLaws, T, Q] using hsec
  · simpa only [RestrictionCompositionLaws, towerCompositor, T, Q] using hres
  · simpa only [TensorLaws, T, Q] using htensor
  · simpa only [TransitionLaws, tensorTransition, finiteUnit, T, Q] using htrans
  · simpa only [StrictInsertionLaws, T] using hstrict

end WeilConjectures.PointSystemInsertion
