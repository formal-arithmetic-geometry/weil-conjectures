/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q84
-/
module

public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Paper.InverseImagePullbackComparisonDerived
public import Sheaf.Paper.PointAutomorphismRestrictionNatural
public import Sheaf.Paper.CoefficientRingedSequenceSite
public import Mathlib.Algebra.Homology.DerivedCategory.Basic

/-! # Restriction and insertion on strict point systems

Source: blueprint main-20261015, sec-trace-formula/sk-d-weil,
prop-trf-rational-frobenius-integral-model.proof.md, clause (3), point-factor
prerequisite, agent-formulated simultaneous-system extension
(blueprint: lem-trf-point-restriction-system-chain-map).

The index n : ℕ denotes the positive exponent n+1. The sequence-site realization
retains arbitrary quotient-linear transitions. The inverse-image colimit insertion
is identity in the recorded canonical site-reindexing coordinates.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
namespace WeilConjectures.PointRestrictionSystem

variable (D : FiniteFieldDatum.{t}) (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The site reindexing for an arbitrary point automorphism, leaving the level fixed.
Source: blueprint proof (3), explicit point-factor prerequisite
(blueprint: lem-trf-point-restriction-system-chain-map). -/
def reindex (g : Spec (.of D.k) ⟶ Spec (.of D.k)) [IsIso g] :=
  (𝟭 ℕ).prod (proEtaleIsoPostcompose g)

private theorem sequenceContinuous {C B : Type*} [Category* C] [Category* B]
    (J : GrothendieckTopology C) (K : GrothendieckTopology B)
    (F : C ⥤ B) [F.IsEquivalence] (hf : CoverPreserving J K F) :
    ((𝟭 ℕ).prod F).IsContinuous (coefficientSequenceTopology J)
      (coefficientSequenceTopology K) := by
  let H := (𝟭 ℕ).prod F
  have : H.IsEquivalence :=
    ((CategoryTheory.Equivalence.refl (C := ℕ)).prod F.asEquivalence).isEquivalence_functor
  have : RepresentablyFlat H := inferInstance
  apply Functor.isContinuous_of_coverPreserving (compatiblePreservingOfFlat _ _)
  constructor
  intro X S hS
  change (S.functorPushforward H).functorPullback (Prod.sectR X.1 B) ∈ K _
  apply K.superset_covering _ (hf.cover_preserve hS)
  rintro Y f ⟨Z, a, b, ha, rfl⟩
  exact ⟨(X.1, Z), Prod.mkHom (𝟙 X.1) a, Prod.mkHom (𝟙 X.1) b, ha, rfl⟩

/-- Reindexing preserves the vertical sequence sheaf condition.
Source: blueprint proof (3); Stacks 0941 and 09A5
(blueprint: lem-trf-point-restriction-system-chain-map).
Proof: on each vertical slice the functor is the covering-preserving site
equivalence induced by g, by lem-weil-proetale-isomorphism-inverse-image.
A sequence sieve covers precisely when its vertical slice covers. Thus the
same equivalence preserves the sequence sheaf condition. -/
@[instance] theorem reindexContinuous
    (g : Spec (.of D.k) ⟶ Spec (.of D.k)) [IsIso g] :
    (reindex D g).IsContinuous
      (coefficientSequenceTopology (ProEt.topology (Spec (.of D.k))))
      (coefficientSequenceTopology (ProEt.topology (Spec (.of D.k)))) := by
  have := (proEtaleIsoPostcompose_equivalence g).1
  exact sequenceContinuous _ _ (proEtaleIsoPostcompose g)
    (proEtaleIsoPostcompose_equivalence g).2.2.2.1.some



/-- The existing sequence coefficient ring, with commutativity forgotten.
Source: blueprint proof (3); Stacks 0941
(blueprint: lem-trf-point-restriction-system-chain-map). -/
abbrev sequenceRing :=
  (sheafCompose (coefficientSequenceTopology (ProEt.topology (Spec (.of D.k))))
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
      (coefficientSequenceCommRingSheaf l E (Spec (.of D.k)))

private theorem postcompose_cocontinuous
    (g : Spec (.of D.k) ⟶ Spec (.of D.k)) [IsIso g] :
    (proEtaleIsoPostcompose g).IsCocontinuous
      (ProEt.topology (Spec (.of D.k))) (ProEt.topology (Spec (.of D.k))) := by
  let e := proEtaleIsoPostcompose_equivalence g
  let eqv : (Spec (.of D.k)).ProEt ≌ (Spec (.of D.k)).ProEt :=
    CategoryTheory.Equivalence.mk (proEtaleIsoPostcompose g)
      (proEtaleIsoPostcompose (inv g)) e.2.1.some.symm e.2.2.1.some
  exact (eqv.toAdjunction.isCocontinuous_iff_coverPreserving _ _).2 e.2.2.2.2.some

private def constantComparisonIso
    (g : Spec (.of D.k) ⟶ Spec (.of D.k)) [IsIso g]
    (A : CommRingCat.{max u (t + 1)}) :
    (isoSectionwiseInverseImage g CommRingCat.{max u (t + 1)}).obj
      ((constantSheaf (ProEt.topology (Spec (.of D.k)))
        CommRingCat.{max u (t + 1)}).obj A) ≅
    (constantSheaf (ProEt.topology (Spec (.of D.k)))
      CommRingCat.{max u (t + 1)}).obj A := by
  have := postcompose_cocontinuous D g
  exact ((proEtaleIsoPostcompose g).pushforwardContinuousSheafificationCompatibility
    CommRingCat.{max u (t + 1)} (ProEt.topology (Spec (.of D.k)))
      (ProEt.topology (Spec (.of D.k)))).symm.app
        ((Functor.const (Spec (.of D.k)).ProEtᵒᵖ).obj A)

private theorem constantComparisonIso_eq
    (g : Spec (.of D.k) ⟶ Spec (.of D.k)) [IsIso g]
    (A : CommRingCat.{max u (t + 1)}) :
    (sheafCompose (ProEt.topology (Spec (.of D.k)))
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
        (constantComparisonIso D g A).hom = isoSectionwiseConstantMap g A := by
  have := postcompose_cocontinuous D g
  apply (isoSectionwiseConstantMap_existsUnique g A).unique
  · intro U a
    let i := (sheafToPresheaf (ProEt.topology (Spec (.of D.k)))
      CommRingCat.{max u (t + 1)}).mapIso
        (((proEtaleIsoPostcompose g).pushforwardContinuousSheafificationCompatibility
          CommRingCat.{max u (t + 1)} (ProEt.topology (Spec (.of D.k)))
            (ProEt.topology (Spec (.of D.k)))).app
              ((Functor.const (Spec (.of D.k)).ProEtᵒᵖ).obj A))
    have h : (proEtaleIsoPostcompose g).op.whiskerLeft
        (toSheafify (ProEt.topology (Spec (.of D.k)))
          ((Functor.const (Spec (.of D.k)).ProEtᵒᵖ).obj A)) ≫ i.inv =
        toSheafify (ProEt.topology (Spec (.of D.k)))
          ((Functor.const (Spec (.of D.k)).ProEtᵒᵖ).obj A) := by
      apply (i.comp_inv_eq).2
      exact ((proEtaleIsoPostcompose g).toSheafify_pullbackSheafificationCompatibility
        CommRingCat.{max u (t + 1)} (ProEt.topology (Spec (.of D.k)))
          (ProEt.topology (Spec (.of D.k)))
            ((Functor.const (Spec (.of D.k)).ProEtᵒᵖ).obj A)).symm
    exact congrArg (fun f ↦ f.app (op U) a) h
  · exact (isoSectionwiseConstantMap_existsUnique g A).exists.choose_spec

set_option backward.isDefEq.respectTransparency.types false

private theorem ringSystem_map {m n : ℕ} (h : n ≤ m) :
    (sheafCompose (ProEt.topology (Spec (.of D.k)))
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
        ((coefficientSequenceCommRingSystem l E (Spec (.of D.k))).map (homOfLE h).op) =
      (integralCoefficientSheafSystem l E (Spec (.of D.k))).map (homOfLE h).op := by
  let ε : (coefficientSequenceCommRingSystem l E (Spec (.of D.k)) ⋙
        sheafCompose (ProEt.topology (Spec (.of D.k)))
          (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})) ⟶
      integralCoefficientSheafSystem l E (Spec (.of D.k)) :=
    NatTrans.ofOpSequence (fun _ ↦ 𝟙 _) (fun k ↦ by
      dsimp only [Functor.comp_map, coefficientSequenceCommRingSystem,
        integralCoefficientSheafSystem]
      rw [Functor.ofOpSequence_map_homOfLE_succ,
        Functor.ofOpSequence_map_homOfLE_succ]
      simp only [Category.comp_id, Category.id_comp]
      rfl)
  have he := ε.naturality (homOfLE h).op
  change _ ≫ 𝟙 _ = 𝟙 _ ≫ _ at he
  simpa only [Category.comp_id, Category.id_comp, Functor.comp_map] using he

private theorem horizontal_map {m n : ℕ} (h : n ≤ m)
    (U : (Spec (.of D.k)).ProEtᵒᵖ) :
    (sequenceRing D l E).obj.map
      (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op =
      ((integralCoefficientSheafSystem l E (Spec (.of D.k))).map
        (homOfLE h).op).hom.app U := by
  have he := congrArg (fun f ↦ f.hom.app U) (ringSystem_map D l E h)
  change (forget₂ CommRingCat RingCat).map
    (((coefficientSequenceCommRingSystem l E (Spec (.of D.k))).map
      (homOfLE h).op).hom.app U ≫
        ((coefficientSequenceCommRingSystem l E (Spec (.of D.k))).obj
          (op n)).obj.map (𝟙 U)) = _
  rw [CategoryTheory.Functor.map_id, Category.comp_id]
  exact he

private theorem sequence_map {X Y : ℕ × (Spec (.of D.k)).ProEt} (f : Y ⟶ X) :
    (sequenceRing D l E).obj.map f.op =
      ((integralCoefficientSheafSystem l E (Spec (.of D.k))).map f.1.op).hom.app
          (op X.2) ≫
        (integralCoefficientSheaf l E (Spec (.of D.k)) Y.1).obj.map f.2.op := by
  have he := congrArg (fun k ↦ k.hom.app (op X.2))
    (ringSystem_map D l E (leOfHom f.1))
  change (forget₂ CommRingCat RingCat).map (_ ≫ _) = _
  rw [Functor.map_comp]
  change (forget₂ CommRingCat RingCat).map
    (((coefficientSequenceCommRingSystem l E (Spec (.of D.k))).map
      (homOfLE (leOfHom f.1)).op).hom.app (op X.2)) ≫ _ = _
  change (forget₂ CommRingCat RingCat).map
    (((coefficientSequenceCommRingSystem l E (Spec (.of D.k))).map
      (homOfLE (leOfHom f.1)).op).hom.app (op X.2)) = _ at he
  rw [he]
  rfl

private theorem finite_comparison_naturality
    (g : Spec (.of D.k) ⟶ Spec (.of D.k)) [IsIso g] (n : ℕ) :
    inverseImageFiniteCoefficientMap l E g (n + 1) ≫
        integralCoefficientSheafTransition l E (Spec (.of D.k)) n =
      (isoSectionwiseInverseImage g RingCat.{max u (t + 1)}).map
        (integralCoefficientSheafTransition l E (Spec (.of D.k)) n) ≫
          inverseImageFiniteCoefficientMap l E g n := by
  let q : CommRingCat.of (ULift.{t + 1}
      (Padic.coefficientExtensionRing l E (n + 2))) ⟶
      CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))) :=
    CommRingCat.ofHom
      ((ULift.ringEquiv : ULift.{t + 1} _ ≃+* _).symm.toRingHom.comp
        ((Padic.coefficientExtensionTransition l E (n + 1)).comp
          (ULift.ringEquiv : ULift.{t + 1} _ ≃+* _).toRingHom))
  have := postcompose_cocontinuous D g
  let e := ((proEtaleIsoPostcompose g).pushforwardContinuousSheafificationCompatibility
    CommRingCat.{max u (t + 1)} (ProEt.topology (Spec (.of D.k)))
      (ProEt.topology (Spec (.of D.k)))).symm
  have h := e.hom.naturality ((Functor.const (Spec (.of D.k)).ProEtᵒᵖ).map q)
  let W := sheafCompose (ProEt.topology (Spec (.of D.k)))
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})
  have h' := congrArg W.map h.symm
  simp only [Functor.map_comp] at h'
  change W.map (constantComparisonIso D g _).hom ≫ _ =
    _ ≫ W.map (constantComparisonIso D g _).hom at h'
  rw [constantComparisonIso_eq, constantComparisonIso_eq] at h'
  exact h'

private def inverseFiniteSystem
    (g : Spec (.of D.k) ⟶ Spec (.of D.k)) [IsIso g] :
    integralCoefficientSheafSystem l E (Spec (.of D.k)) ⟶
      integralCoefficientSheafSystem l E (Spec (.of D.k)) ⋙
        isoSectionwiseInverseImage g RingCat.{max u (t + 1)} :=
  NatTrans.ofOpSequence
    (fun n ↦ inv (inverseImageFiniteCoefficientMap l E g n)) (fun n ↦ by
      dsimp only [Functor.comp_map, integralCoefficientSheafSystem]
      rw [Functor.ofOpSequence_map_homOfLE_succ]
      apply (cancel_mono (inverseImageFiniteCoefficientMap l E g n)).mp
      rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id, Category.assoc,
        ← finite_comparison_naturality, ← Category.assoc, IsIso.inv_hom_id,
        Category.id_comp])

/-- The inverses c_n inverse assemble with exactly the original quotient transitions.
Source: blueprint proof (3), point-factor prerequisite; Stacks 03CO
(blueprint: lem-trf-point-restriction-system-chain-map).
Proof: lem-weil-proetale-isomorphism-inverse-image (3), applied to the quotient
map A_(n+1) to A_n, gives rho_n c_(n+1) = c_n F(rho_n). Compose with the
inverses to obtain F(rho_n) c_(n+1) inverse = c_n inverse rho_n.
Together with vertical naturality this gives a morphism of sequence ring sheaves.
Every section component is prescribed, so extensionality proves uniqueness. -/
theorem coefficient_existsUnique
    (g : Spec (.of D.k) ⟶ Spec (.of D.k)) [IsIso g] :
    ∃! c : sequenceRing D l E ⟶
      ((reindex D g).sheafPushforwardContinuous RingCat.{max u (t + 1)}
        (coefficientSequenceTopology (ProEt.topology (Spec (.of D.k))))
        (coefficientSequenceTopology (ProEt.topology (Spec (.of D.k))))).obj
          (sequenceRing D l E),
      ∀ (n : ℕ) (U : (Spec (.of D.k)).ProEt),
        HEq (c.hom.app (op (n, U)))
          ((inv (pointRestrictionCoefficientMap l E g (some n))).hom.app (op U)) := by
  let c : sequenceRing D l E ⟶
      ((reindex D g).sheafPushforwardContinuous RingCat.{max u (t + 1)}
        (coefficientSequenceTopology (ProEt.topology (Spec (.of D.k))))
        (coefficientSequenceTopology (ProEt.topology (Spec (.of D.k))))).obj
          (sequenceRing D l E) :=
    ⟨{ app X := ((inverseFiniteSystem D l E g).app (op X.unop.1)).hom.app
          (op X.unop.2)
       naturality X Y f := by
         have h := (inverseFiniteSystem D l E g).naturality f.unop.1.op
         have hh := congrArg (fun k ↦ k.hom.app (op X.unop.2)) h
         have hv := ((inverseFiniteSystem D l E g).app (op Y.unop.1)).hom.naturality
           f.unop.2.op
         simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app] at hh
         change (sequenceRing D l E).obj.map f ≫ _ =
           _ ≫ (sequenceRing D l E).obj.map ((reindex D g).map f.unop).op
         rw [show f = f.unop.op from rfl, sequence_map, sequence_map]
         exact (Category.assoc _ _ _).trans
           ((congrArg (fun k ↦
             ((integralCoefficientSheafSystem l E (Spec (.of D.k))).map
               f.unop.1.op).hom.app (op X.unop.2) ≫ k) hv).trans
             ((Category.assoc _ _ _).symm.trans
               ((congrArg (fun k ↦ k ≫
                 ((integralCoefficientSheafSystem l E (Spec (.of D.k)) ⋙
                   isoSectionwiseInverseImage g RingCat).obj
                     (op Y.unop.1)).obj.map f.unop.2.op) hh).trans
                   (Category.assoc _ _ _)))) }⟩
  refine ⟨c, fun _ _ ↦ HEq.rfl, ?_⟩
  intro d hd
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext X
  exact eq_of_heq (hd X.unop.1 X.unop.2)


/-- The unique specified coefficient comparison, rather than a free ring morphism.
Source: blueprint proof (3), point-factor prerequisite
(blueprint: lem-trf-point-restriction-system-chain-map). -/
def coefficient (g : Spec (.of D.k) ⟶ Spec (.of D.k)) [IsIso g] :=
  (coefficient_existsUnique D l E g).exists.choose

/-- G applies inverse image at every level and transports the action by c_n inverse.
Its horizontal maps are the original maps evaluated on reindexed objects.
Source: blueprint proof (3), point-factor prerequisite
(blueprint: lem-trf-point-restriction-system-chain-map). -/
def pull (g : Spec (.of D.k) ⟶ Spec (.of D.k)) [IsIso g] :
    coefficientSequenceModules l E (Spec (.of D.k)) ⥤
      coefficientSequenceModules l E (Spec (.of D.k)) :=
  SheafOfModules.pushforward (F := reindex D g) (coefficient D l E g)

/-- Levelwise sections restricted to R, retaining all original transitions.
Restriction through R to the completion and then B_n is the same as R to A_n.
The scalar ring is the common-universe lift used by the recorded point sections.
Source: blueprint proof (3), point-factor prerequisite; Stacks 03CW and 0941
(blueprint: lem-trf-point-restriction-system-chain-map). -/
abbrev sections : coefficientSequenceModules l E (Spec (.of D.k)) ⥤
    (ℕᵒᵖ ⥤ ModuleCat.{max u (t + 1)} (pointRestrictionScalars.{t, u} l E none)) :=
  coefficientSequenceRestriction l E (Spec (.of D.k)) ⋙
    (Functor.whiskeringRight ℕᵒᵖ _ _).obj (pointRestrictionSections l E D.k none)

set_option backward.isDefEq.respectTransparency.types true

private def vertical {m n : ℕ} (h : n ≤ m) :
    Prod.sectR n (Spec (.of D.k)).ProEt ⟶ Prod.sectR m (Spec (.of D.k)).ProEt where
  app U := Prod.mkHom (homOfLE h) (𝟙 U)
  naturality := fun {_ _} f ↦ by ext <;> simp

private def scalarLeg (n : ℕ) :
    SheafOfModules.derivedChangeRingIndependentCoefficients
      (ProEt.topology (Spec (.of D.k)))
        (completedIntegralCommRingSheafUnrestricted l E (Spec (.of D.k))) ⟶
      ((Prod.sectR n (Spec (.of D.k)).ProEt).sheafPushforwardContinuous RingCat
        (ProEt.topology (Spec (.of D.k)))
        (coefficientSequenceTopology (ProEt.topology (Spec (.of D.k))))).obj
          (sequenceRing D l E) :=
  (sheafCompose (ProEt.topology (Spec (.of D.k)))
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
      (completedIntegralCommRingProjectionUnrestricted l E (Spec (.of D.k)) n) ≫
    eqToHom (coefficientSequenceEvaluationRing_eq l E (Spec (.of D.k)) n).symm

private theorem evaluation_horizontal {m n : ℕ} (h : n ≤ m) :
    eqToHom (coefficientSequenceEvaluationRing_eq l E (Spec (.of D.k)) m).symm ≫
      (Functor.sheafPushforwardContinuousNatTrans (vertical D h) RingCat
        (ProEt.topology (Spec (.of D.k)))
        (coefficientSequenceTopology (ProEt.topology (Spec (.of D.k))))).app
          (sequenceRing D l E) =
      (integralCoefficientSheafSystem l E (Spec (.of D.k))).map (homOfLE h).op ≫
        eqToHom (coefficientSequenceEvaluationRing_eq l E (Spec (.of D.k)) n).symm := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  have hm : (eqToHom (coefficientSequenceEvaluationRing_eq l E
      (Spec (.of D.k)) m).symm).hom.app U = 𝟙 _ := by
    rw [ObjectProperty.eqToHom_hom, eqToHom_app]
    rfl
  have hn : (eqToHom (coefficientSequenceEvaluationRing_eq l E
      (Spec (.of D.k)) n).symm).hom.app U = 𝟙 _ := by
    rw [ObjectProperty.eqToHom_hom, eqToHom_app]
    rfl
  change (eqToHom (coefficientSequenceEvaluationRing_eq l E
      (Spec (.of D.k)) m).symm).hom.app U ≫ _ =
    _ ≫ (eqToHom (coefficientSequenceEvaluationRing_eq l E
      (Spec (.of D.k)) n).symm).hom.app U
  rw [hm, hn, Category.id_comp, Category.comp_id]
  exact horizontal_map D l E h U

private theorem scalarLeg_naturality {m n : ℕ} (h : n ≤ m) :
    scalarLeg D l E m ≫ (Functor.sheafPushforwardContinuousNatTrans
      (vertical D h) RingCat (ProEt.topology (Spec (.of D.k)))
        (coefficientSequenceTopology (ProEt.topology (Spec (.of D.k))))).app
          (sequenceRing D l E) = scalarLeg D l E n := by
  dsimp only [scalarLeg]
  rw [Category.assoc, evaluation_horizontal, ← Category.assoc]
  exact congrArg (fun f ↦ f ≫
    eqToHom (coefficientSequenceEvaluationRing_eq l E (Spec (.of D.k)) n).symm)
      (limit.w (integralCoefficientSheafSystem l E (Spec (.of D.k))) (homOfLE h).op)

private def sequenceVertical {C : Type*} [Category* C] {m n : ℕ} (h : n ≤ m) :
    Prod.sectR n C ⟶ Prod.sectR m C where
  app U := Prod.mkHom (homOfLE h) (𝟙 U)
  naturality := fun {_ _} f ↦ by ext <;> simp

private def genericRestriction
    {C : Type*} [Category* C] (J : GrothendieckTopology C)
    (R : Sheaf (coefficientSequenceTopology J) RingCat.{u}) (A : Sheaf J RingCat.{u})
    [∀ n : ℕ, (Prod.sectR n C).IsContinuous J (coefficientSequenceTopology J)]
    (ρ : ∀ n : ℕ, A ⟶ ((Prod.sectR n C).sheafPushforwardContinuous RingCat J
      (coefficientSequenceTopology J)).obj R)
    (hρ : ∀ {m n : ℕ} (h : n ≤ m),
      ρ m ≫ (Functor.sheafPushforwardContinuousNatTrans (sequenceVertical h) RingCat J
        (coefficientSequenceTopology J)).app R = ρ n) :
    SheafOfModules.{u} R ⥤ (ℕᵒᵖ ⥤ SheafOfModules.{u} A) := by
  let τ {m n : ℕ} (h : n ≤ m) :
      SheafOfModules.pushforward (ρ m) ⟶
        SheafOfModules.pushforward (ρ n) :=
    SheafOfModules.pushforwardNatTrans (ρ m) (sequenceVertical h) ≫
      (SheafOfModules.pushforwardCongr (hρ h)).hom
  exact
    { obj M :=
        { obj n := (SheafOfModules.pushforward (ρ n.unop)).obj M
          map {m n} f := (τ (leOfHom f.unop)).app M
          map_id n := by
            ext V x
            change M.val.presheaf.map _ x = x
            have he : (sequenceVertical (Nat.le_refl n.unop)).app V.unop = 𝟙 _ := by
              apply Prod.hom_ext
              · apply Subsingleton.elim
              · rfl
            change M.val.presheaf.map ((sequenceVertical _).app V.unop).op x = x
            rw [he, op_id, M.val.presheaf.map_id]
            rfl
          map_comp {k m n} f g := by
            ext V x
            change M.val.presheaf.map _ x =
              M.val.presheaf.map _ (M.val.presheaf.map _ x)
            rw [← Functor.map_comp_apply]
            congr 3
            apply Quiver.Hom.unop_inj
            apply Prod.hom_ext
            · apply Subsingleton.elim
            · simp [sequenceVertical] }
      map f :=
        { app n := (SheafOfModules.pushforward (ρ n.unop)).map f
          naturality {m n} g := by
            ext V x
            exact congrArg (fun k ↦ k x)
              (f.val.naturality ((sequenceVertical (leOfHom g.unop)).app V.unop).op) }
      map_id M := by ext n V x; rfl
      map_comp f g := by ext n V x; rfl }


private abbrev concreteRestriction : coefficientSequenceModules l E (Spec (.of D.k)) ⥤
    (ℕᵒᵖ ⥤ scalarReductionSource l E (Spec (.of D.k))) :=
  genericRestriction (ProEt.topology (Spec (.of D.k))) (sequenceRing D l E) _
    (scalarLeg D l E) (fun h ↦ scalarLeg_naturality D l E h)

private theorem pushforward_restrict_obj
    {C : Type*} [Category* C] (J : GrothendieckTopology C)
    (R : Sheaf (coefficientSequenceTopology J) RingCat.{u})
    {A B : Sheaf J RingCat.{u}} (n : ℕ)
    [(Prod.sectR n C).IsContinuous J (coefficientSequenceTopology J)]
    (p : A ⟶ B)
    (φ : B ⟶ ((Prod.sectR n C).sheafPushforwardContinuous RingCat J
      (coefficientSequenceTopology J)).obj R) (M : SheafOfModules.{u} R) :
    (SheafOfModules.pushforward (p ≫ φ)).obj M =
      (SheafOfModules.restrictScalars p).obj ((SheafOfModules.pushforward φ).obj M) := by
  rfl

private theorem restriction_eq : coefficientSequenceRestriction l E (Spec (.of D.k)) =
    concreteRestriction D l E := by
  apply (coefficientSequenceRestriction_exists l E (Spec (.of D.k))).unique
  · exact (coefficientSequenceRestriction_exists l E (Spec (.of D.k))).exists.choose_spec
  · refine ⟨?_, fun _ _ _ _ _ ↦ HEq.rfl, fun {_ _} _ _ _ ↦ HEq.rfl⟩
    intro M n
    exact pushforward_restrict_obj _ _ n _ _ M


private theorem scalarLeg_app (n : ℕ) (U : (Spec (.of D.k)).ProEtᵒᵖ) :
    (scalarLeg D l E n).hom.app U =
      (limit.π (integralCoefficientSheafSystem l E (Spec (.of D.k))) (op n)).hom.app U := by
  have he : (eqToHom (coefficientSequenceEvaluationRing_eq l E
      (Spec (.of D.k)) n).symm).hom.app U = 𝟙 _ := by
    rw [ObjectProperty.eqToHom_hom, eqToHom_app]
    rfl
  simp only [scalarLeg, ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    he]
  rfl


private theorem coefficient_app
    (g : Spec (.of D.k) ⟶ Spec (.of D.k)) [IsIso g] (n : ℕ)
    (U : (Spec (.of D.k)).ProEt) :
    (coefficient D l E g).hom.app (op (n, U)) =
      (inv (pointRestrictionCoefficientMap l E g (some n))).hom.app (op U) :=
  eq_of_heq ((coefficient_existsUnique D l E g).exists.choose_spec n U)

private theorem inverse_square {C : Type*} [Category* C] {W X Y Z : C}
    (a : W ⟶ X) (b : Y ⟶ Z) [IsIso a] [IsIso b]
    (p : W ⟶ Y) (q : X ⟶ Z) (h : a ≫ q = p ≫ b) :
    inv a ≫ p = q ≫ inv b := by
  apply (cancel_epi a).mp
  rw [← Category.assoc, IsIso.hom_inv_id, Category.id_comp, ← Category.assoc, h,
    Category.assoc, IsIso.hom_inv_id, Category.comp_id]

private theorem completed_inverse_projection
    (g : Spec (.of D.k) ⟶ Spec (.of D.k)) [IsIso g] (n : ℕ) :
    inv (inverseImageCompletedCoefficientMap l E g) ≫
      (isoSectionwiseInverseImage g RingCat.{max u (t + 1)}).map
        (limit.π (integralCoefficientSheafSystem l E (Spec (.of D.k))) (op n)) =
      limit.π (integralCoefficientSheafSystem l E (Spec (.of D.k))) (op n) ≫
        inv (inverseImageFiniteCoefficientMap l E g n) := by
  apply inverse_square
  exact limit.lift_π _ _

private theorem vertical_map (n : ℕ) {U V : (Spec (.of D.k)).ProEt} (f : V ⟶ U) :
    (sequenceRing D l E).obj.map (Prod.mkHom (𝟙 n) f).op =
      (integralCoefficientSheaf l E (Spec (.of D.k)) n).obj.map f.op := by
  have h := sequence_map D l E (Prod.mkHom (𝟙 n) f)
  simpa only [op_id, CategoryTheory.Functor.map_id,
    ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app, Category.id_comp] using h

private theorem scalar_restriction (_hl : l ≠ D.p)
    (g : Spec (.of D.k) ⟶ Spec (.of D.k)) [IsIso g] (n : ℕ)
    (b : pointRestrictionScalars.{t, u} l E none) :
    (sequenceRing D l E).obj.map
        (Prod.mkHom (𝟙 n) (pointRestrictionArrow g)).op
        ((scalarLeg D l E n).hom.app (op (ProEt.mk (𝟙 _)))
          (pointRestrictionScalarAt l E (Spec (.of D.k)) none (ProEt.mk (𝟙 _)) b)) =
      (coefficient D l E g).hom.app (op (n, ProEt.mk (𝟙 _)))
        ((scalarLeg D l E n).hom.app (op (ProEt.mk (𝟙 _)))
          (pointRestrictionScalarAt l E (Spec (.of D.k)) none (ProEt.mk (𝟙 _)) b)) := by
  rw [coefficient_app, scalarLeg_app, vertical_map]
  have hn := (point_automorphism_restriction_natural l E D _hl g none).1 b
  have hp := (limit.π (integralCoefficientSheafSystem l E (Spec (.of D.k)))
    (op n)).hom.naturality (pointRestrictionArrow g).op
  have hi := congrArg (fun f ↦ f.hom.app (op (ProEt.mk (𝟙 _))))
    (completed_inverse_projection D l E g n)
  exact (ConcreteCategory.congr_hom hp.symm _).trans
    ((congrArg (fun x ↦
      (limit.π (integralCoefficientSheafSystem l E (Spec (.of D.k)))
        (op n)).hom.app (op ((proEtaleIsoPostcompose g).obj (ProEt.mk (𝟙 _)))) x) hn).trans
          (ConcreteCategory.congr_hom hi _))

private abbrev concreteSections : coefficientSequenceModules l E (Spec (.of D.k)) ⥤
    (ℕᵒᵖ ⥤ ModuleCat.{max u (t + 1)} (pointRestrictionScalars.{t, u} l E none)) :=
  concreteRestriction D l E ⋙
    (Functor.whiskeringRight ℕᵒᵖ _ _).obj (pointRestrictionSections l E D.k none)

private theorem sections_eq : sections D l E = concreteSections D l E := by
  dsimp only [sections, concreteSections]
  rw [restriction_eq]


private def restrictionLinear
    {C : Type*} [Category* C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} (M : SheafOfModules.{u} R)
    {X Y : Cᵒᵖ} (v : X ⟶ Y) (B : RingCat.{u})
    (q : B →+* R.obj.obj X) (q' : B →+* R.obj.obj Y)
    (h : ∀ b : B, R.obj.map v (q b) = q' b) :
    (ModuleCat.restrictScalars q).obj (M.val.obj X) ⟶
      (ModuleCat.restrictScalars q').obj (M.val.obj Y) :=
  ModuleCat.ofHom
    (X := (ModuleCat.restrictScalars q).obj (M.val.obj X))
    (Y := (ModuleCat.restrictScalars q').obj (M.val.obj Y))
    { toFun := M.val.map v
      map_add' := map_add _
      map_smul' b x := by
        change M.val.map v (q b • x) = q' b • M.val.map v x
        rw [M.val.map_smul, h] }

private def genericSections
    {C : Type*} [Category* C] (J : GrothendieckTopology C)
    (R : Sheaf (coefficientSequenceTopology J) RingCat.{u}) (A : Sheaf J RingCat.{u})
    [∀ n : ℕ, (Prod.sectR n C).IsContinuous J (coefficientSequenceTopology J)]
    (ρ : ∀ n : ℕ, A ⟶ ((Prod.sectR n C).sheafPushforwardContinuous RingCat J
      (coefficientSequenceTopology J)).obj R)
    (hρ : ∀ {m n : ℕ} (h : n ≤ m),
      ρ m ≫ (Functor.sheafPushforwardContinuousNatTrans (sequenceVertical h) RingCat J
        (coefficientSequenceTopology J)).app R = ρ n)
    (B : RingCat.{u}) (U : C) (p : B →+* A.obj.obj (op U)) :=
  genericRestriction J R A ρ hρ ⋙ (Functor.whiskeringRight ℕᵒᵖ _ _).obj
    (SheafOfModules.evaluation A (op U) ⋙ ModuleCat.restrictScalars p)

private def genericTransformation
    {C : Type*} [Category* C] (J : GrothendieckTopology C)
    (R : Sheaf (coefficientSequenceTopology J) RingCat.{u}) (A : Sheaf J RingCat.{u})
    [∀ n : ℕ, (Prod.sectR n C).IsContinuous J (coefficientSequenceTopology J)]
    (ρ : ∀ n : ℕ, A ⟶ ((Prod.sectR n C).sheafPushforwardContinuous RingCat J
      (coefficientSequenceTopology J)).obj R)
    (hρ : ∀ {m n : ℕ} (h : n ≤ m),
      ρ m ≫ (Functor.sheafPushforwardContinuousNatTrans (sequenceVertical h) RingCat J
        (coefficientSequenceTopology J)).app R = ρ n)
    (B : RingCat.{u}) (U : C) (p : B →+* A.obj.obj (op U)) (F : C ⥤ C)
    [((𝟭 ℕ).prod F).IsContinuous (coefficientSequenceTopology J)
      (coefficientSequenceTopology J)]
    (c : R ⟶ (((𝟭 ℕ).prod F).sheafPushforwardContinuous RingCat
      (coefficientSequenceTopology J) (coefficientSequenceTopology J)).obj R)
    (v : F.obj U ⟶ U)
    (hs : ∀ (n : ℕ) (b : B),
      R.obj.map (Prod.mkHom (𝟙 n) v).op ((ρ n).hom.app (op U) (p b)) =
        c.hom.app (op (n, U)) ((ρ n).hom.app (op U) (p b))) :
    genericSections J R A ρ hρ B U p ⟶
      SheafOfModules.pushforward c ⋙ genericSections J R A ρ hρ B U p where
  app M :=
    { app n := restrictionLinear M (Prod.mkHom (𝟙 n.unop) v).op B
        (((ρ n.unop).hom.app (op U)).hom.comp p)
        ((c.hom.app (op (n.unop, U))).hom.comp
          (((ρ n.unop).hom.app (op U)).hom.comp p))
        (hs n.unop)
      naturality {m n} f := by
        ext x
        change M.val.presheaf.map _ (M.val.presheaf.map _ x) =
          M.val.presheaf.map _ (M.val.presheaf.map _ x)
        simp only [← Functor.map_comp_apply, ← op_comp]
        congr 3
        apply Quiver.Hom.unop_inj
        apply Prod.hom_ext
        · apply Subsingleton.elim
        · change v ≫ 𝟙 U = F.map (𝟙 U) ≫ v
          rw [F.map_id, Category.comp_id, Category.id_comp] }
  naturality {M N} f := by
    ext n x
    exact (PresheafOfModules.naturality_apply f.val
      (Prod.mkHom (𝟙 n.unop) v).op x).symm

set_option backward.isDefEq.respectTransparency.types false in
private def restrictionTransformation (_hl : l ≠ D.p)
    (g : Spec (.of D.k) ⟶ Spec (.of D.k)) [IsIso g] :
    concreteSections D l E ⟶ pull D l E g ⋙ concreteSections D l E := by
  letI : ((𝟭 ℕ).prod (proEtaleIsoPostcompose g)).IsContinuous
      (coefficientSequenceTopology (ProEt.topology (Spec (.of D.k))))
      (coefficientSequenceTopology (ProEt.topology (Spec (.of D.k)))) :=
    reindexContinuous D g
  exact genericTransformation (ProEt.topology (Spec (.of D.k))) (sequenceRing D l E) _
    (scalarLeg D l E) (fun h ↦ scalarLeg_naturality D l E h)
    (pointRestrictionScalars.{t, u} l E none) (ProEt.mk (𝟙 _))
    (pointRestrictionScalarAt l E (Spec (.of D.k)) none (ProEt.mk (𝟙 _)))
    (proEtaleIsoPostcompose g) (coefficient D l E g) (pointRestrictionArrow g)
    (scalar_restriction D l E _hl g)

private def transportTransformation
    {C A : Type*} [Category* C] [Category* A]
    {F F' : C ⥤ A} (h : F = F') (G : C ⥤ C) (α : F' ⟶ G ⋙ F') :
    F ⟶ G ⋙ F :=
  eqToHom h ≫ α ≫ Functor.whiskerLeft G (eqToHom h.symm)

private theorem transportTransformation_app
    {C : Type*} [Category* C] {B : Type u} [Ring B]
    {F F' : C ⥤ ℕᵒᵖ ⥤ ModuleCat.{u} B} (h : F = F')
    (G : C ⥤ C) (α : F' ⟶ G ⋙ F') (M : C) (n : ℕᵒᵖ) :
    HEq (fun x ↦ (((transportTransformation h G α).app M).app n) x)
      (fun x ↦ ((α.app M).app n) x) := by
  subst F'
  rfl

private theorem complexTransformation_ext
    {C : Type*} [Category* C] [HasZeroMorphisms C]
    {B : Type u} [Ring B] {F G : C ⥤ ℕᵒᵖ ⥤ ModuleCat.{u} B}
    [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
    {v w : F.mapHomologicalComplex (ComplexShape.up ℤ) ⟶
      G.mapHomologicalComplex (ComplexShape.up ℤ)}
    (h : ∀ (M : CochainComplex C ℤ) (i : ℤ) (n : ℕᵒᵖ),
      (fun x ↦ (((v.app M).f i).app n) x) =
        (fun x ↦ (((w.app M).f i).app n) x)) : v = w := by
  apply NatTrans.ext
  funext M
  apply HomologicalComplex.Hom.ext
  funext i
  apply NatTrans.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact congrFun (h M i n) x

private theorem transportComplex_app
    {C : Type*} [Category* C] [HasZeroMorphisms C]
    {B : Type u} [Ring B] {F F' : C ⥤ ℕᵒᵖ ⥤ ModuleCat.{u} B}
    [F.PreservesZeroMorphisms]
    (h : F = F') (G : C ⥤ C) [G.PreservesZeroMorphisms]
    (α : F' ⟶ G ⋙ F') (M : CochainComplex C ℤ) (i : ℤ) (n : ℕᵒᵖ) :
    HEq (fun x ↦ ((((NatTrans.mapHomologicalComplex
      (transportTransformation h G α) (ComplexShape.up ℤ)).app M).f i).app n) x)
      (fun x ↦ ((α.app (M.X i)).app n) x) := by
  exact transportTransformation_app h G α (M.X i) n

/-- Additivity of sections and inverse image on the actual strict-system category.
Source: blueprint proof (3), point-factor prerequisite; Stacks 03CW
(blueprint: lem-trf-point-restriction-system-chain-map).
Proof: both operations act on morphisms by their section components. Evaluation,
restriction of scalars and reindexing preserve pointwise addition of morphisms. -/
theorem operations_additive
    (g : Spec (.of D.k) ⟶ Spec (.of D.k)) [IsIso g] :
    (sections D l E).Additive ∧ (pull D l E g).Additive := by
  constructor
  · constructor
    intro M N f h
    ext n x
    simp only [sections, Functor.comp_map, Functor.whiskeringRight_obj_map,
      Functor.whiskerRight_app, Functor.map_add, NatTrans.app_add]
    rfl
  · constructor
    intro M N f h
    ext U x
    rfl

/-- Additivity of the specified sections functor.
Source: blueprint proof (3) (blueprint: lem-trf-point-restriction-system-chain-map). -/
instance sectionsAdditive : (sections D l E).Additive :=
  (operations_additive D l E (𝟙 _)).1

/-- Additivity of the specified inverse image.
Source: blueprint proof (3) (blueprint: lem-trf-point-restriction-system-chain-map). -/
instance pullAdditive (g : Spec (.of D.k) ⟶ Spec (.of D.k)) [IsIso g] :
    (pull D l E g).Additive := (operations_additive D l E g).2

private instance concreteSections_additive : (concreteSections D l E).Additive := by
  rw [← sections_eq]
  infer_instance

private instance sections_preservesZeroMorphisms :
    (sections D l E).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_additive _

private instance pullSections_preservesZeroMorphisms
    (g : Spec (.of D.k) ⟶ Spec (.of D.k)) [IsIso g] :
    (pull D l E g ⋙ sections D l E).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_additive _

/-- Unbounded cochain complexes of whole R-module towers after sections.
Source: blueprint proof (3), point-factor prerequisite
(blueprint: lem-trf-point-restriction-system-chain-map). -/
abbrev complexSections := (sections D l E).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The same sections construction after the specified levelwise inverse image.
Source: blueprint proof (3), point-factor prerequisite
(blueprint: lem-trf-point-restriction-system-chain-map). -/
abbrev transportedComplexSections
    (g : Spec (.of D.k) ⟶ Spec (.of D.k)) [IsIso g] :=
  (pull D l E g ⋙ sections D l E).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The prescribed restriction/insertion components. HEq identifies only the unchanged
section carriers under the recorded coefficient restriction, which uses equality casts.
In the canonical inverse-image coordinates the colimit insertion is identity.
Source: blueprint proof (3), point-factor prerequisite
(blueprint: lem-trf-point-restriction-system-chain-map). -/
def HasRestrictionComponents
    (g : Spec (.of D.k) ⟶ Spec (.of D.k)) [IsIso g]
    (u : complexSections D l E ⟶ transportedComplexSections D l E g) : Prop :=
  ∀ (M : CochainComplex (coefficientSequenceModules l E (Spec (.of D.k))) ℤ)
    (i : ℤ) (n : ℕ),
    HEq (fun x : (((complexSections D l E).obj M).X i).obj (op n) ↦
      (((u.app M).f i).app (op n)) x)
      (fun x : (M.X i).val.obj (op (n, ProEt.mk (𝟙 (Spec (.of D.k))))) ↦
        (M.X i).val.map (Prod.mkHom (𝟙 n) (pointRestrictionArrow g)).op x)

/-- Restriction/insertion is A_n-linear with its specified transported target action,
and gives the unique natural R-linear chain map of entire strict towers.
The inner natural transformation at each degree enforces the strict transition
identity; its homological-complex structure enforces the chain equation, and the
outer natural transformation enforces naturality in every system chain map.

Source: blueprint proof (3), explicit point-factor prerequisite, agent-formulated
simultaneous-system extension
(blueprint: lem-trf-point-restriction-system-chain-map).

Proof: (1) Apply lem-weil-point-automorphism-restriction-natural with Lambda=A_n
in every degree. Its restriction/insertion formula and sigma(bx)=c_n inverse(b)sigma(x)
give A_n-linearity for the transported action, hence R-linearity.
(2) The coefficient square in coefficient_existsUnique makes F(v_n) quotient-linear.
Restriction of scalars changes neither sections nor restrictions.
(3) In reindexing coordinates, F(v_n)sigma(x)=v_n(V)(x restricted to V)
=v_n(U)(x) restricted to V=sigma(v_n(x)), by naturality of the module-sheaf
morphism v_n. This uses arbitrary v_n, without any cartesian assumption.
(4) These squares assemble to tower maps in each degree. Apply the single-level
naturality to each differential and each chain map f to obtain the chain equation
and Gamma(Gf) u_M = u_M' Gamma(f). Every i,n component is prescribed, proving
uniqueness. There is no degree bound or condition on the transitions. -/
theorem restriction_system_chain_map (_hl : l ≠ D.p)
    (g : Spec (.of D.k) ⟶ Spec (.of D.k)) [IsIso g] :
    (∀ (n : ℕ)
      (M : SheafOfModules.{max u (t + 1)}
        (pointRestrictionRing l E (Spec (.of D.k)) (some n)))
      (b : pointRestrictionScalars.{t, u} l E (some n))
      (x : M.val.obj (op (ProEt.mk (𝟙 (Spec (.of D.k)))))),
      pointRestrictionRaw l E g (some n) M
        (pointRestrictionScalarAt l E (Spec (.of D.k)) (some n) (ProEt.mk (𝟙 _)) b • x) =
      pointRestrictionScalarAt l E (Spec (.of D.k)) (some n) (ProEt.mk (𝟙 _)) b •
        pointRestrictionRaw l E g (some n) M x) ∧
    ∃! u : complexSections D l E ⟶ transportedComplexSections D l E g,
      HasRestrictionComponents D l E g u := by
  constructor
  · intro n M b x
    exact (point_automorphism_restriction_natural l E D _hl g (some n)).2.1 M b x
  · let α := transportTransformation (sections_eq D l E) (pull D l E g)
      (restrictionTransformation D l E _hl g)
    let u := NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ)
    have hu : HasRestrictionComponents D l E g u := by
      intro M i n
      exact (transportComplex_app (sections_eq D l E) (pull D l E g)
        (restrictionTransformation D l E _hl g) M i (op n)).trans HEq.rfl
    refine ⟨u, hu, ?_⟩
    intro v hv
    apply complexTransformation_ext
    intro M i n
    exact eq_of_heq ((hv M i n.unop).trans (hu M i n.unop).symm)

end WeilConjectures.PointRestrictionSystem
