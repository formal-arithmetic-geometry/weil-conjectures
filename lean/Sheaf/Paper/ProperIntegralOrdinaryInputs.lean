/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NG
-/
module

public import Sheaf.Paper.ProperIntegralOrdinaryData
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.AlgebraicGeometry.ChosenCartesianSquare
public import Sheaf.Paper.AdicCoefficientDatum
public import Sheaf.Paper.IntegralUniformCoefficient
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.Paper.PbcActualStrictPullback
public import Sheaf.Paper.PbcQbarCompletedPullback
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.Paper.OrdinaryCompletedIntegralPullback
public import Sheaf.Paper.IntegralStratifiedPerfectCharacterization
import Sheaf.Paper.ProperIntegralStrictModelComparison
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Sheaf.Paper.PbcUniformCompleteTriangulated
import Sheaf.Paper.PbcUniformLocalModelCohomology
import Sheaf.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.FieldBaseChangeDimension
import Sheaf.Paper.PreservationConstructible

/-! # Ordinary integral inputs for a proper Cartesian square

Source: Bhatt--Scholze, Proposition 6.6.11, Lemma 6.5.9, Remark 6.8.15
(blueprint: lem-weil-pbc-proper-integral-ordinary-inputs).

The auxiliary predicates package clauses of this node. Coefficients, operations,
completeness, and constructibility are the published constructions. The pullback
identification is normalized by tensor-unit sections and the universal derived counits.
The completion identification is pinned by the strict tower and its Roos coordinates.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme

namespace WeilConjectures

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] integralOperationsSiteSmall integralOperationsCommHasDerivedCategory
  integralReductionSiteEssentiallySmall
  integralCompletedRingHasDerivedCategory integralReductionTargetHasDerivedCategory
  integralReductionSourceHasDerivedCategory
attribute [local instance 3000] integralTowerHasDerivedCategory
attribute [local irreducible] completedAdicChangeData HasDerivedCategory.standard

local instance inputSiteSmall (T : Scheme.{u}) : EssentiallySmall.{u + 1} T.ProEt :=
  essentiallySmallSelf.{0} _

local instance inputAbSheafify (T : Scheme.{u}) :
    HasSheafify (ProEt.topology T) AddCommGrpCat.{u + 1} :=
  integralCoefficientAbSheafify.{u, 0} T

local instance inputAbLocal (T : Scheme.{u}) :
    (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  integralCoefficientAbLocallyBijective.{u, 0} T

private def inputRestrictionRoundTrip (T : Scheme.{u})
    {R S : Sheaf (ProEt.topology T) RingCat.{u + 1}} (c : R ≅ S) :
    SheafOfModules.restrictScalars.{u + 1} c.hom ⋙
      SheafOfModules.restrictScalars c.inv ≅ 𝟭 (SheafOfModules.{u + 1} S) :=
  NatIso.ofComponents (fun M ↦ (SheafOfModules.fullyFaithfulForget S).preimageIso
    (PresheafOfModules.isoMk (fun U ↦
      (ModuleCat.restrictScalarsComp'App (c.inv.hom.app U).hom
        (c.hom.hom.app U).hom (RingHom.id _) (by
          have h := congr_app (congrArg (fun f : S ⟶ S ↦ f.hom) c.inv_hom_id) U
          exact (congrArg RingCat.Hom.hom h).symm) (M.val.obj U)).symm ≪≫
        ModuleCat.restrictScalarsId'App (RingHom.id _) rfl (M.val.obj U))
      (by intro U V f; ext x; rfl)))
    (by intro M N f; ext U x; rfl)

private def inputRestrictionEquivalence (T : Scheme.{u})
    {R S : Sheaf (ProEt.topology T) RingCat.{u + 1}} (c : R ≅ S) :
    SheafOfModules.{u + 1} S ≌ SheafOfModules.{u + 1} R where
  functor := SheafOfModules.restrictScalars c.hom
  inverse := SheafOfModules.restrictScalars c.inv
  unitIso := (inputRestrictionRoundTrip T c).symm
  counitIso := inputRestrictionRoundTrip T c.symm
  functor_unitIso_comp M := by ext U x; rfl

private theorem inputCoefficientMap {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) {U T : Scheme.{u}} (h : U ⟶ T) :
    completedCoefficientMap h d = (d.integralRingIso h).hom := by
  apply limit.hom_ext
  intro n
  change completedCoefficientMap h d ≫ d.projection U n.unop =
    (d.integralRingIso h).hom ≫ d.projection U n.unop
  calc
    _ = completedCoefficientComponent h d n.unop := limit.lift_π _ n
    _ = _ := by rw [d.projection_comm]; rfl

private theorem inputScalarAdjunction (T : Scheme.{u})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (φ : R ⟶ S) :
    ∃ a : reductionChange T φ ⊣ pbcRestrict.{u} φ,
      ∀ (M : pbcModules T R) (N : pbcModules T S)
        (f : (reductionChange T φ).obj M ⟶ N) (V : T.ProEtᵒᵖ) (x : M.val.obj V),
        (a.homEquiv M N f).val.app V x =
          f.val.app V (reductionTensorSection T φ M V 1 x) := by
  let h := (completedAdicChangeData T φ).choose_spec.choose
  obtain ⟨_, _, ha⟩ := SheafOfModules.sheafRingCoefficientOrdinaryAdjunction φ
  obtain ⟨a, hnorm⟩ := ha (reductionChange T φ) h
    (fun f ↦ (completedAdicChangeData T φ).choose_spec.choose_spec.choose f)
  refine ⟨a, ?_⟩
  intro M N f V x
  have he := hnorm M N (eqToHom (h M).symm ≫ f) V x
  have hh : eqToHom (h M) ≫ (eqToHom (h M).symm ≫ f) = f := by simp
  rw [hh] at he
  exact he

private theorem inputEdge {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) {U T : Scheme.{u}} (h : U ⟶ T) :
    PbcProperIntegralEdgeInputs d h := by
  have hIso : IsIso (completedCoefficientMap h d) := by
    rw [inputCoefficientMap]
    infer_instance
  have hExact : completedModulePullback h d =
      proEtaleRingModulePullback h (d.completedRing T) (d.completedRing U)
        (d.integralRingIso h) := by
    unfold completedModulePullback
    rw [inputCoefficientMap]
    refine CategoryTheory.Functor.ext (fun M ↦
      (completedAdicChangeData U (d.integralRingIso h).hom).choose_spec.choose
        ((proEtaleModuleInverseImage h (d.completedRing T)).obj M)) ?_
    intro M N f
    exact (completedAdicChangeData U (d.integralRingIso h).hom).choose_spec.choose_spec.choose
      ((proEtaleModuleInverseImage h (d.completedRing T)).map f)
  have hLim : PreservesFiniteLimits (completedModulePullback h d) := by
    rw [hExact]
    infer_instance
  have hColim : PreservesFiniteColimits (completedModulePullback h d) := by
    rw [hExact]
    infer_instance
  refine ⟨hIso, ?_, ?_, hLim, hColim, ⟨pbcActualModuleAdjunction h d⟩, ?_⟩
  · intro n
    exact limit.lift_π _ (op n)
  · intro a b v
    let t : adicLisseRingSystem T d.ideal ⋙
        proEtaleSheafInverseImage h CommRingCat.{u + 1} ⟶
          adicLisseRingSystem U d.ideal :=
      NatTrans.ofOpSequence (fun k ↦ (proEtaleConstantComparison h).app
        (CommRingCat.of (A ⧸ d.ideal ^ (k + 1)))) (by
          intro k
          simpa only [Functor.comp_map, adicLisseRingSystem,
            Functor.ofOpSequence_map_homOfLE_succ] using
            (proEtaleConstantComparison h).naturality
              (CommRingCat.ofHom (Ideal.Quotient.factorPowSucc d.ideal (k + 1))))
    let c := Functor.whiskerRight (pbcConstantSystemComparison T d).inv
      (proEtaleSheafInverseImage h CommRingCat.{u + 1}) ≫ t ≫
        (pbcConstantSystemComparison U d).hom
    exact (c.naturality v).symm
  · let φ := completedCoefficientMap h d
    have : (pbcRestrict.{u} φ).IsEquivalence :=
      (inputRestrictionEquivalence U ((adicLisseForget U).mapIso (asIso φ))).isEquivalence_functor
    obtain ⟨adj, hadj⟩ := inputScalarAdjunction U φ
    let F := proEtaleModuleInverseImage h (pbcAdicCompletion T d)
    let e : F ≅ completedModulePullback h d ⋙ pbcRestrict.{u} φ :=
      NatIso.ofComponents (fun M ↦ asIso (adj.unit.app (F.obj M))) (by
        intro M N f
        exact adj.unit.naturality (F.map f))
    have he (M : pbcModules T (pbcAdicCompletion T d)) (V : U.ProEtᵒᵖ)
        (x : (F.obj M).val.obj V) :
        (e.hom.app M).val.app V x = reductionTensorSection U φ (F.obj M) V 1 x := by
      change (adj.unit.app (F.obj M)).val.app V x = _
      have hh := hadj (F.obj M) _ (𝟙 _) V x
      rw [Adjunction.homEquiv_id] at hh
      change (adj.unit.app (F.obj M)).val.app V x =
        reductionTensorSection U φ (F.obj M) V 1 x at hh
      convert hh using 1
    clear_value e
    refine ⟨e, he, ?_⟩
    intro e' he'
    apply Iso.ext
    apply NatTrans.ext
    funext M
    ext V x
    exact (he' M V x).trans (he M V x).symm

private theorem inputGlobalUnit (T : Scheme.{u}) (l : ℕ)
    (h : ∀ x : T, IsUnit (l : T.presheaf.stalk x)) : IsUnit (l : Γ(T, ⊤)) := by
  apply T.toRingedSpace.isUnit_of_isUnit_germ
  intro x hx
  simpa only [map_natCast] using h x

private theorem inputMembership (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (T : Scheme.{u}) [IsNoetherian T]
    (hdim : ∃ n : ℕ, topologicalKrullDim T ≤ (n : WithBot ℕ∞))
    (hinv : ∀ x : T, IsUnit (l : T.presheaf.stalk x))
    (K : PbcCompletedDerived T (pbcIntegralDatum l E)) :
    PbcProperIntegralMembershipAgreement l E T K := by
  have hunit := inputGlobalUnit T l hinv
  have hLim := (integralDetailedCoefficientRestriction_exact T l E).1
  have hColim := (integralDetailedCoefficientRestriction_exact T l E).2
  have : (SheafOfModules.restrictScalars.{u + 1}
      (integralDetailedCoefficientComparison T l E).hom).IsEquivalence :=
    (inputRestrictionEquivalence T (integralDetailedCoefficientComparison T l E)
      ).isEquivalence_functor
  have : (integralDetailedTransport T l E).IsEquivalence :=
    Functor.isEquivalence_mapDerivedCategory
      (SheafOfModules.restrictScalars.{u + 1}
        (integralDetailedCoefficientComparison T l E).hom)
  have hclosed := (pbcIntegralUniformComplete_isTriangulated l E T hdim hinv).1
  refine ⟨(integralStratifiedPerfectCharacterization T l E hdim hunit K).1,
    ⟨(integralDetailedTransport T l E).objPreimage K,
      ⟨(integralDetailedTransport T l E).objObjPreimageIso K⟩⟩, ?_⟩
  intro L e
  exact (ObjectProperty.prop_iff_of_iso _ e).symm.trans
    (integralStratifiedPerfectDetailed T l E hdim hunit L).symm

private theorem inputInterval (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (T : Scheme.{u}) [IsNoetherian T]
    (K : PbcCompletedDerived T (pbcIntegralDatum l E))
    (hK : PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E) K) :
    ∃ a b : ℤ, pbcReductionsCohomologyIn T (pbcIntegralDatum l E) a b K := by
  obtain ⟨a, b, hab⟩ := pbcUniformLocalModelCohomology l E T K hK.2
  refine ⟨a, b, fun n q hq ↦ ?_⟩
  let R := pbcRestrict.{u} (pbcLevelConstantComparison T (pbcIntegralDatum l E) n).hom
  let H := (DerivedCategory.homologyFunctor
    (pbcModules T ((pbcAdicRings T (pbcIntegralDatum l E)).obj (op n))) q).obj
    ((pbcCompletedReduction T (pbcIntegralDatum l E) n).obj K)
  have hz : IsZero ((DerivedCategory.homologyFunctor _ q).obj
      ((pbcConstantReduction T (pbcIntegralDatum l E) n).obj K)) := by
    rcases hq with hq | hq
    · exact (DerivedCategory.isGE_iff _ a).1 (hab n).1 q hq
    · exact (DerivedCategory.isLE_iff _ b).1 (hab n).2.1 q hq
  have hr : IsZero (R.obj H) := hz.of_iso
    ((R.mapDerivedCategoryHomologyFunctorIso q).app
      ((pbcCompletedReduction T (pbcIntegralDatum l E) n).obj K))
  have : R.ReflectsIsomorphisms :=
    (proEtaleRingRestrictScalars_properties
      (pbcLevelConstantComparison T (pbcIntegralDatum l E) n).hom).2.2
  have : IsIso (R.map (0 : H ⟶ H)) := hr.isIso hr _
  have : IsIso (0 : H ⟶ H) := isIso_of_reflects_iso _ R
  exact (Limits.isIsoZero_iff_source_target_isZero H H).1 inferInstance |>.1

private theorem inputOrdinaryMembership (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {U T : Scheme.{u}} (h : U ⟶ T) [IsNoetherian U] [IsNoetherian T]
    (hdU : ∃ d : ℕ, topologicalKrullDim U ≤ (d : WithBot ℕ∞))
    (hdT : ∃ d : ℕ, topologicalKrullDim T ≤ (d : WithBot ℕ∞))
    (hiU : ∀ x : U, IsUnit (l : U.presheaf.stalk x))
    (hiT : ∀ x : T, IsUnit (l : T.presheaf.stalk x))
    (a : PbcProperIntegralPullbackIdentification l E h)
    (K : PbcCompletedDerived T (pbcIntegralDatum l E))
    (hK : PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E) K) :
    PbcIsBoundedConstructibleComplete U (pbcIntegralDatum l E)
      ((completedOrdinaryPullback.{u} h (pbcIntegralDatum l E)).obj K) := by
  have hm := inputMembership l E T hdT hiT K
  obtain ⟨L, ⟨e⟩⟩ := hm.2.1
  have hL := (hm.2.2 L e).mp hK
  have hPull := (ordinaryCompletedIntegralPullback l E h hdU hdT
    (inputGlobalUnit U l hiU) (inputGlobalUnit T l hiT) L hL).1
  have hTransport := (integralStratifiedPerfectDetailed U l E hdU
    (inputGlobalUnit U l hiU) _).mp hPull
  have := (pbcIntegralUniformComplete_isTriangulated l E U hdU hiU).1
  exact ObjectProperty.prop_of_iso _
    (a.derivedIso.app L ≪≫
      (completedOrdinaryPullback.{u} h (pbcIntegralDatum l E)).mapIso e) hTransport

private theorem inputCompletionMatching (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {U T : Scheme.{u}} (h : U ⟶ T)
    (a : PbcProperIntegralPullbackIdentification l E h)
    (b : integralDerivedPullback l E h ⋙ integralDetailedTransport U l E ≅
      integralDetailedTransport T l E ⋙ completedReductionTower.{u} T (pbcIntegralDatum l E) ⋙
        completedTowerPullback.{u} h (pbcIntegralDatum l E) ⋙
          completedTowerRlim.{u} (pbcIntegralDatum l E) U)
    (hm : PbcProperIntegralModelMatching l E h a b)
    (hc : ∀ L : DerivedCategory (integralTowerModules l E T),
      (integralDetailedTransport U l E).map
          ((ordinaryIntegralCompletionComparison l E h).app L) ≫ b.hom.app L =
        a.derivedIso.hom.app L ≫ completedPullbackComparison.{u} h (pbcIntegralDatum l E)
          ((integralDetailedTransport T l E).obj L))
    (K : PbcCompletedDerived T (pbcIntegralDatum l E)) :
    PbcProperIntegralCompletionMatching l E h K := by
  refine ⟨a, b, hm, ?_⟩
  intro L e
  have hn := (pbcActualStrictCompletedPullUnit.{u} (pbcIntegralDatum l E) h).naturality e.hom
  have hu (A : PbcCompletedDerived T (pbcIntegralDatum l E)) :
      (pbcActualStrictCompletedPullUnit.{u} (pbcIntegralDatum l E) h).app A =
        completedPullbackComparison.{u} h (pbcIntegralDatum l E) A := by
    simp only [pbcActualStrictCompletedPullUnit, completedPullbackComparison,
      NatTrans.comp_app, Functor.rightUnitor_inv_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.associator_inv_app, Category.id_comp]
  rw [hu, hu] at hn
  change (completedOrdinaryPullback.{u} h (pbcIntegralDatum l E)).map e.hom ≫
      completedPullbackComparison.{u} h (pbcIntegralDatum l E) K =
    completedPullbackComparison.{u} h (pbcIntegralDatum l E)
        ((integralDetailedTransport T l E).obj L) ≫
      (completedTowerRlim.{u} (pbcIntegralDatum l E) U).map
        ((completedTowerPullback.{u} h (pbcIntegralDatum l E)).map
          ((completedReductionTower.{u} T (pbcIntegralDatum l E)).map e.hom)) at hn
  rw [← Category.assoc, hc, Category.assoc, ← hn, ← Category.assoc]

/-- Arithmetic, coefficient and ordinary integral inputs for a proper Cartesian square.
Source: Bhatt--Scholze, Proposition 6.6.11, Lemma 6.5.9 and Remark 6.8.15
(blueprint: lem-weil-pbc-proper-integral-ordinary-inputs).

Proof:
1. Positive quotient finiteness is the published coefficient-extension theorem and
transitions preserve one. The extended norm of l is its p-adic norm, less than one;
the DVR maximal ideal is generated by the chosen uniformizer. Hence l is zero in
the first quotient.
2. A geometric fibre has dimension at most dim X by the existing field-point
base-change bound, so the assumed finite bound on X works. Properness of f' is
stability under the chosen Cartesian base change.
3. Projection uniqueness identifies the coefficient map with integralRingIso.hom.
Naturality of constant comparisons gives transition compatibility. The scalar-extension
witness identifies module pullback with the exact ringed inverse image. Its published
adjunction and the scalar adjunction unit give the tensor-unit-normalized inverse-image
isomorphism; sectionwise extensionality proves uniqueness.
4. Uniform local models give a common cohomology interval after finite constant
restriction. Exact faithful restriction reflects zero homology, giving the actual
reduction interval. Apply proper constructible preservation with N=l, the residue
annihilation and the geometric bound to obtain the proper direct image membership.
5. Restriction along the detailed coefficient isomorphism is an equivalence, hence so
is its derived transport. Choose a preimage under this equivalence. The two published
stratified-perfect characterizations and isomorphism invariance give membership
agreement. Apply ordinary completed integral pullback to the preimage, then the
normalized derived pullback identification, to obtain ordinary pullback membership.
6. Apply the separate ambient strict-model comparison to g and g'. Its model data
are independent of the input object. Naturality of the actual strict completion unit
extends its equation at transport(L) along every presentation isomorphism e.
Reassociation gives the two CompletionMatching clauses and the asserted conjunction.
The ambient comparison is the remaining separate result; no exchange map is used. -/
theorem pbc_proper_integral_ordinary_inputs
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E]
    {X' X Y' Y : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (f : X ⟶ Y) (g : Y' ⟶ Y) (_square : ChosenCartesianSquare g' f' f g)
    [IsNoetherian X] [IsNoetherian Y] [IsNoetherian X'] [IsNoetherian Y']
    (_hDimX : ∃ d : ℕ, topologicalKrullDim X ≤ (d : WithBot ℕ∞))
    (_hDimY : ∃ d : ℕ, topologicalKrullDim Y ≤ (d : WithBot ℕ∞))
    (_hDimX' : ∃ d : ℕ, topologicalKrullDim X' ≤ (d : WithBot ℕ∞))
    (_hDimY' : ∃ d : ℕ, topologicalKrullDim Y' ≤ (d : WithBot ℕ∞))
    (_hInvX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (_hInvY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y))
    (_hInvX' : ∀ x : X', IsUnit (l : X'.presheaf.stalk x))
    (_hInvY' : ∀ y : Y', IsUnit (l : Y'.presheaf.stalk y))
    [IsProper f] (K : PbcCompletedDerived X (pbcIntegralDatum l E))
    (_hK : PbcIsBoundedConstructibleComplete X (pbcIntegralDatum l E) K) :
    (∀ n : ℕ, 1 ≤ n → Finite (Padic.coefficientExtensionRing l E n)) ∧
    (∀ n : ℕ, 1 ≤ n → Padic.coefficientExtensionTransition l E n 1 = 1) ∧
    (l : Padic.coefficientExtensionRing l E 1) = 0 ∧
    IsProper f' ∧
    (∃ d : ℕ, ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y),
      topologicalKrullDim (pullback f y : Scheme.{u}) ≤ (d : WithBot ℕ∞)) ∧
    PbcProperIntegralEdgeInputs (pbcIntegralDatum l E) f ∧
    PbcProperIntegralEdgeInputs (pbcIntegralDatum l E) f' ∧
    PbcProperIntegralEdgeInputs (pbcIntegralDatum l E) g ∧
    PbcProperIntegralEdgeInputs (pbcIntegralDatum l E) g' ∧
    PbcIsBoundedConstructibleComplete Y (pbcIntegralDatum l E)
      ((completedDerivedDirectImage f (pbcIntegralDatum l E)).obj K) ∧
    PbcIsBoundedConstructibleComplete Y' (pbcIntegralDatum l E)
      ((completedOrdinaryPullback g (pbcIntegralDatum l E)).obj
        ((completedDerivedDirectImage f (pbcIntegralDatum l E)).obj K)) ∧
    PbcIsBoundedConstructibleComplete X' (pbcIntegralDatum l E)
      ((completedOrdinaryPullback g' (pbcIntegralDatum l E)).obj K) ∧
    PbcProperIntegralMembershipAgreement l E X K ∧
    PbcProperIntegralMembershipAgreement l E Y
      ((completedDerivedDirectImage f (pbcIntegralDatum l E)).obj K) ∧
    PbcProperIntegralMembershipAgreement l E Y'
      ((completedOrdinaryPullback g (pbcIntegralDatum l E)).obj
        ((completedDerivedDirectImage f (pbcIntegralDatum l E)).obj K)) ∧
    PbcProperIntegralMembershipAgreement l E X'
      ((completedOrdinaryPullback g' (pbcIntegralDatum l E)).obj K) ∧
    PbcProperIntegralCompletionMatching l E g
      ((completedDerivedDirectImage f (pbcIntegralDatum l E)).obj K) ∧
    PbcProperIntegralCompletionMatching l E g' K := by
  have hAnn : (l : Padic.coefficientExtensionRing l E 1) = 0 := by
    have H := (Padic.extension_integers_dvr l E
      (Padic.coefficientExtensionAbsoluteValue l E)
      (spectralNorm_extends (K := ℚ_[l]) (L := E))).choose_spec.choose_spec
    have hgen := H.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
    change Ideal.Quotient.mk _ (l : Padic.coefficientExtensionIntegers l E) = 0
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    change (l : Padic.coefficientExtensionIntegers l E) ∈
      Ideal.span {Padic.coefficientExtensionUniformizer l E} ^ 1
    change Ideal.span {Padic.coefficientExtensionUniformizer l E} =
      Padic.coefficientExtensionMaximalIdeal l E at hgen
    rw [pow_one, hgen]
    apply (H.2.1 _).2
    have h := spectralNorm_extends (K := ℚ_[l]) (L := E) (l : ℚ_[l])
    rw [map_natCast] at h
    change spectralNorm ℚ_[l] E (l : E) < 1
    rw [h]
    exact Padic.norm_p_lt_one
  have hProper : IsProper f' := by
    rw [← _square.hom_snd]
    infer_instance
  obtain ⟨d, hd⟩ := _hDimX
  have hFib (Ω : Type u) [Field Ω] (y : Spec (.of Ω) ⟶ Y) :
      topologicalKrullDim (pullback f y : Scheme.{u}) ≤ (d : WithBot ℕ∞) :=
    (topologicalKrullDim_pullback_le f y).trans hd
  have : IsProper f' := hProper
  obtain ⟨a, b, hInterval⟩ := inputInterval l E X K _hK
  have hC := (pbc_preservation_constructible l E g' f' f g _square
    ⟨d, hd⟩ _hDimY _hDimX' _hDimY' l (Fact.out : l.Prime).pos hAnn
    (inputGlobalUnit X l _hInvX) (inputGlobalUnit Y l _hInvY)
    (inputGlobalUnit X' l _hInvX') (inputGlobalUnit Y' l _hInvY') d
    (fun y ↦ hFib _ _) a b K _hK hInterval).1
  obtain ⟨ag, bg, hmg, hcg⟩ := pbc_proper_integral_strict_model_comparison l E g
  obtain ⟨ag', bg', hmg', hcg'⟩ := pbc_proper_integral_strict_model_comparison l E g'
  have hM := inputOrdinaryMembership l E g _hDimY' _hDimY _hInvY' _hInvY ag _ hC
  have hE := inputOrdinaryMembership l E g' _hDimX' ⟨d, hd⟩ _hInvX' _hInvX ag' K _hK
  exact ⟨fun n hn ↦ Padic.finite_coefficientExtensionRing l E n hn,
    fun n _ ↦ map_one _, hAnn, hProper, ⟨d, fun Ω _ _ y ↦ hFib Ω y⟩,
    inputEdge _ f, inputEdge _ f', inputEdge _ g, inputEdge _ g', hC, hM, hE,
    inputMembership l E X ⟨d, hd⟩ _hInvX K,
    inputMembership l E Y _hDimY _hInvY _,
    inputMembership l E Y' _hDimY' _hInvY' _,
    inputMembership l E X' _hDimX' _hInvX' _,
    inputCompletionMatching l E g ag bg hmg hcg _,
    inputCompletionMatching l E g' ag' bg' hmg' hcg' K⟩

end WeilConjectures
