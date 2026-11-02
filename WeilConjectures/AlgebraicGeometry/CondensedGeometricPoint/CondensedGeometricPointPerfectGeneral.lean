/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedGeometricPoint.CondensedGeometricPointPerfect
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SmoothPurity.AdmissibleCondensedCoefficients
import all WeilConjectures.AlgebraicGeometry.CondensedGeometricPoint.CondensedCoefficientPoint
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Native.NativeModulePullbackBraiding
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Evaluation.ContractibleRealizationUnderivedModel
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalStructure
import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitudeMapDerivedCategory
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ZetaWeil.ContractibleLisseEvaluation
import WeilConjectures.CategoryTheory.DerivedCategory.Perfect.PerfectRingClassicalGenerator
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Subcategory
import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude

/-! # General perfect realization at a condensed geometric point

Source: literature/blueprint/latest/blueprint/sec-six-functors/sk-lem-finite/
sk-lem-finite.proof.md,
first proof paragraph (blueprint: lem-sf-condensed-geometric-point-perfect-general).

The existing `Statement` records the exact symmetric monoidal point realization, its
closed internal-Hom comparison, evaluation compatibility, unit comparison, and signed
biduality formula. This theorem states that package for every admissible coefficient ring,
with no restriction to one finite quotient or one finite subextension.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj
open AlgebraicGeometry
open AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale.CondensedGeometricPoint

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] (k : Type u) [Field k] [IsAlgClosed k]

private theorem scalar_properties_of_iso
    {Ω : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Ω] [IsCommMonObj Ω] (e : Mon.mk Λ ≅ Mon.mk Ω)
    (h : scalar_properties Ω) : scalar_properties Λ := by
  let T := coherentTopology Profinite.{u}
  let ec : CommMon.mk Λ ≅ CommMon.mk Ω :=
    (CommMon.fullyFaithfulForget₂Mon _).preimageIso e
  let er : InternalAbelianSheafModule.sectionRings T Λ ≅
      InternalAbelianSheafModule.sectionRings T Ω :=
    Functor.isoWhiskerRight (((sheafToPresheaf T Ab.{u + 1}).mapCommMon ⋙
      (Monoidal.commMonFunctorCategoryEquivalence Profinite.{u}ᵒᵖ Ab.{u + 1}).functor
        ).mapIso ec) InternalAbelianSheafModule.commMonToRing
  let e₀ : condensedScalarRing Λ ≃+* condensedScalarRing Ω :=
    RingEquiv.ofBijective (er.hom.app (op (⊤_ Profinite.{u}))).hom
      (ConcreteCategory.bijective_of_isIso _)
  let := h.1
  refine ⟨isNoetherianRing_of_ringEquiv _ e₀.symm, ?_⟩
  intro S hS
  apply (RingHom.Flat.comp_iff_of_bijective_left
    (f := CondensedRing.scalarSectionMap (Mon.mk Λ) S)
    (g := (er.hom.app (op S)).hom)
    (ConcreteCategory.bijective_of_isIso (er.hom.app (op S)))).mp
  have hn : (er.hom.app (op S)).hom.comp
      (CondensedRing.scalarSectionMap (Mon.mk Λ) S) =
      (CondensedRing.scalarSectionMap (Mon.mk Ω) S).comp e₀.toRingHom :=
    congrArg (fun f ↦ f.hom) (er.hom.naturality (terminal.from S).op)
  rw [hn]
  exact (RingHom.Flat.of_bijective e₀.bijective).comp (h.2 S hS)

private theorem admissible_scalar_properties
    (hΛ : CondensedRing.IsAdmissibleCoefficient Λ) : scalar_properties Λ := by
  obtain ⟨ℓ, hℓ, h⟩ := hΛ
  let := hℓ
  rcases h with h | h | h | h | h | h
  · obtain ⟨A, hA, hfin, htop, hd, hr, _, ⟨e⟩⟩ := h
    let := hA
    let := hfin
    let := htop
    let := hd
    let := hr
    let := isNoetherian_of_finite A A
    apply scalar_properties_of_iso Λ e
    apply continuous_scalar_properties A
    intro S
    rw [show ContinuousMap.C (α := S) (R := A) (A := A) = algebraMap A C(S, A)
      from rfl, RingHom.flat_algebraMap_iff]
    apply Module.Flat.of_linearEquiv
      (LinearEquiv.ofBijective (LocallyConstant.toContinuousMapLinearMap A) ?_).symm
    exact ⟨LocallyConstant.toContinuousMap_injective,
      fun f ↦ ⟨⟨f, (IsLocallyConstant.iff_continuous _).2 f.continuous⟩, rfl⟩⟩
  · obtain ⟨e⟩ := h
    apply scalar_properties_of_iso Λ e
    apply continuous_scalar_properties ℤ_[ℓ]
    intro S
    rw [show ContinuousMap.C (α := S) (R := ℤ_[ℓ]) (A := ℤ_[ℓ]) =
      algebraMap _ C(S, ℤ_[ℓ]) from rfl, RingHom.flat_algebraMap_iff]
    let : Module.IsTorsionFree ℤ_[ℓ] C(S, ℤ_[ℓ]) := by
      constructor
      intro a ha f g hfg
      apply ContinuousMap.ext
      intro x
      exact ha.left (ContinuousMap.congr_fun hfg x)
    infer_instance
  · obtain ⟨e⟩ := h
    exact scalar_properties_of_iso Λ e (field_scalar_properties ℚ_[ℓ])
  · obtain ⟨E, ⟨e⟩⟩ := h
    exact scalar_properties_of_iso Λ e (integers_scalar_properties ℓ E)
  · obtain ⟨E, ⟨e⟩⟩ := h
    exact scalar_properties_of_iso Λ e (field_scalar_properties E)
  · obtain ⟨e⟩ := h
    exact scalar_properties_of_iso Λ e (algClosure_scalar_properties ℓ)

private theorem admissible_direct_point
    (hΛ : CondensedRing.IsAdmissibleCoefficient Λ) : DirectPointStatement Λ k :=
  direct_of_scalar_properties Λ k (admissible_scalar_properties Λ hΛ)

private noncomputable instance point_inverse_braided (X : Scheme.{u}) :
    (upperStarFromPoint X).Braided where
  toMonoidal := inferInstance
  braided := Functor.LaxBraided.braided

@[instance_reducible]
private noncomputable def module_pullback_braided
    {C : Type*} [Category* C] [MonoidalCategory C] [SymmetricCategory C]
    [HasCoequalizers C]
    [∀ A : C, PreservesColimitsOfSize.{0, 0} (tensorLeft A)]
    [∀ A : C, PreservesColimitsOfSize.{0, 0} (tensorRight A)]
    {D : Type*} [Category* D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ A : D, PreservesColimitsOfSize.{0, 0} (tensorLeft A)]
    [∀ A : D, PreservesColimitsOfSize.{0, 0} (tensorRight A)]
    (F : C ⥤ D) [F.Braided] [PreservesColimitsOfShape WalkingParallelPair F]
    (R : C) [MonObj R] [IsCommMonObj R] : (F.mapMod R).Braided where
  braided M N := mapMod_braided F M N

set_option maxHeartbeats 3000000 in
-- Transport through the concrete sheaf module equivalences is expensive to elaborate.
private theorem ordinary_monoidal_data :
    ∃ m : (CondensedRing.ordinaryScalarRealization (Mon.mk Λ) (Spec (.of k))).Braided,
      letI := m.toMonoidal
      (CondensedRing.ordinaryScalarRealization (Mon.mk Λ) (Spec (.of k))).PreservesFlat := by
  let T := coherentTopology Profinite.{u}
  let c := commutativeSiteConstantModuleFunctor T (condensedScalarRing Λ)
  let d := condensedScalarExtensionModel Λ
  let e := InternalAbelianSheafModule.sectionModuleEquivalence T Λ
  let E := SheafOfModules.flatScalarExtension T (condensedScalarMap Λ)
  let t : d.E ≅ E := NatIso.ofComponents (fun M ↦ eqToIso (d.obj_eq M)) (by
    intro M N f
    dsimp [E]
    rw [d.map_eq]
    simp
    rfl)
  let L := CondensedRing.Evaluation.terminalScalarRealization T Λ
    (⊤_ Profinite.{u}) terminalIsTerminal
  let G := upperStarFromPoint (Spec (.of k))
  let q := G.mapMod Λ
  let r : CondensedRing.ordinaryScalarRealization (Mon.mk Λ) (Spec (.of k)) ≅ L ⋙ q :=
    Functor.isoWhiskerLeft c (Functor.isoWhiskerRight t (e.inverse ⋙ q)) ≪≫
      (Functor.associator c E (e.inverse ⋙ q)).symm ≪≫
      (Functor.associator (c ⋙ E) e.inverse q).symm
  obtain ⟨L', ha, hf, hp, hb, ⟨adj⟩, _⟩ :=
    CondensedRing.Evaluation.realization_underived_model T Λ
      (⊤_ Profinite.{u}) terminalIsTerminal
  let b := CondensedRing.Evaluation.contractible_realization_underived_data T Λ
    (⊤_ Profinite.{u}) terminalIsTerminal
  let : L.Braided := b.choose_spec.choose
  have : L.PreservesFlat := by
    let i : L ≅ L' :=
      b.choose_spec.choose_spec.some.leftAdjointUniq adj
    let := hp
    constructor
    intro M hM
    exact (ObjectProperty.flat).prop_of_iso (i.app M).symm
      (Functor.PreservesFlat.flat_obj (F := L') hM)
  let : q.Braided := module_pullback_braided G Λ
  let : q.PreservesFlat := q.preservesFlat_of_isEquivalence
  let : (L ⋙ q).PreservesFlat := ⟨fun h ↦
    Functor.PreservesFlat.flat_obj (F := q)
      (Functor.PreservesFlat.flat_obj (F := L) h)⟩
  let := Functor.Monoidal.transport r.symm
  let : NatTrans.IsMonoidal r.symm.hom := Functor.Monoidal.natTransIsMonoidal_of_transport r.symm
  refine ⟨{ braided := (Functor.LaxBraided.ofNatIso r.symm).braided }, ?_⟩
  constructor
  intro M hM
  exact (ObjectProperty.flat).prop_of_iso (r.app M).symm
    (Functor.PreservesFlat.flat_obj (F := L ⋙ q) hM)

private noncomputable instance point_braided : BraidedCategory (Complexes Λ k) :=
  DerivedCategory.braidedCategory' _

private noncomputable instance scalar_braided :
    BraidedCategory (DerivedCategory (ModuleCat.{u + 1} (condensedScalarRing Λ))) :=
  DerivedCategory.braidedCategory' _

private theorem comparison_of_equivalence
    [ObjectProperty.IsMonoidal (ctf Λ k)] [ObjectProperty.IsMonoidal (perfect Λ)]
    [ObjectProperty.IsMonoidalClosed (ctf Λ k)]
    [ObjectProperty.IsMonoidalClosed (perfect Λ)]
    [(ctf Λ k).IsTriangulated] [(perfect Λ).IsTriangulated]
    (h : ∀ K : (ctf Λ k).FullSubcategory, perfect Λ ((fiber Λ k).obj K.obj))
    (m : (restricted Λ k h).Braided)
    (he : (restricted Λ k h).IsEquivalence)
    (ht : ∃ s : (restricted Λ k h).CommShift ℤ,
      letI := s
      (restricted Λ k h).IsTriangulated) : RestrictedComparison Λ k h := by
  let := m.toMonoidal
  let := he
  refine ⟨m, he, ht, fun C D ↦ inferInstance, ?_, ?_⟩
  · intro C D
    exact Functor.LaxMonoidal.ihomComparison_ev (restricted Λ k h) C D
  · intro C
    exact ⟨Functor.Monoidal.ihomObjIso (restricted Λ k h) C (𝟙_ _) ≪≫
      (ihom ((restricted Λ k h).obj C)).mapIso
        (Functor.Monoidal.εIso (restricted Λ k h)).symm⟩

private theorem scalar_perfect_iff
    [IsNoetherianRing (condensedScalarRing Λ)]
    (P : DerivedCategory (ModuleCat.{u + 1} (condensedScalarRing Λ))) :
    perfect Λ P ↔ scalarFiniteCohomology Λ P ∧
      DerivedCategory.finiteTorAmplitude _ P := by
  constructor
  · intro h
    change DerivedCategory.IsPerfect P at h
    refine ⟨⟨(finite_support_iff_bounded P).mpr h.bounded, h.finite_homology⟩, ?_⟩
    obtain ⟨C, a, b, ha, hb, hC, ⟨e⟩⟩ := h
    let := ha
    let := hb
    refine ⟨a, b, (DerivedCategory.torAmplitudeIn _ a b).prop_of_iso e.symm ?_⟩
    apply DerivedCategory.torAmplitudeIn_Q_obj_of_flat C a b
    intro i
    let := (hC i).1
    exact (ModuleCat.flat_iff_flat _).mpr inferInstance
  · rintro ⟨h, ht⟩
    exact DerivedCategory.isPerfect_of_finiteTorAmplitude
      ((finite_support_iff_bounded P).mp h.1) h.2 ht

private theorem dualizable_ihom
    {D : Type*} [Category* D] [MonoidalCategory D] [BraidedCategory D]
    [MonoidalClosed D] (X Y : D) (hX : IsDualizable X) (hY : IsDualizable Y) :
    IsDualizable ((ihom X).obj Y) := by
  obtain ⟨hX⟩ := hX
  let := hX
  let := BraidedCategory.exactPairing_swap X Xᘁ
  exact IsDualizable.of_iso (MonoidalClosed.ihomObjIsoTensor Xᘁ X Y).symm
    ((IsDualizable.ihom_unit (show IsDualizable X from ⟨hX⟩)).tensorObj hY |>.of_iso
      (whiskerRightIso (MonoidalCategory.ihomUnitIsoRightDual X) Y))

private theorem scalar_perfect_closed :
    (perfect Λ).IsMonoidal ∧ (perfect Λ).IsMonoidalClosed := by
  have hd := CondensedRing.perfect_iff_dualizable (R := condensedScalarRing Λ)
  refine ⟨{ prop_unit := (hd _).mpr isDualizable_unit
            prop_tensor := fun X Y hX hY ↦
              (hd _).mpr (((hd X).mp hX).tensorObj ((hd Y).mp hY)) }, ?_⟩
  exact ⟨fun X Y hX hY ↦ (hd _).mpr
    (dualizable_ihom X Y ((hd X).mp hX) ((hd Y).mp hY))⟩

omit [IsAlgClosed k] in
private theorem perfect_image_closed
    (F : DerivedCategory (ModuleCat.{u + 1} (condensedScalarRing Λ)) ⥤ Complexes Λ k)
    [F.Monoidal] :
    ((perfect Λ).ι ⋙ F).essImage.IsMonoidal ∧
      ((perfect Λ).ι ⋙ F).essImage.IsMonoidalClosed := by
  let := (scalar_perfect_closed Λ).1
  let := (scalar_perfect_closed Λ).2
  let Q := ((perfect Λ).ι ⋙ F).essImage
  have hm : Q.IsMonoidal := {
    prop_unit := ⟨𝟙_ (perfect Λ).FullSubcategory, ⟨(Functor.Monoidal.εIso F).symm⟩⟩
    prop_tensor := by
      rintro X Y ⟨P, ⟨eP⟩⟩ ⟨Q, ⟨eQ⟩⟩
      exact ⟨P ⊗ Q, ⟨(Functor.Monoidal.μIso F P.obj Q.obj).symm ≪≫ (eP ⊗ᵢ eQ)⟩⟩ }
  refine ⟨hm, ⟨?_⟩⟩
  rintro X Y ⟨P, ⟨eP⟩⟩ ⟨Q, ⟨eQ⟩⟩
  obtain ⟨hP⟩ := (CondensedRing.perfect_iff_dualizable P.obj).mp P.property
  let := hP
  let := BraidedCategory.exactPairing_swap P.obj P.objᘁ
  let := ExactPairing.map F P.objᘁ P.obj
  let e : F.obj ((ihom P.obj).obj Q.obj) ≅
      (ihom (F.obj P.obj)).obj (F.obj Q.obj) :=
    F.mapIso (MonoidalClosed.ihomObjIsoTensor P.objᘁ P.obj Q.obj) ≪≫
      (Functor.Monoidal.μIso F P.objᘁ Q.obj).symm ≪≫
      (MonoidalClosed.ihomObjIsoTensor (F.obj P.objᘁ) (F.obj P.obj) (F.obj Q.obj)).symm
  refine ⟨⟨(ihom P.obj).obj Q.obj,
    ObjectProperty.prop_ihom (perfect Λ) P.property Q.property⟩, ⟨?_⟩⟩
  exact e ≪≫ (asIso (MonoidalClosed.pre eP.inv)).app (F.obj Q.obj) ≪≫
    (ihom X).mapIso eQ

set_option maxHeartbeats 2000000 in
-- The restricted monoidal equivalence contains the concrete derived functor comparisons.
set_option linter.unusedVariables false in
/-- Evaluation at an algebraically closed point realizes bounded constructible finite-Tor
condensed complexes as perfect complexes over the condensed scalar ring for every admissible
coefficient family. The conclusion includes the exact symmetric monoidal equivalence, the
canonical unit comparison, internal derived Hom and evaluation compatibility, and the
Koszul-signed biduality comparison.

Source: sk-lem-finite.proof.md (path in the module docstring), first proof paragraph.

Proof. Write R = Λ(*) and let J be ordinary scalar realization on the point.
1. Check Noetherian scalars and flat section rings for all six admissible families.
   The exact scalar/section adjunction and finite constant local models give the bounded
   constructible/finite-cohomology equivalence, using the generic point lemmas from
   `CondensedCoefficientPoint`; no finite-field datum is needed.
2. Give J its braided flat-preserving structure by composing terminal scalar realization
   with the point-topos equivalence. Derive this structure and transport it to D(J).
3. The exact faithful strong monoidal flat-preserving J preserves and reflects Tor
   intervals (`DerivedCategory.torAmplitudeIn_mapDerivedCategory_obj_iff`). The bounded
   constructible counit therefore transfers the finite Tor bound to scalar evaluation.
   `DerivedCategory.isPerfect_of_finiteTorAmplitude` is the blueprint's finite-free
   resolution and truncation argument. Conversely a bounded finite-projective model
   has bounded finite cohomology and finite Tor amplitude, both preserved by J.
4. Restrict the exact adjunction to perfect and constructible finite-Tor complexes.
   Its unit is invertible and its counit is invertible on this essential image.
5. Perfect scalar objects are dualizable. Tensor products and internal Homs of such
   objects remain dualizable, so their image is closed under the ambient tensor and Hom.
   The classical-generator description of perfect objects gives triangulated closure;
   the exact fully faithful realization transfers this closure to its essential image.
6. Restrict the derived braided structure and give the inverse its adjoint monoidal
   structure. The canonical internal-Hom comparison of a monoidal equivalence is invertible
   and satisfies its evaluation equation. At the unit it gives the asserted dual formula.
(blueprint: lem-sf-condensed-geometric-point-perfect-general) -/
theorem condensed_geometric_point_perfect_general
    (ell p : ℕ) [Fact ell.Prime] [CharP k p] (hpell : p ≠ ell)
    (hΛ : CondensedRing.IsAdmissibleCoefficient Λ) :
    Statement Λ k := by
  let hs := admissible_scalar_properties Λ hΛ
  let := hs.1
  let J := CondensedRing.ordinaryScalarRealization (Mon.mk Λ) (Spec (.of k))
  obtain ⟨ha, hl, hc, ⟨eJ⟩⟩ :=
    CondensedRing.flat_ordinaryScalarRealization (Mon.mk Λ) hs.2 (Spec (.of k))
  let := ha
  let := hl
  let := hc
  let adjJ : J ⊣ heartFiber Λ k := ordinary_adjunction Λ k
  let : J.IsLeftAdjoint := adjJ.isLeftAdjoint
  let := heart_adjunction_unit Λ k J adjJ
  let := adjJ.fullyFaithfulLOfIsIsoUnit.full
  let := adjJ.fullyFaithfulLOfIsIsoUnit.faithful
  obtain ⟨mJ, hflat⟩ := ordinary_monoidal_data Λ k
  let := mJ
  let := hflat
  let F := J.mapDerivedCategory
  let eD := J.leftDerivedFunctorIsoMapDerivedCategory
  let bD := J.leftDerivedFunctorBraided (fun X Y ↦ by
    simp only [Functor.map_braiding, Category.assoc, Functor.Monoidal.μ_δ,
      Category.comp_id])
  let := bD
  let := Functor.Monoidal.transport eD
  let : NatTrans.IsMonoidal eD.hom := Functor.Monoidal.natTransIsMonoidal_of_transport eD
  let : F.Braided := { braided := (Functor.LaxBraided.ofNatIso eD).braided }
  let eH := heartFiberDerivedIso Λ k
  let : (fiber Λ k).CommShift ℤ := Functor.CommShift.ofIso eH ℤ
  let : NatTrans.CommShift eH.hom ℤ := Functor.CommShift.ofIso_compatibility eH ℤ
  let : (fiber Λ k).IsTriangulated := Functor.isTriangulated_of_iso eH
  obtain ⟨_, _, _, _, _, _, _, _, hG₀, hC₀, a₀, hu₀, hc₀⟩ :=
    admissible_direct_point Λ k hΛ
  let := hu₀
  let := hc₀
  let BC := constantModelBoundedConstructible Λ (Spec (.of k))
  let : BC.IsClosedUnderIsomorphisms :=
    (constantModelConstructibleFiniteTor_wellDefined Λ (Spec (.of k))).2.1
  have counit (K : Complexes Λ k) (hK : BC K) : F.obj ((fiber Λ k).obj K) ≅ K :=
    eJ.app _ ≪≫ BC.ι.mapIso (asIso (a₀.counit.app ⟨K, hK⟩))
  have hG (K : (ctf Λ k).FullSubcategory) : perfect Λ ((fiber Λ k).obj K.obj) := by
    have hf := hG₀ ⟨K.obj, K.property.1⟩
    apply (scalar_perfect_iff Λ _).mpr
    refine ⟨hf, ?_⟩
    obtain ⟨a, b, ht⟩ := K.property.2
    refine ⟨a, b, (DerivedCategory.torAmplitudeIn_mapDerivedCategory_obj_iff J a b _).mp ?_⟩
    exact (DerivedCategory.torAmplitudeIn _ a b).prop_of_iso
      (counit K.obj K.property.1).symm ht
  have hF (P : (perfect Λ).FullSubcategory) : ctf Λ k (F.obj P.obj) := by
    obtain ⟨hP, a, b, hT⟩ := (scalar_perfect_iff Λ P.obj).mp P.property
    exact ⟨BC.prop_of_iso (eJ.app P.obj).symm (hC₀ ⟨P.obj, hP⟩),
      a, b, DerivedCategory.torAmplitudeIn_mapDerivedCategory_obj J hT⟩
  let d₀ := adjJ.mapDerivedCategoryAdjunction
  let ff := d₀.fullyFaithfulLOfIsIsoUnit
  let := ff.full
  let := ff.faithful
  let d := d₀.ofNatIsoRight eH
  let : IsIso d.unit := by infer_instance
  have hEss (K : (ctf Λ k).FullSubcategory) : F.essImage K.obj :=
    ⟨(fiber Λ k).obj K.obj, ⟨counit K.obj K.property.1⟩⟩
  obtain ⟨a, hu, hc⟩ := restrict_adjunction d (perfect Λ) (ctf Λ k) hF hG hEss
  let := hu
  let := hc
  let L := (ctf Λ k).lift ((perfect Λ).ι ⋙ F) hF
  let R := restricted Λ k hG
  let : R.IsEquivalence := inferInstanceAs a.toEquivalence.inverse.IsEquivalence
  let : (perfect Λ).IsMonoidal := (scalar_perfect_closed Λ).1
  let : (perfect Λ).IsMonoidalClosed := (scalar_perfect_closed Λ).2
  let : (perfect Λ).IsTriangulated := by
    dsimp only [perfect]
    rw [DerivedCategory.isPerfectRingComplex_eq_triangEnvelope_singleton]
    infer_instance
  have hctf : ctf Λ k = ((perfect Λ).ι ⋙ F).essImage := by
    funext K
    apply propext
    constructor
    · intro hK
      exact ⟨⟨(fiber Λ k).obj K, hG ⟨K, hK⟩⟩, ⟨counit K hK.1⟩⟩
    · rintro ⟨P, ⟨i⟩⟩
      exact ⟨BC.prop_of_iso i (hF P).1,
        (DerivedCategory.finiteTorAmplitude _).prop_of_iso i (hF P).2⟩
  let : (ctf Λ k).IsMonoidal := by
    rw [hctf]
    exact (perfect_image_closed Λ k F).1
  let : (ctf Λ k).IsMonoidalClosed := by
    rw [hctf]
    exact (perfect_image_closed Λ k F).2
  let : (ctf Λ k).IsTriangulated := by
    rw [hctf]
    infer_instance
  let : L.Monoidal := inferInstanceAs
    ((ctf Λ k).lift ((perfect Λ).ι ⋙ F) hF).Monoidal
  let : L.Braided := { braided := fun X Y ↦
    ObjectProperty.hom_ext _ (Functor.LaxBraided.braided (F := F) X.obj Y.obj) }
  let : a.toEquivalence.functor.Monoidal := inferInstanceAs L.Monoidal
  let : a.toEquivalence.functor.Braided := inferInstanceAs L.Braided
  let : R.CommShift ℤ := by
    dsimp only [R, restricted]
    infer_instance
  let : R.IsTriangulated := by
    dsimp only [R, restricted]
    infer_instance
  let : R.Monoidal := a.toEquivalence.inverseMonoidal
  let m : R.Braided := {
    braided := a.toEquivalence.toAdjunction.rightAdjointLaxMonoidal_μ_comp_map_braiding }
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, hG, ?_⟩
  exact comparison_of_equivalence Λ k hG m inferInstance
    ⟨inferInstance, inferInstance⟩

end AlgebraicGeometry.ProEtale.CondensedGeometricPoint
