/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.SfIdentificationData
import WeilConjectures.SixFunctors.NativePointSectionsPerfect
import WeilConjectures.SixFunctors.NativeSmoothPurityUnit
import WeilConjectures.SixFunctors.NativeTateLineInvertible
import WeilConjectures.SixFunctors.NativeSitePerfectDual
import WeilConjectures.AlgebraicGeometry.DetThmSfCtfStabilityInternalHom
import WeilConjectures.SixFunctors.CtfStabilityDirectImages
import WeilConjectures.AlgebraicGeometry.CompactificationCoherenceCocycle
import WeilConjectures.PoincareDuality.CondensedProperComparison
import WeilConjectures.AlgebraicGeometry.PodCtfAdjunctions
import WeilConjectures.AlgebraicGeometry.CondensedPurityCoefficientChange
import WeilConjectures.CategoryTheory.ShiftedInvertibleEvaluation
import all WeilConjectures.AlgebraicGeometry.RationalP1LineFromPreservation

/-! # Native smooth duality models

Source: the current smooth Poincare identification proof, steps 1 and 3.
(blueprint: lem-sf-identification-geometric-models).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local instance 20000] HasDerivedCategory.ofIsGrothendieckAbelian
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [local instance 10000] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.ProEtale.PurityTransport
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace WeilConjectures.SixFunctors

private theorem admissible_iso (ell : ℕ) [Fact ell.Prime]
    {A B : ScalarSixRing.{u}} (e : A ≅ B)
    (hA : IsLocalizingAdmissibleCoefficient ell A.X) :
    IsLocalizingAdmissibleCoefficient ell B.X := by
  let eM := (CommMon.forget₂Mon _).mapIso e.symm
  rcases hA with h | h | h | h | h | h
  · obtain ⟨A, hA, tA, dA, rA, hf, hn, ⟨h⟩⟩ := h
    exact Or.inl ⟨A, hA, tA, dA, rA, hf, hn, ⟨eM ≪≫ h⟩⟩
  · exact Or.inr (Or.inl ⟨eM ≪≫ h.some⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨eM ≪≫ h.some⟩))
  · obtain ⟨E, ⟨h⟩⟩ := h
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨E, ⟨eM ≪≫ h⟩⟩)))
  · obtain ⟨E, ⟨h⟩⟩ := h
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨E, ⟨eM ≪≫ h⟩⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨eM ≪≫ h.some⟩))))

private theorem coefficient_admissible (ell : ℕ) [Fact ell.Prime]
    (c : Coefficient ell) : IsLocalizingAdmissibleCoefficient ell (c.obj.{u} ell) := by
  cases c with
  | finite A hf n hn =>
    let : TopologicalSpace A := ⊥
    let : DiscreteTopology A := discreteTopology_bot A
    exact Or.inl ⟨A, inferInstance, inferInstance, inferInstance, inferInstance,
      hf, ⟨n + 1, fun a ↦ by rw [nsmul_eq_mul, Nat.cast_pow, hn, zero_mul]⟩,
      ⟨Iso.refl _⟩⟩
  | integers => exact Or.inr (Or.inl ⟨Iso.refl _⟩)
  | rationals => exact Or.inr (Or.inr (Or.inl ⟨Iso.refl _⟩))
  | integral E => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨E, ⟨Iso.refl _⟩⟩))))
  | rational E => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨E, ⟨Iso.refl _⟩⟩)))
  | closure => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨Iso.refl _⟩))))

attribute [-instance] AlgebraicGeometry.ProEtale.RationalP1.internalMonoidal in
private theorem unit_mem (Λ : ScalarSixRing.{u}) (T : Scheme.{u})
    [CompactSpace T] [QuasiSeparatedSpace T] :
    (constantModelBoundedConstructible Λ.X T ⊓ DerivedCategory.finiteTorAmplitude _)
      (𝟙_ _) := by
  have := (constantModelConstructibleFiniteTor_wellDefined Λ.X T).2.1
  refine ⟨(constantModelBoundedConstructible Λ.X T).prop_of_iso
    (DerivedCategory.singleFunctorObjUnitIso _)
    (AlgebraicGeometry.ProEtale.RationalP1.coefficientUnit_boundedConstructible Λ.X T),
    0, 0, ?_⟩
  exact (DerivedCategory.torAmplitudeIn _ 0 0).prop_of_iso
    (DerivedCategory.singleFunctorObjUnitIso _)
    (DerivedCategory.torAmplitudeIn_singleFunctor_obj_of_flat
      (ObjectProperty.flat_of_isDualizable isDualizable_unit))

variable (ell : ℕ) [Fact ell.Prime]
  (D : WeilConjectures.FiniteFieldDatum.{u}) (hEll : ell ≠ D.p)
  (Λ : ScalarSixRing.{u}) (c : PurityTransport.Coefficient ell)
  (e : c.bundled.{u} ell ≅ Λ)
  (X : Over (Spec (.of D.k))) [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom] (d : ℕ)
  [SmoothOfRelativeDimension d X.hom] (cf : Compactification X.hom)
  (K : ConstantModelConstructibleFiniteTor Λ.X X.left)

attribute [-instance] AlgebraicGeometry.ProEtale.RationalP1.internalMonoidal in
include hEll in
private theorem native_adjoint
    (ha : IsLocalizingAdmissibleCoefficient ell Λ.X) :
    Nonempty (ScalarExceptionalAdjoint Λ cf) := by
  let : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  let := PurityCoefficientChange.fieldPrime D
  let := PurityCoefficientChange.fieldDifferent ell D hEll
  let : X.left.Over (Spec (.of D.k)) := ⟨X.hom⟩
  let : (Spec (.of D.k)).Over (Spec (.of D.k)) := ⟨𝟙 _⟩
  let : X.hom.IsOver (Spec (.of D.k)) := ⟨by
    change X.hom ≫ 𝟙 _ = X.hom
    exact Category.comp_id _⟩
  have : LocallyOfFiniteType (X.left ↘ Spec (.of D.k)) := by
    change LocallyOfFiniteType X.hom
    infer_instance
  have : QuasiCompact (X.left ↘ Spec (.of D.k)) := by
    change QuasiCompact X.hom
    infer_instance
  have : IsSeparated (X.left ↘ Spec (.of D.k)) := by
    change IsSeparated X.hom
    infer_instance
  have : LocallyOfFiniteType ((Spec (.of D.k)) ↘ Spec (.of D.k)) := by
    change LocallyOfFiniteType (𝟙 (Spec (.of D.k)))
    infer_instance
  have : QuasiCompact ((Spec (.of D.k)) ↘ Spec (.of D.k)) := by
    change QuasiCompact (𝟙 (Spec (.of D.k)))
    infer_instance
  have : IsSeparated ((Spec (.of D.k)) ↘ Spec (.of D.k)) := by
    change IsSeparated (𝟙 (Spec (.of D.k)))
    infer_instance
  let bc : Compactification.BoundaryCompactification X.hom :=
    ⟨⟨cf, Compactification.quasiCompact_openImmersion cf inferInstance⟩⟩
  obtain ⟨_, _, H⟩ := podGeneralCtfAdjunctions Λ.X ell D.k
    (BaseFieldFiniteCD.of_isAlgClosed ell D.k) X.hom ha
  obtain ⟨h, G, adj, F₀, G₀, α, β, _, _⟩ := H bc
  have hX := (constantModelConstructibleFiniteTor_wellDefined Λ.X X.left).2.1
  have hY := (constantModelConstructibleFiniteTor_wellDefined Λ.X (Spec (.of D.k))).2.1
  let := hX
  let := hY
  refine ⟨{ localizing := h
            right := G
            adjunction := adj
            lower_preserves := ?_
            right_preserves := ?_ }⟩
  · intro M
    exact (constantModelBoundedConstructible Λ.X (Spec (.of D.k)) ⊓
      DerivedCategory.finiteTorAmplitude _).prop_of_iso
      ((localizingClosureProEtale Λ.X (Spec (.of D.k))).ι.mapIso (α.app M))
      (F₀.obj M).property
  · intro M
    exact (constantModelBoundedConstructible Λ.X X.left ⊓
      DerivedCategory.finiteTorAmplitude _).prop_of_iso
      ((localizingClosureProEtale Λ.X X.left).ι.mapIso (β.app M))
      (G₀.obj M).property

attribute [-instance] AlgebraicGeometry.ProEtale.RationalP1.internalMonoidal in
include hEll in
private theorem proper_comparison
    (ha : IsLocalizingAdmissibleCoefficient ell Λ.X) (hp : IsProper X.hom) :
    letI : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
    Nonempty ((pairingOrdinarySections Λ.X D.k X.hom).obj K.obj ≅
      (pairingCompactSections Λ.X D.k cf).obj K.obj) := by
  let := hp
  let : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  let := PurityCoefficientChange.fieldPrime D
  let := PurityCoefficientChange.fieldDifferent ell D hEll
  let : X.left.Over (Spec (.of D.k)) := ⟨X.hom⟩
  let : (Spec (.of D.k)).Over (Spec (.of D.k)) := ⟨𝟙 _⟩
  let : X.hom.IsOver (Spec (.of D.k)) := ⟨by
    change X.hom ≫ 𝟙 _ = X.hom
    exact Category.comp_id _⟩
  have : LocallyOfFiniteType (X.left ↘ Spec (.of D.k)) := by
    change LocallyOfFiniteType X.hom
    infer_instance
  have : QuasiCompact (X.left ↘ Spec (.of D.k)) := by
    change QuasiCompact X.hom
    infer_instance
  have : IsSeparated (X.left ↘ Spec (.of D.k)) := by
    change IsSeparated X.hom
    infer_instance
  have : LocallyOfFiniteType ((Spec (.of D.k)) ↘ Spec (.of D.k)) := by
    change LocallyOfFiniteType (𝟙 (Spec (.of D.k)))
    infer_instance
  have : QuasiCompact ((Spec (.of D.k)) ↘ Spec (.of D.k)) := by
    change QuasiCompact (𝟙 (Spec (.of D.k)))
    infer_instance
  have : IsSeparated ((Spec (.of D.k)) ↘ Spec (.of D.k)) := by
    change IsSeparated (𝟙 (Spec (.of D.k)))
    infer_instance
  let bc : Compactification.BoundaryCompactification X.hom :=
    ⟨⟨cf, Compactification.quasiCompact_openImmersion cf inferInstance⟩⟩
  let bp : Compactification.BoundaryCompactification X.hom :=
    ⟨⟨Compactification.ofIsProper X.hom, by
      change QuasiCompact (𝟙 X.left)
      infer_instance⟩⟩
  obtain ⟨φ, _⟩ := compactification_coherence_cocycle Λ.X ell ha D.k X.hom
  let N := (scalarExceptionalInclusion Λ X.left).obj K
  let q := (φ bp bc).app N
  let F : CohomologyTransport.D Λ.X (Spec (.of D.k)) ⥤
      DerivedCategory.{u + 1} (ModuleCat.{u + 1} (condensedScalarRing Λ.X)) :=
    (CohomologyTransport.sections Λ.X (Spec (.of D.k))).mapDerivedCategory
  exact ⟨F.mapIso ((TraceCupProper.comparison Λ.X X.hom).symm.app K.obj ≪≫ q)⟩

set_option maxHeartbeats 800000 in
-- The assembly elaborates the full restricted-adjunction and scalar-functor records.
attribute [-instance] AlgebraicGeometry.ProEtale.RationalP1.internalMonoidal in
/-- Native geometric input to the smooth identification, without the duality pairing.
Source: current blueprint sk-thm-sf-identification.proof.md, first paragraph,
purity and finiteness (blueprint: lem-sf-identification-geometric-models).

Proof: the algebraic closure has ell-cohomological dimension zero. Exceptional
adjoint existence and constructible finite-Tor stability restrict the Brown right
adjoint to Dctf; the regular unit is bounded constructible of Tor amplitude [0,0].
Transport the normalized purity family along the coefficient isomorphism e; the
invertible mate of the compact-support comparison, evaluated at the unit,
identifies the shifted Tate line with the indicated value of each R, and the mate
counit identity gives the displayed trace equation. The Tate line is
tensor-invertible since a compatible-root pro-etale cover trivializes it.
Internal-Hom stability applies to K and the unit and to K and the exceptional
unit. Purity transports the exceptional-unit membership to the shifted line, and
shifted invertible-factor cancellation identifies the shifted twisted coefficient
dual with the Verdier dual. Locally dualizing a bounded finite-projective model gives
the asserted site-perfect dual and its exact pairing, with the usual evaluation.
Apply geometric-point finiteness to K for compact supports, and to the twisted
coefficient dual for ordinary supports; exact point sections and shift comparison
identify the resulting perfect scalar complexes with the displayed factors.
For proper X, compactification independence followed by the identity
compactification comparison supplies the last isomorphism. These constructions
apply also to empty X, K=0, d=0, and the zero coefficient ring. -/
theorem sfIdentificationGeometricModels
    (E : PadicAlgCl.FiniteIntermediateField ell)
    (hΛ : IsPurityFrobeniusCoefficient ell E Λ) :
    letI : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
    Nonempty (ScalarExceptionalAdjoint Λ cf) ∧
    ∃ hs : (constantModelBoundedConstructible Λ.X (Spec (.of D.k)) ⊓
        DerivedCategory.finiteTorAmplitude _) (𝟙_ _),
    ∀ R : ScalarExceptionalAdjoint Λ cf,
    ∃ γ : (smoothTraceCoefficientLine ell Λ c e X.left d) ⟦2 * (d : ℤ)⟧ ≅
        (R.upper.obj ⟨𝟙_ _, hs⟩).obj,
      (rightDerivedLowerShriekOfCompactification Λ.X cf).map γ.hom ≫
          R.counit ⟨𝟙_ _, hs⟩ =
        smoothTraceUnitOfCoefficientIso ell Λ c e D hEll (pairingSmoothDatum D X d cf) ∧
      IsInvertible (smoothTraceCoefficientLine ell Λ c e X.left d) ∧
      (constantModelBoundedConstructible Λ.X X.left ⊓ DerivedCategory.finiteTorAmplitude _)
        ((ihom K.obj).obj (𝟙_ _)) ∧
      (constantModelBoundedConstructible Λ.X X.left ⊓ DerivedCategory.finiteTorAmplitude _)
        ((ihom K.obj).obj (R.upper.obj ⟨𝟙_ _, hs⟩).obj) ∧
      (constantModelBoundedConstructible Λ.X X.left ⊓ DerivedCategory.finiteTorAmplitude _)
        ((smoothTraceCoefficientLine ell Λ c e X.left d) ⟦2 * (d : ℤ)⟧) ∧
      (constantModelBoundedConstructible Λ.X X.left ⊓ DerivedCategory.finiteTorAmplitude _)
        ((((ihom K.obj).obj (𝟙_ _)) ⊗ smoothTraceCoefficientLine ell Λ c e X.left d)
          ⟦2 * (d : ℤ)⟧) ∧
      (IsPerfectOnCoefficientSite Λ.X X.left K.obj →
        IsPerfectOnCoefficientSite Λ.X X.left ((ihom K.obj).obj (𝟙_ _)) ∧
          ∃ ep : ExactPairing ((ihom K.obj).obj (𝟙_ _)) K.obj,
            ep.evaluation' = (ihom.ev K.obj).app (𝟙_ _)) ∧
      DerivedCategory.IsPerfectRingComplex ((pairingCompactSections Λ.X D.k cf).obj K.obj) ∧
      DerivedCategory.IsPerfectRingComplex
        (((pairingOrdinarySections Λ.X D.k X.hom).obj
          ((ihom K.obj).obj (𝟙_ _) ⊗ smoothTraceCoefficientLine ell Λ c e X.left d))
            ⟦2 * (d : ℤ)⟧) ∧
      (IsProper X.hom → Nonempty
        ((pairingOrdinarySections Λ.X D.k X.hom).obj K.obj ≅
          (pairingCompactSections Λ.X D.k cf).obj K.obj)) := by
  let : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  let := PurityCoefficientChange.fieldPrime D
  let := PurityCoefficientChange.fieldDifferent ell D hEll
  let : X.left.Over (Spec (.of D.k)) := ⟨X.hom⟩
  let : (Spec (.of D.k)).Over (Spec (.of D.k)) := ⟨𝟙 _⟩
  let : X.hom.IsOver (Spec (.of D.k)) := ⟨by
    change X.hom ≫ 𝟙 _ = X.hom
    exact Category.comp_id _⟩
  have : LocallyOfFiniteType (X.left ↘ Spec (.of D.k)) := by
    change LocallyOfFiniteType X.hom
    infer_instance
  have : QuasiCompact (X.left ↘ Spec (.of D.k)) := by
    change QuasiCompact X.hom
    infer_instance
  have : IsSeparated (X.left ↘ Spec (.of D.k)) := by
    change IsSeparated X.hom
    infer_instance
  have : LocallyOfFiniteType ((Spec (.of D.k)) ↘ Spec (.of D.k)) := by
    change LocallyOfFiniteType (𝟙 (Spec (.of D.k)))
    infer_instance
  have : QuasiCompact ((Spec (.of D.k)) ↘ Spec (.of D.k)) := by
    change QuasiCompact (𝟙 (Spec (.of D.k)))
    infer_instance
  have : IsSeparated ((Spec (.of D.k)) ↘ Spec (.of D.k)) := by
    change IsSeparated (𝟙 (Spec (.of D.k)))
    infer_instance
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : QuasiSeparatedSpace X.left := quasiSeparatedSpace_of_quasiSeparated X.hom
  let : ∀ x : X.left, Invertible (ell : X.left.residueField x) := fun x ↦
    (by
      have h := IsUnit.map
        (X.hom.residueFieldAlgebraMap x) (primeUnit D ell hEll)
      simpa using h : IsUnit (ell : X.left.residueField x)).invertible
  have ha := admissible_iso ell e (coefficient_admissible ell c)
  have hs := unit_mem Λ (Spec (.of D.k))
  have hu := unit_mem Λ X.left
  refine ⟨native_adjoint ell D hEll Λ X cf ha, hs, ?_⟩
  intro R
  obtain ⟨γ, hγ⟩ := native_smoothPurity_unit ell D hEll Λ c e
    (pairingSmoothDatum D X d cf) hs R
  have hT := native_tateLine_isInvertible ell Λ c e X.left d
  have hdual := (internalHom_stability (Λ := Λ.X) ell D.k
    (BaseFieldFiniteCD.of_isAlgClosed ell D.k) ha K.obj (𝟙_ _) K.property hu).1
  have hverd := (internalHom_stability (Λ := Λ.X) ell D.k
    (BaseFieldFiniteCD.of_isAlgClosed ell D.k) ha K.obj
      (R.upper.obj ⟨𝟙_ _, hs⟩).obj K.property (R.upper.obj ⟨𝟙_ _, hs⟩).property).1
  have := (constantModelConstructibleFiniteTor_wellDefined Λ.X X.left).2.1
  have := (constantModelConstructibleFiniteTor_wellDefined Λ.X X.left).2.2.2.1
  have hline := (constantModelBoundedConstructible Λ.X X.left ⊓
    DerivedCategory.finiteTorAmplitude _).prop_of_iso γ.symm
      (R.upper.obj ⟨𝟙_ _, hs⟩).property
  obtain ⟨j, _⟩ := MonoidalClosed.shiftedInvertibleEvaluation K.obj
    (smoothTraceCoefficientLine ell Λ c e X.left d)
    (R.upper.obj ⟨𝟙_ _, hs⟩).obj hT (2 * (d : ℤ)) γ
  have htwist := (constantModelBoundedConstructible Λ.X X.left ⊓
    DerivedCategory.finiteTorAmplitude _).prop_of_iso j.symm hverd
  refine ⟨γ, hγ, hT, hdual, hverd, hline, htwist,
    native_sitePerfect_dual Λ.X X.left K.obj, ?_, ?_, ?_⟩
  · exact native_pointSections_perfect ell D hEll Λ E hΛ
      ⟨_, R.lower_preserves K⟩
  · have hpush := (constructibleFiniteTor_stability_direct_images ell D.k
      (BaseFieldFiniteCD.of_isAlgClosed ell D.k) Λ.X ha X.hom).2.2.2.1 _ htwist
    have hperf := native_pointSections_perfect ell D hEll Λ E hΛ ⟨_, hpush⟩
    obtain ⟨P, a, b, hPa, hPb, hP, ⟨i⟩⟩ := hperf
    exact ⟨P, a, b, hPa, hPb, hP,
      ⟨(((pairingOrdinarySections Λ.X D.k X.hom).commShiftIso
          (2 * (d : ℤ))).app _).symm ≪≫ i⟩⟩
  · exact proper_comparison ell D hEll Λ X cf K ha

end WeilConjectures.SixFunctors
