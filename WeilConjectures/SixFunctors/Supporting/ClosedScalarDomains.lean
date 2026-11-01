/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.SixFunctors.Finite.FiniteTorAmplitudeProEtaleModule
public import WeilConjectures.AlgebraicGeometry.SfAffineChartPresentation.PurityAffineChartBounds
public import WeilConjectures.AlgebraicGeometry.Sf.SfFiniteExceptionalInverseImage
public import WeilConjectures.SmoothPurity.Sf.SfDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.Etale.Derived.EtaleDerivedScalarTensor
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import Mathlib.CategoryTheory.Limits.Final
import all WeilConjectures.SixFunctors.Finite.Closed.FiniteClosedRealizationDomain
import WeilConjectures.AlgebraicGeometry.Etale.Scalar.EtaleScalarFlatModel
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicTorAmplitudeTransport
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison

/-! # Finite scalar domains for closed exceptional localization

Source: Weil blueprint, sec-six-functors/sk-prop-sf-biduality-general,
lem-coef-finite-closed-shriek, proof paragraph 3
(blueprint: lem-coef-closed-scalar-domains).

Positive levels are indexed by n+1. All scalar functors are the published ordinary,
uncompleted derived extensions, and all site pullbacks are the specified comparison.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

open CategoryTheory.MonoidalCategory

/-- The actual finite quotient at positive level n+1.
Source: blueprint finite closed shriek, proof paragraph 3
(blueprint: lem-coef-closed-scalar-domains). -/
abbrev closedScalarCoefficient (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (n : ℕ) :=
  Padic.coefficientExtensionRing l E (n + 1)

/-- Ordinary derived extension of constant coefficients on the actual small pro-etale site.
Source: blueprint finite closed shriek, proof paragraph 3; Stacks 06YY
(blueprint: lem-coef-closed-scalar-domains). -/
abbrev closedScalarExtension {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) :=
  @ProEtale.pbcFixedScalarExtension.{u} T.ProEt inferInstance
    (essentiallySmallSelf.{0, u, u + 1} _) (ProEt.topology T) (ULift.{u + 1, u} A)
    (ULift.{u + 1, u} B) inferInstance inferInstance (φ.ulift.{u + 1, u + 1})

/-- Finite-Tor membership in the recorded intrinsic constant-ring presentation, with the
specified Tor interval, together with a bounded constructible etale origin in that interval.
Source: blueprint finite closed shriek, proof paragraph 3
(blueprint: lem-coef-closed-scalar-domains). -/
def ClosedScalarDomain (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (n : ℕ)
    (T : Scheme.{u}) (a b : ℤ)
    (K : DerivedCategory (Sheaf (ProEt.topology T)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (closedScalarCoefficient l E n))))) : Prop :=
  finiteTorConstructibleProEtaleModule l E (n + 1) (Nat.succ_pos n) T K ∧
  HasProEtaleTorAmplitude T (closedScalarCoefficient l E n)
    ((ProEtale.finiteCoefficientIntrinsicRealization T
      (closedScalarCoefficient l E n)).mapDerivedCategory.obj K) a b ∧
  ∃ Q : Etale.DerivedCategoryModule
      (ULift.{u + 1, u} (closedScalarCoefficient l E n)) T,
    finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) T Q ∧
    Etale.DerivedCategory.hasTorAmplitudeIn
      (ULift.{u + 1, u} (closedScalarCoefficient l E n)) T a b Q ∧
    Nonempty ((ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1}
        (ULift.{u + 1, u} (closedScalarCoefficient l E n))) T).mapDerivedCategory.obj
        Q ≅ K)

private theorem closedScalar_fixed_domain
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (n : ℕ)
    (T : Scheme.{u}) (a b : ℤ) (hab : a ≤ b)
    (K : DerivedCategory (Sheaf (ProEt.topology T)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (closedScalarCoefficient l E n)))))
    (hbc : ProEtale.DerivedCategory.boundedConstructible
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (closedScalarCoefficient l E n))) T K)
    (ht : ProEtale.DerivedCategory.torAmplitudeIn
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (closedScalarCoefficient l E n))) T a b K) :
    ClosedScalarDomain l E n T a b K := by
  let := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  have hti := (ProEtale.intrinsic_hasProEtaleTorAmplitude_iff_torAmplitudeIn
    (closedScalarCoefficient l E n) T a b hab K).2 ht
  have hbi := (finiteClosed_intrinsic_bc_realization_iff l E (n + 1) (Nat.succ_pos n) T K).2 hbc
  refine ⟨⟨hbi, a, b, hti⟩, hti, ?_⟩
  obtain ⟨Q, hQ, ⟨e⟩⟩ := hbc
  have hQt := ProEtale.DerivedCategory.torAmplitudeIn_of_mapDerivedCategory
    (ULift.{u + 1, u} (closedScalarCoefficient l E n))
    ((_root_.DerivedCategory.torAmplitudeIn _ a b).prop_of_iso e.symm ht)
  have hQbc := (finiteClosed_etale_bc_iff _ T Q).2 hQ
  have hQti := Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.2 hQt
  exact ⟨Q, ⟨hQbc, a, b, hab, hQti⟩, hQti, ⟨e⟩⟩

/-- Scalar extension preserves the same Tor interval and has a flat constructible etale
model supported in that interval, whose ordinary scalar extension represents K_B.
Both displayed identifications are isomorphisms in the appropriate derived category;
the second is B-linear. No flatness of B over A is required.
Source: blueprint finite closed shriek, proof paragraph 3; Stacks 03TT, 0GKB, 09AL,
06YY and 0G7E (blueprint: lem-coef-closed-scalar-domains).

Proof: Descend K using lem-sf-proetale-constructible-origin(ii), and reflect its Tor
interval using lem-exc-comparison-tor-interval. The scheme is Noetherian by
lem-weil-pbc-finite-type-over-noetherian. Apply lem-sp-etale-scalar-flat-model to obtain
Q supported in [a,b], with flat constructible terms and the same properties after
ordinary scalar extension. Apply the B-linear scalar clause of
lem-sp-etale-chart-comparison-isos to identify the pullback of Q tensor B with K_B.
Both rings are finite and killed by a common power of l. Apply the constructible-origin
and Tor-interval comparisons over B to conclude the stated domain membership. -/
theorem closedScalarDomains_scalar
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E L : Type u) [Field E] [Field L]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    [Algebra (Padic l) L] [FiniteDimensional (Padic l) L] (m n : ℕ)
    (φ : closedScalarCoefficient l E m →+* closedScalarCoefficient l L n)
    (T : Over (Spec (.of D.k)))
    [IsSeparated T.hom] [LocallyOfFiniteType T.hom] [QuasiCompact T.hom]
    (a b : ℤ) (_hab : a ≤ b)
    (K : DerivedCategory (Sheaf (ProEt.topology T.left)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (closedScalarCoefficient l E m)))))
    (_hK : finiteTorConstructibleProEtaleModule l E (m + 1) (Nat.succ_pos m) T.left K)
    (_hTor : HasProEtaleTorAmplitude T.left (closedScalarCoefficient l E m)
      ((ProEtale.finiteCoefficientIntrinsicRealization T.left
        (closedScalarCoefficient l E m)).mapDerivedCategory.obj K) a b) :
    ClosedScalarDomain l L n T.left a b ((closedScalarExtension φ T.left).obj K) ∧
    ∃ Q : CochainComplex (Sheaf T.left.smallEtaleTopology
        (ModuleCat.{u + 1} (ULift.{u + 1, u} (closedScalarCoefficient l E m)))) ℤ,
      (∀ q : ℤ, ObjectProperty.flat (Q.X q)) ∧
      (∀ q : ℤ, IsConstructibleEtaleModuleSheaf (Q.X q)) ∧
      (∀ q : ℤ, q < a ∨ b < q → IsZero (Q.X q)) ∧
      Nonempty ((ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1}
          (ULift.{u + 1, u} (closedScalarCoefficient l E m))) T.left).mapDerivedCategory.obj
          (DerivedCategory.Q.obj Q) ≅ K) ∧
      (∀ q : ℤ, ObjectProperty.flat
        ((ProEtale.etaleSheafExtendScalars (φ.ulift.{u + 1, u + 1}) T.left).obj (Q.X q))) ∧
      (∀ q : ℤ, IsConstructibleEtaleModuleSheaf
        ((ProEtale.etaleSheafExtendScalars (φ.ulift.{u + 1, u + 1}) T.left).obj (Q.X q))) ∧
      Nonempty ((ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1}
          (ULift.{u + 1, u} (closedScalarCoefficient l L n))) T.left).mapDerivedCategory.obj
          (DerivedCategory.Q.obj
            (((ProEtale.etaleSheafExtendScalars
              (φ.ulift.{u + 1, u + 1}) T.left).mapHomologicalComplex (.up ℤ)).obj Q)) ≅
          (closedScalarExtension φ T.left).obj K) := by
  let := Padic.finite_coefficientExtensionRing l E (m + 1) (Nat.succ_pos m)
  let := Padic.finite_coefficientExtensionRing l L (n + 1) (Nat.succ_pos n)
  have : IsLocallyNoetherian T.left := LocallyOfFiniteType.isLocallyNoetherian T.hom
  have : CompactSpace T.left := QuasiCompact.compactSpace_of_compactSpace T.hom
  have : IsNoetherian T.left := ⟨⟩
  let A := ULift.{u + 1, u} (closedScalarCoefficient l E m)
  let B := ULift.{u + 1, u} (closedScalarCoefficient l L n)
  let νA := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T.left
  let νB := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) T.left
  let S := ProEtale.pbcFixedScalarExtension T.left.smallEtaleTopology
    (φ.ulift.{u + 1, u + 1})
  have hbc := (finiteClosed_intrinsic_bc_realization_iff l E (m + 1)
    (Nat.succ_pos m) T.left K).1 _hK.1
  obtain ⟨Qe, hQe, ⟨e⟩⟩ := hbc
  have ht := (ProEtale.intrinsic_hasProEtaleTorAmplitude_iff_torAmplitudeIn
    (closedScalarCoefficient l E m) T.left a b _hab K).1 _hTor
  have hQet := ProEtale.DerivedCategory.torAmplitudeIn_of_mapDerivedCategory A
    ((_root_.DerivedCategory.torAmplitudeIn _ a b).prop_of_iso e.symm ht)
  have hQeti := Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.2 hQet
  let Qb : _root_.DerivedCategory.Bounded (Sheaf T.left.smallEtaleTopology
      (ModuleCat.{u + 1} A)) := ⟨Qe, hQe.1⟩
  have hmodel := Etale.exists_etaleScalarFlatModel T.left A B
    (φ.ulift.{u + 1, u + 1}) a b _hab Qb ((finiteClosed_etale_bc_iff A T.left Qe).2 hQe).1 hQeti
  obtain ⟨Q, hf, hc, hz, ⟨eQ⟩⟩ := hmodel.1
  obtain ⟨_, _, hBf, hBc, _, ⟨eB⟩⟩ := hmodel.2.1 Q hf hc hz ⟨eQ⟩
  let d : νB.mapDerivedCategory.obj (S.obj Qe) ≅
      (closedScalarExtension φ T.left).obj K :=
    ((ProEtale.pbcComparisonReduction T.left (φ.ulift.{u + 1, u + 1})).app Qe).symm ≪≫
      (closedScalarExtension φ T.left).mapIso e
  have hSBc : Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} B)
      T.left (S.obj Qe) := by
    obtain ⟨Q', ⟨e'⟩⟩ := hmodel.2.2.1
    refine ⟨(_root_.DerivedCategory.TStructure.t.bounded).prop_of_iso e' Q'.property, ?_⟩
    intro q
    exact (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).1
      (hmodel.2.2.2.1 q)
  have hSBt := ProEtale.DerivedCategory.torAmplitudeIn_mapDerivedCategory B
    (Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.1 hmodel.2.2.2.2)
  refine ⟨closedScalar_fixed_domain l L n T.left a b _hab _
    ((ProEtale.DerivedCategory.boundedConstructible _ T.left).prop_of_iso d
      (ProEtale.DerivedCategory.boundedConstructible_comparisonUpperStar_mapDerivedCategory_obj
        hSBc)) ?_, Q, ?_, hc, hz, ?_, ?_, hBc, ?_⟩
  · exact (_root_.DerivedCategory.torAmplitudeIn _ a b).prop_of_iso d hSBt
  · intro q
    exact ⟨(exactFunctor _ _).prop_of_iso
      (BraidedCategory.tensorLeftIsoTensorRight (Q.X q)).symm (hf q), hf q⟩
  · exact ⟨νA.mapDerivedCategory.mapIso eQ ≪≫ e⟩
  · intro q
    exact ⟨(exactFunctor _ _).prop_of_iso
      (BraidedCategory.tensorLeftIsoTensorRight _).symm (hBf q), hBf q⟩
  · exact ⟨νB.mapDerivedCategory.mapIso eB.symm ≪≫ d⟩

end WeilConjectures
