/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.Coefficient.FiniteCoefficientVerdierData
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import Mathlib.RingTheory.Ideal.Quotient.Index
import all WeilConjectures.AlgebraicGeometry.Finite.FiniteDualitySiteComparison
import all WeilConjectures.SixFunctors.Etale.EtaleGeometricBiduality
import all Mathlib.Logic.Small.Defs
import WeilConjectures.SixFunctors.Etale.Derived.WeilComplexDual
import WeilConjectures.SixFunctors.FiniteVerdierNativeComparison
import WeilConjectures.SixFunctors.FiniteVerdierFixedScalarTensor
import WeilConjectures.SixFunctors.FiniteVerdierFixedScalarCoherence
import WeilConjectures.SixFunctors.FiniteVerdierScalarHomInvertibility
import WeilConjectures.SixFunctors.FiniteVerdierProEtaleTransitions

/-! Site-specific geometry for finite Verdier coefficient diagrams. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option linter.style.haveILetI false
universe u v w
open Opposite AlgebraicGeometry
open AlgebraicGeometry.ProEtale

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Functor
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed

namespace WeilConjectures

attribute [local implicit_reducible]
  GrothendieckTopology.monoidalCategory_sheaf_of_essentiallySmall
  GrothendieckTopology.braidedCategory_sheaf_of_essentiallySmall
  GrothendieckTopology.symmetricCategory_sheaf_of_essentiallySmall
  GrothendieckTopology.monoidalClosed_sheaf_of_essentiallySmall
  Etale.sheafMonoidalCategory Etale.sheafBraidedCategory Etale.sheafMonoidalClosed
  ProEtale.sheafMonoidalCategory ProEtale.sheafBraidedCategory
  ProEtale.sheafSymmetricCategory ProEtale.sheafMonoidalClosed
  Sheaf.symmetricCategory Sheaf.braidedCategory


attribute [local implicit_reducible] CategoryTheory.catToReflQuiver
  Etale.derivedTensorHomAdjunction Etale.derivedTensorHomAdjunction₂
  finiteVerdierEtaleTensorAt finiteVerdierEtaleHomAt
  finiteVerdierProEtaleTensorAt finiteVerdierProEtaleHomAt

attribute [local irreducible]
  CategoryTheory.Functor.LaxMonoidal.ihomComparison
  DerivedCategory.monoidalClosed_of_hasFunctorialFlatResolution
  pbcFixedScalarExtension Functor.mapDerivedCategory


section ProEtaleGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed
variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))] [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))]


include hl in
private theorem etaleTarget_finiteTor (n : ℕ) :
    finiteTorConstructibleEtale l E (n + 1) (by omega) X
      (finiteDualizingEtaleTerm l E D X n) := by
  letI : Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
    Padic.finite_coefficientExtensionRing l E (n + 1) (by omega)
  let A := ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))
  letI : HasInvertibleExponent A (Spec (.of D.k)) :=
    coefficient_invertible_exponent D l hl E (n + 1)
  letI := (finiteDualizingCompactification D X).hasCompactification
  apply (finiteTorConstructibleEtale_iff_source l E (n + 1) (by omega) X _).2
  exact Etale.constructibleFiniteTor_dualizingComplex A (𝟙 _) _
    (Etale.constructibleFiniteTor_unit A)

include hl in
private theorem proPairing (n : ℕ)
    (W : DerivedCategory (Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} (finiteDualizingCoeff l E n)))) :
    finiteVerdierProEtalePairingAt (finiteDualizingCoeff l E n) X W := by
  letI : Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
    Padic.finite_coefficientExtensionRing l E (n + 1) (by omega)
  let A := finiteDualizingCoeff l E n
  letI : HasInvertibleExponent A (Spec (.of D.k)) :=
    coefficient_invertible_exponent D l hl E (n + 1)
  exact (Etale.ambient_duality_pairing A (X ↘ Spec (.of D.k))).2 W


include hl in
private theorem proTarget_finiteTor (n : ℕ) :
    finiteTorConstructibleProEtaleModule l E (n + 1) (by omega) X
      ((comparisonUpperStar (ModuleCat.{u + 1} (finiteDualizingCoeff l E n))
        X).mapDerivedCategory.obj (finiteDualizingEtaleTerm l E D X n)) := by
  letI : Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
    Padic.finite_coefficientExtensionRing l E (n + 1) (by omega)
  apply (finiteTor_proEtale_iff l E (n + 1) (by omega) X _).2
  exact ProEtale.DerivedCategory.constructibleFiniteTor_mapDerivedCategory _
    ((finiteTorConstructibleEtale_iff_source l E (n + 1) (by omega) X _).1
      (etaleTarget_finiteTor D l hl E X n))


set_option maxHeartbeats 1000000 in
-- Kernel checking of the concrete localization instances needs a larger budget.
/-- Concrete site-level normalized Verdier coefficient diagrams.
The proof constructs the normalized fixed-scalar tensorator, establishes the
finite-Tor domain and target transition facts, and verifies evaluation,
biduality, identity and quotient cocycle by the native tensor-Hom comparison.
(blueprint: lem-coef-verdier-pro-etale-diagrams). -/
theorem finiteVerdier_proEtale_diagrams
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (X : Scheme.{u})
    [X.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] :
  @FiniteVerdierProEtaleComparison X (finiteDualizingCoeff l E)
    (fun _n ↦ inferInstance) (fun {_ _} h ↦ finiteDualizingQuotient l E h)
    (finiteDualizingQuotient_id l E)
    (fun {_ _ _} h g ↦ finiteDualizingQuotient_comp l E h g)
    (finiteDualizingEtaleTerm l E D X)
    (fun n ↦ finiteTorConstructibleEtale l E (n + 1)
      (Nat.succ_le_succ (Nat.zero_le n)) X)
    (fun n ↦ finiteTorConstructibleProEtaleModule l E (n + 1)
      (Nat.succ_le_succ (Nat.zero_le n)) X)
    (fun _ _ _ _ ↦ True) (fun _ _ _ _ ↦ True)
    (fun {_ _} h ↦ finiteDualizingEtaleComparison l E D X h) 0 := by
  classical
  letI : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  let J := Scheme.ProEt.topology X
  let R := finiteDualizingCoeff l E
  let U (n : ℕ) := (comparisonUpperStar (ModuleCat.{u + 1} (R n)) X).mapDerivedCategory
  let W (n : ℕ) := (U n).obj (finiteDualizingEtaleTerm l E D X n)
  let F {n m : ℕ} (h : m ≤ n) := pbcFixedScalarExtension J (finiteDualizingQuotient l E h)
  let uMap {n m : ℕ} (h : m ≤ n) :=
    (pbcComparisonReduction X (finiteDualizingQuotient l E h)).hom.app
      (finiteDualizingEtaleTerm l E D X n) ≫
        (U m).map (finiteDualizingEtaleComparison l E D X h)
  let hPro (n : ℕ) := proPairing D l hl E X n (W n)
  let hc {n m : ℕ} (h : m ≤ n) :=
    finiteVerdier_fixedScalar_tensor J (finiteDualizingQuotient l E h)
  let c {n m : ℕ} (h : m ≤ n) := (hc h).choose
  let μ {n m : ℕ} (h : m ≤ n) := (hc h).choose_spec.choose
  have hn {n m : ℕ} (h : m ≤ n) := (hc h).choose_spec.choose_spec.1
  have hμ {n m : ℕ} (h : m ≤ n) := (hc h).choose_spec.choose_spec.2.1
  have hb {n m : ℕ} (h : m ≤ n) := (hc h).choose_spec.choose_spec.2.2
  have hcoh := finiteVerdier_fixedScalar_coherence J R
    (fun {_ _} h ↦ finiteDualizingQuotient l E h)
    (finiteDualizingQuotient_id l E)
    (fun {_ _ _} h g ↦ finiteDualizingQuotient_comp l E h g)
    (fun {_ _} h ↦ c h) (fun {_ _} h ↦ μ h)
    (fun {_ _} h ↦ hμ h) (fun {_ _} h ↦ hn h)
  have ht := finiteVerdier_proEtale_transitions D l hl E X
  letI (n : ℕ) := DerivedCategory.symmetricCategory
    (Sheaf J (ModuleCat.{u + 1} (R n)))
  letI {n m : ℕ} (h : m ≤ n) : (F h).Monoidal := (c h).toMonoidal
  letI {n m : ℕ} (h : m ≤ n) : (F h).Braided :=
    { toMonoidal := (c h).toMonoidal
      braided := fun K L ↦ (hb h K L).symm }
  refine ⟨hPro, (fun {_ _} h ↦ μ h), ?_, ?_⟩
  · intro n m h
    exact ⟨_, hn h, HEq.rfl⟩
  · apply finiteVerdier_pro_coherent_assembly
      (fun n ↦ ModuleCat.{u + 1} (R n)) X W
      (fun n ↦ finiteTorConstructibleProEtaleModule l E (n + 1) (by omega) X)
      (fun {_ _} h ↦ F h)
      (fun n ↦ normalizedOriginScalarUnit J (finiteDualizingQuotient l E (le_refl n))
        (finiteDualizingQuotient_id l E n))
      (fun {_ _ _} h g ↦ pbcFixedScalarExtensionComp J _ _ _
        (finiteDualizingQuotient_comp l E h g))
      hcoh.1 (fun {_ _ _} h g ↦ hcoh.2 h g) (fun {_ _} h ↦ μ h)
      (fun {_ _} h K L ↦ congrArg Iso.inv (hμ h K L)) hPro
      (fun {_ _} h ↦ uMap h)
    · intro n m h K hK
      exact ht.1 h K hK
    · intro n m h K hK
      exact (finiteVerdier_scalar_hom_isIso D l hl E X h).2 ⟨K, hK⟩
        ⟨W n, proTarget_finiteTor D l hl E X n⟩
    · intro n m h
      exact ht.2.1 h
    · exact ht.2.2.1
    · exact fun {_ _ _} h g ↦ ht.2.2.2 h g


end ProEtaleGeometry

end WeilConjectures
