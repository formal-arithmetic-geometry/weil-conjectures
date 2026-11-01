/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.Coefficient.FiniteCoefficientVerdierData
public import WeilConjectures.SixFunctors.Etale.Derived.WeilComplexDual
public import WeilConjectures.SixFunctors.Etale.EtaleGeometricBiduality
public import WeilConjectures.SixFunctors.Finite.Hom.FiniteHomDomainCalculus
public import WeilConjectures.SixFunctors.FiniteVerdierFixedScalarCoherence
public import WeilConjectures.SixFunctors.FiniteVerdierFixedScalarTensor
public import WeilConjectures.SixFunctors.FiniteVerdierNativeComparison
public import WeilConjectures.SixFunctors.FiniteVerdierProEtaleDiagrams
public import WeilConjectures.SixFunctors.FiniteVerdierScalarHomInvertibility

/-! # Finite Verdier coefficient diagrams without numerical bounds

Source: current blueprint cor-coef-finite-verdier.proof.md, the Hom comparison,
evaluation, double-dual and quotient cocycle sentences.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.ProEtale
namespace WeilConjectures

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

private theorem etaleVerdier_pairing (n : ℕ) :
    finiteVerdierEtalePairingAt (finiteDualizingCoeff l E n) X
      (finiteDualizingEtaleTerm l E D X n) := by
  letI : Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
    Padic.finite_coefficientExtensionRing l E (n + 1) (by omega)
  let A := finiteDualizingCoeff l E n
  letI : HasInvertibleExponent A (Spec (.of D.k)) :=
    coefficient_invertible_exponent D l hl E (n + 1)
  letI := (finiteDualizingCompactification D X).hasCompactification
  exact (Etale.ambient_duality_pairing A (X ↘ Spec (.of D.k))).1

private theorem etaleScalar_finiteTor {n m : ℕ} (h : m ≤ n)
    (K : finiteHomEtale l E X n)
    (hK : finiteTorConstructibleEtale l E (n + 1) (by omega) X K) :
    finiteTorConstructibleEtale l E (m + 1) (by omega) X
      ((finiteHomEtaleReduction l E X h).obj K) := by
  obtain ⟨hcons, a, b, hab, hTor⟩ := hK
  have hh := finiteHomDomain_flatModel D l hl E X h a b hab K hcons hTor
  exact ⟨hh.2.2.1, a, b, hab, hh.2.2.2⟩

/-- Concrete site-level normalized Verdier coefficient diagrams.
The proof constructs the normalized fixed-scalar tensorator, establishes the
finite-Tor domain and target transition facts, and verifies evaluation,
biduality, identity and quotient cocycle by the native tensor-Hom comparison.
(blueprint: lem-coef-verdier-etale-diagrams). -/
theorem finiteVerdier_etale_diagrams
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (X : Scheme.{u})
    [X.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] :
  @FiniteVerdierEtaleComparison X (finiteDualizingCoeff l E)
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
  let J := X.smallEtaleTopology
  let R := finiteDualizingCoeff l E
  let W := finiteDualizingEtaleTerm l E D X
  let F {n m : ℕ} (h : m ≤ n) := pbcFixedScalarExtension J (finiteDualizingQuotient l E h)
  let uMap {n m : ℕ} (h : m ≤ n) := finiteDualizingEtaleComparison l E D X h
  let hEt (n : ℕ) := etaleVerdier_pairing D l hl E X n
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
  have ht := finiteDualizingCoefficientComparisons l E D X hl
  letI (n : ℕ) := DerivedCategory.symmetricCategory
    (Sheaf J (ModuleCat.{u + 1} (R n)))
  letI {n m : ℕ} (h : m ≤ n) : (F h).Monoidal := (c h).toMonoidal
  letI {n m : ℕ} (h : m ≤ n) : (F h).Braided :=
    { toMonoidal := (c h).toMonoidal
      braided := fun K L ↦ (hb h K L).symm }
  refine ⟨hEt, (fun {_ _} h ↦ μ h), ?_, ?_⟩
  · intro n m h
    exact ⟨_, hn h, HEq.rfl⟩
  · apply finiteVerdier_etale_coherent_assembly
      (fun n ↦ ModuleCat.{u + 1} (R n)) X W
      (fun n ↦ finiteTorConstructibleEtale l E (n + 1) (by omega) X)
      (fun {_ _} h ↦ F h)
      (fun n ↦ normalizedOriginScalarUnit J (finiteDualizingQuotient l E (le_refl n))
        (finiteDualizingQuotient_id l E n))
      (fun {_ _ _} h g ↦ pbcFixedScalarExtensionComp J _ _ _
        (finiteDualizingQuotient_comp l E h g))
      hcoh.1 (fun {_ _ _} h g ↦ hcoh.2 h g) (fun {_ _} h ↦ μ h)
      (fun {_ _} h K L ↦ congrArg Iso.inv (hμ h K L)) hEt
      (fun {_ _} h ↦ uMap h)
    · intro n m h K hK
      exact etaleScalar_finiteTor D l hl E X h K hK
    · intro n m h K hK
      exact (finiteVerdier_scalar_hom_isIso D l hl E X h).1 ⟨K, hK⟩
        ⟨W n, etaleTarget_finiteTor D l hl E X n⟩
    · intro n m h
      exact (ht.1 h).2.1
    · exact ht.2.1
    · exact fun {_ _ _} h g ↦ ht.2.2.1 h g

/-- The normalized coefficient diagrams on both sites, without a numerical Tor bound.
The etale construction is proved above by native tensor-Hom transposition and the
finite-coefficient facts. The pro-etale construction uses the same proved calculus
with the transported dualizing object. Their conjunction gives the two-site comparison.

Source: current blueprint cor-coef-finite-verdier.proof.md, sentences 1--4;
DAG cor-coef-finite-verdier, steps 1--3 and the diagram part of step 5.
(blueprint: lem-route-finite-verdier-coefficient-diagrams).
-/
theorem finiteVerdier_coefficient_diagrams
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (X : Scheme.{u})
    [X.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] :
  @FiniteVerdierTwoSitesComparison X (finiteDualizingCoeff l E)
    (fun _n ↦ inferInstance) (fun {_ _} h ↦ finiteDualizingQuotient l E h)
    (finiteDualizingQuotient_id l E) (fun {_ _ _} h g ↦ finiteDualizingQuotient_comp l E h g)
    (finiteDualizingEtaleTerm l E D X)
    (fun n ↦ finiteTorConstructibleEtale l E (n + 1)
      (Nat.succ_le_succ (Nat.zero_le n)) X)
    (fun n ↦ finiteTorConstructibleProEtaleModule l E (n + 1)
      (Nat.succ_le_succ (Nat.zero_le n)) X)
    (fun _ _ _ _ ↦ True) (fun _ _ _ _ ↦ True)
    (fun {_ _} h ↦ finiteDualizingEtaleComparison l E D X h) 0 := by
  exact ⟨finiteVerdier_etale_diagrams D l hl E X,
    finiteVerdier_proEtale_diagrams D l hl E X⟩

end WeilConjectures
