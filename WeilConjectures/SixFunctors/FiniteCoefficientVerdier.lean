/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FiniteCoefficientVerdierData

import WeilConjectures.AlgebraicGeometry.WeilVerdierPreservationStrata
import WeilConjectures.AlgebraicGeometry.FiniteHomDomainCalculus
import WeilConjectures.SixFunctors.FiniteVerdierCoefficientDiagrams
import WeilConjectures.SixFunctors.FiniteVerdierProEtaleLeftTor

/-! # Finite coefficient change for Verdier duality

Source: blueprint cor-coef-finite-verdier.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.ProEtale
namespace WeilConjectures

private theorem coherent_with_left_bounds
    (V : ℕ → Type v) [∀ n, Category.{w} (V n)]
    (T : ∀ n, V n ⥤ V n ⥤ V n) (H : ∀ n, (V n)ᵒᵖ ⥤ V n ⥤ V n)
    (W : ∀ n, V n) (P : ∀ n, ObjectProperty (V n))
    (Tor : ∀ n, ℤ → ℤ → ObjectProperty (V n))
    (S : ∀ {n m : ℕ}, m ≤ n → V n ⥤ V m)
    (unit : ∀ n, S (le_refl n) ≅ 𝟭 (V n))
    (comp : ∀ {n m r : ℕ} (h : m ≤ n) (g : r ≤ m), S h ⋙ S g ≅ S (g.trans h))
    (μ : ∀ {n m : ℕ} (h : m ≤ n),
      Functor.uncurry.obj (T n) ⋙ S h ≅
        (S h).prod (S h) ⋙ Functor.uncurry.obj (T m))
    (ev : ∀ n (K : V n), ((T n).obj (((H n).obj (op K)).obj (W n))).obj K ⟶ W n)
    (δ : ∀ n (K : V n),
      K ⟶ (dualityDoubleFunctor (H n) (W n)).obj K)
    (uMap : ∀ {n m : ℕ} (h : m ≤ n), (S h).obj (W n) ⟶ W m) (d : ℕ)
    (hcore : FiniteVerdierCoherentComparison V T H W P (fun _ _ _ _ ↦ True)
      (fun {_ _} h ↦ S h) unit (fun {_ _ _} h g ↦ comp h g)
      (fun {_ _} h ↦ μ h) ev δ (fun {_ _} h ↦ uMap h) 0)
    (hbound : ∀ {n m : ℕ} (h : m ≤ n) (K : V n), P n K →
      ∀ a b : ℤ, a ≤ b → Tor n a b K →
        Tor m (-b - 2 * (d : ℤ)) (-a)
          ((S h).obj (((H n).obj (op K)).obj (W n))))
    (hiso : ∀ (n : ℕ) (a b : ℤ) {K L : V n}, (K ≅ L) →
      Tor n a b K → Tor n a b L) :
    FiniteVerdierCoherentComparison V T H W P Tor
      (fun {_ _} h ↦ S h) unit (fun {_ _ _} h g ↦ comp h g)
      (fun {_ _} h ↦ μ h) ev δ (fun {_ _} h ↦ uMap h) d := by
  obtain ⟨c, hc, hunit, hcomp⟩ := hcore
  refine ⟨c, ?_, hunit, hcomp⟩
  intro n m h K hK
  obtain ⟨hP, hi, he, hδ, _⟩ := hc h K hK
  refine ⟨hP, hi, he, hδ, ?_⟩
  intro a b hab ht
  have hb := hbound h K hK a b hab ht
  let := hi
  exact ⟨hb, hiso m _ _ (asIso ((c h).app (op K))) hb⟩

private theorem etale_tor_of_iso
    (R : Type (u + 1)) [CommRing R] (X : Scheme.{u}) (a b : ℤ)
    {K L : Etale.DerivedCategoryModule R X} (e : K ≅ L)
    (ht : Etale.DerivedCategory.hasTorAmplitudeIn R X a b K) :
    Etale.DerivedCategory.hasTorAmplitudeIn R X a b L := by
  intro M i hi
  exact IsZero.of_iso (ht M i hi)
    ((_root_.DerivedCategory.homologyFunctor _ i).mapIso
      (((Etale.derivedTensor (ModuleCat.{u + 1} R) X).mapIso e).app
        ((_root_.DerivedCategory.singleFunctor _ 0).obj M))).symm

private theorem proEtale_tor_of_iso
    (X : Scheme.{u}) (R : Type u) [CommRing R] (a b : ℤ)
    {K L : Scheme.proEtaleDerivedCategory X R} (e : K ≅ L)
    (ht : Scheme.HasProEtaleTorAmplitude X R K a b) :
    Scheme.HasProEtaleTorAmplitude X R L a b := by
  refine ⟨ht.1, ?_⟩
  intro A P hA f hf hP M i hi
  obtain ⟨eA⟩ := hA
  exact ht.2 A P ⟨eA ≪≫ e.symm⟩ f hf hP M i hi

private theorem etale_left_tor_bound
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (d : ℕ) (X : Scheme.{u})
    (hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞))
    [X.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    {n m : ℕ} (h : m ≤ n)
    (K : Etale.DerivedCategoryModule (finiteDualizingCoeff l E n) X)
    (hK : finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) X K)
    (a b : ℤ) (hab : a ≤ b)
    (ht : Etale.DerivedCategory.hasTorAmplitudeIn (finiteDualizingCoeff l E n) X a b K) :
    Etale.DerivedCategory.hasTorAmplitudeIn (finiteDualizingCoeff l E m) X
      (-b - 2 * (d : ℤ)) (-a)
      ((Etale.scalarExtension (finiteDualizingQuotient l E h) X).obj
        (((Etale.derivedHom (ModuleCat.{u + 1} (finiteDualizingCoeff l E n)) X).obj
          (op K)).obj (finiteDualizingEtaleTerm l E D X n))) := by
  have hv := verdier_preservation_strata D l hl E (n + 1) (Nat.succ_pos n) X d hd
    a b K hK.1 ht
  have hi : -b - 2 * (d : ℤ) ≤ -a := by omega
  have hr := finiteHomDomain_flatModel D l hl E X h
    (-b - 2 * (d : ℤ)) (-a) hi _ hv.1 hv.2
  exact hr.2.2.2

/-- Finite reductions of Verdier duality, including both sites and all coefficient
quotients. The compatibility equations use the specified evaluation and its transpose.
Source: Weil conjectures blueprint, cor-coef-finite-verdier, order 2142 (main: 2486).
(blueprint: cor-coef-finite-verdier).

Proof:
1. By lem-weil-verdier-preservation-strata the etale dualizing object is finite-Tor
   constructible. A bounded flat model (lem-sf-flat-model) stays bounded and flat
   after reduction; thm-constructible-serre gives constructibility of its cohomology.
2. Apply thm-coef-finite-hom to (K,omega_A), then compose with Hom(K_B,u) for
   the counit-defined u of lem-coef-finite-dualizing. This gives the natural comparison
   and its invertibility on finite-Tor constructible K, without asserting it elsewhere.
3. Its tensor-Hom transpose is scalar extension of evaluation followed by u. The
   balancing tensor comparison gives exactly the displayed evaluation equation.
4. Transpose that equation once more using lem-weil-duality-pairing. Naturality in
   K and the symmetry identify the two transposes, yielding the double-dual square
   S(delta_K);d_DK = delta_KB;D_B(d_K).
5. The quotient cocycles of thm-coef-finite-hom and lem-coef-finite-dualizing,
   together with lem-fix-operation-reduction, give the displayed composite equation.
   Their unit normalizations give the identity case, including at level one.
6. Verdier preservation gives [-b-2d,-a] for D_AK. For every B-module sheaf N,
   (P tensor_A B) tensor_B N is isomorphic to P tensor_A N by balancing, with
   inverse p tensor z mapping to (p tensor 1) tensor z. K-flat computation from
   lem-weil-pbc-ringed-topoi-derived-tensor-pullback preserves the interval after
   reduction. The comparison isomorphism gives the same interval for D_B(K_B).
7. Use lem-sf-proetale-constructible-origin and lem-sf-comparison-tor-amplitude to
   represent a pro-etale input by an etale input with the same interval. Transport
   omega and u by comparison pullback and pbcComparisonReduction. The evaluation
   comparisons of lem-weil-finite-duality-site-comparison identify the Hom map and
   its transpose. Thus steps 2--5 give both equations and the cocycle there, and the
   same balanced-tensor argument in step 6 gives both pro-etale Tor bounds.
-/
theorem finite_coefficient_verdier
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (d : ℕ) (X : Scheme.{u})
    (hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞))
    [X.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] :
    FiniteCoefficientVerdierComparison D l hl E d X hd := by
  obtain ⟨⟨hEt, μEt, hnEt, hcEt⟩, ⟨hPro, μPro, hnPro, hcPro⟩⟩ :=
    finiteVerdier_coefficient_diagrams D l hl E X
  constructor
  · refine ⟨hEt, μEt, hnEt, ?_⟩
    apply coherent_with_left_bounds (hcore := hcEt)
    · intro n m h K hK a b hab ht
      exact etale_left_tor_bound D l hl E d X hd h K hK a b hab ht
    · intro n a b K L e ht
      exact etale_tor_of_iso (finiteDualizingCoeff l E n) X a b e ht
  · refine ⟨hPro, μPro, hnPro, ?_⟩
    apply coherent_with_left_bounds (hcore := hcPro)
    · intro n m h K hK a b hab ht
      exact finiteVerdier_proEtale_left_tor D l hl E d X hd h K hK a b hab ht
    · intro n a b K L e ht
      exact proEtale_tor_of_iso X (Padic.coefficientExtensionRing l E (n + 1)) a b
        ((ProEtale.finiteCoefficientIntrinsicRealization X
          (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory.mapIso e) ht

end WeilConjectures
