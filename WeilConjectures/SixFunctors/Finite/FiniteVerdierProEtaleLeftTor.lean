/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.Coefficient.FiniteCoefficientVerdierData

import all WeilConjectures.AlgebraicGeometry.Finite.FiniteDualitySiteComparison
import all WeilConjectures.SixFunctors.Etale.EtaleGeometricBiduality
import WeilConjectures.SixFunctors.Supporting.WeilVerdierPreservationStrata
import WeilConjectures.SixFunctors.Finite.Hom.FiniteHomDomainCalculus
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicTorAmplitudeTransport
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison

/-! # Tor bounds for reduced pro-etale Verdier duals

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

/-- Scalar reduction of the pro-etale Verdier dual has the uniform dual interval.
This is only the left endpoint bound; it asserts no coefficient-comparison morphism.

Source: current blueprint cor-coef-finite-verdier.proof.md, final Tor-bound sentence;
DAG cor-coef-finite-verdier, step 5, final two sentences.
(blueprint: lem-coef-finite-verdier-proetale-left-tor).

Proof:
By the intrinsic-to-fixed-module Tor equivalence and the fixed-module constructible
equivalence of lem-weil-finite-duality-site-comparison, K is the comparison pullback
nu^*K' of an etale finite-Tor constructible K' with the same interval [a,b] (reflect
the interval along eK : nu^*K' ≅ K through site comparison). Etale Verdier
preservation (lem-weil-verdier-preservation-strata) gives N = RHom(K', omega) the
interval [-b-2d,-a], ordered since a <= b and d >= 0; the flat model of
lem-coef-finite-hom-domain-calculus keeps that interval for N ⊗^L_A B, with no
flatness of B over A. The dualizing term is bounded constructible, so the Hom
comparison of lem-weil-finite-duality-site-comparison gives nu^*N ≅ RHom(nu^*K',
nu^*omega), and contravariance in eK gives nu^*N ≅ RHom(K, nu^*omega). The inverse
of pbcComparisonReduction at N, followed by scalar extension of this isomorphism,
identifies nu^*(N ⊗^L_A B) with the reduced pro-etale dual. Site comparison
preserves the Tor interval of N ⊗^L_A B; transport it along this isomorphism and
apply the intrinsic-to-fixed-module Tor equivalence at B. Every degree-zero test
module sheaf is used; zero input, the empty scheme, identity quotients, d = 0 and
a = b are covered by the same maps and inequalities. -/
theorem finiteVerdier_proEtale_left_tor
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (d : ℕ) (X : Scheme.{u})
    (hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞))
    [X.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    {n m : ℕ} (h : m ≤ n)
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} (finiteDualizingCoeff l E n))))
    (hK : finiteTorConstructibleProEtaleModule l E (n + 1) (Nat.succ_pos n) X K)
    (a b : ℤ) (hab : a ≤ b)
    (ht : Scheme.HasProEtaleTorAmplitude X (Padic.coefficientExtensionRing l E (n + 1))
      ((ProEtale.finiteCoefficientIntrinsicRealization X
        (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory.obj K) a b) :
    Scheme.HasProEtaleTorAmplitude X (Padic.coefficientExtensionRing l E (m + 1))
      ((ProEtale.finiteCoefficientIntrinsicRealization X
        (Padic.coefficientExtensionRing l E (m + 1))).mapDerivedCategory.obj
        ((pbcFixedScalarExtension (Scheme.ProEt.topology X)
          (finiteDualizingQuotient l E h)).obj
          (((finiteVerdierProEtaleHomAt (finiteDualizingCoeff l E n) X).obj (op K)).obj
            ((comparisonUpperStar (ModuleCat.{u + 1} (finiteDualizingCoeff l E n))
              X).mapDerivedCategory.obj (finiteDualizingEtaleTerm l E D X n)))))
      (-b - 2 * (d : ℤ)) (-a) := by
  classical
  let A := Padic.coefficientExtensionRing l E (n + 1)
  let B := Padic.coefficientExtensionRing l E (m + 1)
  let : Finite A := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  let : Finite B := Padic.finite_coefficientExtensionRing l E (m + 1) (Nat.succ_pos m)
  let F := (comparisonUpperStar (ModuleCat.{u + 1} (finiteDualizingCoeff l E n))
    X).mapDerivedCategory
  let G := (comparisonUpperStar (ModuleCat.{u + 1} (finiteDualizingCoeff l E m))
    X).mapDerivedCategory
  let S := @pbcFixedScalarExtension.{u} X.ProEt inferInstance
    (essentiallySmallSelf.{0, u, u + 1} _) (Scheme.ProEt.topology X)
    (finiteDualizingCoeff l E n) (finiteDualizingCoeff l E m)
    inferInstance inferInstance (finiteDualizingQuotient l E h)
  let W := finiteDualizingEtaleTerm l E D X n
  have hsource := (finiteTor_proEtale_iff l E (n + 1) (Nat.succ_pos n) X K).mp hK
  obtain ⟨K', hK', ⟨eK⟩⟩ := hsource.1
  have htK := (intrinsic_hasProEtaleTorAmplitude_iff_torAmplitudeIn A X a b hab K).mp ht
  have htF := (DerivedCategory.torAmplitudeIn _ a b).prop_of_iso eK.symm htK
  have ht' := (ProEtale.DerivedCategory.torAmplitudeIn_mapDerivedCategory_iff a b K').mp htF
  have hctf : finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) X K' :=
    (finiteTorConstructibleEtale_iff_source l E (n + 1) (Nat.succ_pos n) X K').mpr
      ⟨hK', a, b, ht'⟩
  have hte := Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.mpr ht'
  have hv := verdier_preservation_strata D l hl E (n + 1) (Nat.succ_pos n)
    X d hd a b K' hctf.1 hte
  have hi : -b - 2 * (d : ℤ) ≤ -a := by omega
  have hr := finiteHomDomain_flatModel D l hl E X h
    (-b - 2 * (d : ℤ)) (-a) hi _ hv.1 hv.2
  let : HasInvertibleExponent (finiteDualizingCoeff l E n) (Spec (.of D.k)) :=
    coefficient_invertible_exponent D l hl E (n + 1)
  have hW : Etale.DerivedCategory.isBoundedConstructible (finiteDualizingCoeff l E n) X W :=
    (boundedConstructible_iff_source (finiteDualizingCoeff l E n) X W).mpr
      (ProEtale.dualizing_boundedConstructible (finiteDualizingCoeff l E n)
        (X ↘ Spec (.of D.k)))
  have hc := finite_duality_site_comparison D l hl E (n + 1) (Nat.succ_pos n) X
  have hβ := hc.homComparison K' W hctf hW
  let N := ((Etale.derivedHom (ModuleCat.{u + 1} (finiteDualizingCoeff l E n)) X).obj
    (op K')).obj W
  let eN : F.obj N ≅
      ((finiteVerdierProEtaleHomAt (finiteDualizingCoeff l E n) X).obj (op K)).obj
        (F.obj W) :=
    (asIso (siteComparisonEvaluationHom
      (ModuleCat.{u + 1} (finiteDualizingCoeff l E n)) X K' W)) ≪≫
      ((finiteVerdierProEtaleHomAt (finiteDualizingCoeff l E n) X).mapIso
        eK.symm.op).app (F.obj W)
  let eS : G.obj ((Etale.scalarExtension (finiteDualizingQuotient l E h) X).obj N) ≅
      S.obj (((finiteVerdierProEtaleHomAt (finiteDualizingCoeff l E n) X).obj
        (op K)).obj (F.obj W)) :=
    (pbcComparisonReduction.{u} X (finiteDualizingQuotient l E h)).symm.app N ≪≫ S.mapIso eN
  have htred := Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.mp hr.2.2.2
  have htG := ProEtale.DerivedCategory.torAmplitudeIn_mapDerivedCategory
    (finiteDualizingCoeff l E m) htred
  apply (intrinsic_hasProEtaleTorAmplitude_iff_torAmplitudeIn B X
    (-b - 2 * (d : ℤ)) (-a) hi _).mpr
  exact (DerivedCategory.torAmplitudeIn _ _ _).prop_of_iso eS htG

end WeilConjectures
