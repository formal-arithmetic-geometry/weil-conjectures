/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SecSmoothPurity.FiniteNativeTensorComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Braided
public import WeilConjectures.SixFunctors.Etale.Derived.VerdierBiduality
import WeilConjectures.AlgebraicGeometry.FiniteCondensedCtfEquivalence
import WeilConjectures.AlgebraicGeometry.DetThmSfCtfStabilityInternalHom
import WeilConjectures.SixFunctorsBasics.FiniteCoefficientSmallCarrierComparison
import WeilConjectures.AlgebraicGeometry.FiniteCohomologicalDimensionHypothesis

/-! # Constructible internal Homs of finite realizations

Source: latest blueprint, `det-pd-biduality-coefficients.proof.md`, paragraph (i).
The existing relative derived internal Hom retains actual constructibility and finite Tor amplitude.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] WeilConjectures.scalarReductionSiteSmall
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary

/-- Actual internal Hom of two finite-Tor constructible finite realizations remains
bounded constructible with finite Tor amplitude.

Source: latest blueprint, `det-pd-biduality-coefficients.proof.md`, paragraph (i),
internal-Hom compatibility and constructible restriction
(blueprint: lem-sf-finite-condensed-realization-hom-domain).

Proof:
1. Finite constructible descent and comparison of all degree-zero Tor test modules put
   both realized arguments in the actual constant-model constructible finite-Tor domain.
2. The finite ring A is killed by an ell-power. Replace it by an isomorphic finite ring
   in the coefficient universe used in IsLocalizingAdmissibleCoefficient. The induced
   constant condensed ring isomorphism identifies coefficient A with that admissible ring;
   this is the finite-coefficient alternative of admissibility, with no field hypothesis
   on A. Scalar transport preserves the relative tensor, actual internal Hom, constant
   local models, and the Tor tests.
3. Algebraic closedness gives ell-cohomological dimension zero for k and every finitely
   generated extension has finite ell-cohomological dimension. Apply actual-module
   internalHom_stability to the separated finite-type scheme T and the two arguments.
   Transport back along the scalar isomorphism. Its first conclusion is exactly the
   stated conjunction. This uses the existing actual Hom, not one defined by encoding;
   the empty scheme and the zero coefficient ring are included. -/
theorem finiteCondensedRealizationHomDomain
    (p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime] (hpℓ : p ≠ ℓ)
    (k : Type u) [Field k] [IsAlgClosed k] [CharP k p]
    (A : Type u) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A] [IsTopologicalRing A]
    [HasInvertibleExponent (ULift.{u + 1} A) (Spec (.of k))]
    (hA : ∃ m : ℕ, ((ℓ ^ m : ℕ) : A) = 0)
    (enc : ∀ X : Scheme.{u}, Encoding A X)
    (T : Scheme.{u}) (a : T ⟶ Spec (.of k))
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a] :
    let F := internalEtaleRealization A T (enc T)
    ∀ K W : Etale.DerivedCategoryModule (ULift.{u + 1} A) T,
      (Etale.DerivedCategory.isBoundedConstructible (ULift.{u + 1} A) T K ∧
        _root_.DerivedCategory.finiteTorAmplitude _ K) →
      (Etale.DerivedCategory.isBoundedConstructible (ULift.{u + 1} A) T W ∧
        _root_.DerivedCategory.finiteTorAmplitude _ W) →
      constantModelBoundedConstructible (coefficient A) T
          ((ihom (F.obj K)).obj (F.obj W)) ∧
        _root_.DerivedCategory.finiteTorAmplitude _ ((ihom (F.obj K)).obj (F.obj W)) := by
  dsimp only
  let F := internalEtaleRealization A T (enc T)
  let P := Etale.DerivedCategory.isBoundedConstructible (ULift.{u + 1} A) T ⊓
    _root_.DerivedCategory.finiteTorAmplitude _
  let Q := constantModelBoundedConstructible (coefficient A) T ⊓
    _root_.DerivedCategory.finiteTorAmplitude _
  obtain ⟨hF, -⟩ := finiteCondensedCtfEquivalence p ℓ hpℓ k A enc T a
  obtain ⟨A₀, hring, hfin, ⟨r⟩⟩ :=
    CondensedRing.finiteCoefficientSmallCarrierComparison.1 A
  let : CommRing A₀ := hring
  let : Finite A₀ := hfin
  let : TopologicalSpace A₀ := ⊥
  let : DiscreteTopology A₀ := discreteTopology_bot A₀
  have hkill : ∃ m : ℕ, ∀ x : A₀, (ℓ ^ m) • x = 0 := by
    obtain ⟨m, hm⟩ := hA
    refine ⟨m, fun x ↦ ?_⟩
    have hzero : ((ℓ ^ m : ℕ) : A₀) = 0 := by
      simpa only [map_natCast, map_zero] using congrArg r hm
    rw [nsmul_eq_mul, hzero, zero_mul]
  have hΛ : IsLocalizingAdmissibleCoefficient ℓ (coefficient A) := by
    left
    refine ⟨A₀, hring, inferInstance, inferInstance, inferInstance, hfin, hkill, ?_⟩
    have hbot : (inferInstance : TopologicalSpace A) = ⊥ := DiscreteTopology.eq_bot
    cases hbot
    exact ⟨(CommMon.forget₂Mon _).mapIso
      (CondensedRing.finiteCoefficientCarrierIso A A₀ r)⟩
  let : Fact (ringChar k).Prime := ⟨by simpa only [ringChar.eq k p] using
    (Fact.out : p.Prime)⟩
  let : Fact (ringChar k ≠ ℓ) := ⟨by simpa only [ringChar.eq k p] using hpℓ⟩
  let : T.Over (Spec (.of k)) := ⟨a⟩
  let : LocallyOfFiniteType (T ↘ Spec (.of k)) := inferInstanceAs (LocallyOfFiniteType a)
  let : QuasiCompact (T ↘ Spec (.of k)) := inferInstanceAs (QuasiCompact a)
  let : IsSeparated (T ↘ Spec (.of k)) := inferInstanceAs (IsSeparated a)
  intro K W hK hW
  exact (CondensedRing.internalHom_stability (coefficient A) ℓ k
    (BaseFieldFiniteCD.of_isAlgClosed ℓ k) hΛ (F.obj K) (F.obj W)
      (hF ⟨K, hK⟩) (hF ⟨W, hW⟩)).1

end AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary
