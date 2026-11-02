/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleIntegralCoefficientData
public import WeilConjectures.ProEtaleCoefficients.DerivedNakayamaResolution
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm

/-!
# Integral coefficient point equality

Source: the projection-normalized integral coefficient comparison
(blueprint: det-prop-integral-criterion-reductions).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

/-- Continuous-function ring sheaves depend only on the topology.
Source: integral coefficient comparison (blueprint: det-prop-integral-criterion-reductions).
Proof: substitute the topology equality and use proof irrelevance. -/
theorem continuousRingSheaf_topology_eq (T : Type u) [Ring T]
    (t₁ t₂ : TopologicalSpace T) (h : t₁ = t₂)
    (h₁ : @IsTopologicalRing T t₁ _) (h₂ : @IsTopologicalRing T t₂ _) :
    @Profinite.continuousMapRingSheafOfUniverse.{u, u} T t₁ _ h₁ =
      @Profinite.continuousMapRingSheafOfUniverse.{u, u} T t₂ _ h₂ := by
  subst t₂
  rfl

/-- Equality of the spectral-norm and extending-absolute-value integral ring objects.
Source: integral coefficient comparison (blueprint: det-prop-integral-criterion-reductions).
Proof: both norms give the same metric and induced topology on the integer ring;
continuous-function sheaf extensionality and the forgetful functor give the equality. -/
theorem integralPointMon_eq (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :
    Mon.mk (DerivedNakayama.integerRing l E) = sfbCondensedIntegers l E := by
  have hm : (spectralNorm.normedField (Padic l) E).toPseudoMetricSpace =
      (Padic.coefficientExtensionAbsoluteValue l E).toNormedField.toPseudoMetricSpace :=
    PseudoMetricSpace.ext (by
      ext x y
      change spectralNorm (Padic l) E (x - y) = spectralNorm (Padic l) E (-x + y)
      rw [neg_add_eq_sub, ← neg_sub x y,
        spectralNorm_neg (Algebra.IsAlgebraic.isAlgebraic _)])
  have ht := congrArg (fun m : PseudoMetricSpace E ↦
    m.toUniformSpace.toTopologicalSpace) hm.symm
  have hti := congrArg (fun t : TopologicalSpace E ↦
    TopologicalSpace.induced (fun x : Padic.coefficientExtensionIntegers l E ↦ (x : E)) t) ht
  have hs := continuousRingSheaf_topology_eq
    (Padic.coefficientExtensionIntegers l E) _ _ hti
    (by let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField; infer_instance)
    (by let := spectralNorm.normedField (Padic l) E; infer_instance)
  let F : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1} →
      Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) := fun R ↦
    Mon.mk ((sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj R)
  exact congrArg F hs

end AlgebraicGeometry.ProEtale
