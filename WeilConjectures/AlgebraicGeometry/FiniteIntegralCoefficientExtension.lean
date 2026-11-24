/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.NumberTheory.Padics.IntegersFinite
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapCondensedRingMap
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientsFiniteFree
import all WeilConjectures.CategoryTheory.ModuleObjects.ProEtaleCoefficients.FiniteFreeScalarCoordinates
import WeilConjectures.NumberTheory.Padics.LocalFieldIntegralBasis
import WeilConjectures.CategoryTheory.SheafTensor
import WeilConjectures.CategoryTheory.ModuleObjects.Abelian
import WeilConjectures.CategoryTheory.Monoidal.Mod.Limits

/-!
# Exactness and countable products for integral coefficient extension

The coefficient rings are the native pulled-back condensed rings of integers.
The map in the product clause is the canonical map induced by the projections.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

/-- Integral coefficient extension is additive, preserves short exact sequences,
and its canonical countable-product comparison is invertible. -/
theorem finiteIntegralCoefficientExtension_exact_products
    (ℓ : ℕ) [Fact ℓ.Prime] (E F : PadicAlgCl.FiniteIntermediateField ℓ)
    (h : E ≤ F) (T : Scheme.{u}) :
    (Mod.extendScalars (coefficientMap (finiteCoefficientIntegersPointMap ℓ h) T)).Additive ∧
      (∀ K : ShortComplex
          (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
            (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) T)),
        K.ShortExact →
          (K.map (Mod.extendScalars
            (coefficientMap (finiteCoefficientIntegersPointMap ℓ h) T))).ShortExact) ∧
      (∀ M : ℕ → Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
          (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) T),
        IsIso (piComparison
          (Mod.extendScalars (coefficientMap (finiteCoefficientIntegersPointMap ℓ h) T)) M)) := by
  let φ := coefficientMap (finiteCoefficientIntegersPointMap ℓ h) T
  let S := condensedRingObj (Profinite.padicIntegersRingObj ℓ F.1) T
  let R := condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) T
  obtain ⟨b⟩ := (cartesianCoefficients_finiteFree.{u} ℓ h).1
  obtain ⟨e₀, _⟩ := (cartesianCoefficients_finiteFree.{u} ℓ h).2.1 b
  have hlim : PreservesFiniteLimits (Mod.extendScalars φ) :=
    ((cartesianCoefficients_finiteFree.{u} ℓ h).2.2 T).1
  have hcolim : PreservesFiniteColimits (Mod.extendScalars φ) :=
    (Mod.extendRestrictAdjunction φ).leftAdjoint_preservesColimits.preservesFiniteColimits.{0, 0}
  have hadd : (Mod.extendScalars φ).Additive :=
    Functor.additive_of_preserves_binary_products _
  refine ⟨hadd, fun K hK ↦ hK.map_of_exact _, fun M ↦ ?_⟩
  let α : Mod.extendScalars φ ⋙ Mod.comap φ ≅
      Functor.const (Discrete (Fin (finiteCoefficientDegree ℓ h))) ⋙ lim :=
    NatIso.ofComponents (Mod.finiteCoordinateIso (e₀ T))
      (fun f ↦ Mod.finiteCoordinateIso_naturality (e₀ T) f)
  have : PreservesLimitsOfShape (Discrete ℕ) (Mod.extendScalars φ ⋙ Mod.comap φ) :=
    preservesLimitsOfShape_of_natIso α.symm
  have : PreservesLimitsOfShape (Discrete ℕ) (Mod.extendScalars φ ⋙ Mod.forget S) :=
    inferInstanceAs (PreservesLimitsOfShape (Discrete ℕ)
      ((Mod.extendScalars φ ⋙ Mod.comap φ) ⋙ Mod.forget R))
  have : PreservesLimitsOfShape (Discrete ℕ) (Mod.extendScalars φ) :=
    preservesLimitsOfShape_of_reflects_of_preserves _ (Mod.forget S)
  infer_instance

end AlgebraicGeometry.ProEtale
