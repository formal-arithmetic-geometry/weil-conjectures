/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.WeilGroup
public import Sheaf.AlgebraicGeometry.PureDimension
public import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Sheaf.AlgebraicGeometry.FundamentalGroup.CompactCharacterLogarithm
import Sheaf.AlgebraicGeometry.FundamentalGroup.PadicCharactersH1
import Sheaf.CategoryTheory.Galois.AutProfinite
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Sheaf.AlgebraicGeometry.FundamentalGroup.FLCFiber
import Sheaf.NumberTheory.Padics.DeepPrincipalUnitLog
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius
import WeilConjectures.GroupTheory.WeilGroup

/-!
# Finite geometric image of a rank-one Weil character on a curve

Source: Weil conjectures blueprint, main-20261015, sec-purity-real-sheaves,
sk-p-real-rankone, theorem and proof thm-wf-rank-one-finite-geometric-image-curve
(blueprint: thm-wf-rank-one-finite-geometric-image-curve).

The geometric subgroup is the degree kernel in the recorded Weil group, as in
lem-wf-weil-group-exact-sequence and the landed compact-character logarithm statement.
Continuity uses the spectral norm, the unique extension of the adic absolute value.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory

namespace AlgebraicGeometry.Scheme.FiniteEtale

/-- A continuous character of the Weil group of a normal geometrically connected curve
has finite image on its geometric subgroup, equivalently a uniform positive exponent
annihilates all its geometric values.

Source: blueprint main-20261015, sec-purity-real-sheaves/sk-p-real-rankone,
theorem and proof thm-wf-rank-one-finite-geometric-image-curve
(blueprint: thm-wf-rank-one-finite-geometric-image-curve).

Proof plan:
1. By lem-wf-weil-group-exact-sequence choose a degree-one element. Apply
   lem-wf-compact-character-logarithm to obtain N ≥ 1 and the continuous additive
   character λ(g) = log(χ(g)^N), invariant under inverse conjugation by this element,
   with χ(g)^N in 1 + ℓ² 𝒪_E.
2. The fibre-functor description def-galois-fibre-functor and lem-galois-aut-profinite
   make the geometric subgroup compact. Choose a finite ℚ_ℓ-basis of E. Its coordinate
   maps are continuous by lem-sfb-finite-dimensional-linear-map-continuous. Compactness
   bounds their images on λ, so multiplication by one common power ℓ^a puts all the
   coordinates in ℤ_ℓ (def-weil-l-adic-numbers), retaining continuity and invariance.
3. Since ℓ does not divide q, it differs from the field characteristic. Apply
   lem-wf-additive-characters-h1 to each integral coordinate. Its compatible H¹ classes
   are Frobenius-fixed, hence zero by prop-wf-open-curve-h1-no-frobenius-fixed. The
   comparison is injective and ℓ^a is nonzero; all coordinates vanish, so λ = 0.
4. By lem-weil-l-adic-extension-integers-dvr, writing ℓ = uϖ^e gives
   ℓ² 𝒪_E = 𝔪_E^(2e). The inequality 2e > e/(ℓ-1) holds also for ℓ = 2.
   Thus lem-wf-deep-principal-unit-log makes the same logarithm series injective on
   1 + ℓ² 𝒪_E. Since its value is zero, χ(g)^N = 1 for every geometric g.
5. These values are roots of the nonzero polynomial T^N - 1 and are therefore finite.
   Conversely the exponent of a finite image gives such a positive N, with N = 1
   allowed for the trivial image. -/
theorem rankOne_finite_geometricImage_curve
    (k₀ : Type u) [Field k₀] [Finite k₀] {U₀ : Scheme.{u}}
    (p : U₀ ⟶ Spec (.of k₀)) [GeometricallyConnected p] [IsSeparated p]
    [LocallyOfFiniteType p] [QuasiCompact p]
    (hnormal : ∀ z : U₀,
      IsDomain (U₀.presheaf.stalk z) ∧ IsIntegrallyClosed (U₀.presheaf.stalk z))
    (hdim : U₀.IsPureDimension 1)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ U₀)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ¬ ℓ ∣ Nat.card k₀)
    (E : Type v) [Field E] [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]
    (χ : weilGroup p x (Aut (fiber x)) →* Eˣ)
    (hχ : @Continuous _ E inferInstance
      (spectralNorm.normedField (Padic ℓ) E).toUniformSpace.toTopologicalSpace
      (fun w ↦ (χ w : E))) :
    (Set.range (fun g : (weilGroupDeg p x (Aut (fiber x))).ker ↦ χ g.val)).Finite ∧
      ∃ N : ℕ, 1 ≤ N ∧
        ∀ g : (weilGroupDeg p x (Aut (fiber x))).ker, χ g.val ^ N = 1 := by
  sorry

end AlgebraicGeometry.Scheme.FiniteEtale
