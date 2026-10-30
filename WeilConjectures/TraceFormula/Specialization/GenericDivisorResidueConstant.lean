/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.SmoothUniformizer
public import WeilConjectures.TraceFormula.Specialization.GenericDivisorGenericPoint
public import WeilConjectures.TraceFormula.Specialization.ResidueConstantCase

/-!

# The constant case of generic vanishing along a divisor, with coefficients `𝔽_E`

Let `X` be normal of finite type over `k`, `Z = V(h)` a principal divisor, `j : X ∖ Z ⟶ X` and `ζ`
a generic point of `Z`. Then `Le^* Ψ_X(j_! 𝔽_E)` vanishes near `ζ`
(`ProEtale.CondensedRing.nearbyCyclesVanishNear_lowerShriek_unit_residueField`, blueprint
`det-sp-generic-divisor-constant`).

Over a perfect field `k`, the local ring `𝒪_{X,ζ}` is a discrete valuation ring, so `X` is
smooth at `ζ` and some uniformizer defines a smooth morphism to `𝔸¹_k` near `ζ`
(`exists_smooth_polyAffine_irreducible_germ`); the constant case with such a chart is
`nearbyCyclesVanishNear_lowerShriek_unit_residueField_of_uniformizer`.

## Unfinished

The case of an imperfect field `k`,
`ProEtale.CondensedRing.nearbyCyclesVanishNear_lowerShriek_unit_residueField_of_not_perfectField`,
is `sorry`ed: there `X` need not be smooth at `ζ` (for instance `X = 𝔸¹_{k(a^{1/p})}`), and the
blueprint assumes `k` algebraically closed. See its docstring for the planned route.

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] (k' : Type u) [Field k'] [Algebra k k'] [IsSepClosed k']
  [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

omit [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] in
/-- **The constant case over a perfect field** (blueprint `det-sp-generic-divisor-constant`, `k`
perfect): the local ring at a generic point `ζ` of the divisor `V(h)` of the normal scheme `X`
is a discrete valuation ring, so a uniformizer near `ζ` is a smooth morphism to `𝔸¹_k`
(`exists_smooth_polyAffine_irreducible_germ`), and the constant case with a smooth uniformizer
applies. -/
theorem nearbyCyclesVanishNear_lowerShriek_unit_residueField_of_perfectField [PerfectField k]
    (hX : IsNormalScheme X.left) {h : Γ(X.left, ⊤)} (hh : h ≠ 0) {I : X.left.IdealSheafData}
    (hI : I = IdealSheafData.ofIdealTop (Ideal.span {h}))
    (ζ : (centre X I).left) (hζ : closure {ζ} ∈ irreducibleComponents (centre X I).left)
    (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    nearbyCyclesVanishNear X I k' (Profinite.continuousMapRingObj (integersResidueField ℓ E.1)) ζ
      ((D(((overRestrictι X I.support.compl).left)_!open⟦
          Profinite.continuousMapRingObj (integersResidueField ℓ E.1)⟧)).obj (𝟙_ _)) := by
  have := hX.1
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have := (hX.2 (I.subschemeι ζ)).1
  have := (hX.2 (I.subschemeι ζ)).2
  have : IsDiscreteValuationRing (X.left.presheaf.stalk (I.subschemeι ζ)) :=
    IsDiscreteValuationRing.of_maximalIdeal_mem_minimalPrimes_span_singleton
      ((map_ne_zero_iff _ (germ_injective_of_isIntegral X.left (U := ⊤) _ trivial)).2 hh)
      (maximalIdeal_stalk_mem_minimalPrimes (subschemeι_mem_zeroLocus hI ζ)
        (eq_of_specializes_subschemeι hI ζ hζ))
  obtain ⟨W₀, hW₀, f₀, hsm, hf₀⟩ := exists_smooth_polyAffine_irreducible_germ X (I.subschemeι ζ)
  have := hsm
  exact nearbyCyclesVanishNear_lowerShriek_unit_residueField_of_uniformizer k' hX hh hI ζ hζ E W₀
    hW₀ f₀ hf₀

/-- **The constant case over an imperfect field** (blueprint `det-sp-generic-divisor-constant`,
which assumes `k` algebraically closed). Unfinished.

Planned route, with `q = pⁿ`:
1. the power map `D_{(h)} X ⟶ D_{(h^q)} X` over `t ↦ t^q` is a universal homeomorphism of
   models, so `Le^* Ψ` for `(h)` vanishes near `ζ` once it does for `(h^q)`;
2. the relative Frobenius `X ⟶ X^{(q)}` factors through a finite universal homeomorphism
   `g : X ⟶ Y` onto the normalization `Y` of `(X^{(q)})_red`, with `h^q = g^* h_Y` and
   `Rg_* j_! Λ = j_! Λ`; vanishing near `g(ζ)` on `Y` gives vanishing near `ζ` on `X`, finite
   pushforward being conservative;
3. for `n ≫ 0`, `Y` is smooth over `k` at `g(ζ)`: its residue field there becomes separable over
   `k` (MacLane), so the case with a smooth uniformizer applies.
Step 3, the descent of smoothness from `k^{perf}` to a finite level, is the missing input. -/
theorem nearbyCyclesVanishNear_lowerShriek_unit_residueField_of_not_perfectField
    (hk : ¬ PerfectField k)
    (hX : IsNormalScheme X.left) {h : Γ(X.left, ⊤)} (hh : h ≠ 0) {I : X.left.IdealSheafData}
    (hI : I = IdealSheafData.ofIdealTop (Ideal.span {h}))
    (ζ : (centre X I).left) (hζ : closure {ζ} ∈ irreducibleComponents (centre X I).left)
    (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    nearbyCyclesVanishNear X I k' (Profinite.continuousMapRingObj (integersResidueField ℓ E.1)) ζ
      ((D(((overRestrictι X I.support.compl).left)_!open⟦
          Profinite.continuousMapRingObj (integersResidueField ℓ E.1)⟧)).obj (𝟙_ _)) :=
  sorry

/-- **The constant case of generic vanishing along a divisor, with coefficients `𝔽_E`** (blueprint
`det-sp-generic-divisor-constant`): `Le^* Ψ_X(j_! 𝔽_E)` vanishes near a generic point `ζ` of the
divisor `V(h)` of a normal scheme `X`. -/
theorem nearbyCyclesVanishNear_lowerShriek_unit_residueField
    (hX : IsNormalScheme X.left) {h : Γ(X.left, ⊤)} (hh : h ≠ 0) {I : X.left.IdealSheafData}
    (hI : I = IdealSheafData.ofIdealTop (Ideal.span {h}))
    (ζ : (centre X I).left) (hζ : closure {ζ} ∈ irreducibleComponents (centre X I).left)
    (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    nearbyCyclesVanishNear X I k' (Profinite.continuousMapRingObj (integersResidueField ℓ E.1)) ζ
      ((D(((overRestrictι X I.support.compl).left)_!open⟦
          Profinite.continuousMapRingObj (integersResidueField ℓ E.1)⟧)).obj (𝟙_ _)) := by
  by_cases hk : PerfectField k
  · exact nearbyCyclesVanishNear_lowerShriek_unit_residueField_of_perfectField k' hX hh hI ζ hζ E
  · exact nearbyCyclesVanishNear_lowerShriek_unit_residueField_of_not_perfectField k' hk hX hh hI
      ζ hζ E

end AlgebraicGeometry.ProEtale.CondensedRing
