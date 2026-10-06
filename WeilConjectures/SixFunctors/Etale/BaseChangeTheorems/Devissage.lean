/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Abelian.PrimeFactorDevissage
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.TorsionSheaf
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Coefficients
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Injectivity

/-!
# Coefficient dévissage for the exchange morphism

For a cartesian square

```
Y --e--> T
|        |
h        g
v        v
X --p--> S
```

the degree-`q` exchange maps `p⁻¹ Rᵠg_* F ⟶ Rᵠh_* e⁻¹ F`
(`AlgebraicGeometry.Etale.baseChangeHomologyMap`) form a morphism between the long exact
sequences attached to a short exact sequence of coefficient sheaves. By the five lemma, the
class of sheaves at which they are isomorphisms in every degree is stable under extensions.
Consequently, if they are isomorphisms at every sheaf killed by a prime, then also at every
sheaf killed by a positive integer (by induction on the number of prime factors), and, for
`g` quasi-compact and quasi-separated, at every torsion sheaf (as a filtered colimit of such
sheaves).

## Main statements

- `AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_X₂_of_shortExact`: the five-lemma
  transfer.
- `AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_nsmul_id_eq_zero`: the prime-factor
  induction.
- `AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_isTorsionSheaf`: the prime-torsion
  dévissage.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme Etale

variable (Λ : Type (u + 1)) [CommRing Λ] {X S T Y : Scheme.{u}} {p : X ⟶ S} {g : T ⟶ S}
  {e : Y ⟶ T} {h : Y ⟶ X}

/-- The functor induced on bounded below derived categories by the pullback is additive: it is
a lift of the additive functor `Plus.ι ⋙ D(p^*)` through the fully faithful inclusion. -/
instance (p : X ⟶ S) : ((p)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.Additive :=
  have : (((p)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus ⋙ DerivedCategory.Plus.ι).Additive :=
    Functor.additive_of_iso
      ((p)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusCompatibility.symm
  Functor.additive_of_comp_faithful _ DerivedCategory.Plus.ι

instance (p : X ⟶ S) (g : T ⟶ S) (q : ℤ) : (Etale.baseChangeSourceFunctor Λ p g q).Additive := by
  dsimp only [Etale.baseChangeSourceFunctor]
  infer_instance

instance (e : Y ⟶ T) (h : Y ⟶ X) (q : ℤ) : (Etale.baseChangeTargetFunctor Λ e h q).Additive := by
  dsimp only [Etale.baseChangeTargetFunctor]
  infer_instance

/-- The source `F ↦ p⁻¹ Rᵠg_* F` of the exchange map is exact in the middle on short exact
sequences: it is the composite of the triangulated functors `F ↦ F[0]` (on short exact
sequences), `Rg_*`, `p^*` with the homological functor `Hᵠ`. -/
theorem Etale.exact_baseChangeSourceFunctor_map_of_shortExact (p : X ⟶ S) (g : T ⟶ S) (q : ℤ)
    {E : ShortComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))} (hE : E.ShortExact) :
    (E.map (Etale.baseChangeSourceFunctor Λ p g q)).Exact :=
  sorry

/-- The target `F ↦ Rᵠh_* e⁻¹ F` of the exchange map is exact in the middle on short exact
sequences: it is the composite of the triangulated functors `F ↦ F[0]` (on short exact
sequences), `e^*`, `Rh_*` with the homological functor `Hᵠ`. -/
theorem Etale.exact_baseChangeTargetFunctor_map_of_shortExact (e : Y ⟶ T) (h : Y ⟶ X) (q : ℤ)
    {E : ShortComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))} (hE : E.ShortExact) :
    (E.map (Etale.baseChangeTargetFunctor Λ e h q)).Exact :=
  sorry

/-- **Five-lemma transfer for the exchange morphism**: for a short exact sequence
`0 ⟶ F₁ ⟶ F ⟶ F₂ ⟶ 0` of sheaves of `Λ`-modules, if the exchange maps are isomorphisms at `F₁`
and at `F₂` in every degree, then they are isomorphisms at `F` in every degree. The exchange
maps form a morphism between the two long exact sequences
(`AlgebraicGeometry.Etale.exists_connecting_baseChangeHomologyMap`), and in each degree the
five lemma applies to the five adjacent terms.
(blueprint: `lemma-weil-pbc-five-lemma-transfer`) -/
theorem Etale.isIso_baseChangeHomologyMap_X₂_of_shortExact (sq : IsPullback e h g p)
    {E : ShortComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))} (hE : E.ShortExact)
    (h₁ : ∀ q, IsIso (Etale.baseChangeHomologyMap Λ sq q E.X₁))
    (h₃ : ∀ q, IsIso (Etale.baseChangeHomologyMap Λ sq q E.X₃)) (q : ℤ) :
    IsIso (Etale.baseChangeHomologyMap Λ sq q E.X₂) :=
  sorry

/-- **Prime-factor induction for the exchange morphism**: if the exchange maps are
isomorphisms in every degree at every sheaf killed by a prime, then they are isomorphisms in
every degree at every sheaf killed by a positive integer `n`. Induct on the number of prime
factors of `n` using `0 ⟶ F[ℓ] ⟶ F ⟶ ℓF ⟶ 0` for a prime `ℓ ∣ n`
(`CategoryTheory.ObjectProperty.prop_of_nsmul_id_eq_zero`) and the five-lemma transfer
`AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_X₂_of_shortExact`.
(blueprint: `lemma-weil-pbc-prime-factor-induction`) -/
theorem Etale.isIso_baseChangeHomologyMap_of_nsmul_id_eq_zero (sq : IsPullback e h g p)
    (hprime : ∀ r : ℕ, r.Prime → ∀ E : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ),
      r • 𝟙 E = 0 → ∀ q, IsIso (Etale.baseChangeHomologyMap Λ sq q E))
    {n : ℕ} (hn : 0 < n) (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : n • 𝟙 F = 0) (q : ℤ) :
    IsIso (Etale.baseChangeHomologyMap Λ sq q F) :=
  sorry

/-- **Prime-torsion dévissage for the exchange morphism**: let `g` be quasi-compact and
quasi-separated. If the exchange maps are isomorphisms in every degree at every sheaf killed by
a prime, then they are isomorphisms at every torsion sheaf `F`. By the prime-factor induction
`AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_nsmul_id_eq_zero` they are
isomorphisms at the sheaves `F[n]` killed by a positive integer; `F` is their filtered colimit
(`AlgebraicGeometry.Scheme.IsTorsionSheaf.exists_isColimit`), and the source and the target of
the exchange map commute with filtered colimits
(`AlgebraicGeometry.Etale.preservesColimitsOfShape_higherDirectImage`).
(blueprint: `lemma-weil-pbc-prime-torsion-devissage`) -/
theorem Etale.isIso_baseChangeHomologyMap_of_isTorsionSheaf (sq : IsPullback e h g p)
    [QuasiCompact g] [QuasiSeparated g]
    (hprime : ∀ r : ℕ, r.Prime → ∀ E : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ),
      r • 𝟙 E = 0 → ∀ q, IsIso (Etale.baseChangeHomologyMap Λ sq q E))
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsTorsionSheaf F] (q : ℤ) :
    IsIso (Etale.baseChangeHomologyMap Λ sq q F) :=
  sorry

end AlgebraicGeometry
