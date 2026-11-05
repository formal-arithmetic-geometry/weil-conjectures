/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactConstructibleEllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarEllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriekLocalizing

import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarEllAdicFiniteness

/-!
# The exceptional inverse image on `Loc(Dᵇc)` for the `ℓ`-adic coefficient rings

For the three families of `ℓ`-adic coefficient rings, schemes separated of finite type over a
field `k` in which `ℓ` is invertible and which is finite or separably closed (so that
`cd_ℓ(k)` is finite; without this, the compact generation fails, e.g. for `k = ℝ`), the two
inputs of the existence theorem
`AlgebraicGeometry.ProEtale.CondensedRing.exists_rightAdjoint_rightDerivedLowerShriekLocalizing`
(`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriekLocalizing`) are the
theorems

| `Λ` | `sk-lem-brown-hypotheses` | `det-sf-comp-coherence-single` |
| --- | --- | --- |
| `E` | `compactlyGenerates_continuousMapRingObj` | `lowerShriek_continuousMapRingObj` |
| `𝒪_E` | `compactlyGenerates_padicIntegersRingObj` | `lowerShriek_padicIntegersRingObj` |
| `ℚ̄_ℓ` | `compactlyGenerates_padicAlgClRingObj` | `lowerShriek_padicAlgClRingObj` |

(all in the namespace `AlgebraicGeometry.ProEtale.CondensedRing`), and the existence theorem
follows (`exists_rightAdjoint_rightDerivedLowerShriekLocalizing_continuousMapRingObj`, ...).

The statements of `det-sf-comp-coherence-single` take a separated base `Y` of finite type over
`k`, the setting of the blueprint, in which the ind-constructible heart is available. A
noetherian base is needed in any case: over a merely quasi-compact quasi-separated base, `Rp_*`
need not preserve constructibility. For instance the inclusion `p` of the origin into
`Y = Spec k[x₁, x₂, …]` is proper, but `p_* Λ` is supported on the closed point, which is not a
constructible subset of `Y`.

These theorems are separate from the formal part
(`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriekLocalizing`) since their
proofs use the reduction to residue field coefficients, which imports the formal part.

## Sorried input

- The inputs of `isCompactObj_singleLocalizingBoundedConstructible_continuousMapRingObj`,
  `isCompactObj_singleLocalizingBoundedConstructible_padicAlgClRingObj` (blueprint
  `sk-thm-constructible-compactness`) and
  `isCompactObj_singleLocalizingBoundedConstructible_padicIntegersRingObj` (blueprint
  `sk-prop-int-compactness`), that constructible sheaves are compact in `Loc(Dᵇc(X)⟦Λ⟧)`: the
  closure properties of the ind-constructible sheaves (`sk-prop-ind-heart`), the continuity of
  `Ext` out of a constructible sheaf (`sk-lem-constructible-ext-continuity`) and the uniform
  `Ext` bound (`sk-lem-uniform-constructible-ext`), see
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactConstructibleEllAdic`. The
  compactness follows by the finite-window argument and left completeness. By dévissage, all
  bounded constructible complexes are compact
  (`isCompactObj_of_isCompactObj_singleLocalizingBoundedConstructible`).
- The inputs of `properLowerStarHypotheses_continuousMapRingObj`,
  `properLowerStarHypotheses_padicAlgClRingObj` and
  `properLowerStarHypotheses_padicIntegersRingObj` (for `p` proper, `Rp_*` preserves `Dᵇc` and
  direct sums on `Loc(Dᵇc)`): that `Rp_*` preserves `Dᵇc` (blueprint
  `sk-thm-sfb-proper-base-change`) and has finite amplitude and commutes with direct sums on the
  ind-constructible heart (blueprints `sk-lem-proper-heart-bound`,
  `det-prop-int-compactness-direct-sums` (1)), see
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarEllAdic`. The
  commutation with direct sums on `Loc(Dᵇc)` follows by dévissage and left completeness
  (`ProperLowerStarHeartHypotheses.preservesColimitsOfShape`).
-/

@[expose] public section

universe u

open scoped CategoryTheory.Obj

open CategoryTheory Abelian Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-! ### The `ℓ`-adic coefficient rings -/

section EllAdic

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k ≠ ℓ)]

/-! #### The coefficient ring `E` -/

/-! #### The coefficient ring `𝒪_E` -/

/-! #### The coefficient ring `ℚ̄_ℓ` -/

variable {X Y : Scheme.{u}} (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX]
  [IsSeparated aX] (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
  [IsSeparated aY] {f : X ⟶ Y} (c : Compactification f)
  (hk : Finite k ∨ IsSepClosed k)

end EllAdic

end AlgebraicGeometry.ProEtale.CondensedRing
