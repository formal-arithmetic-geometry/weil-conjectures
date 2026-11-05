/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.CoproductsOfHomologyProperty
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructureTriangle
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Proper
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.EtaleOriginHomology
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Stability
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleStratum
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarIntegral

/-!
# Uniform amplitude of the proper direct image of constructible `𝒪_E`-sheaves

Let `E ⊆ ℚ̄_ℓ` be a finite subextension of `ℚ_ℓ` with ring of integers `𝒪_E` and residue field
`𝔽_E`, and `p : Z ⟶ Y` a proper morphism of noetherian schemes whose geometric fibres have
dimension `≤ d`. This file proves that for every constructible `𝒪_{E,Z}`-module object `N`, the
pro-étale direct image `Rp_* N` lies in degrees `≤ 2d`
(`ProEtale.CondensedRing.isLE_rightDerivedLowerStar_singleFunctor_padicIntegers_of_isProper`,
blueprint `det-prop-int-compactness-direct-sums` (1), `det-proper-heart-bound-torsion`), given
that `Rp_*` preserves `Dᵇc(-, 𝔽_E)`.

The proof reduces to the residue field: `Rp_* N` is bounded constructible, so it suffices that its
first derived reduction lies in degrees `≤ 2d`
(`ProEtale.CondensedRing.isLE_of_isLE_derivedReduction`). This reduction is `Rp_*(N ⊗ᴸ 𝔽_E)`,
where `N ⊗ᴸ 𝔽_E` is a bounded constructible complex in degrees `≤ 0`
(`ProEtale.CondensedRing.isLE_derivedReduction_singleFunctor_obj`) of étale origin. With finite
coefficients the pro-étale direct image of such a complex is `ν^*` of the étale one
(`ProEtale.isLE_rightDerivedLowerStar_of_isProper_of_boundedConstructible`), and the étale bound
follows by dévissage from the vanishing of `Rᵠp_* F` for `q > 2d` on single sheaves
(`Etale.isLE_rightDerivedLowerStar_of_isProper`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Obj CategoryTheory.Functor ZeroObject

namespace AlgebraicGeometry

open Scheme

namespace ProEtale.CondensedRing

open PadicAlgCl

variable {ℓ : ℕ} [Fact ℓ.Prime] {E : FiniteIntermediateField ℓ}

end ProEtale.CondensedRing

end AlgebraicGeometry
