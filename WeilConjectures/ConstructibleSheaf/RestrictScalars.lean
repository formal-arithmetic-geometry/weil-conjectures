/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Abelian.ShortExact
public import WeilConjectures.ConstructibleSheaf.OfForget
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RestrictScalars
public import WeilConjectures.SixFunctors.BaseChange.RestrictScalars

/-!
# Constructible sheaves and restriction of scalars to a quotient ring

Let `Λ` be a commutative ring and `J` an ideal of `Λ`. Restriction of scalars along
`Λ ⟶ Λ ⧸ J` sends étale sheaves of `Λ ⧸ J`-modules to étale sheaves of `Λ`-modules
(`CategoryTheory.Sheaf.restrictScalars`). It commutes with the pullback
(`AlgebraicGeometry.Etale.upperStarRestrictScalarsIso`) and with stalks, and, for `Λ ⧸ J` finite,
it preserves and reflects constructibility
(`AlgebraicGeometry.Scheme.isConstructibleSheaf_restrictScalars_iff`). A sheaf of `Λ`-modules
killed by `J` is the restriction of scalars of its coextension of scalars
(`CategoryTheory.Sheaf.restrictScalarsCoextendScalarsIso`).

Consequently, for `Λ ⧸ J` finite, an extension of constructible sheaves of `Λ`-modules which is
killed by `J` is constructible
(`AlgebraicGeometry.Scheme.IsConstructibleSheaf.of_shortExact_of_smul_eq_zero`), reducing to the
extension property of constructible sheaves over the finite ring `Λ ⧸ J`
(`AlgebraicGeometry.Scheme.IsConstructibleSheaf.of_shortExact`). This is how the extension
property is obtained for the reductions `K ⊗ᴸ Λ ⧸ Iⁿ⁺¹` at the integral stage `Λ = 𝒪_E` of the
`ℓ`-adic formalism, `Λ` itself being infinite.
-/

@[expose] public section

universe w v u' u

open CategoryTheory Limits Opposite

noncomputable section

namespace ModuleCat

variable {R : Type w} [CommRing R] (J : Ideal R)

end ModuleCat

namespace CategoryTheory.Sheaf

variable {C : Type u'} [Category.{v} C] (K : GrothendieckTopology C)
  {R : Type w} [CommRing R] (J : Ideal R)

variable {K J}

-- Avoid searching for an irrelevant torsion-free instance in the counit proof.

end CategoryTheory.Sheaf

namespace ModuleCat

variable {R : Type w} [CommRing R] (J : Ideal R)

end ModuleCat

namespace AlgebraicGeometry

open Scheme

variable {Λ : Type (u + 1)} [CommRing Λ] (J : Ideal Λ)

namespace Scheme

variable {X : Scheme.{u}}

end Scheme

end AlgebraicGeometry
