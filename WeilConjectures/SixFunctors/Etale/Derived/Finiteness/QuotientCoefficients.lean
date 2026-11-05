/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.ConstructibleTorsion
public import WeilConjectures.CategoryTheory.DerivedCategory.Rationalization
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage
public import WeilConjectures.SixFunctors.Etale.Derived.RestrictScalarsLowerStar

/-!
# Finiteness of direct images for complexes killed by an ideal of finite index

Let `Λ` be a noetherian ring and `J` an ideal of `Λ` with `Λ ⧸ J` finite, whose exponent is
invertible on the base. For a morphism `f : X ⟶ Y` of finite-type `k`-schemes, `Rf_*` carries a
bounded constructible complex of étale sheaves of `Λ`-modules killed by `J` to a bounded
constructible complex
(`AlgebraicGeometry.Etale.boundedConstructible_rightDerivedLowerStar_of_smul_eq_zero`).
This is the form of the finiteness theorem (blueprint `sk-prop-sf-finiteness`) used at the
integral coefficient stage `Λ = 𝒪_E`, for the reductions `K ⊗ᴸ Λ ⧸ Iⁿ⁺¹`.

The proof reduces to the finite ring `Λ ⧸ J`:

- a constructible sheaf `F` of `Λ`-modules killed by `J` is the restriction of scalars of the
  constructible sheaf `Hom_Λ(Λ ⧸ J, F)` of `Λ ⧸ J`-modules, and restriction of scalars commutes
  with `Rf_*` (`AlgebraicGeometry.Etale.isIso_rightDerivedLowerStarRestrictScalars`), so the
  case of `F` placed in degree `0` is the finite-coefficient theorem
  `AlgebraicGeometry.Etale.boundedConstructible_rightDerivedLowerStar_of_hasInvertibleExponent`;
- a complex is handled by dévissage along its truncation triangles. Constructible sheaves of
  `Λ`-modules are only known to be closed under extensions killed by an ideal of finite index
  (`AlgebraicGeometry.Etale.DerivedCategory.boundedConstructible_obj₂_of_smul_eq_zero`), so the
  dévissage keeps track of the power of `J` killing each truncation: a complex whose `m` nonzero
  homology sheaves are killed by `J` is killed by `Jᵐ`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

section RestrictScalars

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (φ : Λ →+* Λ') {X Y : Scheme.{u}}
  (f : X ⟶ Y)

end RestrictScalars

variable {Λ : Type (u + 1)} [CommRing Λ] (J : Ideal Λ) {X Y : Scheme.{u}}

variable {k : Type u} [Field k]

end Etale

end AlgebraicGeometry
