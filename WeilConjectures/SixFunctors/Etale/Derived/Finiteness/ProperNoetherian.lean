/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Proper

/-!
# Proper direct images over a noetherian base

Let `Λ` be a finite ring killed by an integer invertible on a noetherian scheme `S`, and
`b : Y ⟶ S` a proper morphism. The derived direct image `Rb_*` preserves bounded constructible
complexes of étale sheaves of `Λ`-modules
(`AlgebraicGeometry.Etale.boundedConstructible_rightDerivedLowerStar_of_isProper_of_isNoetherian`,
blueprint `thm-weil-pbc-direct-image-finiteness-proper`): this is the finiteness theorem for
proper morphisms (SGA 4, Exposé XIV, Théorème 1.1) together with the vanishing of `Rᵠb_*` above
twice the dimension of the geometric fibres (Stacks, Tag 095U).

For `S` of finite type over a field this is
`AlgebraicGeometry.Etale.boundedConstructible_rightDerivedLowerStar_of_isProper`.

## Sorried input

`AlgebraicGeometry.Etale.boundedConstructible_rightDerivedLowerStar_of_isProper_of_isNoetherian`
is `sorry`ed for a general noetherian base: the constructibility of proper direct images over
such a base (SGA 4, Exposé XIV) is not formalized. The vanishing part holds over any base
(`AlgebraicGeometry.Etale.isZero_homology_rightDerivedLowerStar_of_isProper`).
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]

/-- Blueprint `thm-weil-pbc-direct-image-finiteness-proper`: for a proper morphism `b : Y ⟶ S` to
a noetherian scheme on which the exponent of the finite ring `Λ` is invertible, `Rb_*` maps
bounded constructible complexes of étale sheaves of `Λ`-modules to bounded constructible complexes
(SGA 4, Exposé XIV, Théorème 1.1; Stacks, Tag 095U). -/
theorem boundedConstructible_rightDerivedLowerStar_of_isProper_of_isNoetherian {Y S : Scheme.{u}}
    [IsNoetherian S] [HasInvertibleExponent Λ S] (b : Y ⟶ S) [IsProper b]
    {K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Y K) :
    Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) S
      ((R((b)_*[ModuleCat.{u + 1} Λ])).obj K) :=
  sorry

end Etale

end AlgebraicGeometry
