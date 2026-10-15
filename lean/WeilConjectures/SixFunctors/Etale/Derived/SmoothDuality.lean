/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.SixFunctors.Etale.Derived.Dualizing

/-!
# Smooth cohomological duality without a chosen orientation

For a smooth separated morphism `f : X ⟶ Y` of pure relative dimension `d` admitting a
compactification, and a finite coefficient ring `Λ` whose exponent is invertible on `Y`, the
relative dualizing complex `ω_f = Rf^! Λ_Y` is a locally constant sheaf of free rank-one
`Λ`-modules placed in degree `-2d`, and `Rf^! K ≅ Lf^* K ⊗ᴸ ω_f` for every `K`. No orientation,
that is no identification of `ω_f` with the Tate twist `Λ(d)[2d]`, is involved.

## Main statements

- `AlgebraicGeometry.Etale.exists_dualizingComplex_iso_and_tensor`
  (`thm-asd-smooth-tensor`).

## Implementation notes

The blueprint states `thm-asd-smooth-tensor` for a Noetherian base; its proof, through the
étale local normal form `fu = p_d e` of a smooth morphism and the adjunctions for étale
morphisms and for the affine-space projections, does not use it, and the statement here is made
for an arbitrary base, as everywhere in `WeilConjectures.SixFunctors.Etale.Derived`. The
canonical tensor morphism `Lf^* K ⊗ᴸ ω_f ⟶ Rf^! K`, the mate of the projection formula, is not
available in the library, so only the existence of an isomorphism is recorded.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {X Y : Scheme.{u}} [HasInvertibleExponent Λ Y]
  (f : X ⟶ Y) [HasCompactification f] (d : ℕ) [SmoothOfRelativeDimension d f]

include d in
/-- Blueprint `thm-asd-smooth-tensor`: Smooth cohomological duality without a chosen
orientation.

Let `f : X ⟶ Y` be smooth, separated, compactifiable and of pure relative dimension `d`, let `Λ`
be a finite ring whose exponent is invertible on `Y`, and put `ω_f = Rf^! Λ_Y`. Then `ω_f[-2d]` is
a locally constant sheaf `L` of free rank-one `Λ`-modules: `L` is locally constant, every stalk
of `L` at a geometric point is free of rank one, and `ω_f ≅ L[2d]`. For every complex `K` on `Y`,
`Lf^* K ⊗ᴸ ω_f ≅ Rf^! K`. -/
theorem exists_dualizingComplex_iso_and_tensor :
    ∃ L : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ), IsLocallyConstantSheaf L ∧
      (∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X),
        Nonempty ((pointSmallEtale s).sheafFiber.obj L ≅ ModuleCat.of Λ Λ)) ∧
      Nonempty (dualizingComplex (ModuleCat.{u + 1} Λ) f ≅
        ((_root_.DerivedCategory.singleFunctor _ 0).obj L)⟦(2 * d : ℤ)⟧) ∧
      ∀ K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
        Nonempty (((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K)).obj
            (dualizingComplex _ f) ≅
          (R(f)^![ModuleCat.{u + 1} Λ]).obj K) :=
  sorry

end Etale

end AlgebraicGeometry
