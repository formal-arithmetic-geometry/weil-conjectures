/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SmoothPurity.Defs
public import WeilConjectures.TraceFormula.PurityTensorMap

/-!

# Compatibility of the smooth orientation with base change

Let `f : X ⟶ Y` be smooth of pure relative dimension `d` and consider a cartesian square
```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```
of separated `k`-schemes of finite type. The orientation `γ_f : ℚ̄_ℓ,X(d)[2d] ⟶ Rf^! ℚ̄_ℓ,Y`
(`AlgebraicGeometry.ProEtale.CondensedRing.smoothOrientation`) is compatible with base change:
pulled back along `g'` and followed by the exceptional base change map
`Lg'^* Rf^! ℚ̄_ℓ,Y ⟶ Rf'^! Lg^* ℚ̄_ℓ,Y ≅ Rf'^! ℚ̄_ℓ,Y'`
(`AlgebraicGeometry.ProEtale.CondensedRing.upperShriekBaseChange`), it is the orientation of
`f'`, up to an isomorphism `Lg'^* ℚ̄_ℓ,X(d)[2d] ≅ ℚ̄_ℓ,X'(d)[2d]` of the Tate twists.

This is a property of the sorried definition `smoothOrientation` of
`WeilConjectures.SmoothPurity.Defs`: the compatibility of smooth purity with base change
(blueprint `sk-prop-sp-purity-bc`, `u^*γ_f(K) = γ_{f'}(v^*K)`) at the unit `K = ℚ̄_ℓ,Y`, owed by
the smooth purity section. It is stated here, `sorry`ed, as
`AlgebraicGeometry.ProEtale.CondensedRing.smoothOrientation_baseChange`; the base change
compatibilities of the smooth trace and of the purity map are derived from it.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Functor.OplaxMonoidal

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

variable {X Y X' Y' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- Blueprint `sk-prop-sp-purity-bc` at the unit (owed by the smooth purity section,
`sec-smooth-purity`): **the orientation is compatible with base change**. For a
cartesian square with `f` (hence `f'`) smooth of pure relative dimension `d`, the pullback of the
orientation `γ_f : ℚ̄_ℓ,X(d)[2d] ⟶ Rf^! ℚ̄_ℓ,Y`, followed by the exceptional base change map at the
unit and `Rf'^! Lg^* ℚ̄_ℓ,Y ≅ Rf'^! ℚ̄_ℓ,Y'`, is the orientation `γ_{f'}` up to an isomorphism
`Lg'^* ℚ̄_ℓ,X(d)[2d] ≅ ℚ̄_ℓ,X'(d)[2d]` of the Tate twists:
```
Lg'^* ℚ̄_ℓ,X(d)[2d] --Lg'^* γ_f--> Lg'^* Rf^! ℚ̄_ℓ,Y ⟶ Rf'^! Lg^* ℚ̄_ℓ,Y ≅ Rf'^! ℚ̄_ℓ,Y'.
```
This is a property of the sorried definition `smoothOrientation`. -/
theorem smoothOrientation_baseChange (sq : IsPullback g' f' f g) (d : ℕ)
    [SmoothOfRelativeDimension d f.left] [SmoothOfRelativeDimension d f'.left] :
    ∃ τ : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g').obj
        (boundedConstructibleTateTwist ℓ X d (2 * d)) ≅
          boundedConstructibleTateTwist ℓ X' d (2 * d),
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g').map
          (smoothOrientation ℓ f d) ≫ upperShriekBaseChange ℓ sq (𝟙_ _) ≫
          (boundedConstructibleUpperShriek ℓ f').map
            (η (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g)) =
        τ.hom ≫ smoothOrientation ℓ f' d :=
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
