/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.AbsoluteFrobenius
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCompIsoUnit

/-!
# The absolute Frobenius and the compactly supported direct image

For a scheme `Y` of characteristic `p` whose absolute `p ^ n`-power Frobenius `F_Y` is proper,
the trivialization `L(F_Y)^* ≅ L(𝟙)^* ≅ 𝟭`
(`AlgebraicGeometry.Etale.leftDerivedUpperStarIterateFrobeniusIso`) induces a trivialization
`R(F_Y)_! ≅ R(F_Y)_* ≅ 𝟭` (`AlgebraicGeometry.Etale.rightDerivedLowerShriekIterateFrobeniusIso`).
These trivializations are compatible with the compactly supported direct image: for
`f : X ⟶ Y`, the two isomorphisms `R(F_X ≫ f)_! = R(f ≫ F_Y)_! ≅ Rf_!` obtained from the
composition isomorphisms and the trivializations of `R(F_X)_!` and `R(F_Y)_!` agree
(`AlgebraicGeometry.Etale.rightDerivedLowerShriekCompIso_iterateFrobenius`).
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ] {p : ℕ} (hp : p.Prime) (n : ℕ)

/-- The trivialization `L(F_Y)^* ≅ 𝟭` of the derived pullback along the absolute `p ^ n`-power
Frobenius: `AlgebraicGeometry.Etale.leftDerivedUpperStarIterateFrobeniusIso` followed by
`L(𝟙)^* ≅ 𝟭`. -/
noncomputable abbrev leftDerivedUpperStarIterateFrobeniusTriv {Y : Scheme.{u}}
    (hY : (p : Γ(Y, ⊤)) = 0) :
    L((Y.iterateFrobenius hp hY n)^*[ModuleCat.{u + 1} Λ]) ≅ 𝟭 _ :=
  leftDerivedUpperStarIterateFrobeniusIso (ModuleCat.{u + 1} Λ) hp hY n ≪≫
    leftDerivedUpperStarId _ Y

/-- The trivialization `R(F_Y)_* ≅ 𝟭` of the derived direct image along the absolute Frobenius,
right adjoint to the trivialization `L(F_Y)^* ≅ 𝟭`. -/
noncomputable def rightDerivedLowerStarIterateFrobeniusIso {Y : Scheme.{u}}
    (hY : (p : Γ(Y, ⊤)) = 0) :
    R((Y.iterateFrobenius hp hY n)_*[ModuleCat.{u + 1} Λ]) ≅ 𝟭 _ :=
  (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (Y.iterateFrobenius hp hY n)).rightAdjointUniq
    (Adjunction.id.ofNatIsoLeft (leftDerivedUpperStarIterateFrobeniusTriv Λ hp n hY).symm)

/-- The trivialization `R(F_Y)_! ≅ R(F_Y)_* ≅ 𝟭` of the compactly supported direct image along a
proper absolute Frobenius. -/
noncomputable def rightDerivedLowerShriekIterateFrobeniusIso {Y : Scheme.{u}}
    (hY : (p : Γ(Y, ⊤)) = 0) [IsProper (Y.iterateFrobenius hp hY n)] :
    R(Y.iterateFrobenius hp hY n)_![ModuleCat.{u + 1} Λ] ≅ 𝟭 _ :=
  rightDerivedLowerShriekIsoRightDerivedLowerStar _ _ ≪≫
    rightDerivedLowerStarIterateFrobeniusIso Λ hp n hY

variable [Finite Λ]

/-- **The absolute Frobenius commutes with the compactly supported direct image**: for
`f : X ⟶ Y` between schemes of characteristic `p` with proper absolute Frobenius, the
isomorphisms
```
R(F_X ≫ f)_! ≅ R(F_X)_! ⋙ Rf_! ≅ Rf_!,    R(f ≫ F_Y)_! ≅ Rf_! ⋙ R(F_Y)_! ≅ Rf_!
```
agree along `F_X ≫ f = f ≫ F_Y`. -/
theorem rightDerivedLowerShriekCompIso_iterateFrobenius {X Y : Scheme.{u}}
    (hX : (p : Γ(X, ⊤)) = 0) (hY : (p : Γ(Y, ⊤)) = 0) (f : X ⟶ Y) [HasCompactification f]
    [QuasiCompact f] [IsProper (X.iterateFrobenius hp hX n)]
    [IsProper (Y.iterateFrobenius hp hY n)] [HasCompactification (X.iterateFrobenius hp hX n ≫ f)]
    [QuasiCompact (X.iterateFrobenius hp hX n ≫ f)]
    [HasCompactification (f ≫ Y.iterateFrobenius hp hY n)]
    [QuasiCompact (f ≫ Y.iterateFrobenius hp hY n)]
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (rightDerivedLowerShriekCompIso Λ (X.iterateFrobenius hp hX n) f).hom.app K ≫
        (R(f)_![ModuleCat.{u + 1} Λ]).map
          ((rightDerivedLowerShriekIterateFrobeniusIso Λ hp n hX).hom.app K) =
      (rightDerivedLowerShriekCongrIso Λ (comp_iterateFrobenius hp f hY hX n).symm).hom.app K ≫
        (rightDerivedLowerShriekCompIso Λ f (Y.iterateFrobenius hp hY n)).hom.app K ≫
        (rightDerivedLowerShriekIterateFrobeniusIso Λ hp n hY).hom.app
          ((R(f)_![ModuleCat.{u + 1} Λ]).obj K) := by
  sorry

end AlgebraicGeometry.Etale
