/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil conjectures project
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarCompAssoc
public import WeilConjectures.SixFunctors.LowerShriek.Formalism.Associativity

/-!
# The compact support formalism of the bounded below étale derived categories

The bounded below derived categories `D⁺(X_ét, A)` of étale sheaves, with the pullbacks `D⁺(f^*)`,
the derived pushforwards `R⁺f_*` and the extensions by zero `D⁺(j_!)` along open immersions,
form a `AlgebraicGeometry.CompactSupportFormalism`, `Etale.derivedPlusFormalism A`. Its compactly
supported direct image along a compactification `c` is `Rf_!(c)[A]+`, and its compactly supported
direct image along a morphism admitting a compactification is `R(f)_![A]+`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A] [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A]
  [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]

variable {X Y : Scheme.{u}} {f : X ⟶ Y}

section Torsion

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

end Torsion

end Etale

end AlgebraicGeometry
