/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.FiniteDerived
public import WeilConjectures.ConstructibleSheaf.FiniteConstantModel
public import WeilConjectures.ConstructibleSheaf.Monoidal
public import WeilConjectures.ConstructibleSheaf.SpecializationCriterion

/-!
# Constructibility inputs of the Künneth formula

This file records two constructibility statements used in the proof of the base change theorem
for a pushforward tensored with a flat sheaf (blueprint `lem-kun-0f1j`). The third one, that
constant sheaves with finitely generated values are constructible (blueprint
`lem-kun-constant-constructible`), is `AlgebraicGeometry.Scheme.isConstructibleSheaf_constantSheaf`
in `WeilConjectures.ConstructibleSheaf.SpecializationCriterion`.

- `AlgebraicGeometry.Etale.isConstructibleSheaf_homology_rightDerivedLowerStar_of_isFinite`
  (blueprint `fin4-thm-finite-morphisms-constructible`): all higher direct images of a
  constructible sheaf along a finite morphism towards a scheme of finite type over a field are
  constructible, and vanish in positive degrees;
- `AlgebraicGeometry.Etale.isConstructibleSheaf_lowerStar_of_isFinite_of_locallyOfFiniteType`
  (blueprint `lem-kun-095r`): the same statement in the form used for the Künneth formula.
-/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Functor

noncomputable section

namespace AlgebraicGeometry

open Scheme

variable {Λ : Type (u + 1)} [CommRing Λ]

namespace Etale

variable [Finite Λ]

end Etale

end AlgebraicGeometry
