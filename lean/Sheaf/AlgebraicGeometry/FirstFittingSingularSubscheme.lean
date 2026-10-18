/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q105
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
public import Sheaf.RingTheory.PresentationFittingIdeal

/-!
# First Fitting singular subscheme

Source: Stacks Project, Divisors, Tags 0C3I, 0C3J, 0C3K, and Morphisms Tag 01UM;
More on Algebra Tags 07Z6, 07Z8, 07ZA (blueprint: def-trf-first-fitting-singular-subscheme).

## Main definitions

* `isFirstFittingIdealSheaf`: the affine-local first Fitting condition.
* `firstFittingIdealSheaf`: the glued ideal sheaf of relative differentials.
* `firstFittingSingularSubscheme`: the resulting closed subscheme inclusion.

## Main statements

* `existsUnique_firstFittingIdealSheaf`: existence and uniqueness of the glued ideal sheaf.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

/-- Affine-local characterization of the first Fitting ideal sheaf of the relative
Kähler differentials.  The finite free presentation is allowed to vary with the affine
open; presentation independence and localization are supplied by
`LinearMap.presentationFittingIdeal_independence_baseChange`. (blueprint:
def-trf-first-fitting-singular-subscheme) -/
def isFirstFittingIdealSheaf {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (J : X.IdealSheafData) : Prop :=
  ∀ U : X.affineOpens,
    ∃ (n : ℕ)
      (π : (Fin n → Γ(X, U.1)) →ₗ[Γ(X, U.1)] Γ(f.relativeDifferentials, U.1)),
      Function.Surjective π ∧ J.ideal U = π.presentationFittingIdeal 1

/-- The affine-local first Fitting ideals glue uniquely to an ideal sheaf.  The proof
uses finite generation of relative differentials on affine charts, independence of the
finite presentation, and compatibility with localization. (blueprint:
def-trf-first-fitting-singular-subscheme)

Proof plan: on each affine chart use the finite-type affine-pair criterion to obtain a
finite presentation of the relative differential module; define the first Fitting ideal
by kernel-row minors; use `LinearMap.presentationFittingIdeal_independence_baseChange`
to show independence of generators and localization; then apply the affine ideal-sheaf
gluing criterion.  Uniqueness follows from `Scheme.IdealSheafData.ext` and the affine
local characterization above. -/
theorem existsUnique_firstFittingIdealSheaf {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] :
    ∃! J : X.IdealSheafData, isFirstFittingIdealSheaf f J := by
  sorry

/-- The glued ideal sheaf whose affine sections are the first Fitting ideals of
`Ω¹_{X/S}`.  Its data is determined uniquely by the affine-local condition above.
(blueprint: def-trf-first-fitting-singular-subscheme) -/
noncomputable def firstFittingIdealSheaf {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] : X.IdealSheafData :=
  Classical.choose (existsUnique_firstFittingIdealSheaf f)

/-- The first-Fitting singular subscheme of `f`, as the closed subscheme cut out by
`firstFittingIdealSheaf f`.  (blueprint: def-trf-first-fitting-singular-subscheme) -/
noncomputable def firstFittingSingularSubscheme {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] :
    (firstFittingIdealSheaf f).subscheme ⟶ X :=
  (firstFittingIdealSheaf f).subschemeι

/-- The first-Fitting singular subscheme inclusion is a closed immersion, as the closed
subscheme of an ideal sheaf.  Source: Stacks Project, Divisors, Section 0C3C; Schemes
Lemma 01IN. (blueprint: def-trf-first-fitting-singular-subscheme) -/
instance firstFittingSingularSubscheme_isClosedImmersion {X S : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFiniteType f] :
    IsClosedImmersion (firstFittingSingularSubscheme f) := by
  dsimp [firstFittingSingularSubscheme]
  infer_instance

end AlgebraicGeometry.Scheme
