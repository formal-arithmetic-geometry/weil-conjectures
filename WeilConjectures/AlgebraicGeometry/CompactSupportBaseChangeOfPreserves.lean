/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompactificationBaseChangeSetting
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleLowerShriekOfPreserves
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenLowerShriekBaseChange
public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Compact-support base change for a fixed compactification

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-prop-open-coefficients/det-def-sfb-shriek-base-change-morphism-definition.md
(blueprint: det-def-sfb-shriek-base-change-morphism-definition).

## Main definitions

* `compactSupportBaseChangeOpenStepOfPreserves`: the second arrow, as a natural isomorphism.
* `boundedConstructibleCompactSupportBaseChangeOfPreserves`: the compact-support base change
  morphism, relative to the supplied compactification and its canonical base change.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
  (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  (H : PreservesBoundedConstructiblePushforwards Λ k)
  {X X' Y Y' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y' ⟶ Y} {g' : X' ⟶ X}

/-- Apply `Rp'_*` to the inverse open exchange for the cartesian open square of the
base-changed compactification. Keeping this arrow as an isomorphism records its asserted
invertibility without any proper-base-change isomorphism assumption.

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-prop-open-coefficients/det-def-sfb-shriek-base-change-morphism-definition.md,
second arrow of the displayed composite
(blueprint: det-def-sfb-shriek-base-change-morphism-definition). -/
noncomputable def compactSupportBaseChangeOpenStepOfPreserves
    (sq : IsPullback g' f' f g) (c : Compactification.BoundaryCompactification f.left) :
    (boundedConstructibleOpenImmersionLowerShriek Λ ℓ c.obj.obj.overI ⋙
        boundedConstructibleUpperStar Λ ℓ (c.obj.obj.overBaseChangeFst sq)) ⋙
        boundedConstructibleLowerStarOfPreserves Λ H
          (c.obj.obj.ofIsPullback sq.overLeft).overG ≅
      (boundedConstructibleUpperStar Λ ℓ g' ⋙
        boundedConstructibleOpenImmersionLowerShriek Λ ℓ
          (c.obj.obj.ofIsPullback sq.overLeft).overI) ⋙
        boundedConstructibleLowerStarOfPreserves Λ H
          (c.obj.obj.ofIsPullback sq.overLeft).overG :=
  Functor.isoWhiskerRight
    (boundedConstructibleOpenImmersionLowerShriekBaseChangeIso' Λ ℓ
      (c.obj.obj.overBaseChange_isPullback_i sq))
    (boundedConstructibleLowerStarOfPreserves Λ H
      (c.obj.obj.ofIsPullback sq.overLeft).overG)

/-- The natural transformation `Ex_!^c : Lg^* Rf_!^c ⟶ Rf'_!^{c'} Lg'^*` on bounded
constructible condensed module complexes. The target writes `Rf'_!^{c'}` as its defining
composite `i'_! ⋙ Rp'_*`, for `c' = c.ofIsPullback sq.overLeft`. Its first arrow is the
recorded `mateEquiv` specialization for the proper square, precomposed with `i_!`.
Its second arrow is the image of the recorded inverse open exchange under `Rp'_*`.
Associators only change parentheses. The supplied `c` remains an argument throughout.

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-prop-open-coefficients/det-def-sfb-shriek-base-change-morphism-definition.md,
defining display and final two sentences
(blueprint: det-def-sfb-shriek-base-change-morphism-definition). -/
noncomputable def boundedConstructibleCompactSupportBaseChangeOfPreserves
    (sq : IsPullback g' f' f g) (c : Compactification.BoundaryCompactification f.left) :
    boundedConstructibleLowerShriekOfCompactificationOfPreserves Λ ℓ H c ⋙
        boundedConstructibleUpperStar Λ ℓ g ⟶
      boundedConstructibleUpperStar Λ ℓ g' ⋙
        (boundedConstructibleOpenImmersionLowerShriek Λ ℓ
          (c.obj.obj.ofIsPullback sq.overLeft).overI ⋙
        boundedConstructibleLowerStarOfPreserves Λ H
          (c.obj.obj.ofIsPullback sq.overLeft).overG) :=
  (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (boundedConstructibleOpenImmersionLowerShriek Λ ℓ c.obj.obj.overI)
      (mateEquiv
        (boundedConstructibleUpperStarLowerStarAdjunctionOfPreserves Λ H c.obj.obj.overG ℓ)
        (boundedConstructibleUpperStarLowerStarAdjunctionOfPreserves Λ H
          (c.obj.obj.ofIsPullback sq.overLeft).overG ℓ)
        (TwoSquare.mk _ _ _ _
          (boundedConstructiblePullbackSquareComparison Λ ℓ
            (c.obj.obj.overBaseChange_isPullback_g sq).toCommSq).hom)).natTrans ≫
    (Functor.associator _ _ _).inv ≫
    (compactSupportBaseChangeOpenStepOfPreserves Λ ℓ H sq c).hom ≫
    (Functor.associator _ _ _).hom

end AlgebraicGeometry.ProEtale.CondensedRing
