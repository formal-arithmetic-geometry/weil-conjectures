/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import WeilConjectures.SixFunctors.BaseChange.Derived
public import Mathlib.Data.ZMod.Basic

/-!
# Injective acyclicity for prime-field sheaves

Source: Stacks Project, Tag 0A4B, property (2)
(blueprint: def-weil-pbc-injective-acyclicity-property).
-/

@[expose] public section

universe u_ia

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

/-- After any cartesian base change, the underlying abelian sheaf of an injective
`ZMod r`-module sheaf has zero positive higher direct images. For prime `r`, this is
`IA_r(f)`. The lift of the coefficient ring changes no modules and supplies the
coefficient universe required by the existing etale functors.
Source: Stacks Project, Tag 0A4B, property (2)
(blueprint: def-weil-pbc-injective-acyclicity-property). -/
def HasPrimeInjectiveAcyclicity {X Y : Scheme.{u_ia}} (f : X ⟶ Y) (r : ℕ) : Prop :=
  ∀ ⦃Y' X' : Scheme.{u_ia}⦄ ⦃g : Y' ⟶ Y⦄ ⦃f' : X' ⟶ Y'⦄ ⦃g' : X' ⟶ X⦄
    (_sq : IsPullback g' f' f g)
    (I : Sheaf X.smallEtaleTopology (ModuleCat.{u_ia + 1} (ULift.{u_ia + 1} (ZMod r)))),
    Injective I → ∀ q : ℤ, 0 < q →
      IsZero ((DerivedCategory.Plus.homologyFunctor
        (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u_ia + 1}) q).obj
        ((lowerStar AddCommGrpCat.{u_ia + 1} f').rightDerivedFunctorPlus.obj
          ((DerivedCategory.Plus.singleFunctor
            (Sheaf X'.smallEtaleTopology AddCommGrpCat.{u_ia + 1}) 0).obj
            ((upperStar AddCommGrpCat.{u_ia + 1} g').obj
              ((sheafCompose X.smallEtaleTopology
                (forget₂ (ModuleCat.{u_ia + 1} (ULift.{u_ia + 1} (ZMod r)))
                  AddCommGrpCat.{u_ia + 1})).obj I)))))

/-- Injective acyclicity for every prime. Source: Stacks Project, Tag 0A4B, property (2)
(blueprint: def-weil-pbc-injective-acyclicity-property). -/
def HasAllPrimeInjectiveAcyclicity {X Y : Scheme.{u_ia}} (f : X ⟶ Y) : Prop :=
  ∀ r : ℕ, r.Prime → HasPrimeInjectiveAcyclicity f r

end AlgebraicGeometry.Etale
