/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.BaseChange.Derived
public import WeilConjectures.AlgebraicGeometry.TorsionEtaleSheaf

/-!
# Proper base change for torsion abelian sheaves

Source: Stacks Project, Tag 0A4B, and the blueprint's derived-exchange formulation
(blueprint: def-weil-pbc-property).
-/

@[expose] public section

universe u_pbc

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- The specified derived exchange map is an isomorphism for every cartesian base change
and every torsion abelian sheaf placed in degree zero. Source: Stacks Project, Tag 0A4B,
property (1), in the blueprint's derived-exchange formulation
(blueprint: def-weil-pbc-property). -/
def HasTorsionAbelianBaseChange {X Y : Scheme.{u_pbc}} (f : X ⟶ Y) : Prop :=
  ∀ ⦃Y' X' : Scheme.{u_pbc}⦄ ⦃g : Y' ⟶ Y⦄ ⦃f' : X' ⟶ Y'⦄ ⦃g' : X' ⟶ X⦄
    (sq : IsPullback g' f' f g) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u_pbc + 1}),
    Scheme.IsTorsionAbelianSheaf F →
      IsIso ((derivedBaseChangeMapPlus AddCommGrpCat.{u_pbc + 1} sq.toCommSq).app
        ((DerivedCategory.Plus.singleFunctor
          (Sheaf X.smallEtaleTopology AddCommGrpCat.{u_pbc + 1}) 0).obj F))

end AlgebraicGeometry.Etale
