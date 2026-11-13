/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTraceExists

/-!
# Restriction and trace for finite étale morphisms

## Main definitions

* `finiteEtaleRestriction`: the unit of inverse image adjoint to direct image.
* `finiteEtaleTrace`: the component of the unique characterized trace family.

For a sheaf of `ℤ/n`-modules, these definitions are applied to its underlying abelian sheaf.
Inverse and direct image are additive, so they preserve annihilation by `n`. Every additive
map between groups killed by `n` is `ℤ/n`-linear for their unique `ℤ/n`-module structures;
thus the same maps are used with these coefficients, including `n = 1`.

## References

* Stacks Project, Tag 03SH
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- Restriction is the unit at `F` of the adjunction `f⁻¹ ⊣ f_*`.
(Stacks, Section 03SH.) -/
noncomputable def finiteEtaleRestriction {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsFinite f] [Etale f] (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    F ⟶ (lowerStar AddCommGrpCat.{u + 1} f).obj
      ((upperStar AddCommGrpCat.{u + 1} f).obj F) :=
  (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app F

/-- Trace is the member at `(f, F)` of the unique family given by
`existsUnique_finiteEtaleTrace`. That family is natural in `F`, commutes with étale
localization, and is the sum map for every finite split covering, including the empty one.
(Stacks, Definition 03SE and the following characterization in Section 03SH.) -/
noncomputable def finiteEtaleTrace {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsFinite f] [Etale f] (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (lowerStar AddCommGrpCat.{u + 1} f).obj
      ((upperStar AddCommGrpCat.{u + 1} f).obj F) ⟶ F :=
  Classical.choose existsUnique_finiteEtaleTrace.exists X Y f inferInstance inferInstance F

end AlgebraicGeometry.Etale
