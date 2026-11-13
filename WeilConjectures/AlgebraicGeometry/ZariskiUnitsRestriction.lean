/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import WeilConjectures.AlgebraicGeometry.Sites.UnitsTorsor
public import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Topology.Sheaves.Functors

/-!
# Restriction of Zariski units and their cohomology

## References

* [Stacks Project, Tag 09NY](https://stacks.math.columbia.edu/tag/09NY)
* [Stacks Project, Tag 02UV](https://stacks.math.columbia.edu/tag/02UV)
* [Stacks Project, Tag 01F7](https://stacks.math.columbia.edu/tag/01F7)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme

/-- The map `O_Xˣ → i_* O_Zˣ` induced by the structure-sheaf map of `i`. -/
noncomputable def unitsSheafToPushforward {Z X : Scheme.{u}} (i : Z ⟶ X) :
    X.unitsSheaf ⟶ ((Opens.map i.base).sheafPushforwardContinuous AddCommGrpCat.{u}
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology Z)).obj Z.unitsSheaf :=
  ⟨Functor.whiskerRight i.c CommRingCat.unitsAddCommGrp⟩

/-- The canonical comparison `H^p(X, i_* O_Zˣ) → H^p(Z, O_Zˣ)`: apply exact inverse
image to the Ext class, identify inverse image of the constant integer sheaf with the
constant integer sheaf, then apply the counit `i⁻¹ i_* O_Zˣ → O_Zˣ`. -/
noncomputable def unitsPushforwardCohomologyComparison {Z X : Scheme.{u}} (i : Z ⟶ X)
    (p : ℕ) :
    Sheaf.H (((Opens.map i.base).sheafPushforwardContinuous AddCommGrpCat.{u}
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology Z)).obj Z.unitsSheaf) p →+
        Sheaf.H Z.unitsSheaf p :=
  letI := lan_preservesFiniteLimits_of_flat (E := AddCommGrpCat.{u}) (Opens.map i.base)
  letI : PreservesFiniteLimits ((Opens.map i.base).sheafPullback AddCommGrpCat.{u}
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology Z)) :=
    Functor.sheafPullbackConstruction.preservesFiniteLimits _ _ _ _
  letI := ((Opens.map i.base).sheafAdjunctionContinuous AddCommGrpCat.{u}
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology Z)).leftAdjoint_preservesColimits
  letI := preservesBinaryBiproducts_of_preservesBinaryProducts
    ((Opens.map i.base).sheafPullback AddCommGrpCat.{u}
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology Z))
  letI := Functor.additive_of_preservesBinaryBiproducts
    ((Opens.map i.base).sheafPullback AddCommGrpCat.{u}
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology Z))
  (Sheaf.H.map (((Opens.map i.base).sheafAdjunctionContinuous AddCommGrpCat.{u}
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology Z)).counit.app Z.unitsSheaf)
    p).comp
      (Sheaf.H.mapFunctor ((Opens.map i.base).sheafPullback AddCommGrpCat.{u}
        (Opens.grothendieckTopology X) (Opens.grothendieckTopology Z))
        (((Opens.map i.base).constantSheafsheafPullbackIso AddCommGrpCat.{u} _ _
          isTerminalTop isTerminalTop).symm.app (AddCommGrpCat.of (ULift ℤ)))
        (((Opens.map i.base).sheafPushforwardContinuous AddCommGrpCat.{u}
          (Opens.grothendieckTopology X) (Opens.grothendieckTopology Z)).obj Z.unitsSheaf) p)

end AlgebraicGeometry.Scheme
