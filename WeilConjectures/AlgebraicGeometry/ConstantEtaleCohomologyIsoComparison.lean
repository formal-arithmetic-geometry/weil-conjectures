/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import WeilConjectures.AlgebraicGeometry.EtaleSheafHExtDerivedComparison
import WeilConjectures.ConstructibleSheaf.Defs
public import Mathlib.Algebra.Category.Grp.Zero

/-! # Comparison of constant etale cohomology along an isomorphism

Source: Stacks Project, Cohomology on Sites, the derived-functor definition of cohomology;
Etale Cohomology, Lemma 09ZC, implicit transport in the affine reduction.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Etale

/-- Vanishing of derived constant etale cohomology agrees with vanishing of the
Ext-defined sheaf cohomology on an isomorphic scheme. No finiteness, affineness,
normality, or separably closed field hypothesis is needed (Stacks, Tag 09ZC). -/
theorem isZero_constant_cohomology_iff_subsingleton_H_of_iso
    (X Y : Scheme.{u}) (e : X ≅ Y)
    (M : Type (u + 1)) [AddCommGroup M] (n : ℕ) :
    IsZero ((cohomology AddCommGrpCat.{u + 1} X (n : ℤ)).obj
      ((DerivedCategory.singleFunctor _ 0).obj
        ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
          (AddCommGrpCat.of M)))) ↔
      Subsingleton (Sheaf.H.{u + 1}
        ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
          (AddCommGrpCat.of M)) n) := by
  let F := (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
    (AddCommGrpCat.of M)
  let c := (Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} e.inv).app
    (AddCommGrpCat.of M)
  let cH := ((Sheaf.functorH.{u + 1} Y.smallEtaleTopology n).mapIso c).addCommGroupIsoToAddEquiv
  let eH := (cohomologyEquiv e.inv F n).trans cH
  obtain ⟨a⟩ := Scheme.nonempty_sheafH_extDerivedIso X n
  constructor
  · intro hz
    have hx : Subsingleton (Sheaf.H.{u + 1} F n) :=
      AddCommGrpCat.subsingleton_of_isZero (hz.of_iso (a.app F))
    exact @Equiv.subsingleton _ _ eH.symm.toEquiv hx
  · intro hy
    have hx : Subsingleton (Sheaf.H.{u + 1} F n) :=
      @Equiv.subsingleton _ _ eH.toEquiv hy
    exact (AddCommGrpCat.isZero_iff_subsingleton.mpr hx).of_iso (a.app F).symm

end AlgebraicGeometry.Etale
