/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.CategoryTheory.Sites.Torsor
import WeilConjectures.AlgebraicGeometry.EtaleSheafHExtDerivedComparison
public import Mathlib.Algebra.Category.Grp.Zero

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- If every torsor under the constant sheaf with value `M` is trivial, then the first
cohomology object of the constant sheaf is zero (Stacks, Tags 03AJ, 09ZB). -/
theorem isZero_constant_cohomology_one_of_torsors_trivial
    (R : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [IsSepClosed (FractionRing R)] (Z : Scheme.{u})
    (i : Z ⟶ Spec (CommRingCat.of R)) [IsClosedImmersion i]
    (M : Type (u + 1)) [AddCommGroup M] [Finite M]
    (h : ∀ T : CategoryTheory.Sheaf.Torsor
      ((constantSheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of M)), T ≈ CategoryTheory.Sheaf.Torsor.trivial _) :
    IsZero ((cohomology AddCommGrpCat.{u + 1} Z 1).obj
      ((DerivedCategory.singleFunctor (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj
        ((constantSheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
          (AddCommGrpCat.of M)))) := by
  let F := (constantSheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
    (AddCommGrpCat.of M)
  have hH : Subsingleton (Sheaf.H.{u + 1} F 1) :=
    (Sheaf.subsingleton_H_one_iff terminalIsTerminal F).mpr h
  obtain ⟨e⟩ := Scheme.nonempty_sheafH_extDerivedIso Z 1
  exact (AddCommGrpCat.isZero_iff_subsingleton.mpr hH).of_iso (e.app F).symm

end AlgebraicGeometry.Etale
