/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import WeilConjectures.AlgebraicGeometry.ArtinSchreierSequence
import WeilConjectures.AlgebraicGeometry.Curve.ArtinSchreierAdditiveVanishing
import WeilConjectures.AlgebraicGeometry.Curve.ArtinSchreierCohomologyEpi
import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated

/-!
# Artin–Schreier vanishing on a smooth connected curve

Source: Stacks Project, Tag 0A3N, dimension one.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Source: Stacks Project, Tag
0A3N. For a smooth separated connected curve over an algebraically closed field of positive
characteristic `p`, the constant étale sheaf `ℤ/p` has zero cohomology in degrees above one. -/
theorem isZero_etaleCohomology_constantZMod_of_one_lt_of_charP
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f]
    (p : ℕ) [Fact p.Prime] [CharP k p] (q : ℕ) (hq : 1 < q) :
    IsZero ((Etale.cohomology AddCommGrpCat.{u + 1} C (q : ℤ)).obj
      ((DerivedCategory.singleFunctor (Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj
        (C.constantZMod p))) := by
  obtain ⟨G, e, a, wp, iota, hzero, ha, hwp, _, hS⟩ :=
    artinSchreier_shortExact f p (Nat.Prime.pos (Fact.out : p.Prime))
  let R := (Sheaf.Γ C.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerivedFunctor
  let T := R.mapTriangle.obj hS.singleTriangle
  have hT : T ∈ distTriang _ :=
    R.map_distinguished _ hS.singleTriangle_distinguished
  have hstep : ((q - 1 : ℕ) : ℤ) + 1 = (q : ℤ) := by omega
  have hepi : Epi ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1}
      ((q - 1 : ℕ) : ℤ)).map T.mor₂) := by
    by_cases hq2 : q = 2
    · subst q
      exact epi_etaleCohomology_artinSchreier_one f p G a wp ha hwp
    · have hG := isZero_etaleCohomology_additive_of_two_le f G e (q - 1) (by omega)
      exact hG.epi _
  have hδ := (DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff
    T hT ((q - 1 : ℕ) : ℤ) (q : ℤ) hstep).mp hepi
  have hG := isZero_etaleCohomology_additive_of_two_le f G e q (by omega)
  exact (DerivedCategory.HomologySequence.exact₁
    T hT ((q - 1 : ℕ) : ℤ) (q : ℤ) hstep).isZero_of_both_zeros
      hδ (hG.eq_zero_of_tgt _)

end AlgebraicGeometry
