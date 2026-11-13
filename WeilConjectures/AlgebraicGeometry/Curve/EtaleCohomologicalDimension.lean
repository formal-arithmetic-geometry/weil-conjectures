/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.AlgebraicGeometry.EtaleSheafHExtDerivedComparison
import WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension

/-!
# Etale cohomological dimension of a smooth connected curve

Source: Stacks Project, Tag 03SC (1).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- For a smooth separated connected curve over an algebraically closed field, every torsion
abelian etale sheaf has zero cohomology above degree two. Cohomology is the homology of derived
global sections, applied to the sheaf in degree zero. -/
theorem IsConnectedCurve.subsingleton_etaleCohomology_of_two_lt
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    [C.Over (Spec (.of k))] [IsConnectedCurve (C ↘ Spec (.of k))]
    [Smooth (C ↘ Spec (.of k))]
    (F : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}) (hF : F.IsTorsion)
    (q : ℕ) (hq : 2 < q) :
    Subsingleton ((Etale.cohomology AddCommGrpCat.{u + 1} C (q : ℤ)).obj
      ((DerivedCategory.singleFunctor
        (Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj F)) := by
  let f : C ⟶ Spec (.of k) := C ↘ Spec (.of k)
  have hq' : 3 ≤ q := by omega
  have h := IsCurve.subsingleton_sheafH_of_three_le_of_forall f
    (fun _ f' _ _ F' hF' ↦ IsCurve.subsingleton_sheafH_two_of_isAffine f' F' hF')
    F hF q hq'
  have : Subsingleton ((Sheaf.functorH C.smallEtaleTopology q).obj F) := h
  obtain ⟨e⟩ := Scheme.nonempty_sheafH_extDerivedIso C q
  exact (e.app F).addCommGroupIsoToAddEquiv.symm.injective.subsingleton

end AlgebraicGeometry
