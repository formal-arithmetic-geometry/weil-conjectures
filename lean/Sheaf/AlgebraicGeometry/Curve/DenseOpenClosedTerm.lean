/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K2
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.Assertions
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Sheaf.AlgebraicGeometry.CohomologyPullbackDerivedUnit
import Sheaf.AlgebraicGeometry.ZeroDimensionalPullbackGlobalSections
import Sheaf.Paper.InverseImageStalkGerm
import Sheaf.Paper.ZeroDimensionalCohomology
import WeilConjectures.SixFunctors.Finite.Exact
import WeilConjectures.SixFunctors.Finite.BaseChange
import WeilConjectures.SixFunctors.OpenClosed.Exact

/-! # Acyclic closed term for a dense-open counit -/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry.Etale

namespace AlgebraicGeometry.IsCurve

/-- The dense-open counit has a short exact cokernel with acyclic degree-one
cohomology on both sides of the field extension and bijective degree-zero comparison.
Source: Stacks Project, Tag 0GJA, proof (five-term exact sequence and remark (c)).
(blueprint: lem-pbc-k2-dense-open-closed-term)

Proof: take the reduced induced closed complement i:Z → X and let B be the underlying
abelian sheaf of i_*i^*F. The open-closed exact sequence, followed by the exact forgetful
functor, gives the asserted short complex. Density excludes the generic points of the
Noetherian curve, so Z is zero dimensional and finite. Its closed points have residue
field k. Finite direct image is exact, so Leray identifies the cohomology of B with
that of i^*F on Z. The latter is a finite product of stalks in degree zero and vanishes
in positive degrees. Closed-immersion base change identifies the inverse image of B
with the analogous closed direct image over k'. The complement after base change is
again a finite union of algebraically closed points. The canonical degree-zero
comparison is the product of the inverse-image stalk identifications, hence bijective.
Empty schemes and the full open give zero closed terms and satisfy the same assertions.
-/
theorem dense_open_closed_term (Λ : Type (u + 1)) [CommRing Λ]
    {k k' : Type u} [Field k] [IsAlgClosed k] [Field k'] [IsAlgClosed k']
    {X X' : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsCurve f]
    {ι : Spec (.of k') ⟶ Spec (.of k)} {f' : X' ⟶ Spec (.of k')}
    {ι' : X' ⟶ X} (h : IsPullback ι' f' f ι)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (U : X.Opens) (hU : Dense (U : Set X)) :
    let A := (sheafCompose X.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F
    let ε := (sheafCompose X.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).map
        ((openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) U.ι).counit.app F)
    ∃ (B : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (b : A ⟶ B)
      (w : ε ≫ b = 0),
      (ShortComplex.mk ε b w).ShortExact ∧
      Function.Bijective (cohomologyMap ι' B 0) ∧
      Subsingleton (Sheaf.H B 1) ∧
      Subsingleton (Sheaf.H (((ι')^*[AddCommGrpCat.{u + 1}]).obj B) 1) := by
  sorry

end AlgebraicGeometry.IsCurve
