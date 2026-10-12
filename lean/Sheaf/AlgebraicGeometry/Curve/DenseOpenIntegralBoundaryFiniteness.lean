/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J2
-/
module

public import Sheaf.AlgebraicGeometry.ConstructibleTorsionCurveSheaf
public import WeilConjectures.AlgebraicGeometry.Curve.Assertions
public import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Ring.ULift
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

-- Keep the declared geometric proof route reachable while the boundary theorem is open.
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.AlgebraicGeometry.EtaleSheafHExtDerivedComparison
import Sheaf.AlgebraicGeometry.ZeroDimensionalSectionsStalks
import Sheaf.Paper.ZeroDimensionalCohomology
import WeilConjectures.SixFunctors.Finite.Exact

/-! # Finite cohomology of the dense-open boundary

Source: Stacks Project, Tags 0GJA and 095L.
(blueprint: lem-pbc-h2-dense-open-integral-boundary-finiteness). -/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.IsCurve

/-- The closed-boundary term of a constructible torsion sheaf on a curve has finite
cohomology in every degree.
Source: Stacks Project, Tag 0GJA, proof, and Tag 095L.
(blueprint: lem-pbc-h2-dense-open-integral-boundary-finiteness).

Proof: Density excludes every generic point from the closed complement Z. Since the
curve is Noetherian of dimension at most one, the reduced scheme underlying Z is a
finite disjoint union of closed points. Their residue fields are k, since k is
algebraically closed and the curve is of finite type. Nilpotent thickening does not
change the small etale topos. Finite direct image along Z -> X is exact; the Leray
comparison identifies the cohomology of Q = i_*i^*F with the cohomology of i^*F on Z.
The small etale topos of Spec k is the topos of sets, so its global sections functor
is exact. Hence positive cohomology is zero. H^0(Q) is the product of the finitely
many geometric stalks of F on Z. The coefficient encoding has the same underlying
abelian stalks as P.F, and constructibility as a set sheaf makes these finite.
Consequently H^0(Q) is finite, and the zero groups in positive degrees are finite.
When Z is empty, its direct image is zero and the same conclusion holds. -/
theorem dense_open_integral_boundary_finiteness {k : Type u} [Field k] [IsAlgClosed k]
    (P : CurveCoefficientPair k) (hP : P.IsConstructible)
    (U : P.C.Opens) (hU : Dense (U : Set P.C)) :
    let E := (forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).inv ⋙
      ModuleCat.restrictScalars (ULift.ringEquiv : ULift.{u + 1} ℤ ≃+* ℤ).toRingHom
    let F := (sheafCompose P.C.smallEtaleTopology E).obj P.F
    let Q := (Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))
      U.closedComplement).obj
        ((Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) U.closedComplement).obj F)
    ∀ q : ℕ, Finite (Sheaf.H
      ((sheafCompose P.C.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) AddCommGrpCat.{u + 1})).obj Q) q) := by sorry

end AlgebraicGeometry.IsCurve
