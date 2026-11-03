/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CondensedOrdinaryCompactSections
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# No negative compact-support cohomology for a coefficient sheaf

Source: latest blueprint, `sec-deligne-laumon-a1/sk-l-dl-a1-endpoints/`
`lem-zl-affine-curve-range.proof.md`, torsion case and lattice argument.
This is the negative-degree sub-step of the range proof.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace WeilConjectures

/-- Compact support of a sheaf has no negative cohomology. No constructibility or
dimension hypothesis is needed for this half of the curve range argument.

Source: latest blueprint, `sec-deligne-laumon-a1/sk-l-dl-a1-endpoints/`
`lem-zl-affine-curve-range.proof.md`, negative-degree assertion
(blueprint: lem-zl-compact-sections-nonnegative).

Proof: exact extension by zero sends the single-degree object to the extension
sheaf in degree zero. The right derived proper direct image of this sheaf is
nonnegative, since it is computed by a nonnegative injective resolution. Exact
geometric-point evaluation commutes with cohomology and sends zero to zero.
-/
theorem compactSections_nonnegative (ell : ℕ) [Fact ell.Prime]
    (k : Type u) [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} {a : X ⟶ Spec (.of k)} (c : Compactification a)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ell) X))
    (i : ℤ) (hi : i < 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (PadicAlgCl ell)) i).obj
      ((condensedQbarCompactSections ell k c).obj
        ((DerivedCategory.singleFunctor _ 0).obj M))) := by
  let J := CondensedRing.openImmersionLowerShriek (Profinite.padicAlgClRingObj ell) c.i
  let P := CondensedRing.lowerStar (Profinite.padicAlgClRingObj ell) c.g
  let E := ProEtale.CondensedQbarGeometricEvaluation.fieldFiber k ell
  let e := (J.mapDerivedCategorySingleFunctor 0).app M
  have hP := P.isGE_rightDerivedFunctor_obj_singleFunctor (J.obj M)
  have hz := (DerivedCategory.isGE_iff _ 0).mp hP i hi
  have hz' := hz.of_iso ((DerivedCategory.homologyFunctor _ i).mapIso
    (P.rightDerivedFunctor.mapIso e))
  exact (E.map_isZero hz').of_iso ((E.mapDerivedCategoryHomologyFunctorIso i).app _).symm

end WeilConjectures
