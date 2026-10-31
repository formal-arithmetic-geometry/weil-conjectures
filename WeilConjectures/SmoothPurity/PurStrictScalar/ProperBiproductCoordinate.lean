/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurStrictScalar.ScalarReductionTowerBalancing
public import WeilConjectures.SmoothPurity.PurStrictScalar.StrictScalarMateEvaluationData
public import WeilConjectures.SmoothPurity.PurStrictScalar.FiniteScalarCoordinateData

/-! Coordinate form of the finite proper biproduct comparison.

Source: Stacks 0B56, 0944.
(blueprint: lem-pur-compact-support-strict-scalar-mate-proper-coordinate)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.StrictTower
namespace WeilConjectures.PurStrictScalar

universe u

/-- Each finite product projection of the proper scalar mate is the corresponding
projection of the normalized coefficient coordinates.  The full proper biproduct
identity follows by `Pi.hom_ext`; this coordinate form is the finite-free column
calculation, using the adjunction counit and the basis normalization.
Source: Stacks 0B56, equation-projection-formula-map, and 0944, lemma-projection-formula.
(blueprint: lem-pur-compact-support-strict-scalar-mate-proper-coordinate). -/
theorem proper_biproduct_coordinate {R S : PurCompactSupport.Coefficients.{u}}
    (a : PurCompactSupport.Change R S) {Z W : Scheme.{u}} (g : Z ⟶ W) (d : ℕ)
    (bW : (∏ᶜ fun _ : Fin d ↦ SheafOfModules.unit ((adicLisseForget W).obj (R.ring W))) ≅
      (pbcRestrict (a.map W)).obj
        (SheafOfModules.unit ((adicLisseForget W).obj (S.ring W))))
    (bZ : (∏ᶜ fun _ : Fin d ↦ SheafOfModules.unit ((adicLisseForget Z).obj (R.ring Z))) ≅
      (pbcRestrict (a.map Z)).obj
        (SheafOfModules.unit ((adicLisseForget Z).obj (S.ring Z))))
    (N : DerivedCategory (pbcModules Z (R.ring Z))) (j : Fin d) :
    (pbcDerivedRestrict (a.map W)).map ((PurCompactSupport.properComparison a g).app N) ≫
        (proEtaleRingRestrictionDerivedDirectImage g
          (R.ring W) (S.ring W) (R.ring Z) (S.ring Z)
          (a.map W) (a.map Z) (R.pull g) (S.pull g) (a.square g)).hom.app
            ((pbcDerivedExtend (a.map Z)).obj N) ≫
        (proEtaleRingDerivedDirectImage g (R.ring W) (R.ring Z) (R.pull g)).map
          ((derivedCoordinates Z (a.map Z) d bZ).hom.app N) ≫
        piComparison
          (proEtaleRingDerivedDirectImage g (R.ring W) (R.ring Z) (R.pull g))
          (fun _ : Fin d ↦ N) ≫
        Pi.π (fun _ : Fin d ↦
          (proEtaleRingDerivedDirectImage g (R.ring W) (R.ring Z) (R.pull g)).obj N) j =
      (derivedCoordinates W (a.map W) d bW).hom.app
        ((proEtaleRingDerivedDirectImage g (R.ring W) (R.ring Z) (R.pull g)).obj N) ≫
        Pi.π (fun _ : Fin d ↦
          (proEtaleRingDerivedDirectImage g (R.ring W) (R.ring Z) (R.pull g)).obj N) j := by
  sorry

end WeilConjectures.PurStrictScalar
