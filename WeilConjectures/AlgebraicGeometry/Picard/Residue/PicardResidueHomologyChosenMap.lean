/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineResidueCycleHomology
public import WeilConjectures.AlgebraicGeometry.DerivedFiberBetti
public import WeilConjectures.AlgebraicGeometry.PerfectComplex
import WeilConjectures.AlgebraicGeometry.PerfectAffineMapRepresentative
public import WeilConjectures.AlgebraicGeometry.Derived.DerivedFiberCohomologyFunctor

/-! # Choice of an affine residue representative

Source: Stacks Project, Tags 08CR and 01IB.
(blueprint: new-picard-residue-homology-chosen-geometric-maps)

This is the per-index choice step in the geometric residue comparison. -/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Choose one chain representative and one target residue comparison from affine
naturality. The conclusion is only the per-index representative square. -/
theorem picard_residue_homology_choose_model_map
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    [∀ (Y : Scheme.{v}) (U : Y.Opens), HasDerivedCategory.{v + 1}
      (SheafOfModules.{v} ((moduleRings Y.toRingedSpace).over U))]
    (W : Scheme.{v}) (w : W) (U : W.Opens) (hU : IsAffineOpen U)
    (hwU : w ∈ U) (p : Ideal Γ(W, U)) [p.IsPrime]
    (hp : p = RingHom.ker (W.evaluation U w hwU).hom)
    (E E' : schemeDerivedCategory W) (b : E ⟶ E')
    (K C : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ)
    (hK : IsStrictlyPerfect W U K) (hC : IsStrictlyPerfect W U C)
    (m : (SheafOfModules.overFunctor.{v}
      (moduleRings W.toRingedSpace) U).mapDerivedCategory.obj E ≅
        DerivedCategory.Q.obj K)
    (m' : (SheafOfModules.overFunctor.{v}
      (moduleRings W.toRingedSpace) U).mapDerivedCategory.obj E' ≅
        DerivedCategory.Q.obj C)
    (eK : affineResidueCycleHomology W U p K ≃+
      derivedFiberCohomology W E 1 w)
    (hNat : ∃ eC : affineResidueCycleHomology W U p C ≃+
        derivedFiberCohomology W E' 1 w,
      ∀ (φ : K ⟶ C),
        DerivedCategory.Q.map φ = m.inv ≫
          (SheafOfModules.overFunctor.{v}
            (moduleRings W.toRingedSpace) U).mapDerivedCategory.map b ≫ m'.hom →
          ∀ z, eC (affineResidueCycleHomologyMap φ z) =
            (derivedFiberCohomologyFunctor W w 1).map b (eK z)) :
    ∃ eC : affineResidueCycleHomology W U p C ≃+
        derivedFiberCohomology W E' 1 w,
      ∃ φ : K ⟶ C, ∀ z, eC (affineResidueCycleHomologyMap φ z) =
        (derivedFiberCohomologyFunctor W w 1).map b (eK z) := by
  let _hp := hp
  obtain ⟨eC, heC⟩ := hNat
  obtain ⟨φ, hφ⟩ := perfect_affine_map_representative W U hU K C hK hC
    (m.inv ≫
      (SheafOfModules.overFunctor.{v}
        (moduleRings W.toRingedSpace) U).mapDerivedCategory.map b ≫ m'.hom)
  exact ⟨eC, φ, heC φ hφ⟩

end AlgebraicGeometry.Scheme
