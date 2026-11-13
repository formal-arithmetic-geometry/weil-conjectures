/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CohomologyFractionPresentation
public import WeilConjectures.AlgebraicGeometry.Ample
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import WeilConjectures.AlgebraicGeometry.OpenCohomologyFractionZeroComparison
import WeilConjectures.AlgebraicGeometry.OpenCohomologyZeroRestriction
import WeilConjectures.AlgebraicGeometry.AffineOpenSectionFractionLocalization

/-! # Localization of cohomology on an ambient affine open

Source: Stacks Project, Tags 09MR (affine-open paragraph) and 01E1 (locality).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

/-- Degree-zero affine localization, expressed on an open of the ambient scheme
(Stacks, Tags 09MR, 01PW and 01E1). -/
theorem affineOpen_cohomology_localization_zero
    (X : Scheme.{u}) (L : X.Modules) [L.IsInvertible] (s : Γ(L, ⊤))
    (F : X.Modules) [F.IsQuasicoherent]
    (S : X.Opens) (hS : (S : Set X) = nonvanishingLocus L s)
    (U : X.Opens) (hU : IsAffineOpen U) :
    ∃ e : CohomologyFractionPresentation L F s 0 U ≃+
        (RingedSpace.openModuleCohomology X.toRingedSpace 0 (U ⊓ S)).obj F,
      ∀ (n : ℕ) (ξ : (RingedSpace.openModuleCohomology X.toRingedSpace 0 U).obj
          (F ⊗ L.tensorPow n : X.Modules)),
        (RingedSpace.openModuleCohomology X.toRingedSpace 0 (U ⊓ S)).map
            (((ρ_ F).inv ≫ F ◁ tensorPowSection (homOfGlobalSection L s) n) :
              F ⟶ (F ⊗ L.tensorPow n : X.Modules))
            (e (cohomologyFraction L F s 0 U n ξ)) =
          (RingedSpace.openModuleCohomologyRestriction X.toRingedSpace 0
            (homOfLE (inf_le_left : U ⊓ S ≤ U))).app (F ⊗ L.tensorPow n : X.Modules) ξ := by
  obtain ⟨q, hq⟩ := openCohomologyFraction_zero_comparison X L F s U
  obtain ⟨a, ha⟩ := affineOpen_sectionFraction_localization X L s F S hS U hU
  let c := ((RingedSpace.openCohomologyZeroSectionsIso X.toRingedSpace (U ⊓ S)).app
    F).addCommGroupIsoToAddEquiv
  refine ⟨(q.trans a).trans c.symm, ?_⟩
  intro n ξ
  let T : X.Modules := F ⊗ L.tensorPow n
  let f : F ⟶ T := (ρ_ F).inv ≫ F ◁ tensorPowSection (homOfGlobalSection L s) n
  apply ((RingedSpace.openCohomologyZeroSectionsIso X.toRingedSpace (U ⊓ S)).app
    T).addCommGroupIsoToAddEquiv.injective
  change (RingedSpace.openCohomologyZeroSectionsIso X.toRingedSpace (U ⊓ S)).hom.app T
      ((RingedSpace.openModuleCohomology X.toRingedSpace 0 (U ⊓ S)).map f
        (c.symm (a (q (cohomologyFraction L F s 0 U n ξ))))) = _
  rw [show (RingedSpace.openCohomologyZeroSectionsIso X.toRingedSpace (U ⊓ S)).hom.app T
      ((RingedSpace.openModuleCohomology X.toRingedSpace 0 (U ⊓ S)).map f
        (c.symm (a (q (cohomologyFraction L F s 0 U n ξ))))) =
        f.app (U ⊓ S) (c (c.symm (a (q (cohomologyFraction L F s 0 U n ξ))))) from
    congrArg (fun g ↦ g (c.symm (a (q (cohomologyFraction L F s 0 U n ξ)))))
      (RingedSpace.openCohomologyZeroSectionsIso_naturality
      X.toRingedSpace (U ⊓ S) f)]
  rw [c.apply_symm_apply, hq]
  exact (ha n _).trans
    (RingedSpace.openCohomologyZeroSectionsIso_restriction X.toRingedSpace
      (homOfLE (inf_le_left : U ⊓ S ≤ U)) T ξ).symm

end AlgebraicGeometry.Scheme.Modules
