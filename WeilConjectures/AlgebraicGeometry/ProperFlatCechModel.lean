/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections
import WeilConjectures.AlgebraicGeometry.DescentFirstProperFlatCechModel

/-! # Bounded flat models for proper relatively flat cohomology

The geometric, pseudo-coherent part of the construction of Mumford's complex.

## References

* [Stacks Project, Tags 0A1H, 0B91 and 064U](https://stacks.math.columbia.edu/tag/0A1H)
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- A proper finitely presented morphism and a finitely presented relatively flat module
admit, near each base point, a bounded nonnegative flat complex `C` computing every
base-changed higher direct image. It has a bounded-above finite-free resolution `Q`.
Unlike the desired finite-free model, `C` need not have finite terms, and `Q` can have
infinitely many nonzero negative terms. -/
theorem exists_proper_flat_cech_model {X T : Scheme.{u}} (f : X ⟶ T) (F : X.Modules)
    [IsProper f] [LocallyOfFinitePresentation f] [QuasiCompact f]
    [HasInjectiveResolutions X.Modules] [F.IsFinitePresentation]
    (hF : F.IsFlatOver f) (t : T) :
    ∃ (U : T.Opens) (C Q : CochainComplex U.toScheme.Modules ℤ) (d : ℕ),
      t ∈ U ∧ C.IsStrictlyGE 0 ∧ C.IsStrictlyLE d ∧
      (∀ n : ℤ, (C.X n).IsFlatOver (𝟙 U.toScheme)) ∧ Q.IsStrictlyLE d ∧
      (∀ n : ℤ, ∃ r : ℕ,
        Nonempty (Q.X n ≅ SheafOfModules.free
          (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin r)))) ∧
      (∃ e : Q ⟶ C, QuasiIso e) ∧
      ∀ {T' X' : Scheme.{u}} (g : T' ⟶ U.toScheme) (g' : X' ⟶ X) (f' : X' ⟶ T')
        [HasInjectiveResolutions X'.Modules], IsPullback g' f' f (g ≫ U.ι) → ∀ q : ℕ,
        Nonempty ((((Modules.pullback g).mapHomologicalComplex _).obj C).homology q ≅
          (higherDirectImage f' q).obj ((Modules.pullback g').obj F))  := by
  exact descent_first_exists_proper_flat_cech_model f F hF t

end AlgebraicGeometry.Scheme.Modules
