/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.FiniteCoordinates.SystemFiniteEvaluationCoordinates
public import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralCompactificationRealizationData
public import WeilConjectures.AlgebraicGeometry.AmbientProperOpen.AmbientProperOpenCalculus

/-! # Evaluated canonical bridge equation for a refinement mate

Source: Stacks 0F7B; the canonical field of `ProperOpenCoherence`.
(blueprint: lem-sf-system-finite-refinement-mate-coordinates).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.AmbientProperOpen
namespace WeilConjectures.IntegralSystemRealization.FiniteCoordinates

attribute [local implicit_reducible] integralCoefficientSheaf integralCoefficientCommRingSheaf
  scalarReductionTargetDerived

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Applying finite evaluation to the canonical bridge equation for the proper/open
refinement square.  This is the bridge-compatible mate equation before the intrinsic
coefficient presentation and fixed open comparison are cancelled.

Source: Stacks 0F7B; `ProperOpenCoherence.canonical`.
(blueprint: lem-sf-system-finite-refinement-mate-coordinates).
-/
theorem canonicalEvaluation (D : FiniteFieldDatum.{u}) (o : Operations l E)
    (z : Realizations l E D o) (m : ℕ)
    {X Y : Spaces D} {f : X ⟶ Y} [QuasiCompact f.hom.left]
    (c d : Compactification f.hom.left) (r : c.Refinement d)
    [QuasiCompact c.i] [QuasiCompact d.i]
    (M : System l E X.obj.left) :
    (coefficientSequenceDerivedEvaluation l E d.Z m).map
        ((z.properOpen.gamma c.i (𝟙 X.obj.left) r.hom d.i
          (r.i_hom.trans (Category.id_comp _).symm)).app M ≫
          (z.canonicalBridge.push l E r.hom).hom.app
            ((Operations.shriek l E o c.i).obj M) ≫
          (SemilinearProperOpen.R (scalarRings l E) (scalarTransitions l E) r.hom).map
            ((z.canonicalBridge.shriek l E c.i).hom.app M)) =
      (coefficientSequenceDerivedEvaluation l E d.Z m).map
        ((z.canonicalBridge.shriek l E d.i).hom.app
          ((Operations.push l E o (𝟙 X.obj.left)).obj M) ≫
          (SemilinearProperOpen.J (scalarRings l E) (scalarTransitions l E) d.i).map
            ((z.canonicalBridge.push l E (𝟙 X.obj.left)).hom.app M) ≫
          (SemilinearProperOpen.gamma (scalarRings l E) (scalarTransitions l E)
            c.i (𝟙 X.obj.left) r.hom d.i
            (r.i_hom.trans (Category.id_comp _).symm)).app M) := by
  have h := z.properOpen.canonical c.i (𝟙 X.obj.left) r.hom d.i
    (r.i_hom.trans (Category.id_comp _).symm) M
  simpa only [Functor.map_comp, Category.assoc] using
    congrArg (coefficientSequenceDerivedEvaluation l E d.Z m).map h

end WeilConjectures.IntegralSystemRealization.FiniteCoordinates
