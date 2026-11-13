/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.ExteriorPower
public import WeilConjectures.RingTheory.KoszulRegularSequence
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import WeilConjectures.AlgebraicGeometry.Modules.Dual

public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
import WeilConjectures.AlgebraicGeometry.SelfTorConormalDualChartIso
import WeilConjectures.RingTheory.SelfTorConormalRegularIso

/-! # The dual exterior-to-self-Tor comparison

## References

* [Stacks Project, Tag 09PQ](https://stacks.math.columbia.edu/tag/09PQ)
* [Stacks Project, Tag 062I](https://stacks.math.columbia.edu/tag/062I)
* [Stacks Project, Tag 0BQY](https://stacks.math.columbia.edu/tag/0BQY)
* [Stacks Project, Tag 06YH](https://stacks.math.columbia.edu/tag/06YH)
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace AlgebraicGeometry

/-- The dual of the conormal-to-self-Tor map is invertible on regular affine charts. -/
theorem selfTor_conormal_dual_chart
    {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [IsClosedImmersion i] (n : ℕ) :
    let B := (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)
    let S := DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0
    let Q := (Scheme.Modules.tensorPullback i).obj
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (-(n : ℤ))).obj
          (S.obj B ⊗ S.obj B))
    ∃ τ : Scheme.Modules.exteriorPower
      ((Scheme.Modules.tensorPullback i).obj i.ker.toModules) n ⟶ Q,
      ∀ (V : Z.Opens) (U : Y.affineOpens)
        (_hU : ∃ (m : ℕ) (f : Fin m → Γ(Y, U.1)),
          Ideal.span (Set.range f) = i.ker.ideal U ∧
            RingTheory.Sequence.IsKoszulRegular f),
        IsIso (((Scheme.Modules.restrictFunctor V.ι).map (Scheme.Modules.dualMap τ)).over
          (V.ι ⁻¹ᵁ (i ⁻¹ᵁ U.1))) := by
  obtain ⟨τ, hτ⟩ := selfTor_conormal_dual_chart_iso i n
  refine ⟨τ, ?_⟩
  intro V U hU
  obtain ⟨r, f, hf, hreg⟩ := hU
  have hc := selfTorConormalComparison_isIso (Γ(Y, U.1) : Type u)
    (i.ker.ideal U) n r f hf hreg
  obtain ⟨a, b, hab⟩ := hτ V U
  rw [hab]
  infer_instance

end AlgebraicGeometry
