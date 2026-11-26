/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Coefficient.ConstructibleExceptionalCoefficientAssemblyData
public import WeilConjectures.SixFunctors.PurCompactSupport.RefinementOpenRestriction
import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Ring.RingOpenMapNormalizedRefinement
import WeilConjectures.SixFunctors.PurCompactSupport.RingOpenMapOpenUnit

/-! # Invertibility of the canonical open map on the finite-Tor domain

## Implementation details

For finite coefficients the cone of `refinementOpenMap` restricts to zero on `X` (open-unit and
restriction calculation) and on its complement (proper base change), hence vanishes by
open-closed conservativity. For completed integral coefficients the same word is applied as a
semilinear-system map to the normalized strict reduction system; conservative system
evaluations make it invertible, and the total limit is identified with `refinementOpenMap`. No
equality of integral arrows is deduced from agreement of their reductions. Naturality, shifts
and the normalization equation are proved separately from the explicit formula.

## References

* [Zheng, Section 5, Lemma 5.13 and Constructions 5.14–5.15]
* [Stacks, Tag 0F7B]
* [Stacks, Tag 0F7I]
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] HasDerivedCategory.standard Padic
universe u v
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ConstructibleExceptionalCoefficients
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- The canonical inverse-transpose open map is invertible on each finite-Tor input. -/
theorem ringOpenMap_isIso
    (D : FiniteFieldDatum.{max u v}) (hl : l ≠ D.p)
    {X Y : Scheme.{max u v}} {f : X ⟶ Y}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    {c d : Compactification f} (r : c.Refinement d) (s : RingStage.{max u v} l)
    (hi : (s.coefficients l).pull (c.i ≫ r.hom) =
      proEtaleRingCompositeCoefficients c.i r.hom
        ((s.coefficients l).ring d.Z) ((s.coefficients l).ring c.Z)
        ((s.coefficients l).ring X)
        ((s.coefficients l).pull r.hom) ((s.coefficients l).pull c.i))
    (K : C.{u, v} l Ω X (s.stage l)) :
    IsIso ((PurCompactSupport.refinementOpenMap (s.coefficients l) r hi).app
      ((RingStage.inclusion.{u, v} l Ω X s).obj K)) := by
  obtain ⟨ε, hε⟩ := exists_normalized_refinement_iso l Ω D hl r s hi K
  have hu : IsIso (PurCompactSupport.openDerivedAdjunction (s.coefficients l) c.i).unit :=
    PurCompactSupport.openDerivedAdjunction_unit_isIso (s.coefficients l) c.i
  let _ : IsIso (PurCompactSupport.openDerivedAdjunction (s.coefficients l) c.i).unit := hu
  have hcomp : IsIso ((PurCompactSupport.openDerivedAdjunction (s.coefficients l) d.i).homEquiv _ _
      ε.hom ≫ PurCompactSupport.refinementRestriction (s.coefficients l) r hi
        ((RingStage.inclusion.{u, v} l Ω X s).obj K)) := by
    rw [hε]
    infer_instance
  obtain ⟨θ, hθ, hθiso, _⟩ :=
    PurCompactSupport.exists_refinementRestriction (s.coefficients l) r hi
  have hres : IsIso (PurCompactSupport.refinementRestriction (s.coefficients l) r hi
      ((RingStage.inclusion.{u, v} l Ω X s).obj K)) := by
    let _ : IsIso θ := hθiso
    rw [← hθ]
    infer_instance
  have heq : (PurCompactSupport.refinementOpenMap (s.coefficients l) r hi).app
      ((RingStage.inclusion.{u, v} l Ω X s).obj K) = ε.hom := by
    apply ((PurCompactSupport.openDerivedAdjunction (s.coefficients l) d.i).homEquiv
      _ _).injective
    apply (cancel_mono
      (PurCompactSupport.refinementRestriction (s.coefficients l) r hi
        ((RingStage.inclusion.{u, v} l Ω X s).obj K))).1
    rw [PurCompactSupport.refinementOpenMap_normalization]
    exact hε.symm
  rw [heq]
  infer_instance

end WeilConjectures.ConstructibleExceptionalCoefficients
