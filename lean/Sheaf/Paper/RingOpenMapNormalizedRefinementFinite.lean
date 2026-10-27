/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.ConstructibleExceptionalCoefficientAssemblyData
public import Sheaf.Paper.RefinementOpenRestriction

/-! # Finite coefficient normalized refinement comparisons -/

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

/-- The finite coefficient part of the normalized refinement comparison.

Source: the finite coefficient construction in Zheng Section 5, Lemma 5.13 and
Constructions 5.14--5.15 (Stacks Tags 0F7B and 0F7I).
(blueprint: lem-sf-ring-open-map-normalized-refinement-finite).

Proof: construct the comparison from the finite coefficient proper/open refinement
word. Its transpose is the open adjunction unit after the canonical restriction;
the finite-Tor and etale-origin calculation makes this word invertible. -/
theorem exists_normalized_refinement_iso_finite
    (D : FiniteFieldDatum.{max u v}) (hl : l ≠ D.p)
    {X Y : Scheme.{max u v}} {f : X ⟶ Y}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    {c d : Compactification f} (r : c.Refinement d)
    (E : FieldStage.{max u v} l) (n : ℕ+)
    (hi : ((RingStage.finite E n).coefficients l).pull (c.i ≫ r.hom) =
      proEtaleRingCompositeCoefficients c.i r.hom
        (((RingStage.finite E n).coefficients l).ring d.Z)
        (((RingStage.finite E n).coefficients l).ring c.Z)
        (((RingStage.finite E n).coefficients l).ring X)
        (((RingStage.finite E n).coefficients l).pull r.hom)
        (((RingStage.finite E n).coefficients l).pull c.i))
    (K : C.{u, v} l Ω X (.finite E n)) :
    ∃ ε :
        (PurCompactSupport.openExtension
          ((RingStage.finite E n).coefficients l) d.i).mapDerivedCategory.obj
          ((RingStage.inclusion.{u, v} l Ω X (RingStage.finite E n)).obj K) ≅
        (PurCompactSupport.push ((RingStage.finite E n).coefficients l) r.hom).obj
          ((PurCompactSupport.openExtension
            ((RingStage.finite E n).coefficients l) c.i).mapDerivedCategory.obj
            ((RingStage.inclusion.{u, v} l Ω X (RingStage.finite E n)).obj K)),
      (PurCompactSupport.openDerivedAdjunction
        ((RingStage.finite E n).coefficients l) d.i).homEquiv _ _ ε.hom ≫
          PurCompactSupport.refinementRestriction ((RingStage.finite E n).coefficients l) r hi
            ((RingStage.inclusion.{u, v} l Ω X (RingStage.finite E n)).obj K) =
        (PurCompactSupport.openDerivedAdjunction
          ((RingStage.finite E n).coefficients l) c.i).unit.app
          ((RingStage.inclusion.{u, v} l Ω X (RingStage.finite E n)).obj K) := by
  sorry

end WeilConjectures.ConstructibleExceptionalCoefficients
