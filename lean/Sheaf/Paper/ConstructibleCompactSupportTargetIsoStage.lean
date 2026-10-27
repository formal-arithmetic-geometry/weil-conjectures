/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficientsData
public import Sheaf.Paper.DerivedPullbackTensorHom

/-! The geometric stagewise comparison underlying target transport.

This is the finite/common-stage part of the target-isomorphism theorem
`(blueprint: lem-sf-constructible-compact-support-target-stage-comparison)`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ConstructibleExceptionalCoefficients
open GeneralAlgebraicallyClosedCoefficients

/-- Stagewise compact-support comparison after an isomorphism of targets.
Source: current blueprint, `cor-coef-verdier-weil-equivariance.proof.md`, final
exceptional-adjunction sentence, finite-stage and common-stage comparison paragraphs.
The theorem records the geometric proper/open comparison and its coefficient descent
on every common finite stage; assembling it over the pair category is separate.
(blueprint: lem-sf-constructible-compact-support-target-stage-comparison).
-/
theorem constructible_compact_support_target_stage_comparison
    (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (D : FiniteFieldDatum.{max u v}) (hl : l ≠ D.p)
    {X Y Z : Scheme.{max u v}}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))] [Z.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of D.k))] [QuasiCompact (Z ↘ Spec (.of D.k))]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    (f : X ⟶ Y) (g : X ⟶ Z) (e : Y ≅ Z) (h : f ≫ e.hom = g)
    [f.IsOver (Spec (.of D.k))] [g.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (S : System.{u, v} l Ω D hl (f := f)) (c : Compactification f)
    (S' : System.{u, v} l Ω D hl (f := g)) (c' : Compactification g) :
    ∃ (q : ∀ i : AlgebraicallyClosedCoefficients.Index l Ω,
      commonInclusion l Ω X i ⋙ (S.ring.operation c .closed).F ≅
        commonInclusion l Ω X i ⋙
          ((S'.ring.operation c' .closed).F ⋙ commonStageDerivedPullback l Ω e.hom)),
      ∀ {i j : AlgebraicallyClosedCoefficients.Index l Ω} (hij : i ≤ j)
        (K : C.{u, v} l Ω X (.rational (commonField l Ω i))),
        (S.ring.operation c .closed).F.map
            (((stageSystem l Ω X).transIso hij).inv.app K) ≫
            (q j).hom.app (((stageSystem l Ω X).T hij).obj K) =
          (q i).hom.app K ≫
            ((S'.ring.operation c' .closed).F ⋙
              commonStageDerivedPullback l Ω e.hom).map
                (((stageSystem l Ω X).transIso hij).inv.app K) := by
  sorry

end WeilConjectures.ConstructibleExceptionalCoefficients
