/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M5
-/
module

public import Sheaf.Paper.ExceptionalIntegralReductionEvaluation

/-! # Left exceptional mate under normalized finite reduction

Source: Zheng, Lemma 5.22 and Proposition 5.26.
(blueprint: lem-sf-exceptional-integral-reduction-left-compatibility)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ExceptionalIntegralScalar
open ConstructibleExceptionalCoefficients
variable (l : ℕ) [Fact l.Prime]
variable (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- The canonical finite evaluation intertwines the left exceptional scalar mate.
Source: Zheng, Lemma 5.22 and Proposition 5.26, reduction compatibility.
Proof: apply the faithful finite full inclusion and substitute the scalar equality
realizations and the definition of integralReductionEvaluation. The source and target
finite tensors are related by PurCompactSupport.finiteReductionIso, the unique
comparison preserving the scalar adjunction units. Substitute d.comparison_normalized:
the left path becomes the ordinary proper scalar mate followed by the open tensor map.
The recorded integral compact-support identification identifies its reduction with
the same proper/open mate. The transport.integral_system_normalized square identifies
that recorded identification with the reconstruction realization; transport.reductionF_eq
and transport.evaluation_support then identify the right path with the same map.
Cancel the finite left realization and the invertible scalar realizations. This uses
whole-system naturality before evaluation, never faithfulness of finite evaluations.
(blueprint: lem-sf-exceptional-integral-reduction-left-compatibility). -/
theorem integralReductionLeftCompatibility
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] (c : Compactification f)
    (operation : ∀ s : RingStage.{u} l, Operation.{u} l Ω X Y (s.stage l))
    (left : ∀ s : RingStage.{u} l, LeftRealization.{u} l Ω c s (operation s))
    (transport : Transported l Ω D hl c operation left)
    (d : Mates l Ω c operation left) (E : FieldStage.{u} l) (n : ℕ) :
    ∀ K : C.{u} l Ω X (.integral E),
      (Mates.q l Ω d (s := .integral E) (t := .finite E ⟨n + 1, Nat.succ_pos n⟩)
        (PurCompactSupport.reduction l E.carrier (n + 1) (Nat.succ_pos n))
        (Allowed.reduction E ⟨n + 1, Nat.succ_pos n⟩)).hom.app K ≫
        (operation (.finite E ⟨n + 1, Nat.succ_pos n⟩)).F.map
          ((integralReductionEvaluation l Ω d E n true
            (transport.reconstruction E true)).hom.app K) =
      (integralReductionEvaluation l Ω d E n false
        (transport.reconstruction E false)).hom.app ((operation (.integral E)).F.obj K) ≫
        ((transport.reconstruction E false).evaluation n).map
          ((transport.reductionF E).hom.app K) ≫
        (transport.evaluationF E n).hom.app
          ((transport.reconstruction E true).equivalence.functor.obj K) := by
  sorry

end WeilConjectures.ExceptionalIntegralScalar
