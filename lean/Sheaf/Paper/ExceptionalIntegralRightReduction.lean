/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.ExceptionalIntegralScalarMates

/-! # Finite reduction of the fixed exceptional right adjoint

This statement concerns only the right finite reduction comparison. The integral
and finite adjoints and the two endpoint reconstruction equivalences are fixed.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ExceptionalIntegralScalar
open ConstructibleExceptionalCoefficients

/-- Finite reduction commutes with the fixed integral exceptional right adjoint.
Source: Zheng, Construction 4.1, Lemma 5.22 and Propositions 5.24 and 5.26(3).
(blueprint: lem-sf-exceptional-integral-right-reduction)

Proof: the reconstruction reduction and evaluation equations identify each
endpoint composite with actual derived extension to the positive finite quotient.
Transport the ordinary etale strict-system exceptional adjunction through the
etale/pro-etale comparison, as in exceptionalSystemTransport. Lemma 5.22 identifies
its finite evaluations and quotient mates with the finite exceptional adjoints;
Proposition 5.24 preserves normalization. Restrict to the common constructible,
cohomological and Tor bounds and apply the actual reduction/limit equivalence.
The supplied left realizations identify the resulting integral and finite left
functors with the fixed ones. Uniqueness of their right adjoints then identifies
the right functors, and Proposition 5.26(3) gives the displayed natural reduction
isomorphism. Use the actual unit and counit in these identifications, so all
comparisons exist on whole systems and no faithfulness of finite evaluation is
asserted. Empty schemes give the zero comparison; n always means exponent n+1. -/
theorem exists_exceptional_integral_right_reduction
    (l : ℕ) [Fact l.Prime] (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω]
    [IsAlgClosure (Padic l) Ω] (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] (c : Compactification f)
    (E : FieldStage.{u} l)
    (integral : Operation.{u} l Ω X Y (.integral E))
    (finite : ∀ n : ℕ, Operation.{u} l Ω X Y (.finite E ⟨n + 1, Nat.succ_pos n⟩))
    (leftIntegral : LeftRealization.{u} l Ω c (.integral E) integral)
    (leftFinite : ∀ n : ℕ,
      LeftRealization.{u} l Ω c (.finite E ⟨n + 1, Nat.succ_pos n⟩) (finite n))
    (RX : Reconstruction l E X) (RY : Reconstruction l E Y) :
    Nonempty (∀ n : ℕ,
      integral.G ⋙ RX.equivalence.functor ⋙ RX.evaluation n ≅
        RY.equivalence.functor ⋙ RY.evaluation n ⋙ (finite n).G) := by
  sorry

end WeilConjectures.ExceptionalIntegralScalar
