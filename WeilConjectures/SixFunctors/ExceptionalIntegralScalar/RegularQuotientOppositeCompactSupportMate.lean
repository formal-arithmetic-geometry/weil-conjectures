/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ExceptionalIntegralScalar.ExceptionalIntegralLeftScalarData

/-! # The opposite compact-support mate for a regular quotient

## References

* Zheng, Lemma 5.22 and Proposition 5.26
* [Stacks, Tag 07A6]
* [Stacks, Tag 0A70]
* [Stacks, Tag 0A71]
* [Stacks, Tag 0GL6]
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

/-- The opposite mate of the prescribed left scalar comparison is invertible
under reverse regular-quotient adjunctions. -/
theorem regularQuotientOppositeCompactSupportMate
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
    (d : LeftMates l Ω c operation left) (E : FieldStage.{u} l) (n : ℕ)
    (RX : C.{u} l Ω X (.finite E ⟨n + 1, Nat.succ_pos n⟩) ⥤
          C.{u} l Ω X (.integral E))
      (RY : C.{u} l Ω Y (.finite E ⟨n + 1, Nat.succ_pos n⟩) ⥤
          C.{u} l Ω Y (.integral E))
      (ax : RX ⊣ (d.scalar (s := .integral E)
        (t := .finite E ⟨n + 1, Nat.succ_pos n⟩)
        (PurCompactSupport.reduction l E.carrier (n + 1) (Nat.succ_pos n))
        (Allowed.reduction E ⟨n + 1, Nat.succ_pos n⟩) true).functor)
      (ay : RY ⊣ (d.scalar (s := .integral E)
        (t := .finite E ⟨n + 1, Nat.succ_pos n⟩)
        (PurCompactSupport.reduction l E.carrier (n + 1) (Nat.succ_pos n))
        (Allowed.reduction E ⟨n + 1, Nat.succ_pos n⟩) false).functor) :
      IsIso ((mateEquiv ax ay).symm
        (d.q (s := .integral E) (t := .finite E ⟨n + 1, Nat.succ_pos n⟩)
          (PurCompactSupport.reduction l E.carrier (n + 1) (Nat.succ_pos n))
          (Allowed.reduction E ⟨n + 1, Nat.succ_pos n⟩)).inv) := by
  sorry

end WeilConjectures.ExceptionalIntegralScalar
