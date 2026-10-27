module

public import Sheaf.Paper.ExceptionalFiniteScalarMatesData

/-! # Exceptional finite scalar operation core

Source: Zheng, Propositions 2.23 and 2.29; Stacks 09AL and 07A4
(blueprint: lem-sf-exceptional-finite-scalar-operation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor
namespace WeilConjectures.ExceptionalFiniteScalar

/-- The finite operation package without the final normalization equation.
(blueprint: lem-sf-exceptional-finite-scalar-operation-core) -/
structure OperationCore
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ)
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    (c : Compactification f) where
  F : finiteTorConstructibleCategory l E (n + 1) (Nat.succ_pos n) X ⥤
    finiteTorConstructibleCategory l E (n + 1) (Nat.succ_pos n) Y
  G : finiteTorConstructibleCategory l E (n + 1) (Nat.succ_pos n) Y ⥤
    finiteTorConstructibleCategory l E (n + 1) (Nat.succ_pos n) X
  left : F ⋙ (finiteTorConstructible l E (n + 1) (Nat.succ_pos n) Y).ι ≅
    (finiteTorConstructible l E (n + 1) (Nat.succ_pos n) X).ι ⋙
      sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (n + 1))
  right : G ⋙ (finiteTorConstructible l E (n + 1) (Nat.succ_pos n) X).ι ≅
    (finiteTorConstructible l E (n + 1) (Nat.succ_pos n) Y).ι ⋙
      exceptional (Padic.coefficientExtensionRing l E (n + 1)) c
  adjunction : F ⊣ G
  [leftShift : F.CommShift ℤ]
  [rightShift : G.CommShift ℤ]
  unitShift : adjunction.unit.CommShift ℤ
  counitShift : adjunction.counit.CommShift ℤ
  leftShiftRealization : left.hom.CommShift ℤ

/-- Construction of the core from the existing finite exceptional operations theorem.
The omitted normalization is a separate, strictly smaller transport statement.
(blueprint: lem-sf-exceptional-finite-scalar-operation-core) -/
theorem operationCore_exists
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) {X Y : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) : Nonempty (OperationCore l E n c) := by
  sorry

/-- The normalized Hom formula for the core operation.
(blueprint: lem-sf-exceptional-finite-scalar-operation-normalization) -/
theorem operationCore_normalized
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) {X Y : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) (o : OperationCore l E n c) :
    ∀ (hY : CompactSpace Y)
      (K : finiteTorConstructibleCategory l E (n + 1) (Nat.succ_pos n) X)
      (N : finiteTorConstructibleCategory l E (n + 1) (Nat.succ_pos n) Y)
      (hK : DerivedCategory.TStructure.t.plus
        ((sfIntrinsicDerivedEquivalence X
          (Padic.coefficientExtensionRing l E (n + 1))).inverse.obj K.obj))
      (hN : DerivedCategory.TStructure.t.plus
        ((sfIntrinsicDerivedEquivalence Y
          (Padic.coefficientExtensionRing l E (n + 1))).inverse.obj N.obj))
      (W : X.FixedEtaleOriginWitness (ULift.{u + 1, u}
        (Padic.coefficientExtensionRing l E (n + 1))) ⟨_, hK⟩)
      (v : o.F.obj K ⟶ N),
      (finiteTorConstructible l E (n + 1) (Nat.succ_pos n) X).ι.map
          (o.adjunction.homEquiv K N v) ≫ o.right.hom.app N =
        ((sfIntrinsicDerivedEquivalence X
          (Padic.coefficientExtensionRing l E (n + 1))).counitIso.app K.obj).inv ≫
          (sfIntrinsicDerivedEquivalence X
            (Padic.coefficientExtensionRing l E (n + 1))).functor.map
            (@ProEtale.specifiedExceptionalHomEquiv _ _ _ _ _ _ _ hY c
              (Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification
                (ULift.{u + 1, u}
                  (Padic.coefficientExtensionRing l E (n + 1))) c)
              ⟨_, hK⟩ W ⟨_, hN⟩
              ((leftFixedIso (Padic.coefficientExtensionRing l E (n + 1)) c K.obj).inv ≫
                (sfIntrinsicDerivedEquivalence Y
                  (Padic.coefficientExtensionRing l E (n + 1))).inverse.map
                  (o.left.inv.app K ≫
                    (finiteTorConstructible l E (n + 1) (Nat.succ_pos n) Y).ι.map v))) := by
  sorry

end WeilConjectures.ExceptionalFiniteScalar
