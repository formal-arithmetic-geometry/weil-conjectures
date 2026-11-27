/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ExceptionalFiniteScalar.ExceptionalFiniteScalarMatesData
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Subcategory
import WeilConjectures.SixFunctors.ExceptionalFiniteScalar.FiniteScalarPreservation
import WeilConjectures.SixFunctors.ExceptionalFiniteScalar.FiniteScalarTorInterval

/-!
# Existence of the finite scalar restriction package

## Implementation details

For `WeilConjectures.ExceptionalFiniteScalar.finiteScalar_exists`: let `K` be constructible of
Tor amplitude in `[r, s]` over `A`. Since `T` is of finite type over `k` and `l ≠ p`, `l` is
invertible on `T`, so `K` is represented by a bounded complex `P` of flat constructible
`A`-modules in degrees `[r, s]`. A bounded complex of flat sheaves is K-flat, so `K ⊗^L_A B` is
computed by `P ⊗_A B`, whose terms are flat over `B` and constructible. Hence `K ⊗^L_A B` is
constructible of Tor amplitude in `[r, s]` over `B`. The functor is the full-subcategory lift
of `ι ⋙ S_a`, and its shift is induced through the fully faithful `ι` from the ambient derived
tensor shift. No flatness of the coefficient map is assumed.

## References

* [Stacks, Tag 06YY]
* [Stacks, Tag 09AL]
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor
namespace WeilConjectures.ExceptionalFiniteScalar

/-- The literal finite scalar restriction package exists at every finite-type `k`-scheme.

The package records preservation of constructibility and the Tor interval, the
equality realization of the restricted ambient tensor functor, and its inherited
commuting shift. -/
theorem finiteScalar_exists
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E L : Type u) [Field E] [Field L] [Algebra (Padic l) E] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
    (n m : ℕ)
    (a : Padic.coefficientExtensionRing l E (n + 1) →+*
      Padic.coefficientExtensionRing l L (m + 1))
    (T : Scheme.{u}) [T.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (T ↘ Spec (.of D.k))] [QuasiCompact (T ↘ Spec (.of D.k))] :
    Nonempty (Scalar l E L n m a T) := by
  classical
  have : (finiteTorConstructible l E (n + 1) (Nat.succ_pos n) T).IsStableUnderShift ℤ :=
    inferInstance
  have : (finiteTorConstructible l L (m + 1) (Nat.succ_pos m) T).IsStableUnderShift ℤ :=
    inferInstance
  let scalarShift : (pbcDerivedExtend (proEtaleConstantRingMap (T := T) a)).CommShift ℤ :=
    WeilConjectures.PurCompactSupport.scalarCommShift _
  let : (pbcDerivedExtend (proEtaleConstantRingMap (T := T) a)).CommShift ℤ := scalarShift
  let hpres : ∀ K : finiteTorConstructibleCategory l E (n + 1) (Nat.succ_pos n) T,
      finiteTorConstructible l L (m + 1) (Nat.succ_pos m) T
        ((pbcDerivedExtend (proEtaleConstantRingMap (T := T) a)).obj K.obj) :=
    finiteScalar_preserves D l _hl E L n m a T
  let hfun : ∀ X, finiteTorConstructible l E (n + 1) (Nat.succ_pos n) T X →
      finiteTorConstructible l L (m + 1) (Nat.succ_pos m) T
        ((pbcDerivedExtend (proEtaleConstantRingMap (T := T) a)).obj X) := by
    intro X hX
    exact hpres ⟨X, hX⟩
  let hcomm :
      (restrictScalar l E L n m T a hpres).CommShift ℤ := by
    change ((finiteTorConstructible l E (n + 1) (Nat.succ_pos n) T).liftFullSubcategory
      (finiteTorConstructible l L (m + 1) (Nat.succ_pos m) T)
      (pbcDerivedExtend (proEtaleConstantRingMap (T := T) a)) hfun).CommShift ℤ
    exact CategoryTheory.ObjectProperty.commShiftLiftFullSubcategory
      (finiteTorConstructible l E (n + 1) (Nat.succ_pos n) T)
      (finiteTorConstructible l L (m + 1) (Nat.succ_pos m) T)
      (pbcDerivedExtend (proEtaleConstantRingMap (T := T) a)) hfun
  let heq : restrictScalar l E L n m T a hpres ⋙
      (finiteTorConstructible l L (m + 1) (Nat.succ_pos m) T).ι =
      (finiteTorConstructible l E (n + 1) (Nat.succ_pos n) T).ι ⋙
        pbcDerivedExtend (proEtaleConstantRingMap (T := T) a) := by
    rfl
  refine ⟨{
    preserves := hpres
    torInterval := by
      intro K r s hK
      exact finiteScalar_torInterval D l _hl E L n m a T K r s hK
    scalar_eq := by
      exact heq
    commShift := hcomm
    realizationShift := by
      change NatTrans.CommShift
        ((CategoryTheory.ObjectProperty.liftFullSubcategoryCompιIso
          (finiteTorConstructible l E (n + 1) (Nat.succ_pos n) T)
          (finiteTorConstructible l L (m + 1) (Nat.succ_pos m) T)
          (pbcDerivedExtend (proEtaleConstantRingMap (T := T) a)) hfun).hom) ℤ
      infer_instance
  }⟩

end WeilConjectures.ExceptionalFiniteScalar
