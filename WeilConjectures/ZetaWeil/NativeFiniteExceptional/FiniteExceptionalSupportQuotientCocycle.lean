/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ZetaWeil.NativeFiniteExceptional.FiniteExceptionalQuotientScalarCoherence

/-! # Cocycle for intrinsic finite support quotient maps

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-poincare-duality/
sec-perfect-complexes-on-the-point-and-two-exchange-formulas/sk-def-ops/sk-thm-sf-package/
lem-coef-finite-exceptional.proof.md, final paragraph
(blueprint: lem-sf-finite-exceptional-support-quotient-cocycle).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme Opposite
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary
open scoped CategoryTheory.Obj CategoryTheory.Functor MonoidalCategory

namespace WeilConjectures.NativeFiniteExceptional

variable (ell : ℕ) [Fact ell.Prime] (E : Type u) [Field E]
  [Algebra (Padic ell) E] [FiniteDimensional (Padic ell) E]
local instance finiteSupportTopology (n : ℕ) : TopologicalSpace (Ring ell E n) := ⊥
local instance finiteSupportDiscrete (n : ℕ) : DiscreteTopology (Ring ell E n) := ⟨rfl⟩
local instance finiteSupportTopologicalRing (n : ℕ) : IsTopologicalRing (Ring ell E n) :=
  inferInstance
local instance finiteSupportFinite (n : ℕ) : Finite (Ring ell E n) :=
  Padic.finite_coefficientExtensionRing ell E (n + 1) (Nat.succ_pos n)

variable (D : FiniteFieldDatum.{u}) (hell : ell ≠ D.p)
variable {X Y : Over (Spec (.of D.k))}
  [Xft : LocallyOfFiniteType X.hom] [Xqc : QuasiCompact X.hom] [Xsep : IsSeparated X.hom]
  [Yft : LocallyOfFiniteType Y.hom] [Yqc : QuasiCompact Y.hom] [Ysep : IsSeparated Y.hom]
  (f : X ⟶ Y) [fsep : IsSeparated f.left]
  [fft : LocallyOfFiniteType f.left] [fqc : QuasiCompact f.left]
  (c : Compactification f.left)
  (encoding : ∀ (n : ℕ) (T : Scheme.{u}), Encoding (Ring ell E n) T)

/-- Intrinsic support comparisons compose through the canonical scalar associator, and
identity support comparison is the normalized scalar unit.
Source: latest blueprint, `lem-coef-finite-exceptional.proof.md`, final paragraph:
tensor associativity and unit normalization of the compact-support comparison
(blueprint: lem-sf-finite-exceptional-support-quotient-cocycle).

Proof plan: write the intrinsic comparison as the restriction of the actual proper/open
compact-support map. The ringed direct-image mate and open scalar comparison satisfy their
composition equations for arbitrary quotient maps, and their identity equations give the
unit. Naturality moves the intermediate comparison through the proper mate; functoriality
then yields the direct comparison. Restriction through the full finite domains preserves
these equalities. The proof is intentionally postponed at stage 2. -/
theorem supportMap_cocycle :
    (∀ {r m n : ℕ} (h : m ≤ r) (k : n ≤ m)
      (K : (domain ell E X.left r).FullSubcategory),
      (Q ell E Y.left k).map
          ((qMap ell E D hell f c encoding h).app K) ≫
        (qMap ell E D hell f c encoding k).app ((Q ell E X.left h).obj K) ≫
        (F ell E D hell f c encoding n).map
          ((finiteSupportTower ell E X.left h k).hom.app K) =
      (finiteSupportTower ell E Y.left h k).hom.app ((F ell E D hell f c encoding r).obj K) ≫
        (qMap ell E D hell f c encoding (k.trans h)).app K) ∧
    (∀ (n : ℕ) (K : (domain ell E X.left n).FullSubcategory),
      (qMap ell E D hell f c encoding (le_refl n)).app K ≫
        (F ell E D hell f c encoding n).map
          ((finiteSupportUnit ell E X.left n).hom.app K) =
      (finiteSupportUnit ell E Y.left n).hom.app
        ((F ell E D hell f c encoding n).obj K)) := by
  sorry

end WeilConjectures.NativeFiniteExceptional
