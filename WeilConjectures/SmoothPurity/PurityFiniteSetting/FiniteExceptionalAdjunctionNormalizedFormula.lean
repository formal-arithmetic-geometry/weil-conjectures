/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.NativeFiniteExceptional.NativeFiniteExceptionalConstructions
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import WeilConjectures.SmoothPurity.NativeCompactSupport.NativeCompactSupportComparison

/-!
# Displayed normalized Hom formula for native finite exceptional adjunctions

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-ladic-summary/sec-change-of-finite-coefficients/sk-lem-sp-reduction/
thm-pur-finite-reduction-of-purity.proof.md, Step 4
(blueprint: lem-route-finite-exceptional-adjunction-normalized-formula).

The coefficient presentation is the normalized section-action encoding of the actual
finite quotient. No withdrawn constant-ring exceptional package is imported.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Scheme
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary

namespace WeilConjectures

open WeilConjectures.NativeFiniteExceptional

variable (P : PurityFiniteSetting.{u}) {X Y : Over (Spec (.of P.field.k))}
  [Xft : LocallyOfFiniteType X.hom] [Xqc : QuasiCompact X.hom]
  [Xsep : IsSeparated X.hom] [Yft : LocallyOfFiniteType Y.hom]
  [Yqc : QuasiCompact Y.hom] [Ysep : IsSeparated Y.hom]
  (f : X ⟶ Y) [fsep : IsSeparated f.left]
  [fft : LocallyOfFiniteType f.left] [fqc : QuasiCompact f.left]
  (c : Compactification f.left)

/-- The selected native finite exceptional adjunction has its displayed normalized
Hom-equivalence formula, including the coefficient-equivalence unit.

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-ladic-summary/sec-change-of-finite-coefficients/sk-lem-sp-reduction/
thm-pur-finite-reduction-of-purity.proof.md, Step 4; native finite exceptional
normalization in the coefficient package
(blueprint: lem-route-finite-exceptional-adjunction-normalized-formula).
Proof: extract the normalization property of the unique adjunction selected by
`NativeFiniteExceptional.adjunction_existsUnique`. Unfold `AdjunctionNormalized`
and specialize to M, L, hM, hL, W and v. The full-subcategory inclusion sends the
lifted Hom input to comparison.hom.app M followed by the encoding inverse image
of v. The right side is precisely the specified exceptional Hom chain followed
by the exceptional image of the inverse encoding counit. For the inverse encoding,
that inverse counit is its unit, so it must be retained. Forget the subcategory
lifts to obtain the displayed equality. The chosen ordinary exceptional functor is
`sfFiniteExceptionalAt`, so no alternate right-adjoint comparison is necessary.
This is a property of the selected normalized adjunction; every origin witness is
allowed and no origin condition is imposed on L. No counit identity is asserted.
-/
theorem PurityFiniteSetting.finiteExceptionalAdjunction_normalized_formula (r : ℕ) :
    let ell := P.coefficients.l
    let E := P.extension
    let A := NativeFiniteExceptional.Ring ell E
    letI (n : ℕ) : TopologicalSpace (A n) := ⊥
    letI (n : ℕ) : DiscreteTopology (A n) := ⟨rfl⟩
    letI (n : ℕ) : IsTopologicalRing (A n) := inferInstance
    letI (n : ℕ) : Finite (A n) :=
      Padic.finite_coefficientExtensionRing ell E (n + 1) (Nat.succ_pos n)
    letI : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
    letI : (Etale.rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} (ULift.{u + 1} (A r))) c).IsLeftAdjoint :=
      Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification
        (ULift.{u + 1} (A r)) c
    ∀ (encoding : ∀ (n : ℕ) (T : Scheme.{u}), Encoding (A n) T)
    (M : _root_.DerivedCategory.Plus
      (Sheaf (ProEt.topology X.left) (ModuleCat.{u + 1} (ULift.{u + 1} (A r)))))
    (L : _root_.DerivedCategory.Plus
      (Sheaf (ProEt.topology Y.left) (ModuleCat.{u + 1} (ULift.{u + 1} (A r)))))
    (hM : domain ell E X.left r ((encoding r X.left).fixedDerived.inverse.obj M.obj))
    (hL : domain ell E Y.left r ((encoding r Y.left).fixedDerived.inverse.obj L.obj))
    (W : FixedEtaleOriginWitness X.left (ULift.{u + 1} (A r)) M)
    (v : (NativeCompactSupport.fixedSupport (A r) c).obj M.obj ⟶ L.obj),
    ((adjunction ell E P.field P.coefficients.different f c encoding r).homEquiv
      ⟨_, hM⟩ ⟨_, hL⟩
      (ObjectProperty.homMk
        ((NativeCompactSupport.comparison (A r) (encoding r) c).hom.app M.obj ≫
          (encoding r Y.left).fixedDerived.inverse.map v))).hom =
      (encoding r X.left).fixedDerived.inverse.map
        (specifiedExceptionalHomEquiv (ULift.{u + 1} (A r)) c M W L v ≫
          (sfFiniteExceptionalAt (ULift.{u + 1} (A r)) c).map
            ((encoding r Y.left).fixedDerived.counitIso.inv.app L.obj)) := by
  sorry

end WeilConjectures
