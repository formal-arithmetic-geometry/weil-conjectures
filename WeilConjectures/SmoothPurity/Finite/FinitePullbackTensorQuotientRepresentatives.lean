/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTowerCore
public import WeilConjectures.SmoothPurity.Finite.FinitePullbackTensorConstruction
import WeilConjectures.SmoothPurity.Finite.FinitePullbackTensorOrdinaryQuotientSquare

/-! # Quotient compatibility on flat K-flat tensor representatives

Source: Stacks Tags 06YY and 07A4, the quotient compatibility step of the
completed pullback/tensor comparison.
(blueprint: lem-pur-finite-pullback-tensor-quotient-representatives).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
namespace WeilConjectures
attribute [local irreducible] Scheme.residueField HasDerivedCategory.standard
  Functor.mapDerivedCategory finitePullbackTensorConstruction
  coefficientFiniteQuotientDerived coefficientFiniteQuotientModel
attribute [local implicit_reducible] integralCoefficientSheaf integralCoefficientCommRingSheaf
  finiteIntrinsicDerivedTensor finiteIntrinsicClosed pullbackTensorCalculus
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
attribute [local instance] sfIntrinsicPullback_additive
  coefficientFiniteQuotientExtensionAdditive

/-- Elementary pasting of the representative normalization squares. -/
private theorem representative_square_pasting {C : Type*} [Category* C]
    {A0 A1 A2 A3 A4 A5 B0 B1 B2 B3 B4 C0 C1 C2 C3 C4 C5
      D0 D1 D2 D3 D4 D5 D6 : C}
    {a : A0 ⟶ A1} {b : A1 ⟶ A2} {t : A2 ⟶ A3} {r : A3 ⟶ A4}
    {p : A4 ⟶ A5} {f : A0 ⟶ B0} {k : B0 ⟶ B1} {s : B1 ⟶ B2}
    {g : A2 ⟶ B2} {v : B2 ⟶ B3} {j : A3 ⟶ B3} {x : B3 ⟶ B4}
    {c : B4 ⟶ A5} {q : B1 ⟶ C0} {z : C0 ⟶ C1} {sn : C1 ⟶ B4}
    {q0 : B0 ⟶ C2} {w : C2 ⟶ C0} {y : C1 ⟶ C3} {sn' : C3 ⟶ A5}
    {d : C2 ⟶ C4} {vay : C4 ⟶ C5} {vkn : C5 ⟶ C3}
    {e : A1 ⟶ D0} {ty : D0 ⟶ D1} {nn : D1 ⟶ A4}
    {et : A0 ⟶ D2} {ha : D2 ⟶ D0} {hy : D1 ⟶ D3} {hq : D2 ⟶ D4}
    {hay : D4 ⟶ D5} {hs : D5 ⟶ D3} {mn : D3 ⟶ D6} {up : A4 ⟶ D6}
    {un : D6 ⟶ A5} {nt : D5 ⟶ C5} {n0 : D4 ⟶ C4}
    (hkm : a ≫ b ≫ g = f ≫ k ≫ s)
    (htnat : g ≫ v = t ≫ j) (hpost : r ≫ p = j ≫ x ≫ c)
    (hax : s ≫ v ≫ x = q ≫ z ≫ sn) (hqnat : k ≫ q = q0 ≫ w)
    (hsnat : sn ≫ c = y ≫ sn') (hchain : w ≫ z ≫ y = d ≫ vay ≫ vkn)
    (henat : a ≫ e = et ≫ ha) (hhay : ha ≫ ty ≫ hy = hq ≫ hay ≫ hs)
    (hmunat : hy ≫ mn = nn ≫ up) (hsplit : p = up ≫ un)
    (hkn : hs ≫ mn ≫ un = nt ≫ vkn ≫ sn') (hfnat : hay ≫ nt = n0 ≫ vay)
    (htot : et ≫ hq ≫ n0 = f ≫ q0 ≫ d) :
    a ≫ b ≫ t ≫ r ≫ p = a ≫ e ≫ ty ≫ nn ≫ p := by
  rw [hpost, ← reassoc_of% htnat, reassoc_of% hkm, reassoc_of% hax,
    reassoc_of% hqnat, hsnat, reassoc_of% hchain]
  rw [reassoc_of% henat, hsplit, ← reassoc_of% hmunat,
    reassoc_of% hhay, hkn, reassoc_of% hfnat, reassoc_of% htot]

attribute [local irreducible] coefficientFiniteTensorModelIso coefficientTotalTensor

end WeilConjectures
