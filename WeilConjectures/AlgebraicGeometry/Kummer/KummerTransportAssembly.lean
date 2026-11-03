/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Kummer.KummerStrictTargetTransport

/-! # Assembly of normalized Kummer transport and finite class uniqueness
Source: diagonal tower system proof, steps (3)--(4).
(blueprint: lem-sfb-kummer-transport-assembly). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe uA vA uB vB uC vC w
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] CategoryTheory.Abelian.Ext
  DerivedCategory.singleFunctors DerivedCategory.singleFunctorIsoCompQ
  diagonalDerivedSingleCounit HasDerivedCategory.standard HomotopyCategory.singleFunctors

/-- Source quotient normalization, strict target transport, and uniqueness of each
scalar adjunct assemble the normalized boundary target.

Source: diagonal tower system proof, steps (3)--(4), the source/target choices
and final finite class comparison (blueprint: lem-sfb-kummer-transport-assembly).

Proof: retain the single strict H, roots identification, and derived isomorphism
b from target transport. At each level choose the normalized source s and target
t. Apply the arbitrary-arrow transport formula to the fixed boundary delta.
Apply the assumed finite-class implication to its scalar-adjunct equation.
The transport evaluation equation identifies the restricted residue class with
the actual evaluated boundary. Substitute this equality into the class predicate, while
retaining both normalizations and all the original strict system data. The
argument is formal in the abelian categories and uses no faithfulness of a
functor on derived categories or detection of strict arrows by evaluation. -/
theorem kummer_transport_assembly
    (ℓ : ℕ) {A : Type uA} [Category.{vA} A] [abA : Abelian A] [hA : HasExt.{w} A]
    {B : Type uB} [Category.{vB} B] [abB : Abelian B] [hB : HasExt.{w} B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)]
    [HasExt.{w} (ℕᵒᵖ ⥤ B)]
    (L : A ⥤ B) (U : B ⥤ A) (ad : L ⊣ U) (D : DiagonalDerivedReduction ℓ L)
    (C : ℕ → Type uC) [catC : ∀ n, Category.{vC} (C n)] [abC : ∀ n, Abelian (C n)]
    [hC : ∀ n, HasExt.{w} (C n)]
    (F : ∀ n, C n ⥤ B) [Fadd : ∀ n, (F n).Additive]
    [Flim : ∀ n, PreservesFiniteLimits (F n)]
    [Fcolim : ∀ n, PreservesFiniteColimits (F n)]
    (V : ∀ n, C n ⥤ A) [Vadd : ∀ n, (V n).Additive]
    [Vlim : ∀ n, PreservesFiniteLimits (V n)]
    [Vcolim : ∀ n, PreservesFiniteColimits (V n)]
    (S M : A) (δ : Ext S M 1) (rootsTower : ℕᵒᵖ ⥤ A)
    (Q P : ∀ n, C n) (g : ∀ n, S ⟶ (V n).obj (Q n))
    (κ : ∀ n, Ext M ((V n).obj (P n)) 1)
    {sourceNorm : ∀ n, ((D.ordinary.E.obj S).obj (op n) ≅ (F n).obj (Q n)) → Prop}
    {finiteClass : ∀ n, Ext ((F n).obj (Q n)) ((F n).obj (P n)) 2 → Prop}
    {rootNorm : ∀ H : ℕᵒᵖ ⥤ B, (H ⋙ U ≅ rootsTower) →
      ∀ n, (H.obj (op n) ≅ (F n).obj (P n)) → Prop}
    (a : D.T.obj ((DerivedCategory.singleFunctor _ 0).obj S) ≅
      (DerivedCategory.singleFunctor _ 0).obj (D.ordinary.E.obj S))
    (ha : a.hom = diagonalDerivedSingleCounit ℓ L D S)
    (hs : ∀ n, ∃ s : (D.ordinary.E.obj S).obj (op n) ≅ (F n).obj (Q n),
      sourceNorm n s)
    (hg : ∀ n s, sourceNorm n s →
      HEq (ad.unit.app S ≫ U.map ((D.ordinary.π n).app S ≫ s.hom)) (g n))
    (ht : Nonempty (KummerTargetData ℓ L U ad D C F V M rootsTower P κ rootNorm))
    (hc : ∀ n (e : Ext (Q n) (P n) 2),
      kummerScalarAdjunct (V n) (g n) e =
        negativeExtProduct δ (κ n) → finiteClass n (exactFunctorExtImage (F n) e)) :
    normalizedBoundaryTarget ℓ L U D S M δ rootsTower
      (fun n => (F n).obj (Q n)) (fun n => (F n).obj (P n))
      sourceNorm rootNorm finiteClass a := by
  obtain ⟨T⟩ := ht
  unfold normalizedBoundaryTarget
  refine ⟨T.H, T.roots, T.b, ?_⟩
  intro n
  obtain ⟨s, hs⟩ := hs n
  refine ⟨s, T.t n, hs, T.normalized n, ?_⟩
  have htransport := T.transport n
  unfold KummerArrowTransport at htransport
  obtain ⟨e, he, heval⟩ := htransport S a ha (Q n) s (g n) (hg n s hs) δ
  rw [heval]
  exact hc n e he

end AlgebraicGeometry.ProEtale
