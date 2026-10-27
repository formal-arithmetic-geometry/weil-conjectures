/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B7
-/
module

public import Sheaf.Paper.CurveRestrictionFiltrationData

/-! # CurveClassicalFiltrationPullback

Source: blueprint latest, real-mixed-by-curves, paragraph 2.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.defProp false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOf false
set_option genInjectivity false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.Endofunctor (IsoAlgebra)
open Opposite
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type (u + 1)) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
  [IsSeparated X₀.hom]

variable (m : ℕ) (hm : 1 ≤ m)
  (C₀ : Over (Spec (.of (D.extensionSubfield m hm))))
  [LocallyOfFiniteType C₀.hom] [QuasiCompact C₀.hom]
  (h₀ : C₀ ⟶ constantExtensionModel D m hm X₀) [IsClosedImmersion h₀.left]


variable [IsSeparated C₀.hom]
  [Fact (∀ x : (D.geometricFiber X₀).left,
    IsUnit (l : (D.geometricFiber X₀).left.presheaf.stalk x))]
  [Fact (∀ x : ((constantExtensionDatum D m hm).geometricFiber C₀).left,
    IsUnit (l : ((constantExtensionDatum D m hm).geometricFiber C₀).left.presheaf.stalk x))]

universe v w

private theorem curve_fibre_exact_of_iso
    {K : Type v} [Field K] {A₁ A₂ A₃ B₁ B₂ B₃ : ModuleCat.{w} K}
    (f : A₁ ⟶ A₂) (g : A₂ ⟶ A₃) (f' : B₁ ⟶ B₂) (g' : B₂ ⟶ B₃)
    (e₁ : A₁ ≅ B₁) (e₂ : A₂ ≅ B₂) (e₃ : A₃ ≅ B₃)
    (hf : f ≫ e₂.hom = e₁.hom ≫ f')
    (hg : g ≫ e₃.hom = e₂.hom ≫ g')
    (h : Function.Injective f' ∧ Function.Exact f' g' ∧ Function.Surjective g') :
    Function.Injective f ∧ Function.Exact f g ∧ Function.Surjective g := by
  let a := e₁.toLinearEquiv
  let b := e₂.toLinearEquiv
  let c := e₃.toLinearEquiv
  have cf (x : A₁) : b (f x) = f' (a x) :=
    congrArg (fun k : A₁ ⟶ B₂ ↦ k x) hf
  have cg (y : A₂) : c (g y) = g' (b y) :=
    congrArg (fun k : A₂ ⟶ B₃ ↦ k y) hg
  refine ⟨?_, ?_, ?_⟩
  · intro x y hxy
    apply a.injective
    apply h.1
    rw [← cf, ← cf, hxy]
  · intro y
    constructor
    · intro hy
      have hy' : g' (b y) = 0 := by rw [← cg, hy, map_zero]
      obtain ⟨x, hx⟩ := (h.2.1 (b y)).mp hy'
      obtain ⟨x₀, rfl⟩ := a.surjective x
      exact ⟨x₀, b.injective ((cf x₀).trans hx)⟩
    · rintro ⟨x, rfl⟩
      apply c.injective
      calc
        c (g (f x)) = g' (b (f x)) := cg _
        _ = g' (f' (a x)) := by rw [cf]
        _ = 0 := h.2.1.apply_apply_eq_zero _
        _ = c 0 := (map_zero c).symm
  · intro z
    obtain ⟨y, hy⟩ := h.2.2 (c z)
    obtain ⟨y₀, hy₀⟩ := b.surjective y
    refine ⟨y₀, c.injective ?_⟩
    rw [cg, hy₀, hy]

omit [IsClosedImmersion h₀.left] in
/-- Ordinary curve inverse image preserves the prescribed classical filtration.
This assertion concerns the classical diagram only, before heart transport.
Source: BS 6.8.4(1),(4), 6.8.15; blueprint real-mixed-by-curves, paragraph 2
(blueprint: lem-zl-curve-classical-filtration-pullback).

Proof:
Define the terms, quotients and two arrows by c.classical, retaining the given
indices, including the sole zero term when r=0. Use the supplied natural
isomorphism of geometric fibre functors to identify each fibre with the original
fibre at the composite geometric point on X. Naturality supplies the inclusion
and quotient squares. Transport F.zero along the initial fibre isomorphism.
Transport the injectivity, kernel-image equality and surjectivity of F.exact
along the same natural fibre isomorphisms. These are exactly the zero and exact
fields needed to construct the prescribed classical filtration. No integral-lattice exactness or
semisimplicity is used. -/
theorem zl_curve_classical_filtration_pullback
    (R : sfCommonStageWeilSheaf D l hl X₀ Ω ⥤
      sfCommonStageWeilSheaf (constantExtensionDatum D m hm) l hl
        (constantExtensionModel D m hm X₀) Ω)
    (RX : ZlClassicalRealization D l hl Ω X₀)
    (RC : ZlClassicalRealization (constantExtensionDatum D m hm) l hl Ω C₀)
    (c : ZlCurveClassicalPullback D l hl Ω X₀ m hm C₀ h₀ RX RC R)
    (hFib : ∀ (κ : Type u) [Field κ] [IsAlgClosed κ]
        (x : Spec (.of κ) ⟶ ((constantExtensionDatum D m hm).geometricFiber C₀).left),
      Nonempty (c.classical ⋙
          IsoAlgebra.forget (lisseAlgebraicAutomorphismPullback
            ((constantExtensionDatum D m hm).geometricFrobenius C₀) l Ω) ⋙
          lisseAlgebraicFiberFunctor l
            ((constantExtensionDatum D m hm).geometricFiber C₀).left x Ω ≅
        IsoAlgebra.forget (lisseAlgebraicAutomorphismPullback
            (D.geometricFrobenius X₀) l Ω) ⋙
          lisseAlgebraicFiberFunctor l (D.geometricFiber X₀).left
            (x ≫ zlCurveGeometricMap D X₀ m hm C₀ h₀) Ω))
    (r : ℕ) (F : ZlClassicalFiltration D l Ω X₀ r) :
    ∀ (κ : Type u) [Field κ] [IsAlgClosed κ]
      (x : Spec (.of κ) ⟶ ((constantExtensionDatum D m hm).geometricFiber C₀).left),
    Subsingleton ((lisseAlgebraicFiberFunctor l
        ((constantExtensionDatum D m hm).geometricFiber C₀).left x Ω).obj
      (c.classical.obj (F.terms 0)).carrier) ∧
    ∀ j : Fin r,
      Function.Injective ((lisseAlgebraicFiberFunctor l
        ((constantExtensionDatum D m hm).geometricFiber C₀).left x Ω).map
        (c.classical.map (F.inclusion j)).hom.f) ∧
      Function.Exact ((lisseAlgebraicFiberFunctor l
        ((constantExtensionDatum D m hm).geometricFiber C₀).left x Ω).map
        (c.classical.map (F.inclusion j)).hom.f)
        ((lisseAlgebraicFiberFunctor l
          ((constantExtensionDatum D m hm).geometricFiber C₀).left x Ω).map
          (c.classical.map (F.quotient j)).hom.f) ∧
      Function.Surjective ((lisseAlgebraicFiberFunctor l
        ((constantExtensionDatum D m hm).geometricFiber C₀).left x Ω).map
        (c.classical.map (F.quotient j)).hom.f) := by
  intro κ _ _ x
  obtain ⟨β⟩ := hFib κ x
  constructor
  · exact ⟨fun a b ↦ (β.app (F.terms 0)).toLinearEquiv.injective
      (@Subsingleton.elim _
        (F.zero κ (x ≫ zlCurveGeometricMap D X₀ m hm C₀ h₀)) _ _)⟩
  · intro j
    exact curve_fibre_exact_of_iso _ _ _ _
      (β.app (F.terms j.castSucc)) (β.app (F.terms j.succ))
      (β.app (F.quotients j))
      (β.hom.naturality (F.inclusion j)) (β.hom.naturality (F.quotient j))
      (F.exact κ (x ≫ zlCurveGeometricMap D X₀ m hm C₀ h₀) j)

end WeilConjectures
