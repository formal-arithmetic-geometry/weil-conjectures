/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CompactSupportFiniteProjection.ConstructibleProjectionMates
import WeilConjectures.SixFunctors.CompactSupportFiniteProjection.FiniteRefinementProjectionRealization
import WeilConjectures.Compactification.CommonRefinement

/-! # Finite projection coherence in operation coordinates -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096

attribute [local irreducible] HasDerivedCategory.standard

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures.CompactSupportFiniteProjection

private theorem map_square
    {A B : Type*} [Category A] [Category B] (F : A ⥤ B)
    {a b c d : A} {f : a ⟶ b} {g : b ⟶ d} {h : a ⟶ c} {i : c ⟶ d}
    (e : f ≫ g = h ≫ i) : F.map f ≫ F.map g = F.map h ≫ F.map i := by
  rw [← F.map_comp, ← F.map_comp, e]

-- Convert the native bifunctor endpoints before specializing its coefficient ring.
private theorem realize_refinement_square
    {D : FiniteFieldDatum.{u}} (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : SixFunctorSpace D} {f : X ⟶ Y} [QuasiCompact f.hom.left]
    (c d : Compactification f.hom.left) (r : c.Refinement d)
    {B : Type*} [Category B] (R : ProEtale.ProperOpenDerived A Y.obj.left ⥤ B)
    (K : ProEtale.ProperOpenDerived A X.obj.left)
    (L : ProEtale.ProperOpenDerived A Y.obj.left)
    (hp :
      ((ProEtale.AmbientProperOpen.RefinementProjection.finiteProjection A d).app K).app L ≫
        ProEtale.AmbientProperOpen.RefinementProjection.finiteComparison D A r
          (((ProEtale.ProperOpenTensor A X.obj.left).obj K).obj
            ((ProEtale.ProperOpenPull A f.hom.left).obj L)) =
      ((ProEtale.ProperOpenTensor A Y.obj.left).map
        (ProEtale.AmbientProperOpen.RefinementProjection.finiteComparison D A r K)).app L ≫
        ((ProEtale.AmbientProperOpen.RefinementProjection.finiteProjection A c).app K).app L) :
    R.map (((ProEtale.ProperOpenTensor A Y.obj.left).map
        (ProEtale.AmbientProperOpen.RefinementProjection.finiteComparison D A r K)).app L) ≫
      R.map (projectionTensorCoordinateComponent (ModuleCat.{u + 1} A) c K L) =
    R.map (projectionTensorCoordinateComponent (ModuleCat.{u + 1} A) d K L) ≫
      R.map (ProEtale.AmbientProperOpen.RefinementProjection.finiteComparison D A r
        (((ProEtale.ProperOpenTensor A X.obj.left).obj K).obj
          ((ProEtale.ProperOpenPull A f.hom.left).obj L))) := by
  have h := map_square R hp.symm
  dsimp only [projectionTensorCoordinateComponent,
    ProEtale.AmbientProperOpen.RefinementProjection.finiteProjection,
    ProEtale.rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar,
    ProEtale.rightDerivedLowerShriekOfCompactification, Functor.postcompose₂,
    Functor.whiskeringLeft₂, Functor.whiskeringRight, Functor.whiskeringLeft,
    Functor.comp_obj, Functor.id_obj] at h ⊢
  exact h

private theorem conjugate_square
    {B : Type*} [Category B] {a₁ a₂ b₁ b₂ A₁ A₂ B₁ B₂ : B}
    (e₁ : a₁ ≅ A₁) (e₂ : a₂ ≅ A₂) (t₁ : b₁ ≅ B₁) (t₂ : b₂ ≅ B₂)
    (a : a₁ ⟶ a₂) (b : b₁ ⟶ b₂) (q : A₁ ⟶ A₂) (r : B₁ ⟶ B₂)
    (p₁ : A₁ ⟶ B₁) (p₂ : A₂ ⟶ B₂)
    (ha : a ≫ e₂.hom = e₁.hom ≫ q)
    (hb : b ≫ t₂.hom = t₁.hom ≫ r) (hp : q ≫ p₂ = p₁ ≫ r) :
    a ≫ (e₂.hom ≫ p₂ ≫ t₂.inv) = (e₁.hom ≫ p₁ ≫ t₁.inv) ≫ b := by
  apply (cancel_mono t₂.hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← Category.assoc a e₂.hom, ha]
  simp only [Category.assoc]
  rw [hp, hb]
  simp only [← Category.assoc t₁.inv t₁.hom, Iso.inv_hom_id, Category.id_comp]

private theorem component_refinement_reverse
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ}
    (S : SixFunctorFiniteOperations D C E (n + 1) (Nat.succ_pos n))
    {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    (c d : Compactification f.hom.left) (r : c.Refinement d)
    (K : sixFunctorFiniteCategory D C E (n + 1) (Nat.succ_pos n) X)
    (L : finiteTorConstructibleCategory C.l E (n + 1) (Nat.succ_pos n) Y.obj.left) :
    ((partialTensor S Y).map ((S.finite.comparison f c d).inv.app K)).app L ≫
        component S f c K L =
      component S f d K L ≫
        (S.finite.comparison f c d).inv.app
          (((partialTensor S X).obj K).obj ((torPull S f).obj L)) := by
  let := Padic.finite_coefficientExtensionRing C.l E (n + 1) (Nat.succ_pos n)
  let RX := realization (C := C) (E := E) (n := n + 1) (hn := Nat.succ_pos n) X
  let RY := realization (C := C) (E := E) (n := n + 1) (hn := Nat.succ_pos n) Y
  let I := (intrinsicFiniteTorsionConstructible C.l E (n + 1)
    (Nat.succ_pos n) Y.obj.left).ι
  obtain ⟨ha, hb⟩ := refinement_realization S f c d r K L
  have hp := (AlgebraicGeometry.ProEtale.AmbientProperOpen.refinementProjectionCounit
    D C.l C.different E n (X := X) (Y := Y) (f := f) c d r).1
      (RX.inverse.obj K.obj) (RY.inverse.obj L.obj)
  apply I.map_injective
  simp only [Functor.map_comp]
  change I.map (((partialTensor S Y).map
      ((S.finite.comparison f c d).inv.app K)).app L) ≫
      ((sourceComparison S f c K L).hom ≫
        RY.functor.map (fixedComponent (C := C) (E := E) (n := n + 1)
          (hn := Nat.succ_pos n) f c (RX.inverse.obj K.obj) (RY.inverse.obj L.obj)) ≫
        (targetComparison S f c K L).inv) =
    ((sourceComparison S f d K L).hom ≫
      RY.functor.map (fixedComponent (C := C) (E := E) (n := n + 1)
        (hn := Nat.succ_pos n) f d (RX.inverse.obj K.obj) (RY.inverse.obj L.obj)) ≫
      (targetComparison S f d K L).inv) ≫ I.map
        ((S.finite.comparison f c d).inv.app
          (((partialTensor S X).obj K).obj ((torPull S f).obj L)))
  apply conjugate_square (sourceComparison S f d K L) (sourceComparison S f c K L)
    (targetComparison S f d K L) (targetComparison S f c K L) _ _ _ _ _ _ ha hb
  have h := realize_refinement_square
    (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E (n + 1))) c d r RY.functor
    (RX.inverse.obj K.obj) (RY.inverse.obj L.obj) hp
  simpa only [fixedComponent,
    fixedTensor, fixedDerivedPull, AlgebraicGeometry.ProEtale.ProperOpenTensor,
    AlgebraicGeometry.ProEtale.ProperOpenPull, RX, RY] using h

private theorem common_reverse_square
    {A B : Type*} [Category A] [Category B] (F : A ⥤ B)
    {a a₁ a₂ : A} {b b₁ b₂ : B}
    (t₁ : a ≅ a₁) (t₂ : a ≅ a₂) (s₁ : b ≅ b₁) (s₂ : b ≅ b₂)
    (p : F.obj a ⟶ b) (p₁ : F.obj a₁ ⟶ b₁) (p₂ : F.obj a₂ ⟶ b₂)
    (h₁ : F.map t₁.inv ≫ p = p₁ ≫ s₁.inv)
    (h₂ : F.map t₂.inv ≫ p = p₂ ≫ s₂.inv) :
    F.map (t₁.inv ≫ t₂.hom) ≫ p₂ = p₁ ≫ (s₁.inv ≫ s₂.hom) := by
  have h₂' : F.map t₂.hom ≫ p₂ = p ≫ s₂.hom := by
    apply (cancel_epi (F.map t₂.inv)).1
    rw [← F.map_comp_assoc, t₂.inv_hom_id, F.map_id, Category.id_comp]
    rw [← Category.assoc, h₂]
    simp only [Category.assoc, s₂.inv_hom_id, Category.comp_id]
  rw [F.map_comp, Category.assoc, h₂', ← Category.assoc, h₁, Category.assoc]

/-- The specified finite projection commutes with the normalized compactification comparison.
Source: current blueprint, sec-six-functors/sk-rem-sf-pf-done/
fix-prop-projection-formula.proof.md, refinement sentence; the refinement calculation
of lem-sf-projection-refinement-descent.
(blueprint: lem-sf-finite-projection-compactification-transport).

Proof: write the positive coefficient level as m + 1. For a single refinement,
refinement_realization identifies the prescribed inverse comparison at both tensor
endpoints with the ambient reverse refinement arrow. The finite clause of
refinementProjectionCounit supplies its projection equation. Realize that equation
with the coefficient-equivalence functor, conjugate by sourceComparison and
targetComparison, and use faithfulness of the full constructible inclusion.
Only these endpoint isomorphisms are cancelled; the projection map is not inverted.
For arbitrary c and d choose a common refinement b. Apply the reverse equation to
b → c and b → d. The comparison cocycle expresses c → d as the inverse of b → c
followed by b → d, and categorical cancellation combines the two squares.
The normalization lemma uses etale origins for K and K tensor f*L; finite Tor is
required only for L. There is no separatedness assumption on X or Y over k.
Identity refinements, zero inputs and empty schemes obey the same cancellations. -/
theorem component_compactification
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
    (S : SixFunctorFiniteOperations D C E n hn) :
    ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    (c d : Compactification f.hom.left) (K : sixFunctorFiniteCategory D C E n hn X)
    (L : finiteTorConstructibleCategory C.l E n hn Y.obj.left),
      ((partialTensor S Y).map ((S.finite.comparison f c d).hom.app K)).app L ≫
          component S f d K L =
        component S f c K L ≫
          (S.finite.comparison f c d).hom.app
            (((partialTensor S X).obj K).obj ((torPull S f).obj L)) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by omega)
  intro X Y f _ _ _ c d K L
  obtain ⟨b, ⟨r⟩, ⟨s⟩⟩ := Compactification.exists_common_refinement c d
  have hr := component_refinement_reverse S f b c r K L
  have hs := component_refinement_reverse S f b d s K L
  let T := ((partialTensor S X).obj K).obj ((torPull S f).obj L)
  let F := (partialTensor S Y).flip.obj L
  have hcomp : S.finite.comparison f c d =
      (S.finite.comparison f b c).symm ≪≫ S.finite.comparison f b d := by
    rw [S.finite.comparison_trans f b c d]
    simp
  have heq := common_reverse_square F
    ((S.finite.comparison f b c).app K) ((S.finite.comparison f b d).app K)
    ((S.finite.comparison f b c).app T) ((S.finite.comparison f b d).app T)
    (component S f b K L) (component S f c K L) (component S f d K L) hr hs
  simpa only [hcomp, F, T, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Iso.app_hom, Iso.app_inv, Functor.flip_obj_map, Functor.flip_obj_obj] using heq

end WeilConjectures.CompactSupportFiniteProjection
