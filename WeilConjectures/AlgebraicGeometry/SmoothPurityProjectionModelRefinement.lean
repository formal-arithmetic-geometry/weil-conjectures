/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SmoothPurityCoordinateProjectionModels

/-! # Refinement coherence for ordered projection models

Source: blueprint latest, sec-smooth-purity/sk-prop-sp-tower-geometric,
`sk-prop-sp-tower-geometric-gluing.proof.md`, Local pairs (blueprint:
lem-sp-projection-model-refinement).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u v v' w w' z z' x x'
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.SpCoordinateAdjunction

private lemma inverse_formula {A : Type v} {B : Type w}
    [Category.{v'} A] [Category.{w'} B]
    {P : ObjectProperty A} {Q : ObjectProperty B} {F : A ⥤ B} {G : B ⥤ A}
    (a : RestrictedPair P Q F G) (M : P.FullSubcategory) (K : Q.FullSubcategory)
    (g : M.obj ⟶ G.obj K.obj) :
    (a.homEquiv M K).symm g = F.map g ≫ a.counit K := by
  change Q.ι.map ((a.adjunction.homEquiv M K).symm (ObjectProperty.homMk g)) = _
  rw [Adjunction.homEquiv_counit]
  rfl

private lemma hom_counit {A : Type v} {B : Type w}
    [Category.{v'} A] [Category.{w'} B]
    {P : ObjectProperty A} {Q : ObjectProperty B} {F : A ⥤ B} {G : B ⥤ A}
    (a : RestrictedPair P Q F G) (K : Q.FullSubcategory) :
    a.homEquiv ⟨G.obj K.obj, a.right_closed K⟩ K (a.counit K) = 𝟙 _ := by
  apply (a.homEquiv _ K).symm.injective
  rw [Equiv.symm_apply_apply, inverse_formula, CategoryTheory.Functor.map_id, Category.id_comp]

private lemma hom_of_counit {A : Type v} {B : Type w}
    [Category.{v'} A] [Category.{w'} B]
    {P : ObjectProperty A} {Q : ObjectProperty B} {F F' : A ⥤ B} {G : B ⥤ A}
    (a : RestrictedPair P Q F G) (a' : RestrictedPair P Q F' G)
    (rho : P.ι ⋙ F ≅ P.ι ⋙ F')
    (hc : ∀ K : Q.FullSubcategory,
      rho.hom.app ⟨G.obj K.obj, a.right_closed K⟩ ≫ a'.counit K = a.counit K)
    (M : P.FullSubcategory) (K : Q.FullSubcategory) (t : F'.obj M.obj ⟶ K.obj) :
    a'.homEquiv M K t = a.homEquiv M K (rho.hom.app M ≫ t) := by
  apply (a.homEquiv M K).symm.injective
  rw [Equiv.symm_apply_apply, inverse_formula, ← hc K]
  rw [← Category.assoc]
  have hn := rho.hom.naturality
    (ObjectProperty.homMk (a'.homEquiv M K t) :
      M ⟶ ⟨G.obj K.obj, a.right_closed K⟩)
  change F.map (a'.homEquiv M K t) ≫ rho.hom.app ⟨G.obj K.obj, a.right_closed K⟩ =
    rho.hom.app M ≫ F'.map (a'.homEquiv M K t) at hn
  rw [hn, Category.assoc, ← inverse_formula, Equiv.symm_apply_apply]

private lemma composite_counit_refinement {A : Type v} {B : Type w} {C : Type x}
    [Category.{v'} A] [Category.{w'} B] [Category.{x'} C]
    {PA : ObjectProperty A} {PB : ObjectProperty B} {PC : ObjectProperty C}
    {F : A ⥤ B} {G : B ⥤ A} {H : B ⥤ C} {I : C ⥤ B}
    {J J' : A ⥤ C} {R : C ⥤ A}
    (a : RestrictedPair PA PB F G) (b : RestrictedPair PB PC H I)
    (c : RestrictedPair PA PC J R) (c' : RestrictedPair PA PC J' R)
    (alpha : PA.ι ⋙ F ⋙ H ≅ PA.ι ⋙ J)
    (alpha' : PA.ι ⋙ F ⋙ H ≅ PA.ι ⋙ J') (beta : I ⋙ G ≅ R)
    (rho : PA.ι ⋙ J ≅ PA.ι ⋙ J')
    (ha : ∀ M, alpha'.hom.app M = alpha.hom.app M ≫ rho.hom.app M)
    (hc : CompositeEquation PA PB PC F G H I J R a b c alpha beta)
    (hc' : CompositeEquation PA PB PC F G H I J' R a b c' alpha' beta)
    (K : PC.FullSubcategory) :
    rho.hom.app ⟨R.obj K.obj, c.right_closed K⟩ ≫ c'.counit K = c.counit K := by
  let M : PA.FullSubcategory :=
    ⟨G.obj (I.obj K.obj), a.right_closed ⟨I.obj K.obj, b.right_closed K⟩⟩
  have hi : rho.hom.app M ≫ alpha'.inv.app M = alpha.inv.app M := by
    apply (cancel_epi (alpha.hom.app M)).mp
    rw [← Category.assoc, ← ha M]
    simp
  have hn := rho.hom.naturality
    (ObjectProperty.homMk (beta.inv.app K.obj) :
      ⟨R.obj K.obj, c.right_closed K⟩ ⟶ M)
  change J.map (beta.inv.app K.obj) ≫ rho.hom.app M =
    rho.hom.app ⟨R.obj K.obj, c.right_closed K⟩ ≫ J'.map (beta.inv.app K.obj) at hn
  rw [hc K, hc' K, ← Category.assoc, ← hn]
  simp only [Category.assoc]
  rw [← Category.assoc (rho.hom.app M) (alpha'.inv.app M), hi]

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The Hom bijection of a projection model is invariant under its supplied
compactification refinement comparison, and its counit is likewise invariant.
Source: blueprint latest, sec-smooth-purity/sk-prop-sp-tower-geometric,
`sk-prop-sp-tower-geometric-gluing.proof.md`, Local pairs
(blueprint: lem-sp-projection-model-refinement).

Proof. In dimension zero, apply identity_left, identity_right and
refinement_composition with identity factor refinements. Naturality of the
identity comparison and cancellation give its compatibility with refinement.
The zero equation of PM then gives the stated Hom equality. In successor
dimension, choose a compactification of the last-coordinate line and of the
preceding projection (the latter exists by Nagata). Refinement_composition
identifies the two composite comparisons after refinement of their target.
Substitute this identity in the two PM._projection_successor CompositeEquations.
Naturality of refinement gives rho followed by the second counit equal to the
first counit. The inverse Hom bijection sends g to F(g) followed by the counit;
its naturality therefore gives the Hom equality. Finally, also in dimension
zero, transpose the second counit and use injectivity of the Hom bijection to
obtain the displayed counit equality. Every step is an equality of actual tower
morphisms; finite evaluation faithfulness is never used. -/
theorem projection_model_refinement
    (pchar : ℕ) [Fact pchar.Prime] (k : Type u) [Field k] [CharP k pchar]
    (_hl : l ≠ pchar) (b : SpTowerShriek.Base l E)
    (o : SpTowerShriek.Operations l E b)
    (q : SpTowerCalculus.Coordinates l E b)
    (z : SpTowerCalculus.FiniteCoordinates l E)
    (h : SpTowerCalculus.Preservation l E k b o q)
    (cal : SpTowerCalculus.Calculus l E k b o q z h)
    (w : _) (a : Foundations l E k b o q w)
    (PM : ProjectionModels l E k b o q z h cal w a)
    (Y : Bases k) (d : ℕ) (c c' : Compactification (proj Y.val.left d))
    (M : (P l E b q (space Y.val.left d)).FullSubcategory)
    (K : (P l E b q Y.val.left).FullSubcategory)
    (t : (SpTowerCalculus.F l E b o q c').obj M.obj ⟶ K.obj) :
    (PM.projection Y d c').homEquiv M K t =
      (PM.projection Y d c).homEquiv M K
        ((cal.composition.refinement (proj Y.val.left d) c c').hom.app M ≫ t) ∧
    (cal.composition.refinement (proj Y.val.left d) c c').hom.app
      ⟨(originalProjectionRight l E b o q (proj Y.val.left d)
        (w (space Y.val.left d)) d).obj K.obj,
        (PM.projection Y d c).right_closed K⟩ ≫
      (PM.projection Y d c').counit K =
      (PM.projection Y d c).counit K := by
  cases d with
  | zero =>
    change Compactification (𝟙 Y.val.left) at c c'
    have hi (N : (P l E b q Y.val.left).FullSubcategory) :
        (cal.composition.identity c).inv.app N ≫
          (cal.composition.refinement (𝟙 Y.val.left) c c').hom.app N =
        (cal.composition.identity c').inv.app N := by
      have hr0 := cal.coherence.refinement_composition (𝟙 Y.val.left) (𝟙 Y.val.left)
        c c c' c' c c' N
      simp only [cal.coherence.refinement_identity, Iso.refl_hom, NatTrans.id_app,
        CategoryTheory.Functor.map_id, Category.id_comp] at hr0
      have hr1 := (Category.id_comp
        ((cal.composition.composition (𝟙 Y.val.left) (𝟙 Y.val.left) (𝟙 Y.val.left)
          (Category.id_comp _) c c' c').hom.app N)).symm.trans hr0
      have hr : (SpTowerCalculus.F l E b o q c').map
          ((cal.composition.identity c).hom.app N) =
          (cal.composition.identity c').hom.app
            ((SpTowerCalculus.restrictedSupport l E k b o q h (𝟙 Y.val.left) c).obj N) ≫
          (cal.composition.refinement (𝟙 Y.val.left) c c').hom.app N :=
        (cal.coherence.identity_left (𝟙 Y.val.left) c' c N).symm.trans
          (hr1.trans (congrArg
            (fun f ↦ f ≫ (cal.composition.refinement (𝟙 Y.val.left) c c').hom.app N)
            (cal.coherence.identity_right (𝟙 Y.val.left) c c' N)))
      have hn := (cal.composition.identity c').hom.naturality
        (ObjectProperty.homMk ((cal.composition.identity c).hom.app N) :
          (SpTowerCalculus.restrictedSupport l E k b o q h (𝟙 Y.val.left) c).obj N ⟶ N)
      have hh :
          (cal.composition.refinement (𝟙 Y.val.left) c c').hom.app N ≫
            (cal.composition.identity c').hom.app N =
          (cal.composition.identity c).hom.app N := by
        apply (cancel_epi ((cal.composition.identity c').hom.app
          ((SpTowerCalculus.restrictedSupport l E k b o q h (𝟙 Y.val.left) c).obj N))).mp
        rw [← Category.assoc, ← hr]
        exact hn
      apply (cancel_mono ((cal.composition.identity c').hom.app N)).mp
      simp only [Category.assoc, hh, Iso.inv_hom_id_app]
    have hh (N : (P l E b q Y.val.left).FullSubcategory)
        (L : (P l E b q Y.val.left).FullSubcategory)
        (f : (SpTowerCalculus.F l E b o q c').obj N.obj ⟶ L.obj) :
        (PM.projection Y 0 c').homEquiv N L f =
          (PM.projection Y 0 c).homEquiv N L
            ((cal.composition.refinement (𝟙 Y.val.left) c c').hom.app N ≫ f) := by
      let R := SpTowerCalculus.realization l E b Y.val.left (q.abelian Y.val.left)
      let S := R.inverse.map ((Foundations.iteration l E a Y 0).inv.app (R.functor.obj L.obj))
      apply (cancel_mono S).mp
      apply (cancel_mono (R.unitIso.inv.app L.obj)).mp
      simp only [Category.assoc]
      calc
        _ = (cal.composition.identity c').inv.app N ≫ f := PM._zero Y c' N L f
        _ = (cal.composition.identity c).inv.app N ≫
            (cal.composition.refinement (𝟙 Y.val.left) c c').hom.app N ≫ f := by
          rw [← Category.assoc, hi N]
        _ = _ := (PM._zero Y c N L
          ((cal.composition.refinement (𝟙 Y.val.left) c c').hom.app N ≫ f)).symm
    refine ⟨hh M K t, ?_⟩
    let N : (P l E b q Y.val.left).FullSubcategory :=
      ⟨(originalProjectionRight l E b o q (proj Y.val.left 0)
        (w (space Y.val.left 0)) 0).obj K.obj, (PM.projection Y 0 c).right_closed K⟩
    exact ((PM.projection Y 0 c).homEquiv N K).injective
      ((hh N K ((PM.projection Y 0 c').counit K)).symm.trans
        ((hom_counit (PM.projection Y 0 c') K).trans
          (hom_counit (PM.projection Y 0 c) K).symm))
  | succ d =>
    have hc := hasCompactification_of_finiteType_over_field k
      (space Y.val.left d) Y.val.left (proj Y.val.left d)
    let cp := HasCompactification.compactification (proj Y.val.left d)
    let cl := affineTraceLineCompactification (space Y.val.left d)
    have ha (N : (P l E b q (space Y.val.left (d + 1))).FullSubcategory) :
        (cal.composition.composition
          (AffineSpace PUnit.{u + 1} (space Y.val.left d) ↘ space Y.val.left d)
          (proj Y.val.left d) (proj Y.val.left (d + 1)) rfl cl cp c').hom.app N =
        (cal.composition.composition
          (AffineSpace PUnit.{u + 1} (space Y.val.left d) ↘ space Y.val.left d)
          (proj Y.val.left d) (proj Y.val.left (d + 1)) rfl cl cp c).hom.app N ≫
        (cal.composition.refinement (proj Y.val.left (d + 1)) c c').hom.app N := by
      have hv := cal.coherence.refinement_composition
        (AffineSpace PUnit.{u + 1} (space Y.val.left d) ↘ space Y.val.left d)
        (proj Y.val.left d) cl cl cp cp c c' N
      simp only [cal.coherence.refinement_identity, Iso.refl_hom, NatTrans.id_app,
        CategoryTheory.Functor.map_id, Category.id_comp] at hv
      exact (Category.id_comp
        ((cal.composition.composition
          (AffineSpace PUnit.{u + 1} (space Y.val.left d) ↘ space Y.val.left d)
          (proj Y.val.left d) (proj Y.val.left (d + 1)) rfl cl cp c').hom.app N)).symm.trans hv
    have he := composite_counit_refinement
      (PM.projection (coordinateBase Y d) 1 cl) (PM.projection Y d cp)
      (PM.projection Y (d + 1) c) (PM.projection Y (d + 1) c')
      (cal.composition.composition
        (AffineSpace PUnit.{u + 1} (space Y.val.left d) ↘ space Y.val.left d)
        (proj Y.val.left d) (proj Y.val.left (d + 1)) rfl cl cp c)
      (cal.composition.composition
        (AffineSpace PUnit.{u + 1} (space Y.val.left d) ↘ space Y.val.left d)
        (proj Y.val.left d) (proj Y.val.left (d + 1)) rfl cl cp c')
      (composeRight l E b q _ _ _ (a.step Y d))
      (cal.composition.refinement (proj Y.val.left (d + 1)) c c')
      ha (PM._projection_successor Y d cl cp c)
      (PM._projection_successor Y d cl cp c')
    exact ⟨hom_of_counit _ _ _ he M K t, he K⟩

end AlgebraicGeometry.ProEtale.SpCoordinateAdjunction
