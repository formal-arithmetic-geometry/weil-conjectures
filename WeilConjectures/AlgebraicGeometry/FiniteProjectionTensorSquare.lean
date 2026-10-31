/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteProjectionExchangeData
import WeilConjectures.SixFunctors.ProperOpenPullTensorComposition

/-! # Canonical tensor compatibility of a pro-etale pullback square -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.FiniteProjectionExchange
variable (A : Type (u + 1)) [CommRing A] [Finite A]

omit [Finite A] in
private theorem tensorMap_comp {X : Scheme.{u}} {K K' K'' M M' M'' : Dcat A X}
    (a : K ⟶ K') (a' : K' ⟶ K'') (b : M ⟶ M') (b' : M' ⟶ M'') :
    tensorMap A (a ≫ a') (b ≫ b') = tensorMap A a b ≫ tensorMap A a' b' := by
  exact (Functor.uncurry.obj (derivedTensor (ModuleCat A) X)).map_comp
    (Prod.mkHom a b) (Prod.mkHom a' b')

omit [Finite A] in
private theorem tensorMap_id {X : Scheme.{u}} (K M : Dcat A X) :
    tensorMap A (𝟙 K) (𝟙 M) = 𝟙 (tensor A X K M) := by
  exact (Functor.uncurry.obj (derivedTensor (ModuleCat A) X)).map_id (K, M)

private theorem tensor_composition {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (K M : Dcat A Z) :
    (mu A (f ≫ g) K M).hom ≫
        tensorMap A ((leftDerivedUpperStarComp (ModuleCat A) f g).hom.app K)
          ((leftDerivedUpperStarComp (ModuleCat A) f g).hom.app M) =
      (leftDerivedUpperStarComp (ModuleCat A) f g).hom.app (tensor A Z K M) ≫
        (pull A f).map (mu A g K M).hom ≫
        (mu A f ((pull A g).obj K) ((pull A g).obj M)).hom := by
  simpa only [Functor.uncurry_obj_map, tensorMap] using
    (properOpenPullTensorComposition (ModuleCat A) f g K M).symm

private theorem congr_tensor {X Y : Scheme.{u}} {f f' : X ⟶ Y} (e : f = f')
    (K M : Dcat A Y) :
    (mu A f K M).hom ≫
        tensorMap A ((leftDerivedUpperStarCongr (ModuleCat A) e).hom.app K)
          ((leftDerivedUpperStarCongr (ModuleCat A) e).hom.app M) =
      (leftDerivedUpperStarCongr (ModuleCat A) e).hom.app (tensor A Y K M) ≫
        (mu A f' K M).hom := by
  subst e
  simp only [leftDerivedUpperStarCongr_rfl, Iso.refl_hom, NatTrans.id_app,
    tensorMap_id, Category.comp_id, Category.id_comp]

/-- The published fixed-scalar square and tensor comparisons satisfy the monoidal square.
Source: prop-sf-pf-coherence.proof.md, proper-factor paragraph.
(blueprint: lem-sf-finite-projection-tensor-square).

Proof: apply the canonical composition comparison twice, to (p',g) and (h,p).
On flat-term K-flat representatives each comparison is the ordinary inverse-image
comparison on pure tensors, and the two resulting composites send a pair of sections
to the same pulled-back pair. The commutative-square equality identifies the composite
morphisms. The uniqueness of the derived bifunctor comparison descends this equation.
Equivalently, transport the tensor diagrams of the normalized ringed-derived composition
and geometric two-isomorphism comparisons to the published fixed-scalar realizations.
Their representative formulas identify the transported maps with mu and theta, rather
than merely supplying a different monoidal structure. No cartesianness, properness,
boundedness or invertibility of an exchange morphism is needed. -/
theorem tensor_square
    {B' B Y' Y : Scheme.{u}} {h : B' ⟶ B} {p' : B' ⟶ Y'}
    {p : B ⟶ Y} {g : Y' ⟶ Y} (s : CommSq h p' p g) (N L : Dcat A Y) :
    (pull A p').map (mu A g N L).hom ≫
      (mu A p' ((pull A g).obj N) ((pull A g).obj L)).hom ≫
      tensorMap A ((theta A s).hom.app N) ((theta A s).hom.app L) =
    (theta A s).hom.app (tensor A Y N L) ≫
      (pull A h).map (mu A p N L).hom ≫
      (mu A h ((pull A p).obj N) ((pull A p).obj L)).hom := by
  let c := leftDerivedUpperStarComp (ModuleCat A) p' g
  let d := leftDerivedUpperStarComp (ModuleCat A) h p
  let e := leftDerivedUpperStarCongr (ModuleCat A) s.w.symm
  have hc := tensor_composition A p' g N L
  have hd := tensor_composition A h p N L
  have he := congr_tensor A s.w.symm N L
  have hci :
      (pull A p').map (mu A g N L).hom ≫
        (mu A p' ((pull A g).obj N) ((pull A g).obj L)).hom ≫
        tensorMap A (c.inv.app N) (c.inv.app L) =
      c.inv.app (tensor A Y N L) ≫ (mu A (p' ≫ g) N L).hom := by
    rw [← cancel_epi (c.hom.app (tensor A Y N L))]
    simp only [Iso.hom_inv_id_app_assoc]
    rw [← reassoc_of% hc]
    simp only [c, ← tensorMap_comp, Iso.hom_inv_id_app, tensorMap_id, Category.comp_id]
  change _ ≫ _ ≫ tensorMap A (c.inv.app N ≫ e.hom.app N ≫ d.hom.app N)
    (c.inv.app L ≫ e.hom.app L ≫ d.hom.app L) =
    (c.inv.app (tensor A Y N L) ≫ e.hom.app (tensor A Y N L) ≫
      d.hom.app (tensor A Y N L)) ≫ _ ≫ _
  simp only [tensorMap_comp, Category.assoc]
  rw [reassoc_of% hci, reassoc_of% he, hd]

end AlgebraicGeometry.ProEtale.FiniteProjectionExchange
