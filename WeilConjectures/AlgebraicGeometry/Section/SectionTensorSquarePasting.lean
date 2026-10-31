/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarCompCoherence
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure


/-! # Pulling a tensor square to a section -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v
open CategoryTheory MonoidalCategory AlgebraicGeometry

namespace AlgebraicGeometry.Etale

/-- A commuting tensor square stays commuting after pullback to a section,
with the recorded compositor and tensor constraints and any specified input
identifications. Source: composition-coherence proof, Step 1, restriction of
the difference-coordinate tower to the diagonal
(blueprint: lem-pur-section-tensor-square-pasting).

Proof: map the commuting square by the section pullback. Naturality of its
inverse tensor constraint moves the input maps outside this pullback. Naturality
of the pullback compositor moves the last map to the zero-section pullback.
The monoidality of that compositor identifies the two inverse tensor constraints
with the single zero-section constraint and the two input compositors. Tensor
bifunctoriality then combines the input maps, and the input identifications
cancel their inverses. No smoothness, section mono, or nonempty object is used. -/
private theorem section_tensor_square_pasting_core
    (A : Type v) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    [UpperStarPreservesFlat A]
    {X W V : Scheme.{u}} (t : X ⟶ W) (F : W ⟶ V) (z : X ⟶ V)
    (hz : z = t ≫ F)
    (K M N : _root_.DerivedCategory (Sheaf W.smallEtaleTopology A)) (K₀ M₀ N₀ :
      _root_.DerivedCategory (Sheaf V.smallEtaleTopology A))
    (K₁ M₁ D E : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    (m : K ⊗ M ⟶ N) (n : K₀ ⊗ M₀ ⟶ N₀)
    (a : K₁ ≅ (upperStar A t).leftDerivedFunctor.obj K)
    (b : M₁ ≅ (upperStar A t).leftDerivedFunctor.obj M)
    (α : K ≅ (upperStar A F).leftDerivedFunctor.obj K₀)
    (β : M ≅ (upperStar A F).leftDerivedFunctor.obj M₀)
    (γ : N ≅ (upperStar A F).leftDerivedFunctor.obj N₀)
    (d : (upperStar A z).leftDerivedFunctor.obj K₀ ≅ D)
    (e : (upperStar A z).leftDerivedFunctor.obj M₀ ≅ E)
    (h : m ≫ γ.hom = (α.hom ⊗ₘ β.hom) ≫
      (leftDerivedUpperStarTensorIso A F K₀ M₀).inv ≫
        (upperStar A F).leftDerivedFunctor.map n) :
    let S := (upperStar A t).leftDerivedFunctor
    let Z := (upperStar A z).leftDerivedFunctor
    let c := leftDerivedUpperStarComp A t F z hz
    (a.hom ⊗ₘ b.hom) ≫ (leftDerivedUpperStarTensorIso A t K M).inv ≫
        S.map m ≫ S.map γ.hom ≫ c.inv.app N₀ =
      ((a.hom ≫ S.map α.hom ≫ c.inv.app K₀ ≫ d.hom) ⊗ₘ
        (b.hom ≫ S.map β.hom ≫ c.inv.app M₀ ≫ e.hom)) ≫
      (d.inv ⊗ₘ e.inv) ≫ (leftDerivedUpperStarTensorIso A z K₀ M₀).inv ≫
        Z.map n := by
  dsimp only
  let S := (upperStar A t).leftDerivedFunctor
  let T := (upperStar A F).leftDerivedFunctor
  let Z := (upperStar A z).leftDerivedFunctor
  let c := leftDerivedUpperStarComp A t F z hz
  have hn : (leftDerivedUpperStarTensorIso A t K M).inv ≫
        S.map (α.hom ⊗ₘ β.hom) =
      (S.map α.hom ⊗ₘ S.map β.hom) ≫
        (leftDerivedUpperStarTensorIso A t (T.obj K₀) (T.obj M₀)).inv := by
    have hh := leftDerivedUpperStarTensorComparison_naturality A t α.hom β.hom
    apply (cancel_epi (leftDerivedUpperStarTensorIso A t K M).hom).1
    simp only [Iso.hom_inv_id_assoc]
    have hh' : (leftDerivedUpperStarTensorIso A t K M).hom ≫
        (S.map α.hom ⊗ₘ S.map β.hom) = S.map (α.hom ⊗ₘ β.hom) ≫
          (leftDerivedUpperStarTensorIso A t (T.obj K₀) (T.obj M₀)).hom := hh
    rw [reassoc_of% hh']
    simp only [Iso.hom_inv_id, Category.comp_id]
  have hc :
      (leftDerivedUpperStarTensorIso A t (T.obj K₀) (T.obj M₀)).inv ≫
        S.map (leftDerivedUpperStarTensorIso A F K₀ M₀).inv ≫ c.inv.app (K₀ ⊗ M₀) =
      (c.inv.app K₀ ⊗ₘ c.inv.app M₀) ≫
        (leftDerivedUpperStarTensorIso A z K₀ M₀).inv := by
    have hh : leftDerivedUpperStarTensorIso A z K₀ M₀ ≪≫
        tensorIso (c.app K₀) (c.app M₀) =
      c.app (K₀ ⊗ M₀) ≪≫ S.mapIso (leftDerivedUpperStarTensorIso A F K₀ M₀) ≪≫
        leftDerivedUpperStarTensorIso A t (T.obj K₀) (T.obj M₀) := by
      apply Iso.ext
      exact leftDerivedUpperStarTensorComparison_comp A t F z hz K₀ M₀
    simpa only [Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv,
      tensorIso_inv, Category.assoc] using (congrArg Iso.inv hh).symm
  have hnat := c.inv.naturality n
  change S.map (T.map n) ≫ c.inv.app N₀ = c.inv.app (K₀ ⊗ M₀) ≫ Z.map n at hnat
  rw [← Functor.map_comp_assoc, h]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn, hnat, reassoc_of% hc]
  simp only [tensorHom_comp_tensorHom_assoc, Category.assoc,
    Iso.hom_inv_id, Category.comp_id, S, Z, c]

/-- The section tensor-square identity in the canonical derived-tensor API.
Source: composition-coherence Step 1
(blueprint: lem-pur-section-tensor-square-pasting).

Proof: the general coefficient-category tensor-square calculation above applies
before coefficient specialization. Its proof maps the square, applies naturality
and monoidality of the pullback compositor, and cancels the input isomorphisms.
Expanding derivedTensorHom over this general coefficient category identifies the
two presentations. In particular no comparison of independently inferred concrete
module-sheaf tensor instances is needed. -/
theorem section_tensor_square_pasting
    (A : Type v) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    [UpperStarPreservesFlat A]
    {X W V : Scheme.{u}} (t : X ⟶ W) (F : W ⟶ V) (z : X ⟶ V)
    (hz : z = t ≫ F)
    (K M N : _root_.DerivedCategory (Sheaf W.smallEtaleTopology A)) (K₀ M₀ N₀ :
      _root_.DerivedCategory (Sheaf V.smallEtaleTopology A))
    (K₁ M₁ D E : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    (m : ((derivedTensor A W).obj K).obj M ⟶ N)
    (n : ((derivedTensor A V).obj K₀).obj M₀ ⟶ N₀)
    (a : K₁ ≅ (upperStar A t).leftDerivedFunctor.obj K)
    (b : M₁ ≅ (upperStar A t).leftDerivedFunctor.obj M)
    (α : K ≅ (upperStar A F).leftDerivedFunctor.obj K₀)
    (β : M ≅ (upperStar A F).leftDerivedFunctor.obj M₀)
    (γ : N ≅ (upperStar A F).leftDerivedFunctor.obj N₀)
    (d : (upperStar A z).leftDerivedFunctor.obj K₀ ≅ D)
    (e : (upperStar A z).leftDerivedFunctor.obj M₀ ≅ E)
    (h : m ≫ γ.hom = (derivedTensorHom A α.hom β.hom) ≫
      (leftDerivedUpperStarTensorIso A F K₀ M₀).inv ≫
        (upperStar A F).leftDerivedFunctor.map n) :
    let S := (upperStar A t).leftDerivedFunctor
    let Z := (upperStar A z).leftDerivedFunctor
    let c := leftDerivedUpperStarComp A t F z hz
    (derivedTensorHom A a.hom b.hom) ≫ (leftDerivedUpperStarTensorIso A t K M).inv ≫
        S.map m ≫ S.map γ.hom ≫ c.inv.app N₀ =
      (derivedTensorHom A (a.hom ≫ S.map α.hom ≫ c.inv.app K₀ ≫ d.hom)
        (b.hom ≫ S.map β.hom ≫ c.inv.app M₀ ≫ e.hom)) ≫
      (derivedTensorHom A d.inv e.inv) ≫ (leftDerivedUpperStarTensorIso A z K₀ M₀).inv ≫
        Z.map n := by
  have hh := section_tensor_square_pasting_core A t F z hz K M N K₀ M₀ N₀ K₁ M₁ D E
    m n a b α β γ d e h
  simpa only [derivedTensorHom, derivedTensor_map_app, derivedTensor_obj_map,
    derivedTensor, MonoidalCategory.curriedTensor_obj_obj,
      MonoidalCategory.curriedTensor_obj_map, MonoidalCategory.curriedTensor_map_app,
    MonoidalCategory.tensorHom_def] using hh

end AlgebraicGeometry.Etale
