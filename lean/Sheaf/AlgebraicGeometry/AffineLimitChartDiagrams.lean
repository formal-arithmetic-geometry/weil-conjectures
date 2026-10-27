/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.LimitAffineTransition
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.WithTerminal.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction

/-!
# Affine chart diagrams along an affine-transition limit

Source: Stacks Project, Limits, Tag 0C4W, first paragraph of the proof; Tags 01YX,
01YW, 01JR and 01I4 (blueprint: lem-trf-affine-limit-chart-diagrams).

The auxiliary constructions only package the given cone, chosen pullbacks, and Mathlib's
algebra tensor product with algebra structures supplied by ring homomorphisms.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

namespace AlgebraicGeometry.AffineLimitChart

set_option autoImplicit false

noncomputable section

/-- The actual stages over `i₀`, with the given limit adjoined as an initial object.
Source: Stacks, Tags 01YX and 0C4W
(blueprint: lem-trf-affine-limit-chart-diagrams). -/
def bases {I : Type u} [Preorder I] (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) (i₀ : I) :
    WithInitial (Over (op i₀)) ⥤ Over (D.obj (op i₀)) :=
  WithInitial.lift (Z := Over.mk (c.π.app (op i₀))) (Over.post D)
    (fun j ↦ Over.homMk (c.π.app j.left) (c.w j.hom))
    (fun j k a ↦ by ext; exact c.w a.left)

/-- The inverse image of a fixed chart, with its actual transition maps.
Source: Stacks, Tag 01JR (blueprint: lem-trf-affine-limit-chart-diagrams). -/
def charts {K : Type u} [Category.{u} K] {S : Scheme.{u}} (F : K ⥤ Over S)
    {Z : Scheme.{u}} (f : Z ⟶ S) : K ⥤ Scheme.{u} :=
  F ⋙ Over.pullback f ⋙ Over.forget Z

/-- Base change of a morphism of charts; both projections are the chosen pullback maps.
Source: Stacks, Tags 01JR and 01I4
(blueprint: lem-trf-affine-limit-chart-diagrams). -/
def mapCharts {K : Type u} [Category.{u} K] {S : Scheme.{u}} (F : K ⥤ Over S)
    {X Y : Over S} (h : X ⟶ Y) : charts F X.hom ⟶ charts F Y.hom where
  app t := pullback.map (F.obj t).hom X.hom (F.obj t).hom Y.hom
    (𝟙 _) h.left (𝟙 _) (by simp) (by simp [Over.w h])
  naturality s t a := by
    apply pullback.hom_ext <;> simp [charts, Over.pullback_map_left, Category.assoc]

/-- Mathlib's algebra tensor product for two specified structure homomorphisms.
Source: Stacks, Algebra, Tag 00CV
(blueprint: lem-trf-affine-limit-chart-diagrams). -/
def tensor {R A B : CommRingCat.{u}} (f : R ⟶ A) (g : R ⟶ B) : CommRingCat.{u} :=
  letI := f.hom.toAlgebra
  letI := g.hom.toAlgebra
  CommRingCat.of (A ⊗[R] B)

/-- A pure tensor in the specified algebra tensor product.
Source: Stacks, Tag 00CV (blueprint: lem-trf-affine-limit-chart-diagrams). -/
def pure {R A B : CommRingCat.{u}} (f : R ⟶ A) (g : R ⟶ B) (a : A) (b : B) :
    tensor f g :=
  letI := f.hom.toAlgebra
  letI := g.hom.toAlgebra
  a ⊗ₜ[R] b

/-- The first factor's canonical coprojection.
Source: Stacks, Tags 00CV and 01I4 (blueprint: lem-trf-affine-limit-chart-diagrams). -/
def left {R A B : CommRingCat.{u}} (f : R ⟶ A) (g : R ⟶ B) : A ⟶ tensor f g :=
  letI := f.hom.toAlgebra
  letI := g.hom.toAlgebra
  CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom

/-- The second factor's canonical coprojection.
Source: Stacks, Tags 00CV and 01I4 (blueprint: lem-trf-affine-limit-chart-diagrams). -/
def right {R A B : CommRingCat.{u}} (f : R ⟶ A) (g : R ⟶ B) : B ⟶ tensor f g :=
  letI := f.hom.toAlgebra
  letI := g.hom.toAlgebra
  CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom

/-- The cocone to the ring at the adjoined limit, with the actual transition homomorphisms.
Source: Stacks, Tag 01YW (blueprint: lem-trf-affine-limit-chart-diagrams). -/
def ringCocone {K : Type u} [Category.{u} K]
    (A : (WithInitial K)ᵒᵖ ⥤ CommRingCat.{u}) :
    Cocone (WithInitial.incl.op ⋙ A) where
  pt := A.obj (op WithInitial.star)
  ι.app j := A.map (WithInitial.starInitial.to (WithInitial.of j.unop)).op
  ι.naturality j k a := by
    dsimp
    rw [Category.comp_id, ← A.map_comp, ← op_comp]
    congr 1

/-- The complete affine chart diagram, including the canonical coordinate comparison.

Source: Stacks, Limits, Tag 0C4W, first proof paragraph
(blueprint: lem-trf-affine-limit-chart-diagrams).

Proof: Work over the upper tail of i₀, equivalently Over (op i₀). The affine-transition
limit theorem (lem-weil-pbc-limit-affine-transition) makes the inverse images of each W₀
an affine limiting diagram. Apply lem-weil-pbc-spec-colimit-limit and uniqueness of limits
to identify its ring with the directed colimit, with the specified projection maps.
The open-fibre-product lemma (lem-weil-pbc-open-fibre-product, Tag 01JR) identifies the
pulled-back X and Y charts with their fibre products over W₀. Preimages of the two finite
unions give the asserted covers, also for an empty cover. The affine-spectrum pullback
lemma (lem-weil-pbc-fibre-product-affine-spectra, Tag 01I4) identifies the chart rings with
A tensor C₀ and A tensor B₀, and identifies both projections with the factor inclusions.
Their universal properties give id tensor phi and alpha tensor id, including the maps to
the limit. Pullback pasting and cancellation (lem-weil-pbc-cartesian-square-pasting) make
every stage-change square cartesian. Finally the balanced tensor relations give F and G
by the displayed pure-tensor formulas: their inverses send c tensor e to (1 tensor c)
tensor e, and a tensor c to c tensor (a tensor 1), respectively. Balancing moves each
scalar between factors, proves both composites are identities, and verifies the E-action.
Their composite extends the two specified ring maps of the cartesian square, and hence
is its canonical coordinate comparison. These computations also cover zero rings and
non-injective structure maps. -/
theorem exists_diagrams
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    (c : Cone D) (hc : IsLimit c) (i₀ : I)
    (U V : Over (D.obj (op i₀))) (g : U ⟶ V)
    (n : ℕ) (m : Fin n → ℕ)
    (R₀ B₀ : Fin n → CommRingCat.{u})
    (C₀ : (j : Fin n) → Fin (m j) → CommRingCat.{u})
    (b : ∀ j, R₀ j ⟶ B₀ j) (φ : ∀ j k, B₀ j ⟶ C₀ j k)
    (w : ∀ j, Spec (R₀ j) ⟶ D.obj (op i₀))
    [∀ j, IsOpenImmersion (w j)]
    (y : ∀ j, Over.mk (Spec.map (b j) ≫ w j) ⟶ V)
    [∀ j, IsOpenImmersion (y j).left]
    (x : ∀ j k, Over.mk (Spec.map (b j ≫ φ j k) ≫ w j) ⟶ U)
    [∀ j k, IsOpenImmersion (x j k).left]
    (hxy : ∀ j k, (x j k).left ≫ g.left = Spec.map (φ j k) ≫ (y j).left)
    (hy : (⋃ j, Set.range (y j).left) = Set.univ)
    (hx : ∀ j, (⋃ k, Set.range (x j k).left) = g.left ⁻¹' Set.range (y j).left) :
    ∃ (A : Fin n → (WithInitial (Over (op i₀)))ᵒᵖ ⥤ CommRingCat.{u})
      (r : ∀ j t, R₀ j ⟶ (A j).obj (op t))
      (eW : ∀ j, charts (bases D c i₀) (w j) ≅ (A j).rightOp ⋙ Scheme.Spec),
      (∀ j, Nonempty (IsColimit (ringCocone (A j)))) ∧
      (∀ j t, (eW j).hom.app t ≫ Spec.map (r j t) =
        pullback.snd ((bases D c i₀).obj t).hom (w j)) ∧
      (∀ j s t (a : s ⟶ t), r j t ≫ (A j).map a.op = r j s) ∧
      ∃ (eY : ∀ j t, (charts (bases D c i₀) (Spec.map (b j) ≫ w j)).obj t ≅
          Spec (tensor (r j t) (b j)))
        (eX : ∀ j k t,
          (charts (bases D c i₀) (Spec.map (b j ≫ φ j k) ≫ w j)).obj t ≅
            Spec (tensor (r j t) (b j ≫ φ j k)))
        (q : ∀ j k t, tensor (r j t) (b j) ⟶ tensor (r j t) (b j ≫ φ j k))
        (vY : ∀ j s t (a : s ⟶ t), tensor (r j t) (b j) ⟶ tensor (r j s) (b j))
        (vX : ∀ j k s t (a : s ⟶ t),
          tensor (r j t) (b j ≫ φ j k) ⟶ tensor (r j s) (b j ≫ φ j k)),
        (∀ j k t (a : (A j).obj (op t)) (z : B₀ j),
          (q j k t).hom (pure (r j t) (b j) a z) =
            pure (r j t) (b j ≫ φ j k) a ((φ j k).hom z)) ∧
        (∀ j s t (a : s ⟶ t) (z : (A j).obj (op t)) (b₁ : B₀ j),
          (vY j s t a).hom (pure (r j t) (b j) z b₁) =
            pure (r j s) (b j) ((A j).map a.op |>.hom z) b₁) ∧
        (∀ j k s t (a : s ⟶ t) (z : (A j).obj (op t)) (c₁ : C₀ j k),
          (vX j k s t a).hom (pure (r j t) (b j ≫ φ j k) z c₁) =
            pure (r j s) (b j ≫ φ j k) ((A j).map a.op |>.hom z) c₁) ∧
        (∀ j t, (eY j t).hom ≫ Spec.map (right (r j t) (b j)) =
          pullback.snd ((bases D c i₀).obj t).hom (Spec.map (b j) ≫ w j)) ∧
        (∀ j k t, (eX j k t).hom ≫ Spec.map (right (r j t) (b j ≫ φ j k)) =
          pullback.snd ((bases D c i₀).obj t).hom (Spec.map (b j ≫ φ j k) ≫ w j)) ∧
        (∀ j t, (eY j t).hom ≫ Spec.map (left (r j t) (b j)) ≫
          (eW j).inv.app t ≫ pullback.fst ((bases D c i₀).obj t).hom (w j) =
            pullback.fst ((bases D c i₀).obj t).hom (Spec.map (b j) ≫ w j)) ∧
        (∀ j k t, (eX j k t).hom ≫ Spec.map (left (r j t) (b j ≫ φ j k)) ≫
          (eW j).inv.app t ≫ pullback.fst ((bases D c i₀).obj t).hom (w j) =
            pullback.fst ((bases D c i₀).obj t).hom (Spec.map (b j ≫ φ j k) ≫ w j)) ∧
        (∀ j s t (a : s ⟶ t),
          (charts (bases D c i₀) (Spec.map (b j) ≫ w j)).map a ≫ (eY j t).hom =
            (eY j s).hom ≫ Spec.map (vY j s t a)) ∧
        (∀ j k s t (a : s ⟶ t),
          (charts (bases D c i₀) (Spec.map (b j ≫ φ j k) ≫ w j)).map a ≫
            (eX j k t).hom = (eX j k s).hom ≫ Spec.map (vX j k s t a)) ∧
        (∀ j t, IsOpenImmersion ((mapCharts (bases D c i₀) (y j)).app t)) ∧
        (∀ j k t, IsOpenImmersion ((mapCharts (bases D c i₀) (x j k)).app t)) ∧
        (∀ t, (⋃ j, Set.range ((mapCharts (bases D c i₀) (y j)).app t)) = Set.univ) ∧
        (∀ j t, (⋃ k, Set.range ((mapCharts (bases D c i₀) (x j k)).app t)) =
          ((mapCharts (bases D c i₀) g).app t) ⁻¹'
            Set.range ((mapCharts (bases D c i₀) (y j)).app t)) ∧
        (∀ j k, ∃ h :
            Over.mk (Spec.map (b j ≫ φ j k) ≫ w j) ⟶
              Over.mk (Spec.map (b j) ≫ w j),
          h.left = Spec.map (φ j k) ∧
          (∀ t, (mapCharts (bases D c i₀) h).app t ≫ (eY j t).hom =
            (eX j k t).hom ≫ Spec.map (q j k t)) ∧
          (∀ s t (a : s ⟶ t), IsPullback
            ((mapCharts (bases D c i₀) h).app s)
            ((charts (bases D c i₀) (Spec.map (b j ≫ φ j k) ≫ w j)).map a)
            ((charts (bases D c i₀) (Spec.map (b j) ≫ w j)).map a)
            ((mapCharts (bases D c i₀) h).app t))) ∧
        (∀ j k s t (a : s ⟶ t),
          ∃ (F : tensor (q j k t) (vY j s t a) ≅
              tensor (φ j k) (right (r j s) (b j)))
            (G : tensor (φ j k) (right (r j s) (b j)) ≅
              tensor (r j s) (b j ≫ φ j k)),
            (∀ (z : (A j).obj (op t)) (c₁ : C₀ j k)
                (z' : (A j).obj (op s)) (b₁ : B₀ j),
              F.hom.hom (pure (q j k t) (vY j s t a)
                (pure (r j t) (b j ≫ φ j k) z c₁) (pure (r j s) (b j) z' b₁)) =
                  pure (φ j k) (right (r j s) (b j)) c₁
                    (pure (r j s) (b j) (((A j).map a.op).hom z * z') b₁)) ∧
            (∀ (c₁ : C₀ j k) (z' : (A j).obj (op s)) (b₁ : B₀ j),
              G.hom.hom (pure (φ j k) (right (r j s) (b j)) c₁
                (pure (r j s) (b j) z' b₁)) =
                  pure (r j s) (b j ≫ φ j k) z' ((φ j k).hom b₁ * c₁)) ∧
            right (q j k t) (vY j s t a) ≫ F.hom =
              right (φ j k) (right (r j s) (b j)) ∧
            right (φ j k) (right (r j s) (b j)) ≫ G.hom = q j k s ∧
            left (q j k t) (vY j s t a) ≫ F.hom ≫ G.hom = vX j k s t a ∧
            right (q j k t) (vY j s t a) ≫ F.hom ≫ G.hom = q j k s) := by
  sorry

end

end AlgebraicGeometry.AffineLimitChart
