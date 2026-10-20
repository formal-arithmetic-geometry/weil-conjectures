/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F3
-/
module

public import Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
import WeilConjectures.AlgebraicGeometry.Modules.DeterminantSplitLinearMaps
import Sheaf.AlgebraicGeometry.Modules.ExteriorSheafPowerComparison
import WeilConjectures.AlgebraicGeometry.Modules.DeterminantSplitLinearBijective

/-!
# Construction of the determinant comparison on a split open

Source: blueprint, Riemann--Roch, proof of (*), determinant paragraph.
(blueprint: lem-sc-determinant-split-comparison).
-/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
private theorem exteriorSheafPowerIso_hom_wedge {X : Scheme.{v}} (M : X.Modules) (n : ℕ)
    (W : X.Opens) (a : Fin n → M.val.obj (op W)) :
    (exteriorSheafPowerIso M n).hom.app W (exteriorSheafSection M n W a) =
      wedge (M := M) (r := n) (U := W) a := by
  rw [← exteriorSheafPowerIso_inv_wedge M n W a]
  exact congrArg (fun k ↦ k.app W (wedge (M := M) (r := n) (U := W) a))
    (exteriorSheafPowerIso M n).inv_hom_id

set_option backward.isDefEq.respectTransparency false in
/-- Construct the comparison independently of any proposed determinant morphism.

Source: blueprint, Riemann--Roch, proof of (*), determinant paragraph
(blueprint: lem-sc-determinant-split-comparison).

Proof: Refine `U` by the common trivializing cover of the two outside terms.
On each subopen of a chart, identify their sections with finite free modules,
and identify the middle term with their product by the splitting.
Apply `exteriorPower.existsUnique_topDirectSum` to these bases and transport its inverse along the
splitting and the rank equality.
The formula first holds for the second-summand lifts. Replacing them by the supplied
lifts changes each by an element of the first summand. Expand the difference by
multilinearity: every term has more than `r₁` first-summand factors. Expanding these
in its rank-`r₁` basis gives a repeated basis vector, hence zero by alternation.
Thus the formula also holds for `l`, even if those lifts are not linear or natural.
Uniqueness on pure wedges implies compatibility with restrictions on each chart: the free generators
restrict to the free generators, and both composites take every tensor of wedges to
the same concatenated wedge. Sheafify the exterior presheaves and the tensor
presheaf. On a subopen of the chart, coverings and refinements are the same whether
viewed in the chart or in `X`. The sheafification universal properties therefore
identify the restrictions of the original exterior sheaves with the exterior
sheaves formed on the chart, compatibly with their units. The monoidal comparison
identifies the sheafification of the tensor presheaf with the tensor of these
sheafifications. Sheafification preserves the comparison isomorphism, and its unit carries
pure tensors of wedges to `tmulSection` of `exteriorSheafSection`s. For each point
of `U`, select a common trivializing chart containing it and intersect
with `U`. The sheafified comparison on this chart gives `d` on all its subopens;
its naturality is the compatibility with restrictions just established. This is
only a local construction: neither gluing between charts nor comparison with a
proposed determinant morphism is asserted here.
Degree zero uses the empty wedge, so zero ranks, the zero ring, and empty opens
require no nonzero or nonempty hypotheses. -/
theorem determinant_split_comparison_exists {X : Scheme.{v}}
    (S : ShortComplex X.Modules) (r₁ r₂ r₃ : ℕ) (hr : r₂ = r₁ + r₃)
    [S.X₁.IsFiniteLocallyFreeOfRank r₁] [S.X₃.IsFiniteLocallyFreeOfRank r₃]
    (U : X.Opens)
    (e : S.X₂.restrict U.ι ≅ S.X₁.restrict U.ι ⊞ S.X₃.restrict U.ι)
    (hf : (restrictFunctor U.ι).map S.f ≫ e.hom = biprod.inl)
    (hg : e.hom ≫ biprod.snd = (restrictFunctor U.ι).map S.g)
    (l : ∀ (W : X.Opens), W ≤ U → S.X₃.val.obj (op W) → S.X₂.val.obj (op W))
    (hl : ∀ W hW b, S.g.val.app (op W) (l W hW b) = b) :
    ∀ x ∈ U, ∃ (V : X.Opens) (hVU : V ≤ U), x ∈ V ∧
      ∃ (d : ∀ (W : X.Opens), W ≤ V →
        (exteriorSheaf S.X₁ r₁ ⊗ exteriorSheaf S.X₃ r₃).val.obj (op W)
          ≃ₗ[X.presheaf.obj (op W)] (exteriorSheaf S.X₂ r₂).val.obj (op W)),
      (∀ W hW (a : Fin r₁ → S.X₁.val.obj (op W))
        (b : Fin r₃ → S.X₃.val.obj (op W)),
        d W hW (tmulSection (exteriorSheafSection S.X₁ r₁ W a)
          (exteriorSheafSection S.X₃ r₃ W b)) =
        exteriorSheafSection S.X₂ r₂ W
          (fun i ↦ Fin.append (fun j ↦ S.f.val.app (op W) (a j))
            (fun j ↦ l W (hW.trans hVU) (b j)) (Fin.cast hr i))) ∧
      (∀ (W Z : X.Opens) (hW : W ≤ V) (hZW : Z ≤ W) y,
        (exteriorSheaf S.X₂ r₂).val.map (homOfLE hZW).op (d W hW y) =
          d Z (hZW.trans hW)
            ((exteriorSheaf S.X₁ r₁ ⊗ exteriorSheaf S.X₃ r₃).val.map
              (homOfLE hZW).op y)) := by
  classical
  obtain ⟨d', ⟨hd', hn'⟩, _⟩ :=
    determinant_split_linear_maps_exists S r₁ r₂ r₃ hr U e hf hg l hl
  let i := (exteriorSheafPowerIso S.X₁ r₁).hom ⊗ₘ
    (exteriorSheafPowerIso S.X₃ r₃).hom
  let j := (exteriorSheafPowerIso S.X₂ r₂).inv
  let d₀ (W : X.Opens) (hW : W ≤ U) :=
    (j.val.app (op W)).hom.comp ((d' W hW).comp (i.val.app (op W)).hom)
  have hd₀ : ∀ W hW (a : Fin r₁ → S.X₁.val.obj (op W))
      (b : Fin r₃ → S.X₃.val.obj (op W)),
      d₀ W hW (tmulSection (exteriorSheafSection S.X₁ r₁ W a)
        (exteriorSheafSection S.X₃ r₃ W b)) =
      exteriorSheafSection S.X₂ r₂ W
        (fun k ↦ Fin.append (fun k ↦ S.f.val.app (op W) (a k))
          (fun k ↦ l W hW (b k)) (Fin.cast hr k)) := by
    intro W hW a b
    have hi := tensorHom_app_tmulSection (exteriorSheafPowerIso S.X₁ r₁).hom
      (exteriorSheafPowerIso S.X₃ r₃).hom (exteriorSheafSection S.X₁ r₁ W a)
      (exteriorSheafSection S.X₃ r₃ W b)
    change i.val.app (op W)
      (tmulSection (M := exteriorSheaf S.X₁ r₁) (N := exteriorSheaf S.X₃ r₃) (U := W)
        (exteriorSheafSection S.X₁ r₁ W a) (exteriorSheafSection S.X₃ r₃ W b)) =
      tmulSection (M := exteriorPower S.X₁ r₁) (N := exteriorPower S.X₃ r₃) (U := W)
        ((exteriorSheafPowerIso S.X₁ r₁).hom.val.app (op W)
          (exteriorSheafSection S.X₁ r₁ W a))
        ((exteriorSheafPowerIso S.X₃ r₃).hom.val.app (op W)
          (exteriorSheafSection S.X₃ r₃ W b)) at hi
    have hi' := hi.trans (congrArg₂ (fun x y ↦
      tmulSection (M := exteriorPower S.X₁ r₁) (N := exteriorPower S.X₃ r₃) (U := W) x y)
      (exteriorSheafPowerIso_hom_wedge S.X₁ r₁ W a)
      (exteriorSheafPowerIso_hom_wedge S.X₃ r₃ W b))
    exact (congrArg (fun x ↦ j.val.app (op W) (d' W hW x)) hi').trans
      ((congrArg (fun x ↦ j.val.app (op W) x) (hd' W hW a b)).trans
        (exteriorSheafPowerIso_inv_wedge S.X₂ r₂ W _))
  have hn : ∀ (W Z : X.Opens) (hW : W ≤ U) (hZW : Z ≤ W) y,
      (exteriorSheaf S.X₂ r₂).val.map (homOfLE hZW).op (d₀ W hW y) =
        d₀ Z (hZW.trans hW)
          ((exteriorSheaf S.X₁ r₁ ⊗ exteriorSheaf S.X₃ r₃).val.map
            (homOfLE hZW).op y) := by
    intro W Z hW hZW y
    exact (PresheafOfModules.naturality_apply j.val (homOfLE hZW).op _).symm.trans
      (congrArg (fun x ↦ j.val.app (op Z) x)
        ((hn' W Z hW hZW _).trans
          (congrArg (d' Z (hZW.trans hW))
            (PresheafOfModules.naturality_apply i.val (homOfLE hZW).op y).symm)))
  intro x hx
  obtain ⟨V, hVU, hxV, hbij'⟩ :=
    determinant_split_linear_maps_locally_bijective S r₁ r₂ r₃ hr U e hf hg l hl d' hd' x hx
  let eT : exteriorSheaf S.X₁ r₁ ⊗ exteriorSheaf S.X₃ r₃ ≅
      exteriorPower S.X₁ r₁ ⊗ exteriorPower S.X₃ r₃ :=
    tensorIso (C := X.Modules) (exteriorSheafPowerIso S.X₁ r₁)
      (exteriorSheafPowerIso S.X₃ r₃)
  let a := fun W : X.Opens ↦
    ((SheafOfModules.evaluation _ (op W)).mapIso eT).toLinearEquiv
  let b := fun W : X.Opens ↦ ((SheafOfModules.evaluation _ (op W)).mapIso
    (exteriorSheafPowerIso S.X₂ r₂)).toLinearEquiv
  have hbij (W : X.Opens) (hW : W ≤ V) :
      Function.Bijective (d₀ W (hW.trans hVU)) :=
    (b W).symm.bijective.comp ((hbij' W hW).comp (a W).bijective)
  let d (W : X.Opens) (hW : W ≤ V) :
      (exteriorSheaf S.X₁ r₁ ⊗ exteriorSheaf S.X₃ r₃).val.obj (op W)
        ≃ₗ[X.presheaf.obj (op W)] (exteriorSheaf S.X₂ r₂).val.obj (op W) :=
    { d₀ W (hW.trans hVU), Equiv.ofBijective (d₀ W (hW.trans hVU)) (hbij W hW) with }
  refine ⟨V, hVU, hxV, d, ?_, ?_⟩
  · intro W hW a b
    exact hd₀ W (hW.trans hVU) a b
  · intro W Z hW hZW y
    exact hn W Z (hW.trans hVU) hZW y

end AlgebraicGeometry.Scheme.Modules
