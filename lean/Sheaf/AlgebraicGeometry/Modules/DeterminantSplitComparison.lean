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
import Sheaf.LinearAlgebra.ExteriorTopDirectSum

/-!
# Construction of the determinant comparison on a split open

Source: blueprint, Riemann--Roch, proof of (*), determinant paragraph.
(blueprint: lem-sc-determinant-split-comparison).
-/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

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
              (homOfLE hZW).op y)) := by sorry

end AlgebraicGeometry.Scheme.Modules
