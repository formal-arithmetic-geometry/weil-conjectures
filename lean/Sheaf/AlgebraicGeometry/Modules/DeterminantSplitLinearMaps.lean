/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts

/-!
# Linear part of the split determinant construction

Source: blueprint `lem-sc-riemann-roch`, proof of (*), determinant paragraph.
(blueprint: lem-sc-split-determinant-linear-maps).
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules

/-- Construct linear wedge maps without asserting invertibility or a rank for the quotient.
Source: blueprint `lem-sc-riemann-roch`, proof of (*), determinant paragraph,
construction and independence of lifts (blueprint: lem-sc-split-determinant-linear-maps).

Proof: On the restricted scheme U, take the linear sheaf splitting
`b ↦ e.inv (0,b)`. Wedge its images with the images under f, first on exterior
presheaves by the alternating and tensor universal properties, then sheafify.
This constructs a sheaf morphism on U; evaluate it on each W contained in U,
using the restriction identifications for exterior powers and tensor sheaves.
For any supplied lift l(b), its difference from the splitting lift lies in the
first summand, hence is f(a') on W. Expand the difference of the concatenated
wedges one entry at a time by multilinearity. Each extra term contains r₁+1
factors from the rank-r₁ sheaf X₁ and vanishes by the rank wedge-zero lemma.
Consequently the evaluated linear maps have the displayed formula even for
nonlinear lifts. Naturality follows from the constructed sheaf morphism. For
uniqueness, any natural family defines a morphism of module sheaves on U.
Locally, sections of the exterior sheaves are sums of wedges and sections of
the tensor sheaf are sums of tensors, by local surjectivity of the sheafification
units. Two morphisms with the formula agree on these local generators and
therefore on all sections by separatedness. Thus the natural family is unique.
No freeness or rank hypothesis on X₃ is needed: only the first
block is used for lift independence. Empty blocks use the degree-zero unit;
empty opens and the zero ring give the same construction. -/
theorem determinant_split_linear_maps_exists {X : Scheme.{v}}
    (S : ShortComplex X.Modules) (r₁ r₂ r₃ : ℕ) (hr : r₂ = r₁ + r₃)
    [S.X₁.IsFiniteLocallyFreeOfRank r₁]
    (U : X.Opens)
    (e : S.X₂.restrict U.ι ≅ S.X₁.restrict U.ι ⊞ S.X₃.restrict U.ι)
    (hf : (restrictFunctor U.ι).map S.f ≫ e.hom = biprod.inl)
    (hg : e.hom ≫ biprod.snd = (restrictFunctor U.ι).map S.g)
    (l : ∀ (W : X.Opens), W ≤ U → S.X₃.val.obj (op W) → S.X₂.val.obj (op W))
    (hl : ∀ W hW b, S.g.val.app (op W) (l W hW b) = b) :
    ∃! (d : ∀ (W : X.Opens), W ≤ U →
      (exteriorSheaf S.X₁ r₁ ⊗ exteriorSheaf S.X₃ r₃).val.obj (op W)
        →ₗ[X.presheaf.obj (op W)] (exteriorSheaf S.X₂ r₂).val.obj (op W)),
      (∀ W hW (a : Fin r₁ → S.X₁.val.obj (op W))
        (b : Fin r₃ → S.X₃.val.obj (op W)),
        d W hW (tmulSection (exteriorSheafSection S.X₁ r₁ W a)
          (exteriorSheafSection S.X₃ r₃ W b)) =
        exteriorSheafSection S.X₂ r₂ W
          (fun i ↦ Fin.append (fun j ↦ S.f.val.app (op W) (a j))
            (fun j ↦ l W hW (b j)) (Fin.cast hr i))) ∧
      (∀ (W Z : X.Opens) (hW : W ≤ U) (hZW : Z ≤ W) y,
        (exteriorSheaf S.X₂ r₂).val.map (homOfLE hZW).op (d W hW y) =
          d Z (hZW.trans hW)
            ((exteriorSheaf S.X₁ r₁ ⊗ exteriorSheaf S.X₃ r₃).val.map
              (homOfLE hZW).op y)) := by sorry

end AlgebraicGeometry.Scheme.Modules
