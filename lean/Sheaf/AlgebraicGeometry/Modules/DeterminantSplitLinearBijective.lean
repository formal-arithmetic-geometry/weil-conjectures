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
import Sheaf.AlgebraicGeometry.Modules.ExteriorSheafLocalFreeComparison
import Sheaf.AlgebraicGeometry.Modules.ExteriorSheafRankWedgeZero
import Sheaf.LinearAlgebra.ExteriorTopDirectSum

/-!
# Local bijectivity of split determinant linear maps

Source: blueprint `lem-sc-riemann-roch`, proof of (*), determinant paragraph.
(blueprint: lem-sc-split-determinant-linear-bijective).
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules

/-- The wedge formula makes given linear maps bijective on common free charts.
Source: blueprint `lem-sc-riemann-roch`, proof of (*), determinant paragraph,
local direct-sum comparison (blueprint: lem-sc-split-determinant-linear-bijective).

Proof: Choose a common trivializing neighborhood V of X₁ and X₃ inside U.
On every W contained in V the outside section modules are free of the stated
ranks. The splitting identifies the middle section module with their product.
The exterior sheafification units on these free charts are bijective, as is
the tensor comparison: finite free exterior presheaves and their tensor are
already sheaves on the chart. Under these identifications, the given linear
map d agrees with the inverse top-direct-sum equivalence on pure tensors of
wedges. Indeed replace each l(b) by the canonical second-summand lift; its
difference is in the first summand, and rank vanishing removes every extra
term. Pure wedges span the exterior modules and pure tensors span the tensor,
so the two linear maps agree everywhere. The comparison is therefore bijective
on W. This argument proves a property of a given map; it constructs no map.
For rank zero use the empty wedge. No cancellation of a scalar or nonzero-ring
hypothesis is used, and the empty-open case remains valid. -/
theorem determinant_split_linear_maps_locally_bijective {X : Scheme.{v}}
    (S : ShortComplex X.Modules) (r₁ r₂ r₃ : ℕ) (hr : r₂ = r₁ + r₃)
    [S.X₁.IsFiniteLocallyFreeOfRank r₁] [S.X₃.IsFiniteLocallyFreeOfRank r₃]
    (U : X.Opens)
    (e : S.X₂.restrict U.ι ≅ S.X₁.restrict U.ι ⊞ S.X₃.restrict U.ι)
    (hf : (restrictFunctor U.ι).map S.f ≫ e.hom = biprod.inl)
    (hg : e.hom ≫ biprod.snd = (restrictFunctor U.ι).map S.g)
    (l : ∀ (W : X.Opens), W ≤ U → S.X₃.val.obj (op W) → S.X₂.val.obj (op W))
    (hl : ∀ W hW b, S.g.val.app (op W) (l W hW b) = b)
    (d : ∀ (W : X.Opens), W ≤ U →
      (exteriorSheaf S.X₁ r₁ ⊗ exteriorSheaf S.X₃ r₃).val.obj (op W)
        →ₗ[X.presheaf.obj (op W)] (exteriorSheaf S.X₂ r₂).val.obj (op W))
    (hd : ∀ W hW (a : Fin r₁ → S.X₁.val.obj (op W))
        (b : Fin r₃ → S.X₃.val.obj (op W)),
        d W hW (tmulSection (exteriorSheafSection S.X₁ r₁ W a)
          (exteriorSheafSection S.X₃ r₃ W b)) =
        exteriorSheafSection S.X₂ r₂ W
          (fun i ↦ Fin.append (fun j ↦ S.f.val.app (op W) (a j))
            (fun j ↦ l W hW (b j)) (Fin.cast hr i))) :
    ∀ x ∈ U, ∃ (V : X.Opens) (hVU : V ≤ U), x ∈ V ∧
      ∀ (W : X.Opens) (hW : W ≤ V), Function.Bijective (d W (hW.trans hVU)) := by sorry

end AlgebraicGeometry.Scheme.Modules
