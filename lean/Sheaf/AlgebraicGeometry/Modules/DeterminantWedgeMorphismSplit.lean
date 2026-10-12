/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T2
-/
module

public import Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
import Sheaf.LinearAlgebra.ExteriorTopDirectSum
import Sheaf.AlgebraicGeometry.Modules.ExteriorTensorLiftHomExt

/-!
# Bijectivity of the wedge morphism on a splitting open

Source: blueprint, Riemann--Roch, proof of (*), determinant paragraph
(blueprint: lem-sc-determinant-wedge-morphism-split).
-/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

/-- A morphism satisfying the wedge formula is bijective on sections over every open
contained in an open on which the sequence splits. No global exactness is needed here.

Source: blueprint, Riemann--Roch, proof of (*), determinant paragraph
(blueprint: lem-sc-determinant-wedge-morphism-split).

Proof: Refine `U` to a cover trivializing the first and third terms. Restrict the given
splitting `e` to these charts; its two compatibility equations identify `S.f` with the
first inclusion and `S.g` with the second projection. Sections of the free outside
terms have bases indexed by `Fin r₁` and `Fin r₃` on each subopen of such a chart.
Apply `exteriorPower.existsUnique_topDirectSum` to these bases, transporting along `e`
and the reindexing `hr`. Its inverse satisfies the wedge formula by choosing the lifts
obtained from the second inclusion. The formula assumed for `φ` therefore identifies
its restriction with this inverse: pure wedges span the exterior powers, pure tensors
span their tensor product, and the maps into their sheafifications are locally
surjective. Apply `exteriorTensor_lift_hom_ext` on each chart (the split quotient is an
epimorphism) to obtain equality of sheaf morphisms. This also handles sections
which are not globally sums of wedges.
Consequently `φ` is an isomorphism on the refined cover. For an arbitrary `W ≤ U`,
local injectivity implies injectivity on `W` by separatedness. For surjectivity, take
local inverse images of a section on the induced cover of `W`; local injectivity makes
them agree on pairwise intersections, so the sheaf property glues them to an inverse
image on `W`. Thus the map on sections is bijective for every such `W`. The argument
also covers zero ranks (the empty wedge is the basis of degree zero), zero rings,
and the empty open or empty scheme. -/
theorem determinant_wedgeMorphism_bijective_of_split {X : Scheme.{v}}
    (S : ShortComplex X.Modules) (r₁ r₂ r₃ : ℕ) (hr : r₂ = r₁ + r₃)
    [S.X₁.IsFiniteLocallyFreeOfRank r₁] [S.X₃.IsFiniteLocallyFreeOfRank r₃]
    (φ : exteriorSheaf S.X₁ r₁ ⊗ exteriorSheaf S.X₃ r₃ ⟶ exteriorSheaf S.X₂ r₂)
    (hφ : ∀ (V : X.Opens) (a : Fin r₁ → S.X₁.val.obj (op V))
      (b : Fin r₃ → S.X₃.val.obj (op V)) (c : Fin r₃ → S.X₂.val.obj (op V)),
      (∀ i, S.g.val.app (op V) (c i) = b i) →
      φ.val.app (op V)
        (tmulSection (exteriorSheafSection S.X₁ r₁ V a)
          (exteriorSheafSection S.X₃ r₃ V b)) =
        exteriorSheafSection S.X₂ r₂ V
          (fun i ↦ Fin.append (fun j ↦ S.f.val.app (op V) (a j)) c (Fin.cast hr i)))
    (U : X.Opens)
    (e : S.X₂.restrict U.ι ≅ S.X₁.restrict U.ι ⊞ S.X₃.restrict U.ι)
    (hf : (restrictFunctor U.ι).map S.f ≫ e.hom = biprod.inl)
    (hg : e.hom ≫ biprod.snd = (restrictFunctor U.ι).map S.g) :
    ∀ W ≤ U, Function.Bijective (φ.app W) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
