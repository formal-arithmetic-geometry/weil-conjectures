/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y3
-/
module

public import Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
public import Mathlib.LinearAlgebra.TensorProduct.Map
import Sheaf.AlgebraicGeometry.Modules.ExteriorSheafLocalFreeComparison

/-! # Section comparisons on a common free chart for a split sequence

Source: blueprint `lem-sc-riemann-roch`, proof of (*), determinant paragraph.
(blueprint: new-y3-determinant-split-chart-comparison).
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
/-- A common free chart identifies the sectionwise exterior and tensor constructions
with their sheaf counterparts, and evaluates a sheaf splitting as a module splitting.
Source: blueprint `lem-sc-riemann-roch`, proof of (*), determinant paragraph,
first step of `lem-sc-split-determinant-linear-bijective`.
(blueprint: new-y3-determinant-split-chart-comparison).

Proof: Choose rank-r and rank-s free covers of the outside terms, using the finite
locally free rank characterization. At a point of U choose members of both covers
containing the point and intersect them with U. On every smaller open W, evaluation
of a finite free sheaf gives a module basis of the same finite size. Restrict the
splitting to this intersection. Evaluation preserves binary biproducts, and the
ModuleCat biproduct-to-product isomorphism gives eW; evaluating hf and hg gives its
two asserted formulas. The restricted middle sheaf is finite free of rank r+s:
use the product of the two free frames, reindexed by finSumFinEquiv.
Apply exteriorSheaf_local_free_comparison to all three frames. Its second conclusion
gives bijectivity of the exterior sheafification units qA, qB and qC on W.
For the tensor comparison, both top exterior sheaves are free of rank one on the
chart, including when either original rank is zero. Their top basis wedge sections
are free generators: on every subopen the unit transports the top exterior basis,
and restriction takes these wedges to the wedges of the restricted frame.
The tensor of these generators is a free generator by IsFreeGenerator.tmulSection.
The tensor product basis has its sole vector equal to this generator under the
composite of TensorProduct.map qA qC and tensorSectionsMap. Comparing these
one-element bases proves bijectivity of that composite. Equivalently, apply
IsFreeGenerator.bijective_tmulSection_right after identifying the two algebraic
top exterior modules by their bases. No scalar is cancelled, and evaluation and
basis transport remain valid over zero rings and on empty opens. -/
theorem determinant_split_chart_comparison {X : Scheme.{v}}
    (S : ShortComplex X.Modules) (r s : ℕ)
    [S.X₁.IsFiniteLocallyFreeOfRank r] [S.X₃.IsFiniteLocallyFreeOfRank s]
    (U : X.Opens)
    (e : S.X₂.restrict U.ι ≅ S.X₁.restrict U.ι ⊞ S.X₃.restrict U.ι)
    (hf : (restrictFunctor U.ι).map S.f ≫ e.hom = biprod.inl)
    (hg : e.hom ≫ biprod.snd = (restrictFunctor U.ι).map S.g) :
    ∀ x ∈ U, ∃ (V : X.Opens) (hVU : V ≤ U), x ∈ V ∧
      ∀ (W : X.Opens), W ≤ V →
        ∃ (a : Module.Basis (Fin r) (X.presheaf.obj (op W)) (S.X₁.val.obj (op W)))
          (c : Module.Basis (Fin s) (X.presheaf.obj (op W)) (S.X₃.val.obj (op W)))
          (eW : S.X₂.val.obj (op W) ≃ₗ[X.presheaf.obj (op W)]
            (S.X₁.val.obj (op W) × S.X₃.val.obj (op W))),
          (∀ z, eW (S.f.val.app (op W) z) = (z, 0)) ∧
          (∀ z, (eW z).2 = S.g.val.app (op W) z) ∧
          Function.Bijective
            (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
              (exteriorSheafPresheaf S.X₂ (r + s))).app (op W)) ∧
          Function.Bijective
            ((tensorSectionsMap (exteriorSheaf S.X₁ r) (exteriorSheaf S.X₃ s) W).comp
              (TensorProduct.map (R := X.presheaf.obj (op W))
                (R₂ := X.presheaf.obj (op W)) (σ₁₂ := RingHom.id _)
                (((PresheafOfModules.sheafificationAdjunction
                  (𝟙 X.ringCatSheaf.obj)).unit.app
                  (exteriorSheafPresheaf S.X₁ r)).app (op W)).hom
                (((PresheafOfModules.sheafificationAdjunction
                  (𝟙 X.ringCatSheaf.obj)).unit.app
                  (exteriorSheafPresheaf S.X₃ s)).app (op W)).hom)) := by sorry

end AlgebraicGeometry.Scheme.Modules
