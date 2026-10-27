/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W9
-/
module

public import Sheaf.Algebra.Homology.OpenTensorScalarUnitData
/-! # Normalized comparisons of strict open tensor towers

Source: Stacks Project, Modules on Sites, Tag 03EK; Cohomology on Sites, Tag 0GL1.
(blueprint: lem-sf-open-tensor-normalized-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe c v r
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open SheafOfModules.LocalizedStrictTensor SheafOfModules.SliceTensorGenerator
namespace SheafOfModules.OpenTensorAugmentation
variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R : Sheaf J CommRingCat.{max c v r}) (V : C)
  [HasSheafify (J.over V) AddCommGrpCat.{max c v r}]
  [(J.over V).WEqualsLocallyBijective AddCommGrpCat.{max c v r}]

/-- The ordinary and coefficient-normalized open tensor isomorphisms.
Source: Stacks 0E8I and 0GL1
(blueprint: lem-sf-open-tensor-normalized-comparison). -/
structure NormalizedComparison (A : AlgebraTowers.{c, v, r} R)
    (e : StrictTotals.{c, v, r} R V A) where
  /-- The ordinary slice total-tensor isomorphism. -/
  gammaBase : source.{c, v, r} R V ≅
    sliceSource.{c, v, r} R V ⋙ ringedOpenExtensionOnComplexes.{c, v, r} R V
  /-- Generator normalization fixes the actual ordinary slice comparison. -/
  base_generator : ∀ (Z : Inputs.{c, v, r} R V) (p q d : ℤ) (h : p + q = d)
    (W : C) (f : W ⟶ V) (x : (Z.1.X p).val.obj (op (Over.mk f)))
    (y : (Z.2.X q).val.obj (op W)),
    ((gammaBase.hom.app Z).f d).val.app (op W)
        (sourceSection.{c, v, r} R V Z p q d h W f x y) =
      extensionSection.{c, v, r} R V _ W f
        (sliceSourceSection.{c, v, r} R V Z p q d h (Over.mk f) x y)
  /-- The chain isomorphism of strict towers, natural in Q and F. -/
  gamma : e.T R V ≅ e.S R V ⋙ extendInputs.{c, v, r} R V
  /-- This is the generator formula for gamma^{A_n} composed with Tot(r tensor 1). -/
  gamma_generator : ∀ (n : ℕᵒᵖ) (Z : Inputs.{c, v, r} R V)
    (p q d : ℤ) (h : p + q = d) (W : C) (f : W ⟶ V)
    (x : (Z.1.X p).val.obj (op (Over.mk f))) (y : (Z.2.X q).val.obj (op W))
    (a b : (A.obj n).right.obj.obj (op W)),
    (((gamma.hom.app n).app Z).f d).val.app (op W)
        (targetSection.{c, v, r} R V (A.obj n) Z p q d h W
          (extensionSection.{c, v, r} R V (Z.1.X p) W f x) y a b) =
      extensionSection.{c, v, r} R V _ W f
        (sliceTargetSection.{c, v, r} R V (A.obj n) Z p q d h (Over.mk f) x y a b)

/-- Normalized module projection comparisons totalize and commute with any
coefficient transitions having the prescribed two-scalar generator formula.
Source: Stacks 0E8I (lemma-j-shriek-and-tensor), 0GL1; the coefficient-linear
refinement of lem-sf-cbc-slice-tensor-generator-coherence.
(blueprint: lem-sf-open-tensor-normalized-comparison).

Proof: totalize the natural normalized module-sheaf comparison psi; extension
preserves each degree's small coproduct because it is a left adjoint. Naturality
in both differentials gives the chain equation with the unchanged sign (-1)^p.
This constructs gammaBase. At each coefficient level first apply the scalar-linear
comparison r to the first input, then psi over that coefficient algebra, then
the identity-on-summands restriction-of-scalars identification. These are
isomorphisms and give the displayed two-scalar formula. Naturality in input
complexes follows degreewise. On either route through a coefficient transition
the formula replaces a,b by q(a),q(b); iterated tensor and sheafification
uniqueness, followed by direct-sum uniqueness, proves its naturality square.
Component inverses are natural by cancellation, giving a strict tower
isomorphism. These constructions use no unit augmentation square. -/
theorem normalizedComparison_exists (A : AlgebraTowers.{c, v, r} R)
    (e : StrictTotals.{c, v, r} R V A) :
    Nonempty (NormalizedComparison.{c, v, r} R V A e) := by sorry

end SheafOfModules.OpenTensorAugmentation
