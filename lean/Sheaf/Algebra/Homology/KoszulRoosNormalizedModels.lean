/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups Q128 and X5
-/
module

public import Sheaf.Algebra.Homology.KoszulRoosComparisonData

/-! # Normalized Koszul and Roos chain models

Source: blueprint main-20261015, sec-smooth-purity/sk-lem-sp-tower, proof paragraph 1.
(blueprint: lem-sp-normalized-koszul-roos-models)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u v r w t z
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped ChangeOfRings

namespace CategoryTheory.KoszulRoos

attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
attribute [local instance] SheafOfModules.monoidalCategory

/-- Normalized chain models for principal regular quotients and strict Roos fibres.
Source: Stacks 0941, 06YP, 06YY; blueprint tower proof paragraph 1, steps 1--6 and 11.
(blueprint: lem-sp-normalized-koszul-roos-models)

Proof: Exact countable products on the pro-etale site commute with cohomology.
The proved derived countable-product universal property identifies their termwise
products with derived products.
Derive the strict Roos functor and normalize its ordinary-limit unit by roosι.
For each power, the regular principal quotient sequence and its cone augmentation
identify total Koszul tensor with restricted derived extension. Derive the ordinary
extension/restriction adjunction, with unit 1 tensor x. Its K-flat normalization is
preserved under replacement by a flat-term K-flat resolution. Tensoring the two
finite-free terms commutes with products. Distribute the tensor through the Roos
shifted cone; on Koszul degree a its previous-degree coordinate has sign (-1)^a,
while its current-degree coordinate is unchanged. Deleting a finite prefix induces
the diagonal product-coordinate map of Roos fibres. Its kernel is the cone of
1 minus a nilpotent finite shift and is contractible, so deletion is a
quasi-isomorphism. Product projections and strict tower maps commute with deletion.
Finally exact restriction leaves the underlying abelian sheaf unchanged, reflects
cohomology vanishing, and hence reflects invertibility of derived morphisms by
applying this detection to their cones. These constructions give precisely the
normalization properties, without claiming the projection-adjoint or coefficient
compatibility conclusions. -/
theorem normalizedKoszulRoosModels (T : AlgebraicGeometry.Scheme.{t})
    [EssentiallySmall.{t + 1} T.ProEt]
    (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology T) CommRingCat.{max z (t + 1)})
    (s : (R.obj ⋙ forget CommRingCat.{max z (t + 1)}).sections)
    [∀ S : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology T) CommRingCat.{max z (t + 1)},
      HasDerivedCategory.{w} (Modules.{t + 1, t, max z (t + 1)} S)]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ Modules.{t + 1, t, max z (t + 1)} R)]
    (_hs : Mono (globalSectionMultiplication R (unitSection R s))) :
    ∃ i : HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology T)
      CommRingCat.{max z (t + 1)},
    letI := i
    ∃ M : Models.{t + 1, t, max z (t + 1), w} R s, Normalization R s M := by
  sorry

end CategoryTheory.KoszulRoos
