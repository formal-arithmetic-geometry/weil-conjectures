/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q22
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceBlowupPresentation
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Strict transforms of algebraic spaces

Source: Stacks Project, Divisors on Spaces, Tag 0862, definition-strict-transform
(blueprint: def-sfb-space-strict-transform-presentation).

A presentation retains the cartesian ambient space and the closed immersion whose
structure-map kernel is precisely the sheaf of exceptional-ideal torsion sections.
The kernel condition determines the closed subspace, including its nonreduced structure.
No object is selected from an existence theorem.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- A model of the strict transform, as a specified closed subspace of the cartesian
pullback. The kernel consists of sections locally annihilated by a power of the image
of the centre ideal. On the blowup this image is the exceptional Cartier ideal, so this
is exactly local power torsion for an equation of the exceptional divisor. Covering
sieves allow the exponent to vary locally. Testing every further restriction expresses
annihilation by the ideal sheaf, even when its global sections do not generate it.
Source: Stacks Project, Divisors on Spaces, Tag 0862, definition-strict-transform
(blueprint: def-sfb-space-strict-transform-presentation). -/
structure StrictTransformPresentation {S : Scheme.{u}} {Y T : AlgebraicSpace S}
    (g : Y ⟶ T) (I : QuasiCoherentIdeal T) (B : BlowupPresentation I) where
  /-- The actual ambient fibre product. -/
  ambient : AlgebraicSpace S
  /-- Projection to the original space. -/
  toSource : ambient ⟶ Y
  /-- Projection to the blowup. -/
  toBlowup : ambient ⟶ B.space
  /-- These projections exhibit the ambient space as the fibre product. -/
  cartesian : IsPullback toSource.hom toBlowup.hom g.hom B.projection.hom
  /-- The closed subspace defined by the exceptional torsion ideal. -/
  space : AlgebraicSpace S
  /-- Its inclusion into the fibre product. -/
  inclusion : space ⟶ ambient
  /-- The inclusion is representable by closed immersions. -/
  closed : IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left) inclusion.hom.hom
  /-- The complete defining ideal, specified on every small etale test. -/
  kernel : ∀ (V : ambient.EtaleSite) (s : ambient.structureSheaf.obj.obj (op V)),
    (moduleStructureMap inclusion).val.app (op V) s = 0 ↔
      ∃ R : Sieve V, R ∈ ambient.etaleTopology V ∧
        ∀ (W : ambient.EtaleSite) (a : W ⟶ V), R a →
          ∃ n : ℕ, ∀ (Z : ambient.EtaleSite) (b : Z ⟶ W),
            ∀ r ∈ idealSectionImage (idealTensorMap (toBlowup ≫ B.projection) I) Z ^ n,
              r * ambient.structureSheaf.obj.map (b ≫ a).op s = 0

end AlgebraicGeometry.AlgebraicSpace
