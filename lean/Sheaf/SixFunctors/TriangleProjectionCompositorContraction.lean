/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U7
-/
module

public import Sheaf.SixFunctors.CompositionProjectionData
import Sheaf.SixFunctors.TriangleProjectionNormalForm
import Sheaf.SixFunctors.OpenTensorNormalization
import Sheaf.Paper.RingedProjectionTensorComposition

/-! # Contraction of the triangle projection word

Source: the composition/refinement calculation of the blueprint and Stacks 0F7J
(blueprint: lem-sf-triangle-projection-compositor-contraction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOfSpec false
set_option genInjectivity false

universe u g h v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.AmbientProperOpen

namespace AlgebraicGeometry.ProEtale.CompactCompositionProjection

variable {G : Type g} [Category.{h} G] {geo : G ⥤ Scheme.{u}}

/-- Contracting the triangle counit normal form gives the projection equation.
Source: blueprint composition/refinement sentence and Stacks 0F7J
(blueprint: lem-sf-triangle-projection-compositor-contraction).

Proof: expand each compactification projection and each composition comparison.
Naturality moves the inner open tensor map through the proper/open mate. The
triangle normal-form theorem then replaces its left word by its right word,
retaining the successive pullbacks. Combine the two proper projections using
the tensor-composition equation and adjunction conjugation. Combine the two
open tensor maps by transposing under the composite open adjunction: the
recorded open-unit normalization and the tensor-pullback composition equation
make their transposes identical. Naturality of the direct and open compositors
contracts the remaining word to the composite projection after alpha tensor
identity. Pullback associativity identifies the final cast with trianglePull.
The same calculation takes place intrinsically on the simultaneous sequence
site for systems and retains every quotient transition. No projection is inverted.
-/
theorem triangleProjectionCompositorContraction
    (F : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ F.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (n : ℕ) :
    TriangleEquations
      (ordinary F (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))
      (ordinaryTensor F (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) ∧
    ∀ (o : WeilConjectures.IntegralSystemRealization.Operations l E)
      (z : WeilConjectures.IntegralSystemRealization.Realizations l E F o),
      TriangleEquations (realizedSystems F l E o z) (realizedTensor F l E o z) := by sorry


end AlgebraicGeometry.ProEtale.CompactCompositionProjection
