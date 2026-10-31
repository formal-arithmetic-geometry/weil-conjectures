/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FieldProjectionSystemData
import WeilConjectures.AlgebraicGeometry.RingedExchangeTensorCoherence

/-! # Proper scalar projection square

Source: latest blueprint, field-extension-towers proof (2)
(blueprint: lem-sp-field-projection-proper-square).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
open WeilConjectures.SemilinearSections

namespace AlgebraicGeometry.ProEtale.FieldShriekSystem

variable (P : PurityFiniteSetting.{u}) (D : Models P)

/-- Scalar extension commutes with the proper counit projection before open extension.
Source: Stacks 0E48 and 07A4, blueprint field-extension-towers proof (2)
(blueprint: lem-sp-field-projection-proper-square).

Proof: realize the four corners on the ringed sequence topoi. The horizontal
maps are identity geometric maps with the specified coefficient homomorphisms;
the vertical maps are induced by g. The ordinary square is the identity on
sections, and its derived comparison is D.pull by the K-flat normalization.
Apply ringed exchange/tensor coherence to M and K. The exchange is exactly
proper P D h g, since both are the mate of that pullback comparison under the
same adjunctions. The tensor comparisons agree on pure tensors, hence agree
after two-variable K-flat localization. Precompose with the source symmetry
and postcompose with direct image of the target symmetry. The signed swap
commutes with scalar extension: the scalar has degree zero and both routes
multiply the homogeneous (a,b) summand by (-1)^(ab). This is the equality below,
with the inverse pullback comparison fixing the target corner. -/
theorem field_projection_proper_square (t : ProjectionTensorComparisons P D)
    (E F : Index P) (h : E ≤ F) {Z Y : Scheme.{u}} (g : Z ⟶ Y)
    (K : SpTowerShriek.D P.coefficients.l E.val Y)
    (M : SpTowerShriek.D P.coefficients.l E.val Z) :
    (D.scalars E F h Y).T.map (leftProper P D t E g K M) ≫
        (proper P D h g).app
          ((SpTowerShriek.tensor P.coefficients.l E.val (D.base E) Z).obj
            ((SpTowerShriek.pull P.coefficients.l E.val (D.base E)
              ((D.operations E).geometry g)).obj K, M)) ≫
        (SpTowerShriek.push P.coefficients.l F.val (D.base F)
          ((D.operations F).geometry g)).map (projectionTarget P D t h g K M).hom =
      (t.scalar E F h Y).hom.app
          (K, (SpTowerShriek.push P.coefficients.l E.val (D.base E)
            ((D.operations E).geometry g)).obj M) ≫
        (SpTowerShriek.tensor P.coefficients.l F.val (D.base F) Y).map
          (Prod.mkHom (𝟙 _) ((proper P D h g).app M)) ≫
        leftProper P D t F g ((D.scalars E F h Y).T.obj K)
          ((D.scalars E F h Z).T.obj M) := by sorry

end AlgebraicGeometry.ProEtale.FieldShriekSystem
