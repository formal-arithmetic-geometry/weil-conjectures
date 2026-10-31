/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FieldProjectionSystemData
import WeilConjectures.SixFunctors.OpenTensorNormalization

/-! # Open scalar projection square

Source: latest blueprint, field-extension-towers proof (2)
(blueprint: lem-sp-field-projection-open-square).
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

/-- Scalar extension commutes with the open tensor factor and pullback compositor.
Source: Stacks 0GL1 and 0E8I, blueprint field-extension-towers proof (2)
(blueprint: lem-sp-field-projection-open-square).

Proof: apply open tensor normalization on the ringed sequence topoi for the
identity geometric square with structural coefficient map. The inverse open
unit mate is precisely D.openIso, and the open tensor mate is the specified
openTensor in D.operations. The sources and targets of the two words are in
the essential image of the open extension. Restrict to the open. The unit
normalizations cancel the open factors. On flat-term K-flat representatives
both remaining maps send (m tensor x) tensor b to
(m tensor b) tensor (x tensor 1), in every total summand. The ordinary geometric
compositors and scalar pullback comparisons preserve these sections, so the
same calculation includes the compositor from j^*p^* to f^*. The two signed
swaps have identical signs on the two routes. Two-variable descent gives
equality on the derived open restriction; its faithfulness on the open image
gives equality before restriction. This works on whole systems, retaining all
coefficient transitions, and does not use faithfulness of level evaluation. -/
theorem field_projection_open_square (t : ProjectionTensorComparisons P D)
    (E F : Index P) (h : E ≤ F) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f)
    (K : SpTowerShriek.D P.coefficients.l E.val Y)
    (W : SpTowerShriek.D P.coefficients.l E.val X) :
    (D.scalars E F h c.Z).T.map (leftOpen P D t E c K W) ≫
        (D.openIso E F h c.i).hom.app
          ((SpTowerShriek.tensor P.coefficients.l E.val (D.base E) X).obj
            ((SpTowerShriek.pull P.coefficients.l E.val (D.base E)
              ((D.operations E).geometry f)).obj K, W)) ≫
        (SpTowerShriek.openD P.coefficients.l F.val (D.base F)
          ((D.operations F).openOp c.i)).map (projectionTarget P D t h f K W).hom =
      (projectionTarget P D t h c.g K
        ((SpTowerShriek.openD P.coefficients.l E.val (D.base E)
          ((D.operations E).openOp c.i)).obj W)).hom ≫
        (SpTowerShriek.tensor P.coefficients.l F.val (D.base F) c.Z).map
          (Prod.mkHom (𝟙 _) ((D.openIso E F h c.i).hom.app W)) ≫
        leftOpen P D t F c ((D.scalars E F h Y).T.obj K)
          ((D.scalars E F h X).T.obj W) := by sorry

end AlgebraicGeometry.ProEtale.FieldShriekSystem
