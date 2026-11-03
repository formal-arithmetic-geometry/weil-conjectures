/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CompactSupportFiniteProjection.FinitePullbackTensorFixedCoordinates
import WeilConjectures.SixFunctors.FinitePartialTensorIdentityNaturalityCoordinatesExpanded

/-! Coordinate form of naturality for the finite partial tensor comparison.
(blueprint: lem-sf-finite-partial-tensor-identity-naturality-coordinates) -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
open CompactSupportFiniteProjection

variable {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
  {E : Type u} [Field E] [Algebra (Padic C.l) E]
  [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}

/-- The coordinate-level naturality square obtained after postcomposing with the
fixed tensor coordinates.  This is the remaining fixed-scalar calculation in
naturality of `pullbackTensorComparison`; the original naturality statement
follows from faithfulness of `coordinates` and cancellation by the coordinate
isomorphism.
Source: Stacks Project, sites-cohomology.tex, Tag 07A4, together with the
fixed-coordinate expansion in `pullbackTensor_fixed_coordinates`.
(blueprint: lem-sf-finite-partial-tensor-identity-naturality-coordinates) -/
theorem finitePartialTensor_identityNaturality_coordinates
    (S : SixFunctorFiniteOperations D C E n hn) (X : SixFunctorSpace D) :
    let U := S.finite.pull (𝟙 X)
    let V := CompactSupportFiniteProjection.torPull S (𝟙 X)
    let T := Functor.uncurry.obj (CompactSupportFiniteProjection.partialTensor S X)
    ∀ (M M' : sixFunctorFiniteCategory D C E n hn X)
      (L L' : finiteTorConstructibleCategory C.l E n hn X.obj.left)
      (f : M ⟶ M') (g : L ⟶ L'),
      (CompactSupportFiniteProjection.coordinates (C := C) (E := E) (n := n)
          (hn := hn) X).map (U.map (T.map (Prod.mkHom f g))) ≫
        (CompactSupportFiniteProjection.coordinates (C := C) (E := E) (n := n)
          (hn := hn) X).map
          (CompactSupportFiniteProjection.pullbackTensorComparison S (𝟙 X) M' L').hom ≫
        (CompactSupportFiniteProjection.targetCoordinates S (𝟙 X) (U.obj M') L').hom =
      (CompactSupportFiniteProjection.coordinates (C := C) (E := E) (n := n)
          (hn := hn) X).map
          (CompactSupportFiniteProjection.pullbackTensorComparison S (𝟙 X) M L).hom ≫
        (CompactSupportFiniteProjection.coordinates (C := C) (E := E) (n := n)
          (hn := hn) X).map
          (T.map (Prod.mkHom (U.map f) (V.map g))) ≫
      (CompactSupportFiniteProjection.targetCoordinates S (𝟙 X) (U.obj M') L').hom  := by
  dsimp
  intro M M' L L' f g
  simp only [Functor.map_comp, Category.assoc]
  rw [CompactSupportFiniteProjection.pullbackTensor_fixed_coordinates]
  simpa only [Functor.uncurry_obj_map, Functor.uncurry_obj_obj, Functor.prod_map,
    Functor.prod_obj, Functor.map_comp, Category.assoc] using
    (finitePartialTensor_identityNaturality_coordinates_expanded S X M M' L L' f g)

end WeilConjectures
