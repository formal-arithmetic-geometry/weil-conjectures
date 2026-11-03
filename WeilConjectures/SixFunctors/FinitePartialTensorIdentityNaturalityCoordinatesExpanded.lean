/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CompactSupportFiniteProjection.FinitePullbackTensorFixedCoordinates
import WeilConjectures.SixFunctors.FinitePartialTensorIdentityNaturalityCoordinatesExpandedCore

/-! The remaining scalar naturality calculation after expanding the pullback tensor
comparison in fixed coordinates.
(blueprint: lem-sf-finite-partial-tensor-identity-naturality-coordinates-expanded) -/

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

set_option maxHeartbeats 800000 in
-- The expanded categorical reassociation needs additional elaboration heartbeats.
/-- After replacing the left comparison by `pullbackTensor_fixed_coordinates`,
all remaining factors satisfy the required naturality equation.  This is the
fixed scalar calculation: tensor coordinates, the upper-star tensor comparison,
and the two fixed pullback realizations are natural in both inputs.
Source: Stacks Project, sites-cohomology.tex, Tag 07A4, and the fixed-coordinate
expansion in `pullbackTensor_fixed_coordinates`.
(blueprint: lem-sf-finite-partial-tensor-identity-naturality-coordinates-expanded) -/
theorem finitePartialTensor_identityNaturality_coordinates_expanded
    (S : SixFunctorFiniteOperations D C E n hn) (X : SixFunctorSpace D) :
    letI := Padic.finite_coefficientExtensionRing C.l E n hn
    let U := S.finite.pull (𝟙 X)
    let V := CompactSupportFiniteProjection.torPull S (𝟙 X)
    let T := Functor.uncurry.obj (CompactSupportFiniteProjection.partialTensor S X)
    ∀ (M M' : sixFunctorFiniteCategory D C E n hn X)
      (L L' : finiteTorConstructibleCategory C.l E n hn X.obj.left)
      (f : M ⟶ M') (g : L ⟶ L'),
      (CompactSupportFiniteProjection.coordinates (C := C) (E := E) (n := n)
          (hn := hn) X).map (U.map (T.map (Prod.mkHom f g))) ≫
        (CompactSupportFiniteProjection.fixedPullRealization S (𝟙 X)
          (T.obj (M', L'))).hom ≫
        (CompactSupportFiniteProjection.fixedDerivedPull
          (C := C) (E := E) (n := n) (𝟙 X)).map
          (CompactSupportFiniteProjection.tensorCoordinates S X M' L').hom ≫
        ((AlgebraicGeometry.ProEtale.leftDerivedUpperStarTensorComparison
          (ModuleCat.{u + 1} (ULift.{u + 1}
          (Padic.coefficientExtensionRing C.l E n))) ((𝟙 X : X ⟶ X).hom.left)).app
          ((CompactSupportFiniteProjection.coordinates (C := C) (E := E) (n := n)
            (hn := hn) X).obj M')).app
          ((realization (C := C) (E := E) (n := n) (hn := hn) X).inverse.obj L'.obj) ≫
        ((CompactSupportFiniteProjection.fixedTensor (C := C) (E := E) (n := n) X).map
          (CompactSupportFiniteProjection.fixedPullRealization S (𝟙 X) M').inv).app
          ((CompactSupportFiniteProjection.fixedDerivedPull
            (C := C) (E := E) (n := n) (𝟙 X)).obj
            ((realization (C := C) (E := E) (n := n) (hn := hn) X).inverse.obj L'.obj)) =
      (CompactSupportFiniteProjection.coordinates (C := C) (E := E) (n := n)
          (hn := hn) X).map
          (CompactSupportFiniteProjection.pullbackTensorComparison S (𝟙 X) M L).hom ≫
        (CompactSupportFiniteProjection.coordinates (C := C) (E := E) (n := n)
          (hn := hn) X).map (T.map (Prod.mkHom (U.map f) (V.map g))) ≫
        (CompactSupportFiniteProjection.targetCoordinates S (𝟙 X) (U.obj M') L').hom := by
  dsimp only
  intro M M' L L' f g
  simp only [Functor.uncurry_obj_map, Functor.uncurry_obj_obj,
    CompactSupportFiniteProjection.targetCoordinates, Iso.trans_hom,
    Functor.mapIso_hom]
  have hpull := (CompactSupportFiniteProjection.pullCoordinatesIso S (𝟙 X)).hom.naturality
    (((CompactSupportFiniteProjection.partialTensor S X).map f).app L ≫
      ((CompactSupportFiniteProjection.partialTensor S X).obj M').map g)
  simp only [Functor.comp_map] at hpull
  have hcoord := CompactSupportFiniteProjection.pullCoordinatesIso_hom_app S (𝟙 X)
    (((CompactSupportFiniteProjection.partialTensor S X).obj M).obj L)
  have hcoord' := CompactSupportFiniteProjection.pullCoordinatesIso_hom_app S (𝟙 X)
    (((CompactSupportFiniteProjection.partialTensor S X).obj M').obj L')
  rw [hcoord, hcoord'] at hpull
  rw [reassoc_of% hpull]
  exact finitePartialTensor_identityNaturality_coordinates_expanded_core S X M M' L L' f g


end WeilConjectures
