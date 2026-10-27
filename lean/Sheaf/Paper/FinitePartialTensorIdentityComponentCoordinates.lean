/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.FinitePullbackTensorFixedCoordinates
import Sheaf.Paper.FiniteDerivedPullbackTensorIdentityComposition

/-! Fixed-coefficient coordinate square for the finite partial tensor identity.
(blueprint: lem-sf-finite-partial-tensor-identity-fixed-coordinates)

The proof expands the prescribed pullback/tensor comparison through the full
constructible inclusion and the coefficient realization.  The two realization
units cancel, and the remaining square is the identity specialization of the
fixed-coefficient derived pullback/tensor comparison.  The latter is the
composition theorem `leftDerivedUpperStarTensorComparison_identityComposition`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.GeneralAlgebraicallyClosedCoefficients
namespace WeilConjectures

variable {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
  {E : Type u} [Field E] [Algebra (Padic C.l) E]
  [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}

/-- The identity-composition equation after passage to fixed coefficient
coordinates and postcomposition with the target coordinate comparison.
Source: Stacks Project, sites-cohomology.tex, Tag 07A4, and the fixed-coefficient
calculation in `lem-sf-finite-derived-pullback-tensor-identity-composition`.
(blueprint: lem-sf-finite-partial-tensor-identity-fixed-coordinates). -/
theorem finitePartialTensor_identityComponent_coordinates
    (S : SixFunctorFiniteOperations D C E n hn) (X : SixFunctorSpace D) :
    let U := S.finite.pull (𝟙 X)
    let V := CompactSupportFiniteProjection.torPull S (𝟙 X)
    let T := Functor.uncurry.obj (CompactSupportFiniteProjection.partialTensor S X)
    let c : ∀ M, U.obj M ≅ U.obj (U.obj M) := fun M ↦
      eqToIso (congrArg (fun f ↦ (S.finite.pull f).obj M)
        (Category.id_comp (𝟙 X)).symm) ≪≫
        (S.finite.pullComposition (𝟙 X) (𝟙 X)).app M
    let d : ∀ L, V.obj L ≅ V.obj (V.obj L) := fun L ↦
      eqToIso (congrArg (fun f ↦ (CompactSupportFiniteProjection.torPull S f).obj L)
        (Category.id_comp (𝟙 X)).symm) ≪≫
        CompactSupportFiniteProjection.torPullComposition S (𝟙 X) (𝟙 X) L
    ∀ (M : sixFunctorFiniteCategory D C E n hn X)
      (L : finiteTorConstructibleCategory C.l E n hn X.obj.left),
      (CompactSupportFiniteProjection.coordinates (C := C) (E := E) (n := n)
        (hn := hn) X).map
          ((CompactSupportFiniteProjection.pullbackTensorComparison S (𝟙 X) M L).hom ≫
            T.map (Prod.mkHom (c M).hom (d L).hom)) ≫
        (CompactSupportFiniteProjection.targetCoordinates S (𝟙 X)
          (U.obj (U.obj M)) (V.obj L)).hom =
      (CompactSupportFiniteProjection.coordinates (C := C) (E := E) (n := n)
        (hn := hn) X).map
          ((c (T.obj (M, L))).hom ≫
            U.map ((CompactSupportFiniteProjection.pullbackTensorComparison S (𝟙 X) M L).hom) ≫
            (CompactSupportFiniteProjection.pullbackTensorComparison S (𝟙 X)
              (U.obj M) (V.obj L)).hom) ≫
        (CompactSupportFiniteProjection.targetCoordinates S (𝟙 X)
          (U.obj (U.obj M)) (V.obj L)).hom := by
  sorry

end WeilConjectures
