/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CompactSupportFiniteProjection.FinitePartialPullbackTensor
import WeilConjectures.AlgebraicGeometry.FiniteDerivedPullbackTensorIdentityComposition
import WeilConjectures.SixFunctors.FinitePartialTensorIdentityComponentCoordinates

/-! The component composition equation for the finite partial tensor comparison.
(blueprint: lem-sf-finite-partial-tensor-identity-component) -/

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

/-- The prescribed comparison has the identity-composition component equation.
This is the second conjunct of the parent theorem after the natural-isomorphism
family has been fixed, and is proved by the coefficient-equivalence cancellation
calculation and `finitePullCompositionNormalization`.
Source: Stacks Project, sites-cohomology.tex, Tag 07A4, and the composition clause
of `lem-pur-derived-pullback-tensor-iso`.
(blueprint: lem-sf-finite-partial-tensor-identity-component). -/
theorem finitePartialTensor_identityComponent
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
    ∀ M L,
      (CompactSupportFiniteProjection.pullbackTensorComparison S (𝟙 X) M L).hom ≫
          T.map (Prod.mkHom (c M).hom (d L).hom) =
        (c (T.obj (M, L))).hom ≫
          U.map ((CompactSupportFiniteProjection.pullbackTensorComparison S (𝟙 X) M L).hom) ≫
          (CompactSupportFiniteProjection.pullbackTensorComparison S (𝟙 X)
            (U.obj M) (V.obj L)).hom := by
  dsimp only
  intro M L
  apply (CompactSupportFiniteProjection.coordinates (C := C) (E := E) (n := n)
    (hn := hn) X).map_injective
  simp only [Functor.map_comp]
  apply (cancel_mono (CompactSupportFiniteProjection.targetCoordinates S (𝟙 X)
    ((S.finite.pull (𝟙 X)).obj ((S.finite.pull (𝟙 X)).obj M))
    ((CompactSupportFiniteProjection.torPull S (𝟙 X)).obj L)).hom).1
  simpa only [Functor.map_comp, Category.assoc] using
    (finitePartialTensor_identityComponent_coordinates S X M L)

end WeilConjectures
