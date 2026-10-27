/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D7
-/
module

public import Sheaf.Paper.ConcreteProjectionFactorizationData

/-! # The open scalar and tensor square

Source: Stacks Project, Cohomology on Sites.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
namespace WeilConjectures.ConcreteProjectionReduction
open AlgebraicGeometry.ProEtale.OpenScalarTensor
variable (m : Models.{u}) (choices : Choices m)

/-- Scalar change commutes with the open tensor map and the compactification
pullback compositor, with no assumption on the schemes' structure maps.
Source: Stacks Tags 0GL1 and 0D6D, open projection and pullback composition.
(blueprint: lem-sf-concrete-open-scalar-tensor-square).

Proof: first omit the pullback compositor in openFactor. The inverse of the open
projection is characterized by its open-adjunction transpose: tensor the open
unit with identity and then apply inverse tensor pullback. Transpose the inverses
of the two routes through the open adjunction. The scalar/open mate respects the
open unit; the scalar and geometric tensor comparisons commute on flat K-flat
representatives. These equations identify the transposes and hence the original
routes. Restore the geometric compositor Lj* Lg* = Lf*. The coefficient/geometric
composition normalization carries lambda for f to the composite of the lambdas
for g and j, including the equality c.comm. Naturality of the tensor maps then
gives the displayed equation. The open projection is invertible; no proper
projection is inverted. The calculation also covers empty opens, zero rings and
identity coefficient maps. -/
theorem open_scalar_tensor_square
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (K : proEtaleDerivedCategory X A)
    (L : proEtaleDerivedCategory Y A) :
    (scalar m φ c.Z).map (openFactor m A c K L).hom ≫
      (openScalar m φ c.i).app (input m A f K L) ≫
      (openImage B c.i).map (inputComparison m choices φ f K L).hom =
    (inputComparison m choices φ c.g ((openImage A c.i).obj K) L).hom ≫
      (tensor m B c.Z).map (Prod.mkHom ((openScalar m φ c.i).app K) (𝟙 _)) ≫
      (openFactor m B c ((scalar m φ X).obj K) ((scalar m φ Y).obj L)).hom := by
  sorry

end WeilConjectures.ConcreteProjectionReduction
