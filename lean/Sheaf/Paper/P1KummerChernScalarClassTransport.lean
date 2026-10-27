/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.P1KummerScalarEndpoints
public import Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Kummer

/-! # Underlying scalar transport for the ordinary P1 Kummer class

These are the two concrete transport identities used by the scalar Chern theorem.
They isolate the Ext comparison from the final Kummer normalization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

/-- Forget the coefficient restriction on a normalized Tate-line insertion.
Source: Stacks 03PL and 06YY; blueprint lem-sp-p1-kummer-chern-scalar.
The two forgetful sheaf functors have definitionally identical underlying additive
maps after restriction of scalars, and the identity natural isomorphism records
that comparison explicitly. -/
def p1KummerScalarForgetLineMap
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    {φ : A →+* B} {N : ℕ} {hA : (N : A) = 0} {hB : (N : B) = 0}
    {T : Scheme.{u}} (e : P1KummerScalarEndpoints φ N hA hB T) :
    (moduleAbelianForget A T).obj
        (Scheme.finiteEtaleTateLine T N A hA) ⟶
      (moduleAbelianForget B T).obj
        (Scheme.finiteEtaleTateLine T N B hB) := by
  let UA := moduleAbelianForget A T
  let UB := moduleAbelianForget B T
  let R := Sheaf.restrictScalars T.smallEtaleTopology φ
  let i : R ⋙ UA ≅ UB := {
    hom := { app := fun X => 𝟙 (UB.obj X)
             naturality := by intro X Y f; ext W x; rfl }
    inv := { app := fun X => 𝟙 (UB.obj X)
             naturality := by intro X Y f; ext W x; rfl }
    hom_inv_id := by ext X W x; rfl
    inv_hom_id := by ext X W x; rfl }
  exact UA.map (show _ ⟶ R.obj _ from e.lineInsertion) ≫ i.hom.app _

/-- The ordinary Ext class of the transported arrow is the forgotten image of the
original class. This is the Ext/shift comparison part of scalar Chern transport.
Source: Stacks 03PL and 06YY.
(blueprint: lem-sp-p1-kummer-chern-class-transport)
Proof: transpose the conjugate through the scalar adjunction, use the endpoint
unit and line derived equations, then apply exact-functor composition comparison
and evaluate on the integral constant generator. -/
theorem p1KummerChernScalar_class_transport
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    {φ : A →+* B} {N : ℕ} {hA : (N : A) = 0} {hB : (N : B) = 0}
    {T : Scheme.{u}} (e : P1KummerScalarEndpoints φ N hA hB T)
    (c : ordinaryFiniteUnit A T ⟶
      (ordinaryFiniteLine A N hA T)⟦(2 : ℤ)⟧) :
    ordinaryFiniteClass B T (Scheme.finiteEtaleTateLine T N B hB) 2
        (e.chernImage c) =
      Sheaf.H.map (p1KummerScalarForgetLineMap e) 2
        (ordinaryFiniteClass A T (Scheme.finiteEtaleTateLine T N A hA) 2 c) := by
  sorry

end AlgebraicGeometry.Etale
