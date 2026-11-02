/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.FLCFiber
public import WeilConjectures.AlgebraicGeometry.Galois.GaloisLisseCorrespondenceData
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import Mathlib.RepresentationTheory.Rep.Basic
public import WeilConjectures.AlgebraicGeometry.LisseModuleSheaves
public import WeilConjectures.RepresentationTheory.PoincareDuality.LAdic
public import WeilConjectures.AlgebraicGeometry.Lisse.LisseAdicSheaves
public import Mathlib.CategoryTheory.Conj
public import WeilConjectures.AlgebraicGeometry.Lisse.LisseAdicFiberFunctors

/-! # Interfaces for finite and adic fibre path transport

These are the unchanged stalks, comparisons and transport records formerly defined in
`FibreFunctorBasepointTransport`. Keeping the interface below its existence theorems lets
finite transport and its adic extension have independent proofs.
Source: Stacks 0BND (2), 0BN5; Weil II (1.1.1) b)-d).
(blueprint: new-e5-fibre-path-transport-data)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme

variable {Y : Scheme.{u}}

/-- The module stalk functor restricted to lisse sheaves. Source: Stacks 0BND (2),
0DV5 (blueprint: new-e5-fibre-path-transport-data). -/
abbrev pathModuleFiber {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) (R : Type (u + 1)) [Ring R] :=
  ObjectProperty.ι (IsLisseModuleSheaf (Y := Y) (Λ := R)) ⋙
    (pointSmallEtale y).ulift.{u + 1}.sheafFiber (A := ModuleCat.{u + 1} R)

/-- The canonical comparison with the underlying set stalk, including the universe lift.
Source: Stacks 0DV5; Weil II (1.1.1) b)
(blueprint: new-e5-fibre-path-transport-data). -/
def pathUnderlyingStalk {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) (R : Type (u + 1)) [Ring R]
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)) :=
  (((pointSmallEtale y).ulift.{u + 1}.sheafFiberCompIso
    (CategoryTheory.forget (ModuleCat.{u + 1} R))).symm.app F ≪≫
      ((pointSmallEtale y).uliftSheafFiberIso (Type (u + 1))).app
        (galoisUnderlyingSetSheaf R F)).toEquiv

set_option genSizeOfSpec false in
set_option genInjectivity false in
set_option genSizeOfSpec false in
set_option genInjectivity false in
set_option genSizeOfSpec false in
set_option genInjectivity false in
set_option genSizeOfSpec false in
set_option genInjectivity false in
set_option genSizeOfSpec false in
set_option genInjectivity false in
end AlgebraicGeometry.Scheme
