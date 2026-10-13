/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.RingTheory.AdicCompletion.Algebra

/-! # Affine formal gluing comparison

Source: Stacks Project, Tags 087W, 0888 and 0889(1).
(blueprint: lem-weil-pbc-affine-completion-baseChange-unit).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

/-- Extension along the adic completion leaves every positive sheaf quotient unchanged.
The source module need not be finite.

Source: Stacks Project, Tags 05GG, 087W and 0889(1).
(blueprint: lem-weil-pbc-affine-completion-baseChange-unit).

Proof: for every positive n the completion projection identifies A/I^n with
S/I^n S. Right exactness of tensor therefore identifies T/I^n T with
(S ⊗ T)/I^n(S ⊗ T), via the map x ↦ 1 ⊗ x, for an arbitrary module T.
Exactness of tilde identifies these module quotients with the sheaf quotients,
and pullback along X ≅ Spec A transports the ideal of global sections to J.
Thus each component of the displayed natural transformation is an isomorphism.
A natural transformation with invertible components is itself invertible. No
completion-as-tensor assertion about the possibly infinite T is used. For I=A
all quotients are zero; for I=0 the completion ring and unit map are the identity.
The zero ring and empty spectrum obey the same quotient argument.
-/
theorem affine_completion_baseChange_unit
    {X : Scheme.{u}} [IsNoetherian X] [IsAffine X] (J : X.IdealSheafData) :
    let A := Γ(X, ⊤)
    let I := J.ideal ⟨⊤, isAffineOpen_top X⟩
    let S := AdicCompletion I A
    let L := tilde.functor A ⋙ Scheme.Modules.pullback X.isoSpec.hom
    let C := L ⋙ formalCompletionFunctor J
    ∀ T : ModuleCat.{u} A,
      IsIso (C.map (ModuleCat.ofHom (TensorProduct.mk A S T (1 : S)))) := by sorry

end AlgebraicGeometry
