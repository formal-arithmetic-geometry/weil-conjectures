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
(blueprint: lem-weil-pbc-affine-formal-map-presentation).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

/-- A completed-module presentation of a formal map, before algebraic gluing.

Source: Stacks Project, Tags 087W, 0888, 00MA and 0889(1).
(blueprint: lem-weil-pbc-affine-formal-map-presentation).

Proof: identify X with Spec of its global sections using the canonical affine
isomorphism. Transport J to its ideal I of global sections. Tag 087W represents N
by a finite module Q over S, and affine coherent sections represent H by a finite
A-module P, with sheafification isomorphism ε. The completion tensor comparison for
finite P gives η. Naturality identifies δ with an S-linear map φ followed by these
comparisons. Remark 0888 identifies the uniform component bound with a positive
annihilating power for the A-linear kernel and cokernel of φ, allowing the exponent
to increase. The displayed equation for η fixes it as the quotient-system map induced
by p ↦ 1 ⊗ p. All statements
hold for I=0, I=A and the zero ring: the unit map induces identity or zero quotient
systems in these cases. This theorem constructs no algebraic candidate T.
-/
theorem affine_formal_map_presentation
    {X : Scheme.{u}} [IsNoetherian X] [IsAffine X] (J : X.IdealSheafData)
    (H : CoherentModules X) (N : CoherentFormalModule X J)
    (δ : N ⟶ (completion X J).obj H)
    (htorsion : ∃ t : ℕ, 1 ≤ t ∧ ∀ e : ℕ,
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι t).2
        (kernel (δ.hom.app (op e)))) ∧
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι t).2
        (cokernel (δ.hom.app (op e))))) :
    let A := Γ(X, ⊤)
    let I := J.ideal ⟨⊤, isAffineOpen_top X⟩
    let S := AdicCompletion I A
    let L := tilde.functor A ⋙ Scheme.Modules.pullback X.isoSpec.hom
    let C := L ⋙ formalCompletionFunctor J
    ∃ (P : ModuleCat.{u} A) (Q : ModuleCat.{u} S),
      letI := Module.restrictScalars A S Q
      letI := IsScalarTower.restrictScalars A S Q
      ∃ (φ : Q →ₗ[S] S ⊗[A] P) (ε : L.obj P ≅ H.obj)
        (ρ : N.obj ≅ C.obj (ModuleCat.of A Q))
        (η : C.obj P ≅ C.obj (ModuleCat.of A (S ⊗[A] P))),
        η.hom = C.map (ModuleCat.ofHom (TensorProduct.mk A S P (1 : S))) ∧
        δ.hom = ρ.hom ≫ C.map (ModuleCat.ofHom (φ.restrictScalars A)) ≫
          η.inv ≫ (formalCompletionFunctor J).map ε.hom ∧
        ∃ t : ℕ, 1 ≤ t ∧
          I ^ t ≤ Module.annihilator A (φ.restrictScalars A).ker ∧
          I ^ t ≤ Module.annihilator A ((S ⊗[A] P) ⧸ (φ.restrictScalars A).range) := by sorry

end AlgebraicGeometry
