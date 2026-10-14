/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Sheaf.AlgebraicGeometry.SymmetricAlgebraAffineComparisonMap
import Sheaf.AlgebraicGeometry.QuasiCoherentAffineSectionBaseChange
import Sheaf.RingTheory.SymmetricAlgebraBaseChange

/-! # Sectionwise comparison before sheafification

Source: Stacks Project, Constructions, Lemma 01LN; Schemes, Lemma 01I8;
Algebra, Lemma 0C6F.
(blueprint: lem-weil-pbc-symmetric-algebra-affine-section-comparison).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Opposite CategoryTheory.Functor
namespace AlgebraicGeometry.SymmetricAlgebraSheaf

/-- The restricted sectionwise symmetric algebra maps to the tilde of its affine sections,
on the affine basis, bijectively on each affine open, with composite the unit.
Source: Stacks Project, Constructions, Lemma 01LN; Algebra, Lemma 0C6F;
Schemes, Lemma 01I8.
(blueprint: lem-weil-pbc-symmetric-algebra-affine-section-comparison).

Proof: put R = O_X(W), M = F(W), A = Sym_R(M). For an affine open V of Spec R,
its image U in X is affine and contained in W. Quasi-coherent section base change identifies
F(U) with O_X(U) tensor_R M. Symmetric algebra base change identifies Sym(F(U)) with
O_X(U) tensor_R A. Apply quasi-coherent affine section base change to tilde(A) on
V contained in top, using isoTop to identify its global sections with A. The chart
structure-sheaf isomorphism then identifies this tensor product with tilde(A)(V).
These identifications send
r tensor a to r times restriction(a), hence commute with restrictions between affine opens.
They therefore give a natural transformation on the full affine basis. Each component
is the displayed composite of isomorphisms, so it is bijective. Its composite with the
affine comparison equals the unit: on 1 tensor a this is affineComparison_toOpen, and
linearity extends the equality to all tensors. This uses no finiteness or separatedness. -/
theorem exists_affineSectionComparison {X : Scheme.{u}}
    (F : X.Modules) [F.IsQuasicoherent] {W : X.Opens} (hW : IsAffineOpen W) :
    let B : (Spec Γ(X, W)).affineOpens → (Spec Γ(X, W)).Opens := Subtype.val
    ∃ γ : (inducedFunctor B).op ⋙ hW.fromSpec.opensFunctor.op ⋙ presheaf F ⋙
        (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat.{u}) ⟶
      (inducedFunctor B).op ⋙
        (Scheme.Modules.toPresheaf (Spec Γ(X, W))).obj
          (tilde (R := Γ(X, W)) (ModuleCat.of Γ(X, W) (sections F (op W)))),
      (∀ V : (Spec Γ(X, W)).affineOpens, Function.Bijective (γ.app (op V))) ∧
      (∀ V : (Spec Γ(X, W)).affineOpens,
        γ.app (op V) ≫
          ((Scheme.Modules.toPresheaf (Spec Γ(X, W))).map
            (affineComparison F hW)).app (op V.1) =
          (whiskerLeft hW.fromSpec.opensFunctor.op
            (whiskerRight (toSheafify (Opens.grothendieckTopology X) (presheaf F))
              (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat.{u}))).app
            (op V.1)) := by sorry

end AlgebraicGeometry.SymmetricAlgebraSheaf
