/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Sheaf.Algebra.Homology.PerfectRHomBaseChangeMap

/-! # Transport of a module Hom comparison to the one-point ring site

Source: Stacks Project, more-algebra.tex, equation-base-change-RHom and
Lemma 0A6A; the one-point-site realization used in the parent statement.
(blueprint: lem-pc-ring-hom-extension-transport)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

namespace CategoryTheory

/-- Transport a normalized ordinary module comparison to the one-point site.
No finite-generation, projectivity, flatness, or invertibility assumption is made.
Invertibility of the transported map is equivalent to bijectivity of the module map.

Source: Stacks Project, more-algebra.tex, equation-base-change-RHom and Lemma 0A6A;
one-point-site realization in step 1 of the parent finite-projective comparison.
(blueprint: lem-pc-ring-hom-extension-transport).

Proof: write * for the unique object of Discrete PUnit. Evaluation at * is an
equivalence between module presheaves for the constant ring A and ordinary A-modules.
Its inverse is the constant module presheaf. More explicitly, the unique arrow
U -> * induces M(*) -> M(U), with inverse induced by * -> U; the presheaf laws
prove the inverse equations. All presheaves are sheaves for the bottom topology.
The internal Hom at * consists of module maps on the slice over *: evaluating
at the identity slice object identifies it with Hom_A(M(*),N(*)). Conversely a
linear map extends to every slice object by conjugating with the two restriction
isomorphisms just described. Naturality follows from the presheaf composition law,
and the two constructions are inverse by naturality at the arrow to the identity.
For scalar extension, its presheaf value at * is B tensor_A M(*). The sheafification
unit is invertible because this presheaf is already a sheaf; its module linearity
makes it a B-linear isomorphism. Transport further along hF(M) to get a B-linear
isomorphism from B tensor_A M(*) to F(M)(*), sending b tensor x to ringExtensionPure.
Apply these identifications to the source F(Hom_A(M,N)) and target
Hom_B(F(M),F(N)), and conjugate k by them. Evaluation's full faithfulness extends
this B-linear map uniquely to a sheaf morphism g. Evaluation reflects isomorphisms;
conjugating by linear equivalences shows that g is invertible exactly when k is
bijective. At *, the asserted formula follows by the two unit identifications,
the identity-slice Hom identification, and hk. At any U, use the unique isomorphism
U -> *: restrictions commute with the sheafification unit, tensor pure sections,
and the internal-Hom evaluation. Thus restriction of the formula at * is the
formula at U, with exactly the given ringExtensionPure expressions. This argument
also applies to zero rings and zero modules and uses no property of k besides
linearity and hk. -/
theorem ringHomExtension_transport
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    (F : RingSiteModules A ⥤ RingSiteModules B)
    (hF : ∀ M, F.obj M = SheafOfModules.changeOfRings (ringSiteMap φ) M)
    (M N : RingSiteModules A) :
    letI := φ.toAlgebra
    ∀ (k : B ⊗[A] ((M.val.obj (op ⟨PUnit.unit⟩)) →ₗ[A]
          (N.val.obj (op ⟨PUnit.unit⟩))) →ₗ[B]
        ((B ⊗[A] (M.val.obj (op ⟨PUnit.unit⟩))) →ₗ[B]
          (B ⊗[A] (N.val.obj (op ⟨PUnit.unit⟩)))))
      (hk : ∀ (b c : B)
        (f : M.val.obj (op ⟨PUnit.unit⟩) →ₗ[A] N.val.obj (op ⟨PUnit.unit⟩))
        (x : M.val.obj (op ⟨PUnit.unit⟩)),
        k (b ⊗ₜ[A] f) (c ⊗ₜ[A] x) = (b * c) ⊗ₜ[A] f x),
    ∃ g : F.obj (SheafOfModules.homObj (R := CochainComplex.onePointRingSheaf A) M N) ⟶
        SheafOfModules.homObj (R := CochainComplex.onePointRingSheaf B) (F.obj M) (F.obj N),
      (IsIso g ↔ Function.Bijective k) ∧ ∀ (U : (Discrete PUnit.{u + 1})ᵒᵖ) (b c : B)
        (f : (SheafOfModules.homObj (R := CochainComplex.onePointRingSheaf A) M N).val.obj U)
        (x : M.val.obj U),
        ((g.val.app U (ringExtensionPure φ F hF _ U b f)).app
          (op (Over.mk (𝟙 U.unop)))) (ringExtensionPure φ F hF M U c x) =
        ringExtensionPure φ F hF N U (b * c) ((f.app (op (Over.mk (𝟙 U.unop)))) x) := by
  sorry

end CategoryTheory
