/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J4
-/
module

public import Sheaf.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.RingTheory.AdicCompletion.Algebra

/-! # Affine section quotients of stabilized formal kernels

Source: Stacks Project, Tags 087W and 087X, affine calculation for claim (a).
(blueprint: lem-weil-pbc-formal-kernel-affine-section-quotients).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- Stabilized formal kernel sections are compatible quotients of one completed submodule.

Source: Stacks Project, Lemma 087X (lemma-inverse-systems-abelian), calculation of
K prime_m, using Lemma 087W (lemma-inverse-systems-affine).
(blueprint: lem-weil-pbc-formal-kernel-affine-section-quotients).

Proof: Restrict both formal systems and their map to U, and transport along U's
canonical isomorphism with Spec Gamma(U,O_X). The affine formal-module equivalence
gives finite completed modules N and P, a completed-linear map f, and compatible
surjective A-linear projections with kernels K^(m+1)N and K^(m+1)P. Put L = ker f.
The reduced-kernel image bound supplies a. At level l = max(m+c,m+a), the image
of the finite-level kernel in N/K^(m+1)N equals the image of L. Stabilization hc
identifies this with the image at m+c. Affine sections preserve kernels and images
of quasi-coherent modules, so hS identifies this image with Gamma(U,S_m).
Restriction of the projection to L followed by this identification defines q_m;
it is surjective and its zero criterion is membership in K^(m+1)N. The components
of j are monic by hS. Apply naturality of j to q_b(z) and cancel j_a on sections
to obtain transition compatibility for every a <= b.
No stalks, localized submodule order maps, or intersection bounds are constructed.
Empty U, zero modules, and zero or unit ideals obey the same quotient formulas. -/
theorem coherentFormalModule_kernel_affine_section_quotients
    {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (F H : CoherentFormalModule X I) (α : F ⟶ H)
    (c : ℕ) (S : ℕᵒᵖ ⥤ X.Modules) (j : S ⟶ F.obj)
    (hc : ∀ (l m : ℕ) (h : m + c ≤ l),
      Subobject.mk
          (Abelian.image.ι (kernel.ι (α.hom.app (op l)) ≫
            F.obj.map (homOfLE (Nat.le_trans (Nat.le_add_right m c) h)).op)) =
        Subobject.mk
          (Abelian.image.ι (kernel.ι (α.hom.app (op (m + c))) ≫
            F.obj.map (homOfLE (Nat.le_add_right m c)).op)))
    (hS : ∀ m : ℕ, ∃ e : S.obj (op m) ≅
      Abelian.image (kernel.ι (α.hom.app (op (m + c))) ≫
        F.obj.map (homOfLE (Nat.le_add_right m c)).op),
      e.hom ≫ Abelian.image.ι (kernel.ι (α.hom.app (op (m + c))) ≫
        F.obj.map (homOfLE (Nat.le_add_right m c)).op) = j.app (op m))
    (U : X.affineOpens) :
    let A := Γ(X, U.1)
    let R := AdicCompletion (I.ideal U) A
    let K := (I.ideal U).map (algebraMap A R)
    ∃ N : ModuleCat.{u} R, Module.Finite R N ∧
      ∃ L : Submodule R N,
        ∃ q : ∀ m : ℕ,
          ((ModuleCat.restrictScalars (algebraMap A R)).obj (ModuleCat.of R L))
            →ₗ[A] Γ(S.obj (op m), U.1),
          (∀ m : ℕ, Function.Surjective (q m)) ∧
          (∀ (a b : ℕ) (h : a ≤ b) (z : L),
            (S.map (homOfLE h).op).app U.1 (q b z) = q a z) ∧
          (∀ (m : ℕ) (z : L), q m z = 0 ↔
            L.subtype z ∈ K ^ (m + 1) • (⊤ : Submodule R N)) := by sorry

end AlgebraicGeometry
