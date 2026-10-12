/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W3
-/
module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Sheaf.AlgebraicGeometry.FormalKernelGradedPieces
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Sheaf.AlgebraicGeometry.FormalSystemsKernelReesFinite
import Sheaf.AlgebraicGeometry.ModulePullbackIdealQuotient

/-! # A polynomial algebra acting on the successive formal kernels

Source: Stacks Project, Cohomology of Schemes, proofs of Lemmas 0884 and 087Z.
(blueprint: lem-weil-pbc-formal-kernel-polynomial-action).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The successive kernels are locally generated in degree zero over a polynomial algebra
in finitely many degree-one variables over the base ring. This is the algebraic input to
graded Serre vanishing; it asserts no cohomological vanishing and needs no ample module.
Source: Stacks Project, Cohomology of Schemes, proof of Lemma 0884, first paragraph,
and Lemma 087Z (blueprint: lem-weil-pbc-formal-kernel-polynomial-action).

Proof:
1. Choose generators x_1,...,x_r of I, which exist since A is Noetherian. The polynomial
algebra A[T_1,...,T_r], with its total-degree grading, maps onto the associated graded
algebra of I by T_i ↦ x_i mod I^2 and a ↦ a mod I in degree zero.
2. Write J = I O_X. The description of the extended ideal on affine opens shows that
every local section of J^k/J^(k+1) locally is a sum of O_X-multiples of degree-k
monomials in the images of the x_i. Thus the induced map from the pulled-back graded
polynomial algebra onto the associated graded sheaf algebra of J is surjective.
3. Use formalSystems_kernel_rees_finite to obtain the graded action on K_n and its
finite local degree-zero generators. For a homogeneous polynomial b of degree k,
evaluate b in the degree-one images of the x_i and act on K_m. Restriction compatibility
of the sheaf action makes this an O_X-linear sheaf morphism K_m → K_(m+k), after the
commutativity identification of degrees. Additivity and the displayed composition law
follow from the graded algebra and module laws. Constants act through f-sharp, giving
the displayed scalar formula.
4. On a neighbourhood with finite degree-zero generators, the old generating formula
expresses every kernel section locally as a sum with coefficients in J^m/J^(m+1).
Locally lift these finitely many coefficients through the surjection of step 2.
Expand each lift as an O_X-linear combination of degree-m polynomial monomials. This
puts the section in the displayed O_X-span of polynomial actions on the same generators.
The construction also covers I = 0 (zero variables, positive kernels vanish), I = A,
the zero ring and the empty scheme. No equality with a pullback of the associated
graded algebra is needed. -/
theorem formalKernel_polynomial_action
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {X : Scheme.{u}} [IsNoetherian X] (f : X ⟶ Spec (CommRingCat.of A))
    (F : CoherentFormalModule X
      ((Scheme.IdealSheafData.ofIdealTop
        (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).comap f)) :
    ∃ r : ℕ,
      ∃ mu : ∀ (m k : ℕ), MvPolynomial.homogeneousSubmodule (Fin r) A k →
        (formalKernelPiece F m ⟶ formalKernelPiece F (m + k)),
      (∀ (m k : ℕ) (b b' : MvPolynomial.homogeneousSubmodule (Fin r) A k),
        mu m k (b + b') = mu m k b + mu m k b') ∧
      (∀ (m k l : ℕ) (b : MvPolynomial.homogeneousSubmodule (Fin r) A k)
        (b' : MvPolynomial.homogeneousSubmodule (Fin r) A l),
        HEq (mu m l b' ≫ mu (m + l) k b)
          (mu m (k + l) ⟨b.val * b'.val, b.property.mul b'.property⟩)) ∧
      (∀ (m : ℕ) (a : A) (U : X.Opens) (t : (formalKernelPiece F m).val.obj (op U)),
        HEq ((mu m 0 ⟨MvPolynomial.C a, MvPolynomial.isHomogeneous_C (Fin r) a⟩).val.app (op U) t)
          ((X.presheaf.map (homOfLE (le_top (a := U))).op).hom
            (((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom a) • t)) ∧
      (∀ x : X, ∃ (U : X.Opens), x ∈ U ∧
        ∃ (s : ℕ) (t : Fin s → (formalKernelPiece F 0).val.obj (op U)),
          ∀ (m : ℕ) (V : X.Opens) (hVU : V ≤ U)
            (v : (formalKernelPiece F m).val.obj (op V)) (y : X), y ∈ V →
            ∃ (W : X.Opens) (hWV : W ≤ V), y ∈ W ∧
              (formalKernelPiece F m).val.map (homOfLE hWV).op v ∈
                Submodule.span ((moduleRings X.toRingedSpace).obj.obj (op W))
                  {z | ∃ (i : Fin s) (b : MvPolynomial.homogeneousSubmodule (Fin r) A m),
                    HEq z ((mu 0 m b).val.app (op W)
                      ((formalKernelPiece F 0).val.map
                        (homOfLE (hWV.trans hVU)).op (t i)))}) := by sorry

end AlgebraicGeometry
