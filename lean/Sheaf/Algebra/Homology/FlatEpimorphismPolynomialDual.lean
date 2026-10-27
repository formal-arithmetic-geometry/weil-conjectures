/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q116
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import Sheaf.Algebra.Homology.DerivedCoinductionAdjunction
public import WeilConjectures.RingTheory.KoszulDualComplex
import Sheaf.Algebra.Homology.BaseChangeRHomPerfect
import Sheaf.Algebra.Homology.DerivedHomProjectiveResolution
import WeilConjectures.RingTheory.KoszulConormalBasis
import WeilConjectures.RingTheory.KoszulRegularSequenceDualComplex
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.RingTheory.RegularSequenceKoszulRegular

/-! # Polynomial duality for flat ring epimorphisms

Source: Stacks Project, dualizing.tex, Tag 0C0H, self-base-change calculation;
more-algebra.tex, Tag 0A6A(1); duality.tex, Tag 0BQZ
(blueprint: lem-trf-flat-epimorphism-polynomial-dual).

The graph polynomial ring is written as A[x₁,...,xₙ], the standard presentation of
P ⊗[R] A. Its quotient map evaluates xᵢ at the image aᵢ of the original variable.
The first isomorphism is normalized through the actual restriction/coinduction
adjunction and an ordered Koszul roof, rather than an arbitrary Hom comparison.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u wP wS wA

open CategoryTheory
open scoped TensorProduct

namespace ModuleCat

/-- The ordered graph equations xᵢ - aᵢ. No regularity or nonzero-ring assumption.
Source: Stacks 0C0H and 0BQZ
(blueprint: lem-trf-flat-epimorphism-polynomial-dual). -/
def polynomialDualGraphSequence {A : Type u} [CommRing A] (n : ℕ) (a : Fin n → A) :
    Fin n → MvPolynomial (Fin n) A :=
  fun i ↦ MvPolynomial.X i - MvPolynomial.C (a i)

/-- The recorded Koszul complex of the graph equations, in degrees -n through zero.
Source: Stacks 0C0H and 0BQZ
(blueprint: lem-trf-flat-epimorphism-polynomial-dual). -/
def polynomialDualGraphKoszul {A : Type u} [CommRing A] (n : ℕ) (a : Fin n → A) :
    CochainComplex (ModuleCat.{u} (MvPolynomial (Fin n) A)) ℤ :=
  (ExteriorAlgebra.koszulComplex (MvPolynomial (Fin n) A) n
    (polynomialDualGraphSequence n a)).extend ComplexShape.embeddingDownNat

/-- Ordered dual Koszul normalization of the graph-coinduction isomorphism.
The augmentation ε is the evaluation quotient, specified on every degree-zero element.
The adjunction mate of e⁻¹ is represented by the shifted Koszul roof z. Its top
functional is a cycle of the recorded signed dual Koszul complex and evaluates to
(-1)^(n(n-1)/2) on e₀ ∧ ... ∧ eₙ₋₁ after evaluation in A. By the canonical comparison
H^n ≅ ⋀^n Hom(I/I²,A) of lem-sc-koszul-regular-sequence-dual-complex, whose determinant
normalization carries the Stacks ordered-contraction sign (-1)^(n(n-1)/2), this class
is exactly the wedge of the dual ordered conormal basis, i.e. the inverse image of 1
under evaluation on the ordered conormal basis. This fixes the actual first isomorphism,
not an independently chosen cohomology isomorphism. The target single in degree n is A[-n].
Source: Stacks 0C0H, 0A70, 0A71 and 0BQZ
(blueprint: lem-trf-flat-epimorphism-polynomial-dual). -/
def IsOrderedPolynomialDualGraphIso {A : Type u} [CommRing A]
    (n : ℕ) (a : Fin n → A)
    [HasDerivedCategory.{wS} (ModuleCat.{u} (MvPolynomial (Fin n) A))]
    [HasDerivedCategory.{wA} (ModuleCat.{u} A)]
    (e : (derivedCoinduction (MvPolynomial.eval a)).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} (MvPolynomial (Fin n) A)) 0).obj
          (ModuleCat.of (MvPolynomial (Fin n) A) (MvPolynomial (Fin n) A))) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} A) (n : ℤ)).obj (ModuleCat.of A A)) :
    Prop :=
  ∃ ε : polynomialDualGraphKoszul n a ⟶
      (CochainComplex.singleFunctor (ModuleCat.{u} (MvPolynomial (Fin n) A)) 0).obj
        ((restrictScalars (MvPolynomial.eval a)).obj (ModuleCat.of A A)),
    QuasiIso ε ∧
    (∀ x : ⋀[MvPolynomial (Fin n) A]^0 (Fin n →₀ MvPolynomial (Fin n) A),
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0
        ((restrictScalars (MvPolynomial.eval a)).obj (ModuleCat.of A A))).hom
        (ε.f 0 (((ExteriorAlgebra.koszulComplex (MvPolynomial (Fin n) A) n
          (polynomialDualGraphSequence n a)).extendXIso
            ComplexShape.embeddingDownNat (i := 0) rfl).inv x)) =
        MvPolynomial.eval a (exteriorPower.zeroEquiv (MvPolynomial (Fin n) A)
          (Fin n →₀ MvPolynomial (Fin n) A) x)) ∧
    ∃ z : (polynomialDualGraphKoszul n a)⟦-(n : ℤ)⟧ ⟶
        (CochainComplex.singleFunctor (ModuleCat.{u} (MvPolynomial (Fin n) A)) 0).obj
          (ModuleCat.of (MvPolynomial (Fin n) A) (MvPolynomial (Fin n) A)),
      DerivedCategory.Q.map z =
        DerivedCategory.Q.map (ε⟦-(n : ℤ)⟧') ≫
          DerivedCategory.Q.map
            (((CochainComplex.singleFunctors (ModuleCat.{u} (MvPolynomial (Fin n) A))).shiftIso
              (-(n : ℤ)) (n : ℤ) 0 (neg_add_cancel (n : ℤ))).hom.app
                ((restrictScalars (MvPolynomial.eval a)).obj (ModuleCat.of A A))) ≫
          ((restrictScalars (MvPolynomial.eval a)).mapDerivedCategorySingleFunctor
            (n : ℤ)).inv.app (ModuleCat.of A A) ≫
          ((derivedCoinductionAdjunction (MvPolynomial.eval a)).homEquiv _ _).symm e.inv ∧
      ∃ y : (ExteriorAlgebra.koszulDualComplex (MvPolynomial (Fin n) A) n
          (polynomialDualGraphSequence n a)).cycles n,
        (ExteriorAlgebra.koszulDualComplex (MvPolynomial (Fin n) A) n
          (polynomialDualGraphSequence n a)).iCycles n y =
            ((ExteriorAlgebra.koszulComplex (MvPolynomial (Fin n) A) n
              (polynomialDualGraphSequence n a)).extendXIso
                ComplexShape.embeddingDownNat (i := n) rfl).inv ≫
            ((polynomialDualGraphKoszul n a).shiftFunctorObjXIso
              (-(n : ℤ)) 0 (-(n : ℤ)) (zero_add _).symm).inv ≫
            z.f 0 ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) 0
              (ModuleCat.of (MvPolynomial (Fin n) A) (MvPolynomial (Fin n) A))).hom ∧
        MvPolynomial.eval a
          (((ExteriorAlgebra.koszulDualComplex (MvPolynomial (Fin n) A) n
            (polynomialDualGraphSequence n a)).iCycles n y).hom
              (exteriorPower.ιMulti (MvPolynomial (Fin n) A) n
                (fun i ↦ Finsupp.single i 1))) = (-1 : A) ^ (n * (n - 1) / 2)

/-- Polynomial dualizing objects for a flat ring epimorphism, with ordered graph
Koszul normalization and the original coinduced A-action on both isomorphisms.
No Noetherian or regular-base hypothesis is imposed, and n=0 and A=0 are included.
Source: Stacks 0C0H, expanded by More on Algebra 0A6A(1) and Duality 0BQZ
(blueprint: lem-trf-flat-epimorphism-polynomial-dual).

Proof (the node's six steps):
1. Substitution gives S/(x₁-a₁,...,xᵢ-aᵢ)=A[xᵢ₊₁,...,xₙ]. Multiplication by the
next monic polynomial xᵢ₊₁-aᵢ₊₁ is injective by its highest coefficient, including
when A=0. Thus the graph sequence is weakly regular.
2. lem-weil-pbc-regular-sequence-koszul-regular makes its Koszul complex a finite
free resolution of A. lem-sc-koszul-conormal-basis identifies the conormal basis
in this order. lem-sc-koszul-regular-sequence-dual-complex computes the signed
dual in degree n; evaluation on the ordered conormal basis sends the dual ordered
wedge to 1, i.e. a top cocycle with value (-1)^(n(n-1)/2) on e₀ ∧ ... ∧ eₙ₋₁.
3. lem-trf-derived-coinduction-adjunction and
lem-sc-derived-hom-projective-resolution compute graph coinduction by this dual.
For a lift s of b in A, h(ab)=h(sa)=s h(a), so the computed top identification
is A-linear for the original coinduction action. Apply
lem-sf-derived-concentrated-single in D(A). Under the actual adjunction its
inverse is the normalized ordered Koszul roof appearing in the predicate above.
4. lem-weil-pbc-flat-tensor-exact makes tensor with A exact and identifies derived
base change P→S with ordinary tensor. Multiplication A⊗[R]A≅A identifies the
base change of A with A. For every A-module V, v↦v⊗1 is invertible since
V⊗[R]A=V⊗[A](A⊗[R]A); balancing gives v⊗b=bv⊗1.
5. Apply lem-pc-base-change-rhom-perfect to the perfect P-object A[0] and P[0].
Using step 4 compares the underlying P-cohomology of C_A^P(P) and C_A^S(S).
This is the only use of perfectness, and requires no Noetherian hypothesis.
6. Lift each b in A to p in P along the given surjection. Its coinduction action
on either Hom complex is multiplication by that lift, so the P-linear comparison
is A-linear for the original actions. Reconstruct in D(A) using
lem-sf-derived-concentrated-single and shift by n. For n=0 the empty exterior
wedge is 1; for A=0 both objects and all displayed maps are zero. -/
theorem exists_flatEpimorphism_polynomialDual_iso
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (hflat : (algebraMap R A).Flat)
    (hmul : Function.Bijective (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A))
    (n : ℕ) (p : MvPolynomial (Fin n) R →ₐ[R] A) (hp : Function.Surjective p)
    [HasDerivedCategory.{wP} (ModuleCat.{u} (MvPolynomial (Fin n) R))]
    [HasDerivedCategory.{wS} (ModuleCat.{u} (MvPolynomial (Fin n) A))]
    [HasDerivedCategory.{wA} (ModuleCat.{u} A)]
    (hperfect : DerivedCategory.IsPerfectRingComplex
      ((restrictScalars p.toRingHom).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)))) :
    (∃ e : (derivedCoinduction (MvPolynomial.eval (fun i ↦ p (MvPolynomial.X i)))).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} (MvPolynomial (Fin n) A)) 0).obj
          (ModuleCat.of (MvPolynomial (Fin n) A) (MvPolynomial (Fin n) A))) ≅
          (DerivedCategory.singleFunctor (ModuleCat.{u} A) (n : ℤ)).obj (ModuleCat.of A A),
      IsOrderedPolynomialDualGraphIso n (fun i ↦ p (MvPolynomial.X i)) e) ∧
    Nonempty (((derivedCoinduction p.toRingHom).obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} (MvPolynomial (Fin n) R)) 0).obj
        (ModuleCat.of (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) R))))⟦(n : ℤ)⟧ ≅
          (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)) := by
  sorry

end ModuleCat
