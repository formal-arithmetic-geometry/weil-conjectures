module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # Finite polynomial models of tensor principal opens

Source: Stacks Project, Tag 0F31, proof of (3) implies (1), affine algebra paragraph
(blueprint: lem-sfb-tensor-principal-polynomial-model).

The coefficient map, specialization map and linear polynomial are explicit constructions.
The main statement includes the ring pushout, the cartesian scheme square and both set identities.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open scoped TensorProduct
open CategoryTheory

namespace AlgebraicGeometry.TensorPrincipalPolynomialModel

/-- Coefficient extension from `A[t₁,…,tₙ]` to `C[t₁,…,tₙ]`.
Source: Stacks Project, Tag 0F31, affine algebra paragraph
(blueprint: lem-sfb-tensor-principal-polynomial-model). -/
noncomputable def coefficientMap (A C : Type u) [CommRing A] [CommRing C] [Algebra A C] (n : ℕ) :
    MvPolynomial (Fin n) A →+* MvPolynomial (Fin n) C :=
  MvPolynomial.map (algebraMap A C)

/-- Specialization sends constants `c` to `1 ⊗ c` and the variable `i` to `b i ⊗ 1`.
Source: Stacks Project, Tag 0F31, affine algebra paragraph
(blueprint: lem-sfb-tensor-principal-polynomial-model). -/
noncomputable def specialization {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] {n : ℕ} (b : Fin n → B) :
    MvPolynomial (Fin n) C →+* B ⊗[A] C :=
  MvPolynomial.eval₂Hom
    (Algebra.TensorProduct.includeRight : C →ₐ[A] B ⊗[A] C).toRingHom
    (fun i => b i ⊗ₜ[A] (1 : C))

/-- The linear polynomial with coefficients `c i`, allowing the empty sum.
Source: Stacks Project, Tag 0F31, affine algebra paragraph
(blueprint: lem-sfb-tensor-principal-polynomial-model). -/
noncomputable def linearPolynomial {C : Type u} [CommRing C] {n : ℕ} (c : Fin n → C) :
    MvPolynomial (Fin n) C :=
  ∑ i, MvPolynomial.C (c i) * MvPolynomial.X i

/-- Every tensor principal open has a finite polynomial model with its specified pushout
and image identities, without finiteness or flatness hypotheses.

Source: Stacks Project, Tag 0F31, proof of (3) implies (1), affine algebra paragraph
(blueprint: lem-sfb-tensor-principal-polynomial-model).

Proof plan:
1. Pure tensors generate the tensor product as a module
   [def-weil-pbc-module-tensor-product]. Absorb scalars into the first factors to write
   `g` as a finite sum `∑ i, b i ⊗ c i`.
2. Tensor balancing and the polynomial universal property
   [def-weil-pbc-mv-polynomial-ring] give the three specified ring maps. Check the
   commuting square on coefficients and variables; compute the specialization of the
   linear polynomial term by term to obtain `g`.
3. Given compatible `u` and `v`, restrict `u` to constants of `C`. Compatibility gives a
   common `A`-algebra structure on `E`. The bilinear pairing `(b,c) ↦ v b * u (C c)`
   induces the tensor map. Check unit and multiplication on pure tensors, then extend
   by finite sums. Check its composites on polynomial generators. Uniqueness follows
   because every pure tensor is the product of the two canonical inclusions.
4. Apply the same tensor construction to `S ⊗[R] B`, where `R=A[t]` and `S=C[t]`.
   The maps to `B ⊗[A] C` and back are inverse: one composite by the pushout uniqueness,
   the other on pure tensors. The affine fibre-product theorem
   [lem-weil-pbc-fibre-product-affine-spectra] identifies the projections, hence gives
   the stated cartesian square.
5. On spectra the map is contraction [def-weil-affine-spectrum]. Thus membership in
   the inverse image of `D(h)` is exactly nonmembership of `k(h)=g` in the prime ideal.
6. Apply [lem-weil-pbc-base-change-image] to this cartesian square and the subset `D(h)`;
   substitute the preceding inverse-image identity.
7. For `g=0`, the empty expansion `n=0` and `h=0` is allowed. Both principal opens are
   empty. The construction also applies to zero rings throughout. -/
theorem exists_model (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] (g : B ⊗[A] C) :
    ∃ (n : ℕ) (b : Fin n → B) (c : Fin n → C),
      g = ∑ i, b i ⊗ₜ[A] c i ∧
      specialization (A := A) (C := C) b (linearPolynomial c) = g ∧
      (specialization (A := A) (C := C) b).comp (coefficientMap A C n) =
        (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[A] C).comp
          (MvPolynomial.aeval b).toRingHom ∧
      (∀ (E : Type (max u v)) [CommRing E] (u : MvPolynomial (Fin n) C →+* E) (v : B →+* E),
        u.comp (coefficientMap A C n) = v.comp (MvPolynomial.aeval b).toRingHom →
        ∃! w : B ⊗[A] C →+* E,
          w.comp (specialization (A := A) (C := C) b) = u ∧
          w.comp Algebra.TensorProduct.includeLeftRingHom = v ∧
          ∀ (x : B) (y : C), w (x ⊗ₜ[A] y) = v x * u (MvPolynomial.C y)) ∧
      IsPullback
        (Spec.map (CommRingCat.ofHom (specialization (A := A) (C := C) b)))
        (Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[A] C)))
        (Spec.map (CommRingCat.ofHom (coefficientMap A C n)))
        (Spec.map (CommRingCat.ofHom (MvPolynomial.aeval b).toRingHom)) ∧
      (Spec.map (CommRingCat.ofHom (specialization (A := A) (C := C) b))).base ⁻¹'
        (PrimeSpectrum.basicOpen (linearPolynomial c) : Set (PrimeSpectrum _)) =
          (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum _)) ∧
      (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[A] C))).base ''
          (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum _)) =
        (Spec.map (CommRingCat.ofHom (MvPolynomial.aeval b).toRingHom)).base ⁻¹'
          ((Spec.map (CommRingCat.ofHom (coefficientMap A C n))).base ''
            (PrimeSpectrum.basicOpen (linearPolynomial c) : Set (PrimeSpectrum _))) := by
  sorry

end AlgebraicGeometry.TensorPrincipalPolynomialModel
