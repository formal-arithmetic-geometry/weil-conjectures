/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q81
-/
module

public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.RingTheory.Support
public import WeilConjectures.Mathlib.Topology.KrullDimension
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Sheaf.TraceFormula.LocalGenericBasisUniversalInjective
import WeilConjectures.Topology.IrreducibleOpenComplementDimension

/-!
# A generic free submodule and the dimension of its cokernel support

Source: Stacks Project, Tags 05I3 and 05I5, `lemma-induction-step` and
`proposition-finite-type-flat-at-point`, first proof, induction step.
(blueprint: lem-trf-generic-free-cokernel-dimension-drop)
-/

@[expose] public section

set_option autoImplicit false

universe u v w t z y

namespace RingHom

open scoped TensorProduct

/-- A generic free submodule can be chosen from any finite generating list. Its cokernel
is finite and flat at the specified point over the local base, the sequence is universally
exact, and its closed-fibre support is proper and has strictly smaller dimension.

Source: Stacks Project, Tag 05I3, `lemma-induction-step`, and Tag 05I5,
`proposition-finite-type-flat-at-point`, first proof, induction step.
(blueprint: lem-trf-generic-free-cokernel-dimension-drop)

Proof:
1. The closed fibre C = B/mB is B tensor kappa(m), hence is a nonzero domain by the
   geometric-fibre hypothesis. Thus p = mB is prime and kappa(p) is the fraction field
   of C. Its zero prime is the generic point of the integral closed fibre. These use
   def-weil-residue-field, def-weil-pbc-module-localization,
   def-weil-pbc-module-tensor-product and def-weil-affine-spectrum.
2. The prescribed generators span N tensor kappa(p). Scan this finite list, retaining
   a vector precisely when it is outside the span of those already retained. The retained
   vectors form a basis. Send the standard basis of B^r to their original generators;
   the resulting alpha is an isomorphism after tensoring with kappa(p). When this vector
   space is zero, retain the empty list, giving r = 0. This uses
   def-weil-finitely-generated-module and def-weil-pbc-module-tensor-product.
3. Apply lem-trf-local-generic-basis-universal-injective, namely
   RingHom.local_generic_basis_universal_injective, to alpha, q and the given flatness
   of N_q. This gives A-universal injectivity and flatness of the localized cokernel.
4. The images of the original generators generate Q = N/range(alpha). Tensor right
   exactness (lem-weil-pbc-tensor-right-exact), together with universal injectivity,
   makes 0 to L tensor B^r to L tensor N to L tensor Q to 0 exact. Taking L to be any
   A-algebra gives the asserted base-change sequence; L = A gives injectivity of alpha.
5. Tensoring the cokernel sequence with kappa(p) shows Q tensor kappa(p) = 0.
   The closed-fibre module C tensor_B Q is canonically Q/mQ, and its localization at
   zero is Q tensor_B kappa(p): send q tensor (b/s) to bq/s, with inverse q/s to
   q tensor (1/s). The tensor relations kill mQ and show these maps are inverse.
   Thus its support misses the generic point. By
   lem-weil-pbc-finite-module-support-annihilator its support is the zero locus of its
   annihilator, hence closed and proper.
6. Apply new-node-irreducible-open-complement-dimension, namely
   irreducible_open_complement_dimension, to the nonempty open complement of this
   support in the irreducible n-dimensional closed fibre. If the support is nonempty,
   its dimension is at most some e < n, hence strictly less than n. At any point its
   local dimension is at most its total dimension by def-kun-dimension (take the whole
   support as an open neighbourhood). For n = 0 nonempty support is impossible.

Here Z is required to equal the actual support of (B/mB) tensor_B Q, the canonical
closed-fibre realization of Q/mQ. Points of Spec(B/mB) are compared with p and q via
comap along the quotient map, avoiding any arbitrary choice of a point or prime instance.
-/
theorem generic_free_cokernel_dimension_drop
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [IsLocalRing A]
    (hflat : RingHom.Flat (algebraMap A B)) (hfp : Algebra.FinitePresentation A B)
    (hgeom : ∀ (a : PrimeSpectrum A) (K : Type (max u v w)) [Field K]
      [Algebra A K] (ι : a.asIdeal.ResidueField →+* K),
      algebraMap A K = ι.comp (algebraMap A a.asIdeal.ResidueField) →
      IsDomain (K ⊗[A] B))
    (n : ℕ)
    (hdim : topologicalKrullDim
      (PrimeSpectrum (B ⧸ Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A))) =
        (n : WithBot ℕ∞))
    (q : PrimeSpectrum B)
    (hq : q.asIdeal.comap (algebraMap A B) = IsLocalRing.maximalIdeal A)
    (N : Type t) [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
    [Module.Finite B N]
    (hNq : @Module.Flat A (LocalizedModule q.asIdeal.primeCompl N) _ _
      (Module.compHom (LocalizedModule q.asIdeal.primeCompl N) (algebraMap A B))) :
    ∃ hp : (Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A)).IsPrime,
      ∀ (s : ℕ) (x : Fin s → N) (_hx : Submodule.span B (Set.range x) = ⊤),
      ∃ (r : ℕ) (α : (Fin r → B) →ₗ[B] N) (j : Fin r ↪ Fin s)
        (Z : Set (PrimeSpectrum
          (B ⧸ Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A)))),
        (∀ i : Fin r, α (Pi.single i 1) = x (j i)) ∧
        Function.Bijective (LinearMap.lTensor
          (@Ideal.ResidueField B _
            (Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A)) hp) α) ∧
        Module.Finite B (N ⧸ LinearMap.range α) ∧
        (∀ (L : Type z) [AddCommGroup L] [Module A L],
          Function.Injective (LinearMap.lTensor L (α.restrictScalars A))) ∧
        @Module.Flat A (LocalizedModule q.asIdeal.primeCompl (N ⧸ LinearMap.range α)) _ _
          (Module.compHom (LocalizedModule q.asIdeal.primeCompl (N ⧸ LinearMap.range α))
            (algebraMap A B)) ∧
        (∀ (A' : Type y) [CommRing A'] [Algebra A A'],
          Function.Injective (LinearMap.lTensor A' (α.restrictScalars A)) ∧
          Function.Exact (LinearMap.lTensor A' (α.restrictScalars A))
            (LinearMap.lTensor A' ((LinearMap.range α).mkQ.restrictScalars A)) ∧
          Function.Surjective
            (LinearMap.lTensor A' ((LinearMap.range α).mkQ.restrictScalars A))) ∧
        Z = Module.support
          (B ⧸ Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A))
          ((B ⧸ Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A)) ⊗[B]
            (N ⧸ LinearMap.range α)) ∧
        IsClosed Z ∧ Z ≠ Set.univ ∧
        (∀ ξ, PrimeSpectrum.comap
          (Ideal.Quotient.mk (Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A))) ξ =
            ⟨Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A), hp⟩ → ξ ∉ Z) ∧
        (Z.Nonempty → topologicalKrullDim Z < (n : WithBot ℕ∞)) ∧
        (∀ ξ : Z, PrimeSpectrum.comap
          (Ideal.Quotient.mk (Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A))) ξ.val =
            q → topologicalKrullDimAt ξ < (n : WithBot ℕ∞)) ∧
        (n = 0 → Z = ∅) := by
  sorry

end RingHom
