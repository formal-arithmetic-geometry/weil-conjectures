/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.TensorProduct.Maps
import WeilConjectures.AlgebraicGeometry.GeometricIrreducibilityFiniteSeparableTest
import WeilConjectures.FieldTheory.RelativeAlgebraicClosurePolynomialQuotientField

/-!
# Algebraic closure in a field extension implies geometric irreducibility

Source: Stacks Project, Algebra, Tag 037P (lemma-field-extension-geometrically-irreducible)
(blueprint: lem-zl-field-extension-algebraically-closed-geometric).
-/

@[expose] public section

universe u

open CategoryTheory
open scoped TensorProduct

namespace AlgebraicGeometry

/-- If a field extension has no new elements algebraic over its base, its spectrum is
geometrically irreducible over the base.

Source: Stacks Project, Algebra, Tag 037P (lemma-field-extension-geometrically-irreducible)
(blueprint: lem-zl-field-extension-algebraically-closed-geometric).

Proof (blueprint, step by step):
1. Apply the finite-separable geometric-irreducibility criterion to reduce to showing that
   `Spec (K ⊗[k] E)` is irreducible for every finite separable extension `E/k`; identify this
   spectrum with the corresponding affine base change.
2. Choose a primitive element `α` of `E/k`, and let `P` be its monic irreducible minimal
   polynomial; use the quotient presentation `E ≃ k[T]/(P)`.
3. Identify `K ⊗[k] E` with `K[T]/(P_K)` by the two mutually inverse maps on coefficients and
   on `T`.
4. A factorization of `P_K` into monic nonconstant factors has coefficients algebraic over `k`
   by the monic-divisor coefficient lemma. The hypothesis puts those coefficients in `k`, which
   contradicts irreducibility of `P`.
5. The quotient by the irreducible positive-degree polynomial is a nonzero field by the PID
   Bezout argument. Its spectrum is one point, hence irreducible, and the criterion gives the
   result.
-/
theorem geometricallyIrreducible_of_isAlgebraic_mem
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    (h : ∀ x : K, IsAlgebraic k x → ∃ y : k, algebraMap k K y = x) :
    GeometricallyIrreducible
      (Spec.map (CommRingCat.ofHom (algebraMap k K))) := by
  classical
  rw [geometricallyIrreducible_iff,
    geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms]
  have htensor : ∀ (E : Type u) [Field E] [Algebra k E],
      IrreducibleSpace (Spec (CommRingCat.of (K ⊗[k] E))) := by
    apply (Algebra.irreducibleSpace_tensorProduct_iff_finite_separable k K).mpr
    intro E _ _ _ _
    let pb := Field.powerBasisOfFiniteOfSeparable k E
    let P := minpoly k pb.gen
    have hP : P.Monic := minpoly.monic pb.isIntegral_gen
    have hPirr : Irreducible P := minpoly.irreducible pb.isIntegral_gen
    let e : AdjoinRoot P ≃ₐ[k] E :=
      AdjoinRoot.equiv' P pb
        (by rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]) (minpoly.aeval k pb.gen)
    let Q := P.map (Algebra.TensorProduct.includeRight : k →ₐ[k] K ⊗[k] k).toRingHom
    let e₁ := Algebra.TensorProduct.congr (AlgEquiv.refl : K ≃ₐ[k] K) e.symm
    let e₂ := AdjoinRoot.tensorAlgEquiv (R := k) (T := K) P Q rfl
    let r := (Algebra.TensorProduct.rid k K K).toRingEquiv
    have hmap : Q.map r.toRingHom = P.map (algebraMap k K) := by
      rw [Polynomial.map_map]
      congr 1
      ext x
      simp [r, Algebra.TensorProduct.rid_tmul, Algebra.smul_def]
    let e₃ := AdjoinRoot.mapRingEquiv r Q (P.map (algebraMap k K))
      (hmap ▸ Associated.refl _)
    let equiv := e₁.toRingEquiv.trans (e₂.toRingEquiv.trans e₃)
    have hirr :=
      (Polynomial.irreducible_map_and_isField_quotient_of_isAlgebraic_mem h P hP hPirr).2.2.2
    exact (PrimeSpectrum.homeomorphOfRingEquiv equiv).irreducibleSpace_iff.mpr hirr
  intro E _ _
  exact (pullbackSpecIso k K E).hom.homeomorph.irreducibleSpace_iff.mpr (htensor E)

end AlgebraicGeometry
