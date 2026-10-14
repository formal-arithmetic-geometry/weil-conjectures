/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V3
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.TensorProduct.Basic

public import Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.AlgebraicGeometry.Limits

/-! # Normalized Galois component stalks as integral-closure local factors

Source: Stacks Project, Tags 09EV, 035H and 0307.
(blueprint: lem-sbc-dvr-galois-components-stalk-factor) -/

@[expose] public section

universe u
open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Identify the actual stalk and every structural germ with a generic field factor.

Source: Stacks Project, Tags 09EV, 035H and 0307.
(blueprint: lem-sbc-dvr-galois-components-stalk-factor)

Proof: The root algebra A is a DVR by 09EV (for n = 1 use evaluation).
Its punctured spectrum is Spec Frac(A), since pi = t^n. Pull the given
coproduct isomorphism back to Spec A. On its i-th component the affine
pullback ring is D_i = E_i tensor_B A = E_i tensor_K Frac(A).
Finite separability of E_i/K makes D_i a finite product of fields; its
field factors are D_i/P for maximal ideals P. Integral closure in a
finite product is the product of the integral closures, componentwise:
a monic equation restricts to each factor, and the product of finitely
many monic equations works in the reverse direction. By 035H, relative
normalization on the affine target is the spectrum of this integral
closure. A point x consequently selects one index i, one field factor P,
and a prime Q in S = integralClosure A (D_i/P). The standard affine-stalk
localization isomorphism identifies its stalk with S_Q. The contraction
of Q to A is precisely the image prime of x, hence is (t). These affine
identifications are over A, so the localization isomorphism sends the
structural image of every s in A to its germ at x, not merely the root.
Tag 0307 ensures compatibility with the local description. The empty
coproduct has no point x. This step uses no degree bound or invertibility
of n: it is an identification, independent of the tame calculation. -/
theorem dvr_galois_components_stalk_factor
    (B : CommRingCat.{u}) [IsDomain B] [IsDiscreteValuationRing B]
    (pi : B) (hpi : Irreducible pi) (n : ℕ) (hnpos : 0 < n)
    (r : ℕ) (E : Fin r → Type u) [∀ i, Field (E i)]
    [∀ i, Algebra (FractionRing B) (E i)]
    (hE : ∀ i, FiniteDimensional (FractionRing B) (E i) ∧
      IsGalois (FractionRing B) (E i))
    (X : Scheme.{u}) (p : X ⟶ Spec (CommRingCat.of (FractionRing B)))
    (e : X ≅ ∐ fun i : Fin r ↦ Spec (CommRingCat.of (E i)))
    (he : e.hom ≫ Sigma.desc (fun i : Fin r ↦
      Spec.map (CommRingCat.ofHom (algebraMap (FractionRing B) (E i)))) = p) :
    let A := AdjoinRoot ((Polynomial.X : Polynomial B) ^ n - Polynomial.C pi)
    let q := Spec.map (CommRingCat.ofHom (algebraMap B A))
    let j := Spec.map (CommRingCat.ofHom (algebraMap B (FractionRing B)))
    let a := pullback.snd (p ≫ j) q
    ∀ (hqc : QuasiCompact a) (hqs : QuasiSeparated a),
    letI := hqc
    letI := hqs
    ∀ (x : a.normalization),
      (a.fromNormalization x).asIdeal = Ideal.span
        {AdjoinRoot.root ((Polynomial.X : Polynomial B) ^ n - Polynomial.C pi)} →
    letI : ∀ i, Algebra B (E i) := fun i ↦
      ((algebraMap (FractionRing B) (E i)).comp
        (algebraMap B (FractionRing B))).toAlgebra
    ∃ (i : Fin r) (P : Ideal (E i ⊗[B] A)) (hP : P.IsMaximal),
    letI := hP
    let F := (E i ⊗[B] A) ⧸ P
    let alpha : A →+* F := (Ideal.Quotient.mk P).comp
      (Algebra.TensorProduct.includeRight : A →ₐ[B] E i ⊗[B] A).toRingHom
    letI := alpha.toAlgebra
    let S := integralClosure A F
    ∃ (Q : Ideal S) (hQ : Q.IsPrime),
    letI := hQ
    Q.comap (algebraMap A S) = Ideal.span
      {AdjoinRoot.root ((Polynomial.X : Polynomial B) ^ n - Polynomial.C pi)} ∧
    ∃ (epsilon : Localization.AtPrime Q ≃+* a.normalization.presheaf.stalk x),
      ∀ s : A, epsilon (algebraMap S (Localization.AtPrime Q) (algebraMap A S s)) =
        (a.fromNormalization.stalkMap x).hom
          (StructureSheaf.toStalk A (a.fromNormalization x) s) := by sorry

end AlgebraicGeometry.Scheme
