/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N2
-/
module

public import Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

/-! # Integral-closure charts for reduced Artinian tensor algebras

Source: Stacks Project, Tags 035H and 0307; reduced Artinian ring decomposition.
(blueprint: lem-sbc-reduced-artinian-tensor-normalization-charts) -/

@[expose] public section

universe u
open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- A finite affine coproduct with reduced Artinian base changes has normalization
charts given by integral closures in its residue fields.

Source: Stacks Project, Tags 035H and 0307; reduced Artinian ring decomposition.
(blueprint: lem-sbc-reduced-artinian-tensor-normalization-charts)

Proof: Base change commutes with the finite coproduct. Its i-th component
is Spec D_i, where D_i = E_i tensor_B A, with the right structural A-map.
A reduced Artinian ring is the finite product of its residue fields D_i/P
at maximal ideals P. Under this product isomorphism the quotient maps
are the projections. The integral closure of A in a finite product is the
product of the integral closures: a monic equation projects coordinatewise,
and conversely the product of a finite family of monic annihilating
polynomials annihilates a tuple whose coordinates are integral.
The affine relative-normalization construction of Tag 035H consequently
identifies the normalization with the finite coproduct of Spec S_iP,
where S_iP = integralClosure A (D_i/P), as schemes over Spec A.
The summand inclusions give open immersions c with precisely the displayed
structural equation, and their images cover the normalization. Choose a
summand containing x. The empty coproduct has empty normalization and
therefore contributes no point. Tag 0307 ensures the affine descriptions
agree on localizations. No DVR, selected base prime, or stalk assertion
is used in this chart construction. -/
theorem reduced_artinian_tensor_normalization_charts
    (B A : CommRingCat.{u}) [Algebra B A]
    (r : ℕ) (E : Fin r → Type u) [∀ i, CommRing (E i)] [∀ i, Algebra B (E i)]
    (hD : ∀ i, IsArtinianRing (E i ⊗[B] A) ∧ _root_.IsReduced (E i ⊗[B] A))
    (X : Scheme.{u}) (p : X ⟶ Spec B)
    (e : X ≅ ∐ fun i : Fin r ↦ Spec (CommRingCat.of (E i)))
    (he : e.hom ≫ Sigma.desc (fun i : Fin r ↦
      Spec.map (CommRingCat.ofHom (algebraMap B (E i)))) = p) :
    let a := pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap B A)))
    ∀ (hqc : QuasiCompact a) (hqs : QuasiSeparated a),
    letI := hqc
    letI := hqs
    ∀ x : a.normalization,
    ∃ (i : Fin r) (P : Ideal (E i ⊗[B] A)) (hP : P.IsMaximal),
    letI := hP
    let F := (E i ⊗[B] A) ⧸ P
    let alpha : A →+* F := (Ideal.Quotient.mk P).comp
      (Algebra.TensorProduct.includeRight : A →ₐ[B] E i ⊗[B] A).toRingHom
    letI := alpha.toAlgebra
    let S := integralClosure A F
    ∃ c : Spec (CommRingCat.of S) ⟶ a.normalization,
      IsOpenImmersion c ∧
      c ≫ a.fromNormalization = Spec.map (CommRingCat.ofHom (algebraMap A S)) ∧
      x ∈ Set.range c := by sorry

end AlgebraicGeometry.Scheme
