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

import Sheaf.AlgebraicGeometry.Morphisms.FiniteAffineTensorBaseChange
import Sheaf.AlgebraicGeometry.Morphisms.FiniteAffineNormalizationCoproduct
import Sheaf.AlgebraicGeometry.Morphisms.ReducedArtinianAffineNormalizationCharts

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
The universal property of relative normalization identifies the normalization
of this finite coproduct with the coproduct of the component normalizations.
A reduced Artinian ring is the finite product of its residue fields D_i/P
at maximal ideals P, with quotient maps as projections. Applying the same
normalization coproduct result reduces each component to these residue
fields. The affine relative-normalization construction of Tag 035H
identifies their normalizations with Spec S_iP, where
S_iP = integralClosure A (D_i/P), as schemes over Spec A.
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
      x ∈ Set.range c := by
  dsimp only
  intro hqc hqs
  let := hqc
  let := hqs
  intro x
  let D (i : Fin r) := E i ⊗[B] A
  let (i : Fin r) : Algebra A (D i) :=
    (Algebra.TensorProduct.includeRight : A →ₐ[B] E i ⊗[B] A).toRingHom.toAlgebra
  obtain ⟨t, ht⟩ := finite_affine_tensor_base_change B A r E X p e he
  obtain ⟨n, hn⟩ := finite_affine_normalization_coproduct A r D _
    (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap B A)))) t ht
  let N (i : Fin r) :=
    (Spec.map (CommRingCat.ofHom (algebraMap A (D i)))).normalization
  obtain ⟨i, y, hy⟩ := (sigmaOpenCover N).exists_eq (n.inv x)
  have hy' : (Sigma.ι N i ≫ n.hom) y = x := by
    rw [Hom.comp_apply]
    change n.hom ((sigmaOpenCover _).f i y) = x
    rw [hy]
    rw [← Hom.comp_apply, n.inv_hom_id]
    rfl
  let : IsArtinianRing (D i) := (hD i).1
  let : _root_.IsReduced (D i) := (hD i).2
  obtain ⟨P, hP, c, hc, hcomp, hmem⟩ :=
    reduced_artinian_affine_normalization_charts A (D i) y
  refine ⟨i, P, hP, c ≫ Sigma.ι N i ≫ n.hom, ?_, ?_, ?_⟩
  · let := hc
    infer_instance
  · rw [Category.assoc, Category.assoc, hn, hcomp]
  · obtain ⟨z, hz⟩ := hmem
    refine ⟨z, ?_⟩
    rw [Hom.comp_apply, hz, hy']

end AlgebraicGeometry.Scheme
