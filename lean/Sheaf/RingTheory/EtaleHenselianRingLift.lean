/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Sheaf.AlgebraicGeometry.EtaleResidueTriples
public import Mathlib.RingTheory.Henselian
import Sheaf.RingTheory.HenselianEtaleRetraction

/-!
# Ring-valued lifting from a single etale algebra
Source: Stacks Project, Algebra, Tag 08HQ, using Tag 04GG.
-/

@[expose] public section
universe u
open CategoryTheory Algebra
namespace AlgebraicGeometry.Scheme

open scoped _root_.TensorProduct in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem single_etale_lift_field
    {R : Type u} [CommRing R] {S A : Type u} [CommRing S] [CommRing A]
    [Algebra R S] [Algebra R A] [HenselianLocalRing S] [Algebra.Etale R A]
    {K : Type u} [Field K] [Algebra S K] [Algebra R K] [IsScalarTower R S K]
    (hker : RingHom.ker (algebraMap S K) = IsLocalRing.maximalIdeal S)
    (hsurj : Function.Surjective (algebraMap S K)) (χ : A →ₐ[R] K) :
    ∃! f : A →ₐ[R] S, (IsScalarTower.toAlgHom R S K).comp f = χ := by
  classical
  let B := S ⊗[R] A
  let φ : B →ₐ[S] K := AlgHom.liftEquiv R S A K χ
  let q := RingHom.ker φ.toRingHom
  let m := IsLocalRing.maximalIdeal S
  have : q.IsPrime := RingHom.ker_isPrime φ.toRingHom
  have hq : q.comap (algebraMap S B) = m := by
    ext s
    change φ (algebraMap S B s) = 0 ↔ s ∈ m
    rw [φ.commutes]
    exact congrArg (fun j : Ideal S ↦ s ∈ j) hker |>.to_iff
  have units {T : Type u} [CommRing T] (f : T →+* K) (j : Ideal T) [j.IsPrime]
      (hj : j = RingHom.ker f) : j.primeCompl ≤ (IsUnit.submonoid K).comap f := by
    intro x hx
    change IsUnit (f x)
    rw [isUnit_iff_ne_zero]
    intro he
    exact hx (by simpa [hj, RingHom.mem_ker] using he)
  let η : m.ResidueField →+* K :=
    Ideal.ResidueField.lift m (algebraMap S K) hker.ge (units _ m hker.symm)
  let ψ : q.ResidueField →+* K :=
    Ideal.ResidueField.lift q φ.toRingHom le_rfl (units _ q rfl)
  have hηsurj : Function.Surjective η := by
    intro y
    obtain ⟨s, rfl⟩ := hsurj y
    exact ⟨algebraMap S m.ResidueField s, Ideal.ResidueField.lift_algebraMap ..⟩
  let θ := Ideal.ResidueField.map m q (algebraMap S B) hq.symm
  have hθ : ψ.comp θ = η := by
    apply Ideal.ResidueField.ringHom_ext
    ext s
    simp only [RingHom.comp_apply, θ, Ideal.ResidueField.map_algebraMap,
      ψ, η, Ideal.ResidueField.lift_algebraMap]
    exact φ.commutes s
  have hres : Function.Bijective θ := by
    refine ⟨RingHom.injective θ, ?_⟩
    intro y
    obtain ⟨x, hx⟩ := hηsurj (ψ y)
    refine ⟨x, RingHom.injective ψ ?_⟩
    exact (DFunLike.congr_fun hθ x).trans hx
  have : AlgebraicGeometry.Etale
      (AlgebraicGeometry.Scheme.Spec.map (CommRingCat.ofHom (algebraMap S B)).op) := by
    apply (AlgebraicGeometry.HasRingHomProperty.Spec_iff
      (P := @AlgebraicGeometry.Etale) (φ := CommRingCat.ofHom (algebraMap S B))).mpr
    exact (RingHom.etale_algebraMap).mpr inferInstance
  have hσ : ∃! σ : B →ₐ[S] S, m.comap σ.toRingHom = q := by
    have hAlg : TensorProduct.leftAlgebra = (algebraMap S B).toAlgebra :=
      toAlgebra_algebraMap.symm
    have h := existsUnique_algHom_of_henselianLocalRing_etale
      (algebraMap S B) q hq hres
    rw [← hAlg] at h
    exact h
  obtain ⟨σ, hσ, hσuniq⟩ := hσ
  let π : S →ₐ[S] K := Algebra.ofId S K
  have red (σ' : B →ₐ[S] S) (hσ' : m.comap σ'.toRingHom = q) : π.comp σ' = φ := by
    apply AlgHom.ext
    intro b
    obtain ⟨s, hs⟩ := hsurj (φ b)
    have hdiff : b - algebraMap S B s ∈ q := by
      change φ (b - algebraMap S B s) = 0
      simp only [map_sub, AlgHom.commutes, hs, sub_self]
    rw [← hσ'] at hdiff
    change σ' (b - algebraMap S B s) ∈ m at hdiff
    have hz : algebraMap S K (σ' (b - algebraMap S B s)) = 0 := by
      rw [← RingHom.mem_ker, hker]
      exact hdiff
    change algebraMap S K (σ' b) = φ b
    simpa only [map_sub, AlgHom.commutes, Algebra.algebraMap_self,
      RingHom.id_apply, sub_eq_zero, hs] using hz
  let f := (AlgHom.liftEquiv R S A S).symm σ
  have hf : (IsScalarTower.toAlgHom R S K).comp f = χ := by
    apply AlgHom.ext
    intro a
    have ha := DFunLike.congr_fun (red σ hσ) (1 ⊗ₜ[R] a)
    change algebraMap S K (σ (1 ⊗ₜ[R] a)) = φ (1 ⊗ₜ[R] a) at ha
    change algebraMap S K (σ (1 ⊗ₜ[R] a)) = χ a
    exact ha.trans ((AlgHom.liftEquiv_tmul χ 1 a).trans (one_smul S (χ a)))
  refine ⟨f, hf, ?_⟩
  intro f' hf'
  let σ' := AlgHom.liftEquiv R S A S f'
  have hred : π.comp σ' = φ := by
    apply Algebra.TensorProduct.ext_ring
    apply AlgHom.ext
    intro a
    simpa [σ', φ, π, AlgHom.liftEquiv_tmul] using DFunLike.congr_fun hf' a
  have hσ' : m.comap σ'.toRingHom = q := by
    ext b
    change σ' b ∈ IsLocalRing.maximalIdeal S ↔ φ b = 0
    rw [← hker]
    change algebraMap S K (σ' b) = 0 ↔ φ b = 0
    have hb := DFunLike.congr_fun hred b
    change algebraMap S K (σ' b) = φ b at hb
    rw [hb]
  simpa only [σ', Equiv.symm_apply_apply, f] using
    congrArg (AlgHom.liftEquiv R S A S).symm (hσuniq σ' hσ')

set_option backward.isDefEq.respectTransparency false in
/-- A pointed map from an etale algebra has a unique lift into a henselian local ring.
Source: Stacks Project, Algebra, Tag 08HQ (lemma-map-into-henselian).
(blueprint: lem-sc-etale-henselian-ring-lift).

Proof: Give B and S their R-algebra structures using alpha and beta. The equality hbeta
makes theta an R-algebra map to K. Form S tensor_R B, etale over S, and its map to K
from theta and epsilon. Its kernel lies over the maximal ideal of S. Since epsilon is
surjective, the residue extension at this kernel is trivial: the induced embedding of
its residue field into K is injective, while the residue field of S already maps onto K.
The henselian etale retraction theorem gives the unique S-algebra retraction at that
prime. Its reduction is the given tensor-product map: subtract an element of S with
the same residue to check this on each tensor-product element. Restrict to B to obtain
the lift. Conversely, any lift extends to an S-algebra retraction with this same kernel;
retraction uniqueness gives uniqueness of the original lift. -/
theorem etale_henselian_ring_lift
    (R B S : CommRingCat.{u}) [HenselianLocalRing S]
    (alpha : R ⟶ B) (halpha : Etale (Spec.map alpha))
    (beta : R ⟶ S) (K : Type u) [Field K]
    (epsilon : S →+* K) (hsurj : Function.Surjective epsilon)
    (hker : RingHom.ker epsilon = IsLocalRing.maximalIdeal S)
    (theta : B →+* K) (hbeta : theta.comp alpha.hom = epsilon.comp beta.hom) :
    ∃! f : B →+* S, f.comp alpha.hom = beta.hom ∧ epsilon.comp f = theta := by
  let : Algebra R B := alpha.hom.toAlgebra
  let : Algebra R S := beta.hom.toAlgebra
  let : Algebra S K := epsilon.toAlgebra
  let : Algebra R K := (epsilon.comp beta.hom).toAlgebra
  let : IsScalarTower R S K := IsScalarTower.of_algebraMap_eq' rfl
  have : Algebra.Etale R B :=
    ((HasRingHomProperty.Spec_iff (P := @Etale)).mp halpha).toAlgebra
  let theta' : B →ₐ[R] K :=
    { __ := theta
      commutes' := fun r ↦ DFunLike.congr_fun hbeta r }
  obtain ⟨f, hf, hu⟩ := single_etale_lift_field hker hsurj theta'
  refine ⟨f.toRingHom, ⟨?_, congrArg AlgHom.toRingHom hf⟩, ?_⟩
  · exact RingHom.ext f.commutes
  · intro g hg
    let g' : B →ₐ[R] S :=
      { __ := g
        commutes' := fun r ↦ DFunLike.congr_fun hg.1 r }
    have hred : (IsScalarTower.toAlgHom R S K).comp g' = theta' := by
      apply AlgHom.ext
      exact fun b ↦ DFunLike.congr_fun hg.2 b
    exact congrArg AlgHom.toRingHom (hu g' hred)

end AlgebraicGeometry.Scheme
