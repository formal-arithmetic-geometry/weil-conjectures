/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q39
-/
module

public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Sheaf.AlgebraicGeometry.LocalNoetherianApproximation
import Sheaf.RingTheory.NoetherianGeometricallyIntegralProjective

/-!
# Projectivity of a flat finitely presented algebra with geometrically integral fibres

Source: Stacks Project, More on Flatness, Tag 05FT,
`lemma-fibres-irreducible-flat-projective-nonnoetherian`
(blueprint: lem-trf-affine-geometrically-integral-projective).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory AlgebraicGeometry TensorProduct

namespace Algebra

-- Integral affine base changes give the scheme-theoretic geometric property.
private theorem geometric_of_domains
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (h : ∀ (K : Type u) [Field K] [Algebra R K], IsDomain (S ⊗[R] K)) :
    GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  rw [GeometricallyIntegral.eq_geometrically, geometrically_iff_of_commRing]
  intro K _ _ Y fst snd hp
  have := h K
  have := IsIntegral.of_isIso (pullbackSpecIso R S K).inv
  exact IsIntegral.of_isIso hp.isoPullback.inv

private theorem geometric_fibre
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (h : GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap R S))))
    (p : PrimeSpectrum R) :
    GeometricallyIntegral (Spec.map (CommRingCat.ofHom
      (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber S)))) := by
  have := h
  have hg : GeometricallyIntegral
      (Limits.pullback.fst (Spec.map (CommRingCat.ofHom
        (algebraMap R p.asIdeal.ResidueField)))
        (Spec.map (CommRingCat.ofHom (algebraMap R S)))) := inferInstance
  rw [← pullbackSpecIso_inv_fst' R p.asIdeal.ResidueField S]
  exact MorphismProperty.RespectsIso.precomp _ _ _ hg

private theorem geometric_ulift
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (h : GeometricallyIntegral (Spec.map (CommRingCat.ofHom f))) :
    GeometricallyIntegral (Spec.map (CommRingCat.ofHom (f.ulift.{u, u}))) := by
  let eR := ULift.ringEquiv (R := R)
  let eS := ULift.ringEquiv (R := S)
  have he : Spec.map (CommRingCat.ofHom (f.ulift.{u, u})) =
      Spec.map eS.toCommRingCatIso.inv ≫ Spec.map (CommRingCat.ofHom f) ≫
        Spec.map eR.toCommRingCatIso.hom := by
    simp only [← Spec.map_comp]
    rfl
  rw [he]
  rw [← Category.assoc]
  exact MorphismProperty.RespectsIso.postcomp _ (Spec.map eR.toCommRingCatIso.hom) _
    (MorphismProperty.RespectsIso.precomp _ _ _ h)

-- Implement the three-step Noetherian approximation proof of Tag 05FT.
private theorem projective_of_geometric
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FinitePresentation R S] (hflat : (algebraMap R S).Flat)
    (h : GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap R S)))) :
    Module.Projective R S := by
  obtain ⟨R₀, S₀, alg, a, b, hR₀, hS₀, hf₀, hg₀, hp⟩ :=
    exists_local_noetherian_approximation (.of R) (.of S) hflat (geometric_fibre R S h)
  let := alg
  have : Algebra.FiniteType ℤ R₀ := by
    rw [← RingHom.finiteType_algebraMap]
    exact hR₀
  have : IsNoetherianRing R₀ := Algebra.FiniteType.isNoetherianRing ℤ R₀
  have : Module.Projective R₀ S₀ :=
    projective_of_noetherian_geometricallyIntegral_fibres R₀ S₀ hS₀ hf₀
      (fun p ↦ geometric_ulift _ (hg₀ p))
  let : Algebra R₀ R := a.toAlgebra
  let : Algebra S₀ S := b.toAlgebra
  let : Algebra R₀ S := (algebraMap R S).comp a |>.toAlgebra
  have : IsScalarTower R₀ R S := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower R₀ S₀ S := IsScalarTower.of_algebraMap_eq' (by
    exact congrArg CommRingCat.Hom.hom hp.w.symm)
  have : Algebra.IsPushout R₀ R S₀ S :=
    CommRingCat.isPushout_iff_isPushout.mp hp.flip
  exact Module.Projective.of_equiv' (Algebra.IsPushout.equiv R₀ R S₀ S).toLinearEquiv

-- Every field-valued map factors through the residue field of its prime kernel.
private theorem domain_of_field
    (R : Type u) (B : Type v) [CommRing R] [CommRing B] [Algebra R B]
    (hfibres : ∀ (p : Spec (.of R)) (K : Type (max u v w)) [Field K] [Algebra R K]
      (ι : (Spec (.of R)).residueField p →+* K),
      algebraMap R K =
        ι.comp (((Scheme.ΓSpecIso (.of R)).inv ≫ (Spec (.of R)).Γevaluation p).hom) →
      IsDomain (B ⊗[R] K))
    (K : Type (max u v w)) [Field K] [Algebra R K] : IsDomain (B ⊗[R] K) := by
  let p : PrimeSpectrum R := ⟨RingHom.ker (algebraMap R K), RingHom.ker_isPrime _⟩
  have : p.asIdeal.IsPrime := p.isPrime
  let j : p.asIdeal.ResidueField →+* K :=
    Ideal.ResidueField.lift p.asIdeal (algebraMap R K) le_rfl (by
      intro r hr
      exact isUnit_iff_ne_zero.mpr hr)
  let ι := j.comp (Scheme.Spec.residueFieldIso (.of R) p).hom.hom
  apply hfibres p K ι
  have he : ((Scheme.ΓSpecIso (.of R)).inv ≫ (Spec (.of R)).Γevaluation p) =
      CommRingCat.ofHom (algebraMap R p.asIdeal.ResidueField) ≫
        (Scheme.Spec.residueFieldIso (.of R) p).inv := by
    exact (Scheme.Spec.algebraMap_residueFieldIso_inv (.of R) p).symm
  rw [he]
  ext r
  simp [ι, j]

set_option backward.isDefEq.respectTransparency false in
attribute [-instance] ULift.smulLeft ULift.mulAction ULift.smulZeroClass ULift.distribSMul
  ULift.distribMulAction ULift.smulWithZero ULift.mulActionWithZero ULift.module in
/-- A flat finitely presented commutative algebra whose fibres remain domains after every
residue-field extension is projective over the base. Here `ι` specifies the field extension
and the equality specifies the induced `R`-algebra structure on `K`. The canonical map
`R → κ(p)` is global evaluation after `Scheme.ΓSpecIso`. Projectivity itself means that the
canonical surjection from the free module `B →₀ R` splits, so includes the direct-summand
formulation.

Source: Stacks Project, More on Flatness, Tag 05FT
(blueprint: lem-trf-affine-geometrically-integral-projective).

Proof:
1. Any map from `R` to a field has a prime kernel and factors through its residue
   field. `Scheme.Spec.residueFieldIso` identifies this factorization with the
   `Γevaluation` compatibility in the hypothesis. Thus `B ⊗[R] K` is a domain for
   every field-valued `R`-algebra in the specified universe.
2. Lift both rings to the common universe `max u v w`. Tensor equivalences for
   compatible scalar actions preserve the domain condition. The affine tensor
   pullback isomorphism and integrality of the spectrum of a domain show that
   `Spec B → Spec R` is geometrically integral; its algebraic fibres inherit this
   property by base change.
3. Apply `exists_local_noetherian_approximation`
   (lem-trf-local-noetherian-approximation) to obtain a finite type integer ring
   `R₀`, a finite type flat algebra `S₀` with geometrically integral fibres, and a
   cocartesian square identifying `B` with `R ⊗[R₀] S₀`.
4. The ring `R₀` is Noetherian by finite type over the integers. Apply
   `projective_of_noetherian_geometricallyIntegral_fibres`
   (lem-trf-local-noetherian-fibres-projective) to `R₀ → S₀`.
5. Projectivity ascends along tensor base change
   (lem-trf-local-projective-tensor-base-change). Transfer it through the pushout's
   linear equivalence, and then through the canonical universe-lift equivalences.
   No finite generation as an `R`-module or Noetherian hypothesis on `R` is used.
-/
theorem projective_of_geometricallyIntegral_fibres
    (R : Type u) (B : Type v) [CommRing R] [CommRing B] [Algebra R B]
    [Algebra.FinitePresentation R B] (hflat : RingHom.Flat (algebraMap R B))
    (hfibres : ∀ (p : Spec (.of R)) (K : Type (max u v w)) [Field K] [Algebra R K]
      (ι : (Spec (.of R)).residueField p →+* K),
      algebraMap R K =
        ι.comp (((Scheme.ΓSpecIso (.of R)).inv ≫ (Spec (.of R)).Γevaluation p).hom) →
      IsDomain (B ⊗[R] K)) :
    Module.Projective R B := by
  -- The approximation and scheme APIs use one universe; preserve all input universes.
  let R' := ULift.{max u v w} R
  let B' := ULift.{max u v w} B
  let : Algebra R' B' := ULift.algebra' R B'
  have hfp : (algebraMap R' B').FinitePresentation := by
    have h₁ := RingHom.FinitePresentation.of_bijective
      (f := (ULift.ringEquiv : R' ≃+* R).toRingHom) ULift.ringEquiv.bijective
    have h₂ := RingHom.finitePresentation_algebraMap.mpr
      (inferInstance : Algebra.FinitePresentation R B)
    have h₃ := RingHom.FinitePresentation.of_bijective
      (f := (ULift.ringEquiv : B' ≃+* B).symm.toRingHom) ULift.ringEquiv.symm.bijective
    exact (h₃.comp h₂).comp h₁
  have : Algebra.FinitePresentation R' B' :=
    RingHom.finitePresentation_algebraMap.mp hfp
  have hf : (algebraMap R' B').Flat := RingHom.Flat.ulift_iff.mpr hflat
  have hg : GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap R' B'))) := by
    apply geometric_of_domains R' B'
    intro K _ algK
    let : Algebra R K := ((algebraMap R' K).comp ULift.ringEquiv.symm.toRingHom).toAlgebra
    have := domain_of_field R B hfibres K
    have : SMulCommClass R' R B' := ⟨fun _ _ _ ↦ smul_comm ..⟩
    have : SMulCommClass R R' B' := SMulCommClass.symm _ _ _
    have hsB (r : R') (b : B') : r.down • b = r • b := by
      simp only [Algebra.smul_def]
      rfl
    have hsK (r : R') (k : K) : r.down • k = r • k := by
      simp only [Algebra.smul_def]
      rfl
    have : TensorProduct.CompatibleSMul R R' B' K := ⟨fun r b k ↦ by
      rw [← hsB r b, ← hsK r k]
      exact TensorProduct.smul_tmul (R := R) (R' := R) r.down b k⟩
    have : TensorProduct.CompatibleSMul R' R B' K := ⟨fun r b k ↦ by
      rw [hsB (ULift.up r) b, hsK (ULift.up r) k]
      exact TensorProduct.smul_tmul (R := R') (R' := R') (ULift.up r) b k⟩
    let e : B' ⊗[R'] K ≃ₐ[R] B ⊗[R] K :=
      (Algebra.TensorProduct.equivOfCompatibleSMul R R' R B' K).trans
        (Algebra.TensorProduct.congr ULift.algEquiv (AlgEquiv.refl (R := R) (A₁ := K)))
    exact e.toRingEquiv.toMulEquiv.isDomain _
  have := projective_of_geometric R' B' hf hg
  have : RingHomInvPair (ULift.ringEquiv : R' ≃+* R).toRingHom
      (ULift.ringEquiv : R' ≃+* R).symm.toRingHom := ⟨rfl, rfl⟩
  have : RingHomInvPair (ULift.ringEquiv : R' ≃+* R).symm.toRingHom
      (ULift.ringEquiv : R' ≃+* R).toRingHom := ⟨rfl, rfl⟩
  let e : LinearEquiv (ULift.ringEquiv : R' ≃+* R).toRingHom
      (σ' := (ULift.ringEquiv : R' ≃+* R).symm.toRingHom) B' B :=
    { ULift.ringEquiv with map_smul' := fun _ _ ↦ rfl }
  exact Module.Projective.of_equiv
    (σ' := (ULift.ringEquiv : R' ≃+* R).symm.toRingHom) e

end Algebra
