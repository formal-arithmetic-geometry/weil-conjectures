/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Sheaf.RingTheory.QuasiFiniteAtPrime
import Sheaf.RingTheory.EtaleFiniteFactorDecomposition
import Sheaf.RingTheory.RetractionBaseChangeNoQuasiFinite
import Mathlib.RingTheory.TensorProduct.Pi
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.Algebra.Algebra.Shrink

/-!
# Finite-type splitting from étale retractions

Source: Stacks Project, Algebra, Lemma Tag 04GG, proof of (8) ⇒ (11), using Tag 00UK
(blueprint: lem-weil-pbc-etale-retraction-finite-type-splitting).
-/

@[expose] public section

universe u v

namespace Algebra

-- The original existential names an equivalence unused in the following conjuncts.
-- Keep that signature unchanged while suppressing its unused-binder warning.
set_option linter.unusedVariables false in
/--
Source: Stacks Project, Algebra, Lemma Tag 04GG, proof of (8) ⇒ (11)
(blueprint: lem-weil-pbc-etale-retraction-finite-type-splitting).

Assuming that every étale algebra with a rational point over the closed point
retracts to the local ring, a finite-type algebra splits into a finite factor
and a factor with no quasi-finite point above the maximal ideal.

Proof:
1. Apply `lem-weil-pbc-finite-type-etale-finite-factor-decomposition` (Stacks 00UK)
   to `R → S` at the maximal ideal. It gives an étale `R → R'`, a prime `m'` over
   the maximal ideal with the same residue field, and `R' ⊗[R] S ≅ A' × B'`,
   with `A'` finite and no quasi-finite point of `B'` over `m'`.
2. Apply the retraction hypothesis to obtain `τ : R' →ₐ[R] R` with inverse image
   of the maximal ideal equal to `m'` (the source prints this equality backwards).
3. Set `A = A' ⊗[R', τ] R` and `B = B' ⊗[R', τ] R`. Tensor cancellation and
   preservation of the two-factor product give `S ≅ A × B`. Tensoring finite
   module generators of `A'` gives finite generators of `A`. The product
   projection makes `B` a quotient of `S`, hence a finite-type `R`-algebra.
4. The residue-field map induced by `τ` is inverse to the original residue-field
   isomorphism (`def-weil-residue-field`), so tensor cancellation identifies
   `B ⊗[R] κ` with `B' ⊗[R'] κ(m')`. The corresponding fibre spectra are
   homeomorphic, with their points corresponding to primes over the respective
   base primes. By `def-weil-pbc-ring-map-quasi-finite-at-prime`, quasi-finiteness
   is isolatedness in the fibre. No point on the second fibre is isolated, so
   neither is any point on the first.

The factors are allowed in the same universe as `S`, including zero rings. The
étale test algebras range over `Type (max u v)`, as in
`finite_algebra_is_product_local_rings`: an étale `R`-algebra is essentially small
over `R`, so this universe holds every one the proof needs, whereas a test universe
smaller than that of `R` could leave the hypothesis vacuous.
-/
theorem etale_retraction_finite_type_splitting
    (R : Type u) [CommRing R] [IsLocalRing R]
    (hR : ∀ (R' : Type (max u v)) [CommRing R'] [Algebra R R'],
      Algebra.Etale R R' →
        ∀ (p : Ideal R') [p.IsPrime],
          ∀ (hp : p.comap (algebraMap R R') = IsLocalRing.maximalIdeal R),
            Function.Bijective
                (Ideal.ResidueField.mapₐ (IsLocalRing.maximalIdeal R) p
                  (Algebra.ofId R R') hp.symm) →
              ∃ (τ : R' →ₐ[R] R),
                p = (IsLocalRing.maximalIdeal R).comap τ.toRingHom)
    (S : Type v) [CommRing S] [Algebra R S] [Algebra.FiniteType R S] :
    ∃ (A B : Type v) (_ : CommRing A) (_ : CommRing B)
      (_ : Algebra R A) (_ : Algebra R B) (_ : Algebra.FiniteType R B),
      (∃ e : S ≃ₐ[R] A × B,
        Module.Finite R A ∧
          (∀ q : PrimeSpectrum B,
            q.comap (algebraMap R B) = IsLocalRing.maximalIdeal R →
              ¬ IsQuasiFiniteAtPrime R B q)) := by
  classical
  obtain ⟨R', cR', aR', et, P, pp, hp, A', cA', aA', B', cB', aB', ftB',
    hres, ⟨e⟩, finA', hbad⟩ :=
    exists_etale_finiteFactor_decomposition (S := S) (IsLocalRing.maximalIdeal R)
  let _ := cR'
  let _ := aR'
  have := et
  have := pp
  have := hp
  let _ := cA'
  let _ := aA'
  let _ := cB'
  let _ := aB'
  have := ftB'
  have := finA'
  -- Lift the neighborhood to the universe quantified over by `hR`.
  let R'' := ULift.{v} R'
  let σ : R'' ≃ₐ[R] R' := ULift.algEquiv
  have : Algebra.Etale R R'' := Algebra.Etale.of_equiv σ.symm
  let P'' : Ideal R'' := P.comap σ.toRingHom
  have hp'' : P''.comap (algebraMap R R'') = IsLocalRing.maximalIdeal R := by
    rw [show P''.comap (algebraMap R R'') = P.comap (algebraMap R R') by
      ext x
      change σ (algebraMap R R'' x) ∈ P ↔ algebraMap R R' x ∈ P
      rw [σ.commutes]]
    exact (P.over_def _).symm
  have hup : P = P''.comap σ.symm.toRingHom := by
    ext x
    change x ∈ P ↔ σ (σ.symm x) ∈ P
    rw [σ.apply_symm_apply]
  let g := Ideal.ResidueField.map P P'' σ.symm.toRingHom hup
  have hg : Function.Bijective g := by
    let g' := Ideal.ResidueField.map P'' P σ.toRingHom rfl
    have h₁ : g'.comp g = RingHom.id _ := by
      apply Ideal.ResidueField.ringHom_ext
      ext x
      simp [g, g', Ideal.ResidueField.map_algebraMap]
    have h₂ : g.comp g' = RingHom.id _ := by
      apply Ideal.ResidueField.ringHom_ext
      ext x
      simp [g, g', Ideal.ResidueField.map_algebraMap]
    exact ⟨Function.LeftInverse.injective (congrArg DFunLike.coe h₁ |> congrFun),
      Function.RightInverse.surjective (congrArg DFunLike.coe h₂ |> congrFun)⟩
  have hres'' : Function.Bijective
      (Ideal.ResidueField.mapₐ (IsLocalRing.maximalIdeal R) P''
        (Algebra.ofId R R'') hp''.symm) := by
    have hcomp : (Ideal.ResidueField.mapₐ (IsLocalRing.maximalIdeal R) P''
        (Algebra.ofId R R'') hp''.symm).toRingHom =
        g.comp (Ideal.ResidueField.mapₐ (IsLocalRing.maximalIdeal R) P
          (Algebra.ofId R R') (P.over_def _)).toRingHom := by
      apply Ideal.ResidueField.ringHom_ext
      ext x
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        Ideal.ResidueField.mapₐ_apply, Ideal.ResidueField.map_algebraMap,
        Algebra.ofId_apply]
      simp only [g, Ideal.ResidueField.map_algebraMap]
      exact congrArg (algebraMap R'' P''.ResidueField) (σ.symm.commutes x).symm
    change Function.Bijective
      (Ideal.ResidueField.mapₐ (IsLocalRing.maximalIdeal R) P''
        (Algebra.ofId R R'') hp''.symm).toRingHom
    rw [hcomp]
    exact hg.comp hres
  obtain ⟨τ'', hτ''⟩ := hR R'' inferInstance P'' hp'' hres''
  let τ : R' →ₐ[R] R := τ''.comp σ.symm.toAlgHom
  have hτ : P = (IsLocalRing.maximalIdeal R).comap τ.toRingHom := by
    rw [hup, hτ'']
    rfl
  let : Algebra R' R := τ.toRingHom.toAlgebra
  have : IsScalarTower R R' R :=
    IsScalarTower.of_algebraMap_eq' (by ext x; exact (τ.commutes x).symm)
  let A₀ := TensorProduct R' R A'
  let B₀ := TensorProduct R' R B'
  let e₀ : S ≃ₐ[R] A₀ × B₀ :=
    (Algebra.TensorProduct.lid R S).symm.trans
      ((Algebra.TensorProduct.cancelBaseChange R R' R R S).symm.trans
        ((Algebra.TensorProduct.congr (AlgEquiv.refl : R ≃ₐ[R] R) e).trans
          (Algebra.TensorProduct.prodRight R' R R A' B')))
  have : Small.{v} A₀ := small_of_surjective
    ((Prod.fst_surjective).comp e₀.surjective)
  have : Small.{v} B₀ := small_of_surjective
    ((Prod.snd_surjective).comp e₀.surjective)
  let A := Shrink.{v} A₀
  let B := Shrink.{v} B₀
  let eA : A₀ ≃ₐ[R] A := (Shrink.algEquiv R A₀).symm
  let eB : B₀ ≃ₐ[R] B := (Shrink.algEquiv R B₀).symm
  let E : S ≃ₐ[R] A × B := e₀.trans (AlgEquiv.prodCongr eA eB)
  have : Module.Finite R A := Module.Finite.equiv eA.toLinearEquiv
  have : Algebra.FiniteType R B := Algebra.FiniteType.of_surjective
    ((AlgHom.snd R A B).comp E.toAlgHom)
    (Prod.snd_surjective.comp E.surjective)
  refine ⟨A, B, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, E, inferInstance, ?_⟩
  exact no_quasiFiniteAtPrime_of_retraction_baseChange τ P hτ B' B eB hbad

end Algebra
