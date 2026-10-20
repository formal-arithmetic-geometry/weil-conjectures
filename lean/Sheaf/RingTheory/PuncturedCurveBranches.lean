/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.LocalCurveBranches
public import Sheaf.RingTheory.ExcellentRing
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Limits

import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Sheaf.RingTheory.QuasiExcellentNagata
import Sheaf.RingTheory.SemilocalNormalizationDimOne
import WeilConjectures.RingTheory.ReducedNoetherianTotalRingFractions
import Sheaf.RingTheory.LocalCurvePrincipalTotalFractions
import Mathlib.AlgebraicGeometry.OpenImmersion
import Sheaf.RingTheory.IsExcellentFiniteTypeLocalization
import WeilConjectures.RingTheory.FiniteOverHenselianLocalProduct

/-!
# DVR branches of a punctured strictly local curve

Source: literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-a1-kummer/
`lem-exc-punctured-curve-branches.md`,
order 1918 (Stacks Tags 0C3S and 00PD)
(blueprint: lem-exc-punctured-curve-branches).
-/

noncomputable section

@[expose] public section

set_option autoImplicit false

universe u

open Set RingTheory AlgebraicGeometry CategoryTheory CategoryTheory.Limits

private theorem branch_dimension (R : Type u) [CommRing R] [IsLocalRing R]
    (hdim : ringKrullDim R = 1) (a : excLocalCurveBranchIndex R) :
    ringKrullDim (excLocalCurveBranchQuotient R a) = 1 := by
  have hp : a.1.IsPrime := a.2.isPrime
  have := hp
  have hnotmax : ¬ a.1.IsMaximal := by
    intro hm
    have hsub : Subsingleton (PrimeSpectrum R) := by
      refine ⟨fun x y ↦ PrimeSpectrum.ext ?_⟩
      have heq (z : PrimeSpectrum R) : z.asIdeal = a.1 := by
        have hle : z.asIdeal ≤ a.1 := by
          rw [IsLocalRing.eq_maximalIdeal hm]
          exact IsLocalRing.le_maximalIdeal z.isPrime.ne_top
        exact hle.antisymm (a.2.2 ⟨z.isPrime, bot_le⟩ hle)
      exact (heq x).trans (heq y).symm
    have hz : ringKrullDim R ≤ 0 := Order.krullDim_nonpos_of_subsingleton
    rw [hdim] at hz
    exact (by decide : ¬ (1 : WithBot ℕ∞) ≤ 0) hz
  have hnfield : ¬ IsField (R ⧸ a.1) := by
    intro h
    exact hnotmax ((Ideal.Quotient.maximal_ideal_iff_isField_quotient a.1).mpr h)
  apply le_antisymm ((ringKrullDim_quotient_le a.1).trans_eq hdim)
  apply Order.one_le_krullDim_iff.mpr
  obtain ⟨q, hq, hqp⟩ := Ring.not_isField_iff_exists_prime.mp hnfield
  exact ⟨⟨⊥, Ideal.isPrime_bot⟩, ⟨q, hqp⟩,
    show (⊥ : Ideal (R ⧸ a.1)) < q from bot_lt_iff_ne_bot.mpr hq⟩

private theorem finite_henselian_domain (R B : Type u) [CommRing R] [CommRing B]
    [HenselianLocalRing R] [Algebra R B] [Module.Finite R B] [IsDomain B] :
    HenselianLocalRing B := by
  classical
  obtain ⟨r, A, rings, algebras, henselian, localMaps, ⟨e⟩, hfinite, hres⟩ :=
    HenselianLocalRing.finite_over_henselian_exists_algEquiv_pi R B
  let := rings
  let := algebras
  have := henselian
  have hne : Nonempty (Fin r) := by
    by_contra h
    have : IsEmpty (Fin r) := not_nonempty_iff.mp h
    exact zero_ne_one (e.injective (Subsingleton.elim (e 0) (e 1)))
  have hsub : Subsingleton (Fin r) := by
    refine ⟨fun i j ↦ ?_⟩
    by_contra hij
    let x : ∀ k, A k := Pi.single i 1
    let y : ∀ k, A k := Pi.single j 1
    have hxy : x * y = 0 := by
      ext k
      by_cases hk : k = i
      · subst k; simp [x, y, Ne.symm hij]
      · simp [x, y, hk]
    have hzero : e.symm x * e.symm y = 0 := by
      rw [← map_mul, hxy, map_zero]
    rcases mul_eq_zero.mp hzero with hx | hy
    · have hi := congrFun (congrArg e hx) i
      simp [x] at hi
    · have hj := congrFun (congrArg e hy) j
      simp [y] at hj
  have := hsub
  let i := Classical.choice hne
  let f : B →+* A i := (Pi.evalRingHom A i).comp e.toRingHom
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      apply e.injective
      funext j
      have : j = i := Subsingleton.elim _ _
      subst j
      exact hxy
    · intro x
      obtain ⟨y, hy⟩ := e.surjective (Pi.single i x)
      exact ⟨y, by simpa [f] using congrFun hy i⟩
  exact HenselianLocalRing.of_ringEquiv (RingEquiv.ofBijective f hf).symm

private theorem branch_properties (R : Type u) [CommRing R]
    (hExcellent : IsExcellent R) [IsStrictlyHenselianLocalRing R]
    (hDim : ringKrullDim R = 1) (hAlgClosed : IsAlgClosed (IsLocalRing.ResidueField R))
    (a : excLocalCurveBranchIndex R) :
    ∃ hLocal : IsLocalRing (excLocalCurveBranchIntegralClosure R a),
      IsDiscreteValuationRing (excLocalCurveBranchIntegralClosure R a) ∧
      IsStrictlyHenselianLocalRing (excLocalCurveBranchIntegralClosure R a) ∧
      IsExcellent (excLocalCurveBranchIntegralClosure R a) ∧
      (∃ e : @IsLocalRing.ResidueField (excLocalCurveBranchIntegralClosure R a) _ hLocal ≃+*
          IsLocalRing.ResidueField R,
        ∀ r : R, e (@IsLocalRing.residue (excLocalCurveBranchIntegralClosure R a) _ hLocal
          (excLocalCurveBranchAlgebraMap R a r)) = IsLocalRing.residue R r) ∧
      IsFractionRing (excLocalCurveBranchIntegralClosure R a)
        (excLocalCurveBranchFractionRing R a) := by
  classical
  have := hExcellent.1.1
  have := a.2.isPrime
  let A := excLocalCurveBranchQuotient R a
  let K := excLocalCurveBranchFractionRing R a
  let N := integralClosure A K
  have hN2 : IsN2 A K := (isNagataRing_of_isQuasiExcellent R hExcellent.1).2 a.1
  have : Module.Finite A N := isN1_of_isN2 A K hN2
  have : Module.Finite R N := Module.Finite.trans A N
  have : IsLocalRing A :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk a.1) Ideal.Quotient.mk_surjective
  obtain ⟨_, hDedekind, hDimN, hFrac⟩ :=
    integralClosure.semilocal_normalization_dim_one A (branch_dimension R hDim a) K
  have := hDedekind
  have := finite_henselian_domain R N
  have : IsLocalHom (algebraMap R N) := by
    apply ((IsLocalRing.local_hom_TFAE (algebraMap R N)).out 4 0).mp
    exact IsLocalRing.eq_maximalIdeal
      (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (IsLocalRing.maximalIdeal N))
  have : Module.Finite (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField N) :=
    inferInstance
  have := hAlgClosed
  let e : IsLocalRing.ResidueField R ≃+* IsLocalRing.ResidueField N :=
    RingEquiv.ofBijective _ IsAlgClosed.algebraMap_bijective_of_isIntegral
  have hStrict : IsStrictlyHenselianLocalRing N :=
    ⟨IsSepClosed.of_ringEquiv e⟩
  have hDVR : IsDiscreteValuationRing N := by
    apply ((IsDiscreteValuationRing.TFAE N ?_).out 2 0).mp hDedekind
    intro hfield
    have hz := ringKrullDim_eq_zero_of_isField hfield
    rw [hDimN] at hz
    exact (by decide : (1 : WithBot ℕ∞) ≠ 0) hz
  refine ⟨(inferInstance : IsLocalRing N), hDVR, hStrict, ?_, ⟨e.symm, ?_⟩, hFrac⟩
  · exact (isExcellent_finiteType_localization hExcellent (⊥ : Submonoid N)).2
  · intro r
    change e.symm (IsLocalRing.residue N (algebraMap R N r)) = IsLocalRing.residue R r
    apply e.injective
    rw [e.apply_symm_apply]
    exact (IsLocalRing.ResidueField.algebraMap_residue r).symm

private theorem total_fraction_branches (R : Type u) [CommRing R]
    [IsNoetherianRing R] [IsReduced R] :
    Nonempty (FractionRing R ≃ₐ[R]
      (∀ a : excLocalCurveBranchIndex R, excLocalCurveBranchFractionRing R a)) := by
  classical
  obtain ⟨t, q, hfields, _, hres, _, hmaps, hbij⟩ :=
    reduced_noetherian_total_ring_fractions (R := R)
  let E : Fin t ≃ excLocalCurveBranchIndex R := q.trans
    { toFun := fun p ↦ ⟨p.1.asIdeal, p.2⟩
      invFun := fun p ↦ ⟨⟨p.1, p.2.isPrime⟩, p.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  let φ := fun i ↦ (hmaps i).choose
  have hφ (i : Fin t) : (φ i).comp (algebraMap R (FractionRing R)) =
      algebraMap R (Localization.AtPrime (q i).1.asIdeal) := (hmaps i).choose_spec.1
  let ψ : FractionRing R →ₐ[R] (∀ i, Localization.AtPrime (q i).1.asIdeal) :=
    { __ := RingHom.pi φ
      commutes' := fun r ↦ funext fun i ↦ DFunLike.congr_fun (hφ i) r }
  let e₁ := AlgEquiv.ofBijective ψ (hbij φ hφ)
  let e₂ (i : Fin t) : Localization.AtPrime (q i).1.asIdeal ≃ₐ[R]
      excLocalCurveBranchFractionRing R (E i) :=
    (AlgEquiv.ofBijective
      (IsScalarTower.toAlgHom R (Localization.AtPrime (q i).1.asIdeal)
        (Ideal.ResidueField (q i).1.asIdeal)) (hres i)).trans
      ((FractionRing.algEquiv (R ⧸ (q i).1.asIdeal)
        (Ideal.ResidueField (q i).1.asIdeal)).symm.restrictScalars R)
  exact ⟨e₁.trans ((AlgEquiv.piCongrRight e₂).trans
    (AlgEquiv.piCongrLeft R (fun a ↦ excLocalCurveBranchFractionRing R a) E))⟩

/-- The punctured spectrum is the finite scheme coproduct of the canonical component
fields, whose normalization rings are excellent strictly henselian DVRs with the original
residue field. Source: blueprint lemma 1918; Stacks Tags 0C3R, 0C3S and 00PD
(blueprint: lem-exc-punctured-curve-branches).

Proof:
1. Minimal primes are finite by Noetherianity. Each quotient by a minimal prime is a
   one-dimensional local Noetherian domain (a longer chain contradicts dimension one).
2. Excellence implies Nagata (lem-exc-quasi-excellent-nagata). Apply N-2 to the identity
   field extension to obtain finite normalization of each component and their product.
3. Apply lem-sc-semilocal-dim-one-normalization: each normalization is a semilocal normal
   Noetherian one-dimensional domain with the original component fraction field.
4. The finite-over-henselian-local-product theorem decomposes each normalization. A domain
   has no nontrivial idempotents, so there is exactly one local henselian factor. Its residue
   extension is finite over the algebraically closed original residue field, hence the
   canonical residue map is an isomorphism and the normalization is strictly henselian.
5. Apply lem-sc-normal-dim1-dvr (Stacks 00PD) to each normal one-dimensional local domain.
6. Finiteness implies finite type, so lem-exc-finite-type-localization-excellent gives
   excellence of every normalization.
7. Choose the principal puncture of lem-exc-local-curve-principal-total-fractions. Its
   localization is the total fraction ring, canonically the product of component fields by
   lem-weil-pbc-reduced-noetherian-total-ring-fractions. The component maps are quotient
   maps followed by fraction inclusions and agree with the branch-algebra construction.
8. The principal-localization open immersion identifies the puncture as schemes with this
   product's spectrum. The finite affine coproduct theorem gives the displayed coproduct
   over Spec R, with the canonical component maps.
-/
theorem punctured_curve_has_dvr_branches
    (R : Type u) [CommRing R] [IsReduced R]
    (hExcellent : IsExcellent R) [IsStrictlyHenselianLocalRing R]
    (hDim : ringKrullDim R = (1 : WithBot ℕ∞))
    (p : ℕ) (hp : Nat.Prime p)
    (hChar : ringChar (IsLocalRing.ResidueField R) = p)
    (hAlgClosed : IsAlgClosed (IsLocalRing.ResidueField R)) :
    Finite (excLocalCurveBranchIndex R) ∧
    ∃ hLocal : ∀ a : excLocalCurveBranchIndex R,
        IsLocalRing (excLocalCurveBranchIntegralClosure R a),
      (∀ a : excLocalCurveBranchIndex R,
        IsDiscreteValuationRing (excLocalCurveBranchIntegralClosure R a)) ∧
      (∀ a : excLocalCurveBranchIndex R,
        IsStrictlyHenselianLocalRing (excLocalCurveBranchIntegralClosure R a)) ∧
      (∀ a : excLocalCurveBranchIndex R, IsExcellent (excLocalCurveBranchIntegralClosure R a)) ∧
      (∀ a : excLocalCurveBranchIndex R,
        ∃ e : @IsLocalRing.ResidueField (excLocalCurveBranchIntegralClosure R a) _ (hLocal a) ≃+*
            IsLocalRing.ResidueField R,
          ∀ r : R, e (@IsLocalRing.residue (excLocalCurveBranchIntegralClosure R a) _ (hLocal a)
            (excLocalCurveBranchAlgebraMap R a r)) = IsLocalRing.residue R r) ∧
      (∀ a : excLocalCurveBranchIndex R,
        IsFractionRing (excLocalCurveBranchIntegralClosure R a)
          (excLocalCurveBranchFractionRing R a)) ∧
      ∃ U : (Spec (.of R)).Opens,
        (∀ x : Spec (.of R), x ∈ U ↔ x ≠ IsLocalRing.closedPoint R) ∧
        ∃ e : U.toScheme ≅
            ∐ (fun a : excLocalCurveBranchIndex R ↦
              Spec (.of (excLocalCurveBranchFractionRing R a))),
          e.hom ≫ Sigma.desc (fun a ↦ Spec.map
            (CommRingCat.ofHom (algebraMap R (excLocalCurveBranchFractionRing R a)))) = U.ι := by
  classical
  -- The construction works in every residue characteristic.
  have _ := hp
  have _ := hChar
  clear hp hChar
  have := hExcellent.1.1
  have hfinite : Finite (excLocalCurveBranchIndex R) :=
    (minimalPrimes.finite_of_isNoetherianRing R).fintype.finite
  have H := fun a ↦ branch_properties R hExcellent hDim hAlgClosed a
  choose hLocal hDVR hStrict hExc hResidue hFrac using H
  refine ⟨hfinite, hLocal, hDVR, hStrict, hExc, hResidue, hFrac, ?_⟩
  obtain ⟨f, hf, hfm, _, hrad, hbij⟩ :=
    IsLocalRing.exists_parameter_principal_total_fractions R hDim
  obtain ⟨eQ⟩ := total_fraction_branches R
  let E : Localization.Away f ≃ₐ[R]
      (∀ a : excLocalCurveBranchIndex R, excLocalCurveBranchFractionRing R a) :=
    (AlgEquiv.ofBijective
      (IsLocalization.Away.liftAlgHom (S := Localization.Away f)
        (f := Algebra.ofId R (FractionRing R)) f
        (IsLocalization.map_units (FractionRing R) ⟨f, hf⟩)) hbij).trans eQ
  let U : (Spec (.of R)).Opens := PrimeSpectrum.basicOpen f
  let g := Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away f)))
  let eA := asIso (sigmaSpec (fun a : excLocalCurveBranchIndex R ↦
    CommRingCat.of (excLocalCurveBranchFractionRing R a))) ≪≫
      Scheme.Spec.mapIso E.toRingEquiv.toCommRingCatIso.op
  have hcan : eA.hom ≫ g = Sigma.desc (fun a ↦ Spec.map
      (CommRingCat.ofHom (algebraMap R (excLocalCurveBranchFractionRing R a)))) := by
    apply Sigma.hom_ext
    intro a
    dsimp only [eA, Iso.trans_hom, asIso_hom]
    rw [Category.assoc, ι_sigmaSpec_assoc, Sigma.ι_desc]
    change Spec.map (CommRingCat.ofHom (Pi.evalRingHom _ a)) ≫
      Spec.map (CommRingCat.ofHom E.toRingHom) ≫ g = _
    dsimp only [g]
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    ext r
    exact congrFun (E.commutes r) a
  have hrange : Set.range U.ι = Set.range (eA.hom ≫ g) := by
    rw [Scheme.Opens.range_ι, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
    have hefull : Set.range eA.hom = Set.univ := eA.hom.homeomorph.surjective.range_eq
    rw [hefull, Set.image_univ]
    exact congrArg SetLike.coe (Scheme.Hom.opensRange_localizationAway (R := .of R) f).symm
  refine ⟨U, ?_, IsOpenImmersion.isoOfRangeEq U.ι (eA.hom ≫ g) hrange, ?_⟩
  · intro x
    change f ∉ x.asIdeal ↔ x ≠ IsLocalRing.closedPoint R
    have hclosed : f ∈ x.asIdeal ↔ x = IsLocalRing.closedPoint R := by
      constructor
      · intro hx
        apply PrimeSpectrum.ext
        apply le_antisymm (IsLocalRing.le_maximalIdeal x.isPrime.ne_top)
        rw [← hrad]
        exact x.isPrime.radical_le_iff.mpr ((Ideal.span_singleton_le_iff_mem x.asIdeal).mpr hx)
      · rintro rfl
        exact hfm
    exact not_congr hclosed
  · rw [← hcan]
    exact IsOpenImmersion.isoOfRangeEq_hom_fac _ _ hrange

end
