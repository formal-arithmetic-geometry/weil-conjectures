/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Fitting.FittingIdealSheaf
public import WeilConjectures.RingTheory.TraceFormula.PresentationFittingIdeal
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import WeilConjectures.AlgebraicGeometry.Morphisms.AffineModuleGermLocalization
import WeilConjectures.AlgebraicGeometry.QuasiCoherentIdealZeroSetAffine
import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.AlgebraicGeometry.OpenImmersion
import WeilConjectures.RingTheory.TraceFormula.AffinePrincipalFittingGenerators
import WeilConjectures.AlgebraicGeometry.Fitting.FittingIdealSheafAffineSections
import WeilConjectures.AlgebraicGeometry.Fitting.FittingSheafArbitraryPullback
import WeilConjectures.AlgebraicGeometry.Finite.FiniteStalkGeneratorsNeighborhood
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# The bounded-generator locus cut out by a Fitting ideal

Source: Stacks Project, Divisors, Tags 0C3C, 0C3F and 05P8(2); More on Algebra,
Tag 07ZC(1),(3),(4) (blueprint: lem-trf-fitting-ideal-generate-locally).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

private theorem generators_transport {R : Type u} [CommRing R]
    {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) (r : ℕ) :
    (∃ s : Fin r → M, Submodule.span R (Set.range s) = ⊤) ↔
      ∃ s : Fin r → N, Submodule.span R (Set.range s) = ⊤ := by
  have step {M N : Type u} [AddCommGroup M] [Module R M]
      [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N)
      (h : ∃ s : Fin r → M, Submodule.span R (Set.range s) = ⊤) :
      ∃ s : Fin r → N, Submodule.span R (Set.range s) = ⊤ := by
    obtain ⟨s, hs⟩ := h
    refine ⟨e ∘ s, ?_⟩
    rw [Set.range_comp]
    change Submodule.span R (e.toLinearMap '' Set.range s) = ⊤
    rw [← Submodule.map_span, hs, Submodule.map_top, e.range]
  exact ⟨step e, step e.symm⟩

private theorem local_fitting_eq_top_iff {R : Type u} [CommRing R] [IsLocalRing R]
    {M : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (r n : ℕ) (π : (Fin n → R) →ₗ[R] M) (hπ : Function.Surjective π) :
    π.presentationFittingIdeal r = ⊤ ↔
      ∃ s : Fin r → M, Submodule.span R (Set.range s) = ⊤ := by
  constructor
  · intro h
    obtain ⟨s, hs⟩ := LinearMap.exists_fin_generators_quotient_fittingTorsion r (1 : R)
      ⟨n, π, hπ, by simpa using h⟩
    have hk : LinearMap.ker (LinearMap.lsmul R M (1 : R)) = ⊥ := by
      ext m
      simp
    exact (generators_transport ((LinearMap.ker
      (LinearMap.lsmul R M (1 : R))).quotEquivOfEqBot hk) r).mp ⟨s, hs⟩
  · rintro ⟨s, hs⟩
    let q := Fintype.linearCombination R s
    have hq : Function.Surjective q :=
      (span_range_eq_top_iff_surjective_fintypeLinearCombination R s).mp hs
    rw [(LinearMap.presentationFittingIdeal_independence_baseChange.{u, u, u} r π hπ).1 r q hq]
    simp [LinearMap.presentationFittingIdeal]

private theorem affine_fitting_stalk (S : Scheme.{u}) (F : S.Modules)
    [F.IsFiniteType] [F.IsQuasicoherent] (r : ℕ) (U : S.affineOpens) (x : U.1)
    (n : ℕ) (π : (Fin n → Γ(S, U.1)) →ₗ[Γ(S, U.1)] Γ(F, U.1))
    (hπ : Function.Surjective π) :
    (¬ π.presentationFittingIdeal r ≤ (U.2.primeIdealOf x).asIdeal) ↔
      ∃ s : Fin r → (RingedSpace.moduleStalkFunctor S.toRingedSpace x.1).obj F,
        Submodule.span (S.presheaf.stalk x.1) (Set.range s) = ⊤ := by
  let A := Γ(S, U.1)
  let B := S.presheaf.stalk x.1
  let Mx := TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x.1
  let : Algebra A B := S.presheaf.algebra_section_stalk x
  let : Module B Mx := inferInstanceAs (Module B (F.presheaf.stalk x.1))
  let : Module A Mx := Module.compHom _ (S.presheaf.germ U.1 x.1 x.2).hom
  let : IsScalarTower A B Mx :=
    ⟨fun a b m ↦ mul_smul (S.presheaf.germ U.1 x.1 x.2 a) b m⟩
  let := U.2.isLocalization_stalk x
  let := finite_sections_of_finiteType F U.2
  obtain ⟨f, _, hf⟩ := isLocalizedModule_affine_germ F inferInstance U.1 U.2 x
  let := hf
  let e := (IsLocalizedModule.isBaseChange
    (U.2.primeIdealOf x).asIdeal.primeCompl B f).equiv
  have hbase := (LinearMap.presentationFittingIdeal_independence_baseChange.{u, u, u} r π hπ).2.1 B
  have hloc :
      (¬ π.presentationFittingIdeal r ≤ (U.2.primeIdealOf x).asIdeal) ↔
        Ideal.map (algebraMap A B) (π.presentationFittingIdeal r) = ⊤ := by
    constructor
    · exact IsLocalization.AtPrime.map_eq_top_of_not_le (R := A) (S := B)
    · intro htop hle
      have hle' := Ideal.map_mono (f := algebraMap A B) hle
      rw [htop, IsLocalization.AtPrime.map_eq_maximalIdeal
        (U.2.primeIdealOf x).asIdeal B] at hle'
      exact (IsLocalRing.maximalIdeal.isMaximal B).ne_top (top_le_iff.mp hle')
  rw [hloc, ← hbase.2, local_fitting_eq_top_iff r n _ hbase.1]
  exact generators_transport e r

private theorem ideal_stalk_surjective (S : Scheme.{u}) (K : S.IdealSheafData)
    (x : S) :
    (x ∉ K.support) ↔ Function.Surjective
      ((RingedSpace.moduleStalkFunctor S.toRingedSpace x).map K.toModulesι).hom := by
  have h := (S.quasi_coherent_ideal_zero_set_affine K).2.2.2.2
    K.subscheme K.subschemeι K.ker_subschemeι
  rw [K.range_subschemeι] at h
  change (¬ x ∈ (K.support : Set S)) ↔ _
  rw [h]
  simp only [Set.mem_ofPred_eq, not_not]

private theorem fitting_stalk_generators (S : Scheme.{u}) (F : S.Modules)
    [F.IsFiniteType] [F.IsQuasicoherent] (r : ℕ) (x : S) :
    (x ∉ (fittingIdealSheaf F r).support) ↔
      ∃ s : Fin r → (RingedSpace.moduleStalkFunctor S.toRingedSpace x).obj F,
        Submodule.span (S.presheaf.stalk x) (Set.range s) = ⊤ := by
  obtain ⟨U, hU, hx, _⟩ := exists_isAffineOpen_mem_and_subset
    (U := (⊤ : S.Opens)) (show x ∈ (⊤ : S.Opens) from trivial)
  let V : S.affineOpens := ⟨U, hU⟩
  let := finite_sections_of_finiteType F hU
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := Γ(S, U)) (M := Γ(F, U))
  let π := Fintype.linearCombination Γ(S, U) s
  have hπ : Function.Surjective π :=
    (span_range_eq_top_iff_surjective_fintypeLinearCombination Γ(S, U) s).mp hs
  rw [ideal_stalk_surjective]
  rw [(S.quasi_coherent_ideal_zero_set_affine (fittingIdealSheaf F r)).2.1 V ⟨x, hx⟩]
  rw [(fittingIdealSheaf_affine_sections F r V n π hπ).1]
  exact affine_fitting_stalk S F r V ⟨x, hx⟩ n π hπ

/-- The affine kernel-minor ideals glue to `fittingIdealSheaf F r`. Its support is the
underlying closed set of `(fittingIdealSheaf F r).subscheme`, whose canonical inclusion
is a closed immersion. The complement represents the locus where an arbitrary pullback
is locally generated by at most `r` sections. At each point, membership in the complement,
the ideal stalk being the whole local ring, generation on a neighbourhood, and generation
of the module stalk by at most `r` elements are equivalent. Families of exactly `r`
sections/elements encode "at most `r`" by padding with zeros, including `r = 0`.
Surjectivity of the inclusion of ideal stalks expresses equality with the local ring.
Source: Stacks Project, Divisors, Tags 0C3C, 0C3F, 05P8(2); More on Algebra, Tag 07ZC.
(blueprint: lem-trf-fitting-ideal-generate-locally)

Proof:
1. The affine-sections theorem computes the ideal on any affine generating presentation.
2. The affine germ-localization theorem identifies the module stalk with base change of
   the finite affine section module. Presentation independence and base change identify
   its Fitting ideal with the extended affine Fitting ideal. The latter is the unit ideal
   precisely when the affine ideal is not contained in the point's prime ideal.
3. Over the local ring, apply the principal-Fitting generator theorem with generator 1.
   Multiplication by 1 has zero kernel, so its quotient is the original module. Conversely,
   a presentation on r generators has unit rth Fitting ideal by convention. The ideal
   zero-set dictionary identifies the same condition with surjectivity of the ideal stalk.
4. The finite-type stalk/neighbourhood criterion extends a stalk generating family to a
   neighbourhood, and takes germs of neighbourhood generators in the other direction.
5. Arbitrary tensor pullback preserves finite type and quasi-coherence and pulls back
   the Fitting ideal. Its support is the inverse image of the original support. The
   pointwise criterion therefore says exactly that the morphism has image in the open
   complement, which is equivalent to factorization through that open subscheme.
-/
theorem fitting_ideal_generate_locally (S : Scheme.{u}) (F : S.Modules)
    [F.IsFiniteType] [F.IsQuasicoherent] (r : ℕ) :
    (∀ (U : S.affineOpens) (n : ℕ)
      (π : (Fin n → Γ(S, U.1)) →ₗ[Γ(S, U.1)] Γ(F, U.1)),
      Function.Surjective π → (fittingIdealSheaf F r).ideal U =
        π.presentationFittingIdeal r) ∧
    (∀ (T : Scheme.{u}) (g : T ⟶ S),
      (∀ t : T, ∃ U : T.Opens, t ∈ U ∧
        ∃ s : ULift.{u} (Fin r) → (((tensorPullback g).obj F).over U).sections,
          Epi ((((tensorPullback g).obj F).over U).freeHomEquiv.symm s)) ↔
      ∃ h : T ⟶ Scheme.Opens.toScheme (X := S) (fittingIdealSheaf F r).support.compl,
        h ≫ Scheme.Opens.ι (X := S) (fittingIdealSheaf F r).support.compl = g) ∧
    (∀ x : S,
      (x ∉ (fittingIdealSheaf F r).support ↔
        Function.Surjective ((RingedSpace.moduleStalkFunctor S.toRingedSpace x).map
          (fittingIdealSheaf F r).toModulesι).hom) ∧
      (x ∉ (fittingIdealSheaf F r).support ↔
        ∃ U : S.Opens, x ∈ U ∧
          ∃ s : ULift.{u} (Fin r) → (F.over U).sections,
            Epi ((F.over U).freeHomEquiv.symm s)) ∧
      (x ∉ (fittingIdealSheaf F r).support ↔
        ∃ s : Fin r → (RingedSpace.moduleStalkFunctor S.toRingedSpace x).obj F,
          Submodule.span (S.presheaf.stalk x) (Set.range s) = ⊤)) := by
  classical
  have hlocal (X : Scheme.{u}) (M : X.Modules) [M.IsFiniteType] [M.IsQuasicoherent]
      (x : X) :
      (x ∉ (fittingIdealSheaf M r).support) ↔
        ∃ U : X.Opens, x ∈ U ∧
          ∃ s : ULift.{u} (Fin r) → (M.over U).sections,
            Epi ((M.over U).freeHomEquiv.symm s) :=
    (fitting_stalk_generators X M r x).trans
      (finite_stalk_generators_iff_neighbourhood X M x r)
  refine ⟨?_, ?_, ?_⟩
  · intro U n π hπ
    exact (fittingIdealSheaf_affine_sections F r U n π hπ).1
  · intro T g
    obtain ⟨hft, hqc, _, hfit⟩ := fittingSheaf_arbitrary_pullback g F r
    let := hft
    let := hqc
    have hsupport : ∀ t : T,
        t ∉ (fittingIdealSheaf ((tensorPullback g).obj F) r).support ↔
          g t ∉ (fittingIdealSheaf F r).support := by
      intro t
      rw [hfit, Scheme.IdealSheafData.support_comap]
      rfl
    constructor
    · intro h
      have hrange : Set.range g ⊆ Set.range
          (Scheme.Opens.ι (X := S) (fittingIdealSheaf F r).support.compl) := by
        rw [Scheme.Opens.range_ι]
        rintro _ ⟨t, rfl⟩
        exact (hsupport t).mp ((hlocal T ((tensorPullback g).obj F) t).mpr (h t))
      exact ⟨IsOpenImmersion.lift _ g hrange, IsOpenImmersion.lift_fac _ _ _⟩
    · rintro ⟨h, hh⟩ t
      apply (hlocal T ((tensorPullback g).obj F) t).mp
      apply (hsupport t).mpr
      rw [← hh]
      exact (h t).2
  · intro x
    exact ⟨ideal_stalk_surjective S _ x, hlocal S F x,
      fitting_stalk_generators S F r x⟩

end AlgebraicGeometry.Scheme.Modules
