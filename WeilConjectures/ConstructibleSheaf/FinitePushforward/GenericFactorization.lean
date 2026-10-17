/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.FinitePushforward.RadicialEtale
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.RingHom.Etale

/-!
# Generic radicial-étale factorization of finite morphisms

Let `S` be an integral Noetherian affine scheme and `g : Z ⟶ S` a finite morphism. There are
universal homeomorphisms `a : Y ⟶ Z` and `u : Y ⟶ T` and a finite morphism `t : T ⟶ S` with
`a ≫ g = u ≫ t` such that `t` becomes étale over a nonempty open of `S`
(`AlgebraicGeometry.Scheme.Hom.exists_isUniversalHomeomorphism_etale_isPullback`). With
`S = Spec A` and `Z = Spec B`, one takes `Y = Spec B_red` and `T = Spec C` for the subalgebra
`C ⊆ B_red` of `Algebra.exists_subalgebra_isUniversalHomeomorphism_etale`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- **Generic radicial-étale factorization.** For a finite morphism `g : Z ⟶ S` to an integral
Noetherian affine scheme there are universal homeomorphisms `a : Y ⟶ Z`, `u : Y ⟶ T` and a
finite morphism `t : T ⟶ S` with `a ≫ g = u ≫ t`, together with an open immersion
`j : S' ⟶ S` from a nonempty scheme such that the base change `t' : T' ⟶ S'` of `t` along
`j` is étale. -/
theorem Scheme.Hom.exists_isUniversalHomeomorphism_etale_isPullback {S Z : Scheme.{u}}
    [IsIntegral S] [IsAffine S] [IsNoetherian S] (g : Z ⟶ S) [IsFinite g] :
    ∃ (Y T S' T' : Scheme.{u}) (a : Y ⟶ Z) (u : Y ⟶ T) (t : T ⟶ S) (j : S' ⟶ S)
      (j' : T' ⟶ T) (t' : T' ⟶ S'), IsUniversalHomeomorphism a ∧ IsUniversalHomeomorphism u ∧
      IsFinite t ∧ a ≫ g = u ≫ t ∧ IsOpenImmersion j ∧ Nonempty S' ∧ IsPullback j' t' t j ∧
      Etale t' := by
  classical
  have : IsAffine Z := isAffine_of_isAffineHom g
  have : IsNoetherianRing Γ(S, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top S⟩
  let : Algebra Γ(S, ⊤) Γ(Z, ⊤) := g.appTop.hom.toAlgebra
  have : Module.Finite Γ(S, ⊤) Γ(Z, ⊤) := g.finite_appTop
  set N := _root_.nilradical Γ(Z, ⊤)
  have : _root_.IsReduced (Γ(Z, ⊤) ⧸ N) :=
    (Ideal.isRadical_iff_quotient_reduced _).1 (Ideal.radical_isRadical _)
  have : Module.Finite Γ(S, ⊤) (Γ(Z, ⊤) ⧸ N) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ Γ(S, ⊤) N).toLinearMap
      Ideal.Quotient.mk_surjective
  obtain ⟨C, r, hr, hC, hEt⟩ :=
    Algebra.exists_subalgebra_isUniversalHomeomorphism_etale (A := Γ(S, ⊤)) (R := Γ(Z, ⊤) ⧸ N)
  have := C.moduleFinite_of_isNoetherianRing
  set Ar := Localization.Away r
  set Cr := Localization (Algebra.algebraMapSubmonoid C (.powers r))
  have : IsScalarTower Γ(S, ⊤) Ar Cr := isScalarTower_localizationAlgebra _ _
  -- the reduction `Spec (Γ(Z, ⊤) ⧸ N) ⟶ Z`
  have hsurj : Function.Surjective (PrimeSpectrum.comap (Ideal.Quotient.mk N)) := by
    intro x
    have : x ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk N)) := by
      rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective,
        Ideal.mk_ker]
      exact nilradical_le_prime x.asIdeal
    exact this
  have : Surjective (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk N))) := ⟨hsurj⟩
  -- the pullback square of spectra
  have hpo : Algebra.IsPushout Γ(S, ⊤) Ar C Cr :=
    (Algebra.isPushout_of_isLocalization (.powers r) Ar C Cr).symm
  have hpb := (isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_of_isPushout Γ(S, ⊤) Ar C Cr)).flip
  have : IsDomain Ar := IsLocalization.isDomain_localization
    (powers_le_nonZeroDivisors_of_noZeroDivisors hr)
  refine ⟨Spec (.of (Γ(Z, ⊤) ⧸ N)), Spec (.of C), Spec (.of Ar), Spec (.of Cr),
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk N)) ≫ Z.isoSpec.inv,
    Spec.map (CommRingCat.ofHom (algebraMap C _)),
    Spec.map (CommRingCat.ofHom (algebraMap Γ(S, ⊤) C)) ≫ S.isoSpec.inv,
    Spec.map (CommRingCat.ofHom (algebraMap Γ(S, ⊤) Ar)) ≫ S.isoSpec.inv,
    Spec.map (CommRingCat.ofHom (algebraMap C Cr)), Spec.map (CommRingCat.ofHom (algebraMap Ar Cr)),
    inferInstance, inferInstance, ?_, ?_, inferInstance,
    ⟨(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum Ar)⟩, ?_, ?_⟩
  · have : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, ⊤) C))) :=
      (IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.2 inferInstance)
    infer_instance
  · rw [Category.assoc, ← Scheme.isoSpec_inv_naturality, ← Spec.map_comp_assoc,
      ← Spec.map_comp_assoc]
    rfl
  · exact hpb.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) S.isoSpec.symm (by simp) (by simp)
      (by simp) (by simp)
  · exact (HasRingHomProperty.Spec_iff (P := @Etale)).2 (RingHom.etale_algebraMap.2 hEt)

end AlgebraicGeometry
