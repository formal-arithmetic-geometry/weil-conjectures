/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.GaloisTraceInfinite.FieldTowerMoebius
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.GaloisTraceInfinite.TowerUnique
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UnitTransportExtendScalars
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushIntegersModPowFinal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CoefficientChangeRestrictedSplitMonoTorsion

/-!
# The derived unit of an infinite Galois extension with `𝒪_E`-coefficients splits

Let `Ω/L` be a Galois extension whose finite Galois subextensions have degrees prime to `ℓ`
(for instance a pro-`p` extension, `p ≠ ℓ`), `h : G ⟶ Spec L` and `g : G ×_L Ω ⟶ G`. For a
derived complete `𝒪_E`-complex `K` on `G` whose reductions modulo `ℓⁿ⁺¹` are bounded below of
étale origin, the unit `K ⟶ Rg_* Lg^* K` is a split monomorphism
(`ProEtale.CondensedRing.isSplitMono_derivedUnit_galois_padicIntegers`): this is the integral form
of the Hochschild–Serre splitting of SGA 4½, [Th. finitude], Lemme 3.4.

The proof lifts the torsion splittings with `ProEtale.isSplitMono_of_derivedCompleteIntegers_of_unique_retractions`.
Modulo `ℓⁿ⁺¹` the reduction of the unit is the unit with coefficients `𝒪_E/ℓⁿ⁺¹`
(`ProEtale.CondensedRing.map_unit_comp_derivedPushPullExtendScalarsHom`, the push comparison
being invertible by `isIso_derivedUpperStarExtendScalarsPushHom_integersModPow_app`), compatibly
with the Galois actions. There it has a `Gal(Ω/L)`-invariant retraction
(`ProEtale.exists_invariant_retraction_derivedUnit_galois`), which is unique
(`ProEtale.eq_of_invariant_retraction_derivedUnit_galois`, from the Möbius decomposition of the
infinite level, `ProEtale.galoisTowerMoebiusDecomposition`). The reduction of an invariant
retraction is invariant, the Galois action being defined with integral coefficients.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace PadicAlgCl

variable {ℓ : ℕ} [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]

/-- A natural number prime to `ℓ` is a unit in `𝒪_E ⧸ ℓⁿ`. -/
lemma isUnit_natCast_integersModPow (n : ℕ) {d : ℕ} (hd : ¬ ℓ ∣ d) :
    IsUnit (d : integersModPow ℓ E n) := by
  have hcop : Nat.Coprime d (ℓ ^ n) :=
    Nat.Coprime.pow_right n (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hd))
  have h := (Nat.isCoprime_iff_coprime.2 hcop).map (Int.castRingHom (integersModPow ℓ E n))
  have h0 : ((ℓ ^ n : ℕ) : integersModPow ℓ E n) = 0 := by
    change integersModPowMk ℓ E n ((ℓ ^ n : ℕ) : integers ℓ E) = 0
    rw [integersModPowMk, Ideal.Quotient.eq_zero_iff_mem, Nat.cast_pow]
    exact Ideal.subset_span rfl
  simp only [eq_intCast, Int.cast_natCast, h0] at h
  exact isCoprime_zero_right.1 h

end PadicAlgCl

namespace AlgebraicGeometry.ProEtale

open Scheme CondensedRing

variable {L Ω : Type u} [Field L] [Field Ω] [Algebra L Ω] [IsGalois L Ω] {G : Scheme.{u}}
  (h : G ⟶ Spec (.of L))

/-- **The Galois invariant retraction of the derived unit is unique** (torsion coefficients in
which the degrees of the finite Galois subextensions of `Ω/L` are invertible): two retractions of
`C ⟶ Rg_* Lg^* C` fixed by the derived unit transports along all the `Spec σ`, `σ ∈ Gal(Ω/L)`,
are equal, for `C` bounded below of étale origin. -/
theorem eq_of_invariant_retraction_derivedUnit_galois (T₀ : Type) [TopologicalSpace T₀]
    [CommRing T₀] [IsTopologicalRing T₀] [DiscreteTopology T₀] [Finite T₀]
    (hp : ∀ L' : FiniteGaloisIntermediateField L Ω, IsUnit ((Module.finrank L L' : ℕ) : T₀))
    (C : DerivedCategory (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology G) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T₀) G)))
    (hC : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} T₀)) G
      ((finiteCoefficientDerivedEquivalence G T₀).functor.obj C))
    {R R' : R((pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω))))_*⟦
        Profinite.continuousMapRingObj T₀⟧).obj
          (L((pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω))))^*⟦
            Profinite.continuousMapRingObj T₀⟧).obj C) ⟶ C}
    (hR : (CondensedRing.derivedUpperStarLowerStarAdjunction (Profinite.continuousMapRingObj T₀)
      (pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω))))).unit.app C ≫ R = 𝟙 _)
    (hR' : (CondensedRing.derivedUpperStarLowerStarAdjunction (Profinite.continuousMapRingObj T₀)
      (pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω))))).unit.app C ≫ R' = 𝟙 _)
    (hinv : ∀ σ : Ω ≃ₐ[L] Ω, derivedUnitTransport (Profinite.continuousMapRingObj T₀)
      (pullbackAction h _ specGaloisAction_comp σ)
      (pullbackAction_fst h _ specGaloisAction_comp σ)
      (pullbackAction_fst h _ specGaloisAction_comp σ) C ≫ R = R)
    (hinv' : ∀ σ : Ω ≃ₐ[L] Ω, derivedUnitTransport (Profinite.continuousMapRingObj T₀)
      (pullbackAction h _ specGaloisAction_comp σ)
      (pullbackAction_fst h _ specGaloisAction_comp σ)
      (pullbackAction_fst h _ specGaloisAction_comp σ) C ≫ R' = R') :
    R = R' := by
  obtain ⟨K, a, hKa, hterms, ⟨e⟩⟩ := exists_complex_of_plusEtaleOrigin T₀ C hC
  choose F₀ hF₀ using hterms
  have hd : ∀ (j : FiniteGaloisIntermediateField L Ω)
      (N : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology G) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousMapRingObj T₀) G)),
      IsIso (Fintype.card ((galoisTower Ω h).Γ j) • 𝟙 N) := fun j N ↦ by
    have hc : Fintype.card ((galoisTower Ω h).Γ j) = Module.finrank L j := by
      change Fintype.card (j ≃ₐ[L] j) = _
      rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank]
    rw [hc]
    exact CondensedRing.isIso_nsmul_id_mod_of_isUnit _ (Profinite.continuousMapConstRingHom T₀)
      (hp j) N
  have hc := fun n ↦ isColimitModuleCocone_galoisTower Ω h T₀ (K.X n)
    (essImage_comparisonUpperStar_X T₀ (K.X n) (F₀ n) (hF₀ n).some)
  have hK := fun n ↦
    rightAcyclic_condensedRingLowerStar_upperStar_of_iso (Ω := Ω) T₀ h (K.X n) (F₀ n) (hF₀ n)
  exact (galoisTowerMoebiusDecomposition h (Profinite.continuousMapRingObj T₀) hd K
    hc).eq_of_retraction_derivedUnit_of_iso a hK e hR hR' (fun _ _ ↦ hinv _) (fun _ _ ↦ hinv' _)

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

variable {ℓ : ℕ} [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
  {L Ω : Type u} [Field L] [Field Ω] [Algebra L Ω] [IsGalois L Ω] {G : Scheme.{u}}
  (h : G ⟶ Spec (.of L))

/-- The reduction modulo `ℓⁿ⁺¹` of `L(φ') f ≫ s` is `L(φ) f` followed by the reduction of `s`. -/
lemma derivedExtendScalarsReduction_map_comp (n : ℕ)
    {A B B' : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology G) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) G))} (f : B' ⟶ B)
    (s : L(Mod.extendScalars (integersModPowReduction G ℓ E.1 (n + 1 + 1))).obj B ⟶
      L(Mod.extendScalars (integersModPowReduction G ℓ E.1 (n + 1 + 1))).obj A) :
    Mod.derivedExtendScalarsReduction (integersModPowReduction G ℓ E.1 (n + 1 + 1))
        (modPowTransition G ℓ E.1 (n + 1)) (integersModPowReduction G ℓ E.1 (n + 1))
        (integersModPowReduction_comp_modPowTransition G ℓ E.1 (n + 1))
        (L(Mod.extendScalars (integersModPowReduction G ℓ E.1 (n + 1 + 1))).map f ≫ s) =
      L(Mod.extendScalars (integersModPowReduction G ℓ E.1 (n + 1))).map f ≫
        Mod.derivedExtendScalarsReduction (integersModPowReduction G ℓ E.1 (n + 1 + 1))
          (modPowTransition G ℓ E.1 (n + 1)) (integersModPowReduction G ℓ E.1 (n + 1))
          (integersModPowReduction_comp_modPowTransition G ℓ E.1 (n + 1)) s := by
  simp only [Mod.derivedExtendScalarsReduction, Functor.map_comp]
  rw [← Category.assoc, ← Category.assoc, ← Category.assoc]
  congr 2
  exact ((Mod.derivedExtendScalarsCompIso _ _ _ _).hom.naturality f).symm

/-- **The derived unit of an infinite Galois extension of degrees prime to `ℓ` splits with
`𝒪_E`-coefficients** at every derived complete complex whose reductions modulo `ℓⁿ⁺¹` are bounded
below of étale origin. -/
theorem isSplitMono_derivedUnit_galois_padicIntegers
    (hp : ∀ L' : FiniteGaloisIntermediateField L Ω, ¬ ℓ ∣ Module.finrank L L')
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology G) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) G)))
    (hK : derivedCompleteIntegers ℓ E G K) (m : ℤ) [K.IsGE m]
    (hred : ∀ n : ℕ, DerivedCategory.plusEtaleOrigin
      (ModuleCat.{u + 1} (ULift.{u + 1} (integersModPow ℓ E.1 (n + 1)))) G
      ((finiteCoefficientDerivedEquivalence G (integersModPow ℓ E.1 (n + 1))).functor.obj
        (L(Mod.extendScalars (integersModPowReduction G ℓ E.1 (n + 1))).obj K))) :
    IsSplitMono ((derivedUpperStarLowerStarAdjunction (Profinite.padicIntegersRingObj ℓ E.1)
      (pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω))))).unit.app K) := by
  -- the Galois action with integral coefficients
  let u (σ : Ω ≃ₐ[L] Ω) := derivedUnitTransport (Profinite.padicIntegersRingObj ℓ E.1)
    (pullbackAction h _ specGaloisAction_comp σ) (pullbackAction_fst h _ specGaloisAction_comp σ)
    (pullbackAction_fst h _ specGaloisAction_comp σ) K
  -- the comparison of the reduction of `Rg_* Lg^* K` with `Rg_* Lg^*` of the reduction
  have hc (n : ℕ) : IsIso (derivedPushPullExtendScalarsHom
      (Profinite.padicIntegersRingObjToIntegersModPow ℓ E.1 (n + 1))
      (pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω))))
      (pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω)))) K) := by
    have := isGE_leftDerivedUpperStar_obj (Profinite.padicIntegersRingObj ℓ E.1)
      (pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω)))) K m
    have := isIso_derivedUpperStarExtendScalarsPushHom_integersModPow_app ℓ E.1 (n + 1)
      (pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω))))
      ((L((pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω))))^*⟦
        Profinite.padicIntegersRingObj ℓ E.1⟧)).obj K) m
    infer_instance
  let c (n : ℕ) := asIso (derivedPushPullExtendScalarsHom
      (Profinite.padicIntegersRingObjToIntegersModPow ℓ E.1 (n + 1))
      (pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω))))
      (pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω)))) K)
  have hη (n : ℕ) := map_unit_comp_derivedPushPullExtendScalarsHom
    (Profinite.padicIntegersRingObjToIntegersModPow ℓ E.1 (n + 1))
    (pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω)))) K
  have hu (n : ℕ) (σ : Ω ≃ₐ[L] Ω) := map_derivedUnitTransport_comp_derivedPushPullExtendScalarsHom
    (Profinite.padicIntegersRingObjToIntegersModPow ℓ E.1 (n + 1))
    (pullbackAction h _ specGaloisAction_comp σ) (pullbackAction_fst h _ specGaloisAction_comp σ)
    (pullbackAction_fst h _ specGaloisAction_comp σ) K
  have hunit (n : ℕ) : ∀ L' : FiniteGaloisIntermediateField L Ω,
      IsUnit ((Module.finrank L L' : ℕ) : integersModPow ℓ E.1 (n + 1)) := fun L' ↦
    isUnit_natCast_integersModPow E.1 (n + 1) (hp L')
  refine ProEtale.isSplitMono_of_derivedCompleteIntegers_of_unique_retractions _ hK
    (fun n r ↦ ∀ σ, L(Mod.extendScalars (integersModPowReduction G ℓ E.1 (n + 1))).map (u σ) ≫ r =
      r) (fun n ↦ ?_) (fun n r r' hr hr' h₁ h₁' ↦ ?_) (fun n r hr _ σ ↦ ?_)
  · obtain ⟨R₀, h₁, h₂⟩ := exists_invariant_retraction_derivedUnit_galois h
      (integersModPow ℓ E.1 (n + 1)) (hunit n) _ (hred n)
    refine ⟨(c n).hom ≫ R₀, fun σ ↦ ?_, ?_⟩
    · change _ ≫ derivedPushPullExtendScalarsHom _ _ _ K ≫ R₀ = _
      rw [reassoc_of% (hu n σ), h₂]
    · change _ ≫ derivedPushPullExtendScalarsHom _ _ _ K ≫ R₀ = _
      rw [reassoc_of% (hη n), h₁]
  · have hη' : (derivedUpperStarLowerStarAdjunction _
        (pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω))))).unit.app _ ≫
          (c n).inv = L(Mod.extendScalars (integersModPowReduction G ℓ E.1 (n + 1))).map
            ((derivedUpperStarLowerStarAdjunction (Profinite.padicIntegersRingObj ℓ E.1)
              (pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω))))).unit.app K) := by
      rw [Iso.comp_inv_eq]
      exact (hη n).symm
    have hu' (σ : Ω ≃ₐ[L] Ω) : derivedUnitTransport _
        (pullbackAction h _ specGaloisAction_comp σ)
        (pullbackAction_fst h _ specGaloisAction_comp σ)
        (pullbackAction_fst h _ specGaloisAction_comp σ) _ ≫ (c n).inv =
          (c n).inv ≫ L(Mod.extendScalars (integersModPowReduction G ℓ E.1 (n + 1))).map
            (u σ) := by
      rw [Iso.eq_inv_comp, ← Category.assoc, Iso.comp_inv_eq]
      exact (hu n σ).symm
    have := eq_of_invariant_retraction_derivedUnit_galois h (integersModPow ℓ E.1 (n + 1))
      (hunit n) _ (hred n) (R := (c n).inv ≫ r) (R' := (c n).inv ≫ r')
      (by rw [reassoc_of% hη', h₁]) (by rw [reassoc_of% hη', h₁'])
      (fun σ ↦ by rw [reassoc_of% (hu' σ), hr σ]) (fun σ ↦ by rw [reassoc_of% (hu' σ), hr' σ])
    exact (cancel_epi _).1 this
  · rw [← derivedExtendScalarsReduction_map_comp, hr σ]

end AlgebraicGeometry.ProEtale.CondensedRing
