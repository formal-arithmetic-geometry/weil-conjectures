/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.LocallyFree
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleUpperStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralConstantComplex
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralConstantRegularEnd
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DerivedComplete.IntegralLocalStructure
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Constructible
public import WeilConjectures.TraceFormula.OpenCover

/-!
# Local criteria for bounded constructibility

Let `Λ` be a commutative condensed ring and `X` a noetherian scheme with a finite stratification
`X = ∐ₛ Xₛ` and pro-étale covers `𝒰ₛ` of the strata. We record:

* a module object over `Λ_X` whose pullbacks to all members of all the covers `𝒰ₛ` vanish is
  zero (`ProEtale.CondensedRing.isZero_of_forall_isZero_upperStar_stratification`);
* a module object over `Λ_X` whose pullbacks to all members of all the covers `𝒰ₛ` are finitely
  presented is constructible
  (`ProEtale.CondensedRing.isConstructibleModuleObject_of_isFinitelyPresented_upperStar`);
* the constant modules `⊕ⱼ 𝒪_E/ϖ^{eⱼ} ⊕ 𝒪_E^r` are finitely presented
  (`ProEtale.isFinitelyPresented_integralConstantModule`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme

namespace CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- On a noetherian scheme, given a finite stratification and pro-étale covers of its strata,
there is a finite jointly surjective family of quasi-compact morphisms `W ⟶ X`, each factoring
as an open immersion into a member of the cover of a stratum followed by the structure maps. -/
lemma exists_finite_cover_of_stratification {X : Scheme.{u}} [IsNoetherian X]
    (S : Scheme.Stratification X)
    (𝒰 : ∀ s : Fin S.n, Scheme.Cover.{u} Scheme.proetalePrecoverage (S.domain s)) :
    ∃ (κ : Type) (_ : Finite κ) (W : κ → Scheme.{u}) (g : ∀ p, W p ⟶ X)
      (_ : ∀ p, QuasiCompact (g p)), (∀ x, ∃ p, x ∈ Set.range (g p).base) ∧
      ∀ p, ∃ (s : Fin S.n) (i : (𝒰 s).I₀) (h : W p ⟶ (𝒰 s).X i),
        g p = h ≫ (𝒰 s).f i ≫ S.immersion s := by
  -- the strata are quasi-compact
  have hc (a : Fin S.n) : CompactSpace (S.domain a) := by
    have := (S.immersion a).isEmbedding.isInducing.noetherianSpace
    infer_instance
  -- finitely many affine opens of members of the covers cover each stratum
  have hqc (a : Fin S.n) : QuasiCompactCover (𝒰 a).toPreZeroHypercover := by
    rw [← Scheme.presieve₀_mem_qcPrecoverage_iff]
    exact (show _ ∈ propQCPrecoverage @WeaklyEtale _ from (𝒰 a).mem₀).1
  have hfin (a : Fin S.n) := QuasiCompactCover.exists_isAffineOpen_of_isCompact
    (𝒰 a).toPreZeroHypercover (U := ⊤) (by simpa using isCompact_univ)
  choose N j W hW hcov using hfin
  refine ⟨Σ a : Fin S.n, Fin (N a), inferInstance, fun p ↦ W p.1 p.2,
    fun p ↦ (W p.1 p.2).ι ≫ (𝒰 p.1).f (j p.1 p.2) ≫ S.immersion p.1, fun p ↦ ?_, fun x ↦ ?_,
    fun p ↦ ⟨p.1, j p.1 p.2, (W p.1 p.2).ι, rfl⟩⟩
  · have : IsAffine (W p.1 p.2) := hW p.1 p.2
    exact quasiCompact_of_compactSpace _
  · obtain ⟨a, ha⟩ := Set.mem_iUnion.1 (S.iUnion_stratum_eq_univ ▸ Set.mem_univ x)
    rw [← S.range_immersion a] at ha
    obtain ⟨y, rfl⟩ := ha
    have hy : y ∈ ⋃ i, (𝒰 a).f (j a i) '' (W a i) := by
      rw [hcov a]
      trivial
    obtain ⟨i, z, hz, rfl⟩ := Set.mem_iUnion.1 hy
    obtain ⟨w, rfl⟩ : z ∈ Set.range (W a i).ι := by
      rw [Scheme.Opens.range_ι]
      exact hz
    exact ⟨⟨a, i⟩, w, rfl⟩

/-- On a noetherian scheme, a module object over `Λ_X` whose pullbacks to all members of
pro-étale covers of the strata of a finite stratification vanish is zero. -/
theorem isZero_of_forall_isZero_upperStar_stratification {X : Scheme.{u}} [IsNoetherian X]
    (S : Scheme.Stratification X)
    (𝒰 : ∀ s : Fin S.n, Scheme.Cover.{u} Scheme.proetalePrecoverage (S.domain s))
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : ∀ s i, IsZero (((𝒰 s).f i ≫ S.immersion s)^*⟦Λ⟧.obj M)) : IsZero M := by
  obtain ⟨κ, _, W, g, _, hg, hfac⟩ := exists_finite_cover_of_stratification S 𝒰
  refine isZero_of_forall_isZero_upperStar Λ g hg M fun p ↦ ?_
  obtain ⟨s, i, h, hp⟩ := hfac p
  rw [hp]
  exact ((h)^*⟦Λ⟧.map_isZero (hM s i)).of_iso ((upperStarComp Λ h _).app M)

/-- A module object over `Λ_X` whose pullbacks to all members of pro-étale covers of the strata
of a finite stratification are finitely presented is constructible. -/
theorem isConstructibleModuleObject_of_isFinitelyPresented_upperStar {X : Scheme.{u}}
    (S : Scheme.Stratification X)
    (𝒰 : ∀ s : Fin S.n, Scheme.Cover.{u} Scheme.proetalePrecoverage (S.domain s))
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : ∀ s i, Mod.IsFinitelyPresented (condensedRingObj Λ ((𝒰 s).X i))
      (((𝒰 s).f i ≫ S.immersion s)^*⟦Λ⟧.obj M)) :
    IsConstructibleModuleObject (condensedRingObj Λ X) M :=
  ⟨S, fun s ↦ (isLocallyFinitelyPresented_mapMod_iff Λ (S.immersion s) M).2
    ⟨𝒰 s, fun i ↦ (isFinitelyPresented_mapMod_iff Λ ((𝒰 s).f i) _).2
      ((hM s i).of_iso ((upperStarComp Λ _ _).app M))⟩⟩

end CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]

/-- The constant module `⊕ⱼ 𝒪_E/ϖ^{eⱼ} ⊕ 𝒪_E^r` over `𝒪_{E,V}` is finitely presented. -/
lemma isFinitelyPresented_integralConstantModule [Algebra ℚ_[ℓ] E]
    [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] (V : Scheme.{u})
    (ϖ : PadicAlgCl.integers ℓ E) (k r : ℕ) (e : Fin k → ℕ) :
    Mod.IsFinitelyPresented _ (integralConstantModule ℓ E V ϖ k r e) :=
  (prop_biproduct_of_forall (fun M ↦ Mod.IsFinitelyPresented _ M) (fun e h ↦ h.of_iso e)
    (fun _ hX ↦ Mod.IsFinitelyPresented.of_isZero hX) (fun _ _ hX hY ↦ hX.biprod hY) _
    fun _ ↦ Mod.isFinitelyPresented_cokernel_regular _).biprod
    (Mod.IsFree.isFinitelyPresented ⟨r, ⟨Iso.refl _⟩⟩)

end AlgebraicGeometry.ProEtale
