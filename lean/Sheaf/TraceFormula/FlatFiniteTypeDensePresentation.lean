/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Restrict
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Sheaf.TraceFormula.SchematicallyDenseOpen
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
import Mathlib.RingTheory.LocalProperties.FinitePresentation
import Mathlib.LinearAlgebra.TensorProduct.Pi
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import WeilConjectures.AlgebraicGeometry.Modules.FiniteDescent
import WeilConjectures.Mathlib.RingTheory.Flat.Localization
import WeilConjectures.RingTheory.OpenFlatLocus
import Sheaf.TraceFormula.FlatFiniteTypeFlatPointLocal

/-!
# Relative flatness extends finite presentation from a dense open

Source: Stacks Project, `flat.tex`, Tag 081N, lemma
`lemma-flat-finite-type-finitely-presented-over-dense-open`
(blueprint: lem-trf-flat-finite-type-dense-presentation).
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory
open AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme.Modules

private theorem exists_fg_localized_eq {B M : Type*} [CommRing B]
    [AddCommGroup M] [Module B M] (K : Submodule B M) (T : Submonoid B)
    (h : (K.localized T).FG) :
    ∃ L : Submodule B M, L.FG ∧ L ≤ K ∧ L.localized T = K.localized T := by
  classical
  change (K.localized' (Localization T) T (LocalizedModule.mkLinearMap T M)).FG at h
  rw [Submodule.localized'_eq_span] at h
  obtain ⟨s, hs, he⟩ := Submodule.fg_span_iff_fg_span_finset_subset _ |>.mp h
  obtain ⟨t, ht, htf, hts⟩ := Set.exists_subset_image_finite_and.mp
    (show ∃ s' ⊆ (LocalizedModule.mkLinearMap T M) '' (K : Set M),
      s'.Finite ∧ Submodule.span (Localization T) s' = K.localized T from
      ⟨s, hs, s.finite_toSet, he.symm.trans
        (Submodule.localized'_eq_span _ _ _ _).symm⟩)
  refine ⟨Submodule.span B t, Submodule.fg_span htf, Submodule.span_le.mpr ht, ?_⟩
  change (Submodule.span B t).localized' (Localization T) T
    (LocalizedModule.mkLinearMap T M) = K.localized T
  simpa only [Submodule.localized'_span] using hts

private theorem exists_fg_localized_eq_finite {B M ι : Type*} [CommRing B]
    [AddCommGroup M] [Module B M] [Finite ι] (K : Submodule B M)
    (T : ι → Submonoid B) (h : ∀ i, (K.localized (T i)).FG) :
    ∃ L : Submodule B M, L.FG ∧ L ≤ K ∧ ∀ i, L.localized (T i) = K.localized (T i) := by
  classical
  choose L hL hLK hLe using fun i ↦ exists_fg_localized_eq K (T i) (h i)
  refine ⟨⨆ i, L i, Submodule.fg_iSup L hL, iSup_le hLK, fun i ↦ ?_⟩
  apply le_antisymm
  · exact (Submodule.localized'gi _ _ _).gc.monotone_l (iSup_le hLK)
  · rw [← hLe i]
    exact (Submodule.localized'gi _ _ _).gc.monotone_l (le_iSup L i)

private noncomputable def localized_quotient_equiv {B M : Type*} [CommRing B]
    [AddCommGroup M] [Module B M] (K L : Submodule B M) (T : Submonoid B)
    (h : L.localized T = K.localized T) :
    LocalizedModule T (M ⧸ L) ≃ₗ[Localization T] LocalizedModule T (M ⧸ K) :=
  (localizedQuotientEquiv T L).symm ≪≫ₗ
    Submodule.quotEquivOfEq _ _ h ≪≫ₗ localizedQuotientEquiv T K

private theorem flat_localized_of_flat {A B M : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]
    [Module.Flat A M] (T : Submonoid B) : Module.Flat A (LocalizedModule T M) := by
  rw [Module.flat_localizedModule_iff]
  intro J y hy
  exact ⟨1, T.one_mem, by
    simpa using (Module.Flat.lTensor_preserves_injective_linearMap
      (M := M) J.subtype J.subtype_injective) (hy.trans (map_zero _).symm)⟩

private theorem exists_flat_away {A B M : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]
    [Algebra.FinitePresentation A B] [Module.FinitePresentation B M]
    (q : PrimeSpectrum B) (hq : Module.Flat A (LocalizedModule q.asIdeal.primeCompl M)) :
    ∃ g : B, g ∉ q.asIdeal ∧ Module.Flat A (LocalizedModule.Away g M) := by
  obtain ⟨_, ⟨g, rfl⟩, hg, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.isOpen_iff.mp
      (Module.isOpen_setOf_flat_localizedModule (R := A) (M := M)) q hq
  refine ⟨g, hg, ?_⟩
  rw [Module.flat_localizedModule_iff]
  intro J y hy
  have hrad : g ∈ (Submodule.span B {y}).annihilator.radical := by
    rw [Ideal.radical_eq_sInf, Submodule.mem_sInf]
    rintro Q ⟨hQ, hprime⟩
    by_contra hgQ
    obtain ⟨t, ht, hty⟩ := (Module.flat_localizedModule_iff _).mp
      (hsub (show (⟨Q, hprime⟩ : PrimeSpectrum B) ∈ PrimeSpectrum.basicOpen g from hgQ))
      J y hy
    exact ht (hQ ((Submodule.mem_annihilator_span_singleton _ _).mpr hty))
  obtain ⟨n, hn⟩ := hrad
  exact ⟨g ^ n, ⟨n, rfl⟩, (Submodule.mem_annihilator_span_singleton _ _).mp hn⟩

private theorem flat_torsion_detection {A M ι : Type*} [CommRing A]
    [AddCommGroup M] [Module A M] [Module.Flat A M] [Finite ι]
    (a : ι → A)
    (hdense : ∀ r : A, (∀ i, ∃ n : ℕ, a i ^ n * r = 0) → r = 0)
    (m : M) (hm : ∀ i, ∃ n : ℕ, a i ^ n • m = 0) : m = 0 := by
  classical
  let := Fintype.ofFinite ι
  choose n hn using hm
  let d : A →ₗ[A] (ι → A) := LinearMap.pi fun i ↦ (a i ^ n i) • LinearMap.id
  have hd : Function.Injective d := by
    apply LinearMap.ker_eq_bot.mp
    apply le_antisymm _ bot_le
    intro r hr
    exact hdense r fun i ↦ ⟨n i, by simpa [d] using congrFun hr i⟩
  have hz : d.lTensor M (m ⊗ₜ[A] (1 : A)) = 0 := by
    apply (TensorProduct.piRight A A M (fun _ : ι ↦ A)).injective
    ext i
    simp only [LinearMap.lTensor_tmul, TensorProduct.piRight_apply,
      TensorProduct.piRightHom_tmul, map_zero, Pi.zero_apply]
    simp only [d, LinearMap.pi_apply, LinearMap.smul_apply, LinearMap.id_apply,
      smul_eq_mul, mul_one]
    apply (TensorProduct.rid A M).injective
    simpa using hn i
  have hzero := (Module.Flat.lTensor_preserves_injective_linearMap (M := M) d hd)
    (hz.trans (map_zero _).symm)
  simpa using congrArg (TensorProduct.rid A M) hzero

private theorem exists_smul_mem_of_localized_eq {B P : Type*} [CommRing B]
    [AddCommGroup P] [Module B P] (K L : Submodule B P) (T : Submonoid B)
    (he : L.localized T = K.localized T) {x : P} (hx : x ∈ K) :
    ∃ t : T, t • x ∈ L := by
  have hx' : LocalizedModule.mkLinearMap T P x ∈ L.localized T := by
    rw [he]
    exact ⟨x, hx, 1, by simp⟩
  obtain ⟨y, hy, t, ht⟩ := hx'
  have ht' : LocalizedModule.mkLinearMap T P (t • x) =
      LocalizedModule.mkLinearMap T P y := by
    simpa using congrArg (fun z ↦ t • z) ht.symm
  obtain ⟨s, hs⟩ := IsLocalizedModule.exists_of_eq (S := T) ht'
  change (s : B) • ((t : B) • x) = (s : B) • y at hs
  exact ⟨s * t, by
    change ((s : B) * (t : B)) • x ∈ L
    simpa only [mul_smul, hs] using L.smul_mem (s : B) hy⟩

private theorem localized_eq_of_flat_dense {A B P ι : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [AddCommGroup P] [Module A P] [Module B P] [IsScalarTower A B P]
    [Finite ι] (a : ι → A)
    (hdense : ∀ r : A, (∀ i, ∃ n : ℕ, a i ^ n * r = 0) → r = 0)
    (K L : Submodule B P) (hLK : L ≤ K)
    (he : ∀ i, L.localized (.powers (algebraMap A B (a i))) =
      K.localized (.powers (algebraMap A B (a i)))) (g : B)
    [Module.Flat A (LocalizedModule.Away g (P ⧸ L))] :
    L.localized (.powers g) = K.localized (.powers g) := by
  apply le_antisymm ((Submodule.localized'gi _ _ _).gc.monotone_l hLK)
  rw [Submodule.localized'_eq_span, Submodule.span_le]
  rintro _ ⟨x, hx, rfl⟩
  have hz : LocalizedModule.mkLinearMap (.powers g) (P ⧸ L) (L.mkQ x) = 0 := by
    apply flat_torsion_detection a hdense
    intro i
    obtain ⟨⟨_, n, rfl⟩, hn⟩ := exists_smul_mem_of_localized_eq K L _ (he i) hx
    refine ⟨n, ?_⟩
    have hn' : ((algebraMap A B (a i)) ^ n) • x ∈ L := hn
    have hq : (a i ^ n) • L.mkQ x = 0 := by
      rw [← LinearMap.map_smul_of_tower, ← algebraMap_smul B, map_pow]
      exact (Submodule.Quotient.mk_eq_zero L).mpr hn'
    simp only [← LinearMap.map_smul_of_tower, hq, map_zero]
  obtain ⟨t, ht⟩ := (IsLocalizedModule.eq_zero_iff (.powers g)
    (LocalizedModule.mkLinearMap (.powers g) (P ⧸ L))).mp hz
  have htL : t • x ∈ L := by
    have ht' : L.mkQ ((t : B) • x) = 0 := by
      rw [LinearMap.map_smul]
      exact ht
    exact (Submodule.Quotient.mk_eq_zero L).mp ht'
  exact ⟨t • x, htL, t, by simp⟩

private theorem fg_localized_of_quotient_fp {B P : Type*} [CommRing B]
    [AddCommGroup P] [Module B P] [Module.Finite B P]
    (K : Submodule B P) (T : Submonoid B)
    [Module.FinitePresentation (Localization T) (LocalizedModule T (P ⧸ K))] :
    (K.localized T).FG := by
  have : Module.FinitePresentation (Localization T)
      (LocalizedModule T P ⧸ K.localized T) :=
    Module.FinitePresentation.of_equiv (localizedQuotientEquiv T K).symm
  have h := Module.FinitePresentation.fg_ker (K.localized T).mkQ
    (Submodule.mkQ_surjective _)
  simpa only [Submodule.ker_mkQ] using h

/-- The affine finite-relation argument of Stacks Tag 081N. The injection into the base-open
localizations is expressed by its elementary power-torsion criterion. Choose finitely many
relations agreeing at the prime and at the finitely many base elements. The stalk criterion
05I7 and openness 00RC give a flat neighborhood of this finitely presented approximation.
Flatness and density kill its kernel there, so the original quotient is finitely presented
on a basic-open cover and therefore globally. -/
private theorem Module.finitePresentation_quotient_of_flat_dense
    {A B P ι : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup P] [Module A P] [Module B P] [IsScalarTower A B P]
    [Algebra.FinitePresentation A B] [Module.FinitePresentation B P] [Finite ι]
    (K : Submodule B P) [Module.Flat A (P ⧸ K)] (a : ι → A)
    (hdense : ∀ r : A, (∀ i, ∃ n : ℕ, a i ^ n * r = 0) → r = 0)
    (hfp : ∀ i, Module.FinitePresentation (Localization.Away (algebraMap A B (a i)))
      (LocalizedModule.Away (algebraMap A B (a i)) (P ⧸ K))) :
    Module.FinitePresentation B (P ⧸ K) := by
  classical
  let s : Set B := {g | Module.FinitePresentation (Localization.Away g)
    (LocalizedModule.Away g (P ⧸ K))}
  have hs : Ideal.span s = ⊤ := by
    by_contra hne
    obtain ⟨q, hq, hsq⟩ := Ideal.exists_le_maximal (Ideal.span s) hne
    have := hq.isPrime
    have hflatq := flat_localized_of_flat (A := A) (M := P ⧸ K) q.primeCompl
    have hflatq' : @Module.Flat A (LocalizedModule q.primeCompl (P ⧸ K)) _ _
        (Module.compHom _ (algebraMap A B)) := by
      convert hflatq using 1
      exact Module.ext' _ _ fun a m ↦ algebraMap_smul B a m
    have hfpq : Module.FinitePresentation (Localization.AtPrime q)
        (LocalizedModule q.primeCompl (P ⧸ K)) :=
      Module.finitePresentation_localizedModule_atPrime_of_flat (A := A) q hflatq'
    let T : Option ι → Submonoid B := fun i ↦ match i with
      | none => q.primeCompl
      | some i => .powers (algebraMap A B (a i))
    have hT (i : Option ι) : (K.localized (T i)).FG := by
      cases i with
      | none => exact fg_localized_of_quotient_fp K q.primeCompl
      | some i =>
        have := hfp i
        exact fg_localized_of_quotient_fp K (.powers (algebraMap A B (a i)))
    obtain ⟨L, hL, hLK, he⟩ := exists_fg_localized_eq_finite K T hT
    have : Module.FinitePresentation B (P ⧸ L) :=
      Module.finitePresentation_of_surjective L.mkQ (Submodule.mkQ_surjective L)
        (by simpa only [Submodule.ker_mkQ] using hL)
    have hflatLq : Module.Flat A (LocalizedModule q.primeCompl (P ⧸ L)) :=
      Module.Flat.of_linearEquiv ((localized_quotient_equiv K L _ (he none)).restrictScalars A)
    obtain ⟨g, hg, hflatg⟩ := exists_flat_away (⟨q, hq.isPrime⟩ : PrimeSpectrum B) hflatLq
    have heg : L.localized (.powers g) = K.localized (.powers g) :=
      localized_eq_of_flat_dense a hdense K L hLK (fun i ↦ he (some i)) g
    have hfpL : Module.FinitePresentation (Localization.Away g)
        (LocalizedModule.Away g (P ⧸ L)) := inferInstance
    have hgs : g ∈ s := Module.FinitePresentation.of_equiv (localized_quotient_equiv K L _ heg)
    exact hg (hsq (Ideal.subset_span hgs))
  exact Module.FinitePresentation.of_localizationSpan s hs fun g ↦ g.2

/-- Finite modules may be used in the affine density argument by choosing a finite free
surjection and taking its actual kernel. This is the finite-free presentation reduction in
Stacks Tag 081N. -/
private theorem Module.finitePresentation_of_flat_dense
    {A B N ι : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N]
    [Algebra.FinitePresentation A B] [Module.Finite B N] [Module.Flat A N] [Finite ι]
    (a : ι → A)
    (hdense : ∀ r : A, (∀ i, ∃ n : ℕ, a i ^ n * r = 0) → r = 0)
    (hfp : ∀ i, Module.FinitePresentation (Localization.Away (algebraMap A B (a i)))
      (LocalizedModule.Away (algebraMap A B (a i)) N)) :
    Module.FinitePresentation B N := by
  obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' B N
  let P := Fin n → B
  let e := p.quotKerEquivOfSurjective hp
  have : Module.Flat A (P ⧸ p.ker) :=
    Module.Flat.of_linearEquiv (e.restrictScalars A)
  have hfp' (i : ι) :
      Module.FinitePresentation (Localization.Away (algebraMap A B (a i)))
        (LocalizedModule.Away (algebraMap A B (a i)) (P ⧸ p.ker)) := by
    have := hfp i
    exact Module.FinitePresentation.of_equiv
      (IsLocalizedModule.mapEquiv (.powers (algebraMap A B (a i)))
        (LocalizedModule.mkLinearMap (.powers (algebraMap A B (a i))) (P ⧸ p.ker))
        (LocalizedModule.mkLinearMap (.powers (algebraMap A B (a i))) N)
        (Localization.Away (algebraMap A B (a i))) e).symm
  have := Module.finitePresentation_quotient_of_flat_dense p.ker a hdense hfp'
  exact Module.FinitePresentation.of_equiv e

private theorem affine_dense_power_cover {S : Scheme.{u}} (V : S.affineOpens)
    (U : S.Opens) (hretro : IsRetrocompact (U : Set S)) (hdense : SchematicallyDenseOpen U) :
    ∃ (t : Finset Γ(S, V)),
      (∀ a ∈ t, S.basicOpen a ≤ V.1 ⊓ U) ∧
      (∀ x ∈ V.1 ⊓ U, ∃ a ∈ t, x ∈ S.basicOpen a) ∧
      (∀ r : Γ(S, V), (∀ a ∈ t, ∃ n : ℕ, a ^ n * r = 0) → r = 0) := by
  classical
  let I := {a : Γ(S, V) // S.basicOpen a ≤ V.1 ⊓ U}
  have hc : IsCompact ((V.1 ⊓ U : S.Opens) : Set S) := by
    simpa only [Opens.coe_inf, Set.inter_comm] using hretro V.2.isCompact V.1.isOpen
  have hcov : ((V.1 ⊓ U : S.Opens) : Set S) ⊆ ⋃ a : I, (S.basicOpen a.1 : Set S) := by
    intro x hx
    obtain ⟨a, ha, hxa⟩ := V.2.exists_basicOpen_le (⟨x, hx⟩ : (V.1 ⊓ U : S.Opens)) hx.1
    exact Set.mem_iUnion.mpr ⟨⟨a, ha⟩, hxa⟩
  obtain ⟨t, ht⟩ := hc.elim_finite_subcover (fun a : I ↦ (S.basicOpen a.1 : Set S))
    (fun a ↦ (S.basicOpen a.1).isOpen) hcov
  refine ⟨t.image Subtype.val, ?_, ?_, ?_⟩
  · intro a ha
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp ha
    exact a.2
  · intro x hx
    obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.mp (ht hx)
    exact ⟨a.1, Finset.mem_image.mpr ⟨a, ha, rfl⟩, hxa⟩
  · intro r hr
    apply hdense V.1
    rw [map_zero]
    apply TopCat.Presheaf.IsSheaf.section_ext S.toRingedSpace.sheaf.2
    intro x hx
    obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.mp (ht hx)
    have ha' := a.2
    obtain ⟨n, hn⟩ := hr a.1 (Finset.mem_image.mpr ⟨a, ha, rfl⟩)
    have := V.2.isLocalization_basicOpen a.1
    have hz : S.presheaf.map (homOfLE (S.basicOpen_le a.1)).op r = 0 :=
      (IsLocalization.map_eq_zero_iff (.powers a.1) Γ(S, S.basicOpen a.1) r).mpr
        ⟨⟨a.1 ^ n, ⟨n, rfl⟩⟩, hn⟩
    refine ⟨S.basicOpen a.1, ha', hxa, ?_⟩
    rw [map_zero]
    change S.presheaf.map (homOfLE ha').op
      (S.presheaf.map (homOfLE inf_le_left).op r) = 0
    rw [← Functor.map_comp_apply]
    exact hz

set_option backward.isDefEq.respectTransparency false in
private theorem finitePresentation_sections_of_restrict {X : Scheme.{u}} (F : X.Modules)
    (W : X.Opens) [hW : (F.restrict W.ι).IsFinitePresentation]
    (D : X.affineOpens) (hDW : D.1 ≤ W) :
    Module.FinitePresentation Γ(X, D.1) Γ(F, D.1) := by
  open Scheme.Modules in
  let v := IsOpenImmersion.lift W.ι D.2.fromSpec (by
    rw [Scheme.Opens.range_ι]
    exact (show Set.range D.2.fromSpec ⊆ D.1 from D.2.opensRange_fromSpec.le).trans hDW)
  have hv : v ≫ W.ι = D.2.fromSpec := IsOpenImmersion.lift_fac _ _ _
  have : IsOpenImmersion (v ≫ W.ι) := by rw [hv]; infer_instance
  have : IsOpenImmersion v := IsOpenImmersion.of_comp v W.ι
  have hn : ((F.restrict W.ι).restrict v).IsFinitePresentation := inferInstance
  have hcomp : ((restrictFunctor W.ι ⋙ restrictFunctor v).obj F).IsFinitePresentation := hn
  have hfinal : (F.restrict D.2.fromSpec).IsFinitePresentation :=
    @Scheme.Modules.isFinitePresentation_of_iso _ _ _
      (((Scheme.Modules.restrictFunctorComp v W.ι).app F).symm ≪≫
        (Scheme.Modules.restrictFunctorCongr hv).app F) hcomp
  have hsections : Module.FinitePresentation Γ(X, D.1)
      (moduleSpecΓFunctor.obj (F.restrict D.2.fromSpec)) :=
    Scheme.Modules.finitePresentation_sections_top (F.restrict D.2.fromSpec)
  exact Module.FinitePresentation.of_equiv
    (Scheme.Modules.sectionsRestrictFromSpecLinearEquiv F D.2)

private theorem finitePresentation_localized_of_basicOpen {X : Scheme.{u}}
    (F : X.Modules) [F.IsQuasicoherent] (W : X.affineOpens) (b : Γ(X, W))
    (hfp : Module.FinitePresentation Γ(X, X.basicOpen b) Γ(F, X.basicOpen b)) :
    Module.FinitePresentation (Localization.Away b) (LocalizedModule.Away b Γ(F, W)) := by
  let : Module Γ(X, W) Γ(F, X.basicOpen b) :=
    Module.compHom _ (algebraMap Γ(X, W) Γ(X, X.basicOpen b))
  have : IsScalarTower Γ(X, W) Γ(X, X.basicOpen b) Γ(F, X.basicOpen b) :=
    ⟨fun a c m ↦ by
      change (algebraMap Γ(X, W) Γ(X, X.basicOpen b) a * c) • m =
        algebraMap Γ(X, W) Γ(X, X.basicOpen b) a • c • m
      exact mul_smul _ _ _⟩
  let r : Γ(F, W) →ₗ[Γ(X, W)] Γ(F, X.basicOpen b) :=
    { toFun := F.presheaf.map (homOfLE (X.basicOpen_le b)).op
      map_add' := map_add _
      map_smul' := Scheme.Modules.map_smul F _ }
  have := Scheme.Modules.isLocalizedModule_basicOpen F W.2 b
  have := W.2.isLocalization_basicOpen b
  let er := IsLocalization.algEquiv (.powers b) (Localization.Away b) Γ(X, X.basicOpen b)
  let : Module (Localization.Away b) Γ(F, X.basicOpen b) :=
    Module.compHom _ er.toRingEquiv.toRingHom
  have : IsScalarTower Γ(X, W) (Localization.Away b) Γ(F, X.basicOpen b) :=
    IsScalarTower.of_algebraMap_smul fun a m ↦ by
      change er (algebraMap Γ(X, W) (Localization.Away b) a) • m =
        algebraMap Γ(X, W) Γ(X, X.basicOpen b) a • m
      rw [er.commutes]
  have : Module.FinitePresentation (Localization.Away b) Γ(F, X.basicOpen b) :=
    Module.FinitePresentation.of_ringEquiv er.toRingEquiv (fun _ _ ↦ rfl)
  let e := (IsLocalizedModule.linearEquiv (.powers b) r
    (LocalizedModule.mkLinearMap (.powers b) Γ(F, W))).extendScalarsOfIsLocalization
      (.powers b) (Localization.Away b)
  exact Module.FinitePresentation.of_equiv e

namespace AlgebraicGeometry

/-- If a finite-type quasi-coherent module is flat over a locally finitely presented
morphism, finite presentation over a retrocompact schematically dense base open extends
to the whole source.

Source: Stacks Project, `flat.tex`, Tag 081N, lemma
`lemma-flat-finite-type-finitely-presented-over-dense-open`
(blueprint: lem-trf-flat-finite-type-dense-presentation).

The proof follows the affine argument of Tag 081N. Finite presentation is reduced to affine
charts; retrocompactness gives a finite principal cover of the base open and schematic density
gives injectivity into the product of the corresponding localizations. At a prime of the
affine source, the Tag 05I7 stalk lemma (\`lem-trf-flat-finite-type-flat-point-local\`)
provides finite presentation of the localized module. A finite-relation approximation agreeing
at that prime and on the base-open localizations is then flat on a neighborhood by the Tag 00RC
openness-of-flatness input (\`lem-weil-pbc-openness-of-flatness\`). The localization comparison
diagram and the density injection identify this approximation with the original module on that
neighborhood, giving a basic-open cover by finitely presented localizations; finite presentation
of the sheaf is local on the source. -/
theorem flat_finite_type_dense_presentation
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f]
    (F : X.Modules) (hF : Scheme.Modules.IsQuasiCoherentFiniteType F)
    (hflat : Scheme.Modules.IsFlatOver F f) (U : S.Opens)
    (hUretro : IsRetrocompact (U : Set S))
    (hUdense : SchematicallyDenseOpen U)
    (hUfp : (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).obj F |>.IsFinitePresentation) :
    F.IsFinitePresentation := by
  classical
  have : F.IsQuasicoherent := hF.1
  have : F.IsFiniteType := hF.2
  have hsections (V : S.affineOpens) (W : X.affineOpens) (e : W.1 ≤ f ⁻¹ᵁ V.1) :
      Module.FinitePresentation Γ(X, W.1) Γ(F, W.1) := by
    let := (f.appLE V.1 W.1 e).hom.toAlgebra
    let : Module Γ(S, V.1) Γ(F, W.1) :=
      Module.compHom _ (f.appLE V.1 W.1 e).hom
    have : IsScalarTower Γ(S, V.1) Γ(X, W.1) Γ(F, W.1) :=
      IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
    have : Algebra.FinitePresentation Γ(S, V.1) Γ(X, W.1) :=
      f.finitePresentation_appLE V.2 W.2 e
    have : Module.Finite Γ(X, W.1) Γ(F, W.1) := finite_sections_of_finiteType F W.2
    have : Module.Flat Γ(S, V.1) Γ(F, W.1) := hflat V W e
    obtain ⟨t, htle, htcover, htdense⟩ := affine_dense_power_cover V U hUretro hUdense
    apply Module.finitePresentation_of_flat_dense (fun a : t ↦ a.1)
      (fun r hr ↦ htdense r fun a ha ↦ hr ⟨a, ha⟩)
    intro a
    apply finitePresentation_localized_of_basicOpen F W
    have hbasic : X.basicOpen (f.appLE V.1 W.1 e a.1) ≤ f ⁻¹ᵁ U := by
      rw [Scheme.basicOpen_appLE]
      exact inf_le_right.trans (f.preimage_mono ((htle a.1 a.2).trans inf_le_right))
    exact @finitePresentation_sections_of_restrict X F (f ⁻¹ᵁ U) hUfp
      (X.affineBasicOpen (f.appLE V.1 W.1 e a.1)) hbasic
  let I := {p : S.affineOpens × X.affineOpens // p.2.1 ≤ f ⁻¹ᵁ p.1.1}
  have hfp (i : I) : Module.FinitePresentation Γ(X, i.1.2.1)
      Γ(F.restrict i.1.2.2.fromSpec, ⊤) := by
    have := hsections i.1.1 i.1.2 i.2
    exact Module.FinitePresentation.of_equiv
      (sectionsRestrictFromSpecLinearEquiv F i.1.2.2).symm
  have hpres (i : I) : ∃ P : (F.restrict i.1.2.2.fromSpec).Presentation, P.IsFinite := by
    have := hfp i
    exact exists_presentation_isFinite_of_finitePresentation _
  choose P hP using hpres
  apply isFinitePresentation_of_iSup_opensRange_eq_top F
    (fun i : I ↦ i.1.2.2.fromSpec) (P := P)
  apply eq_top_iff.mpr
  intro x hx
  obtain ⟨V, hV, hxV, _⟩ := exists_isAffineOpen_mem_and_subset
    (show f x ∈ (⊤ : S.Opens) from trivial)
  obtain ⟨W, hW, hxW, hWV⟩ := exists_isAffineOpen_mem_and_subset
    (show x ∈ f ⁻¹ᵁ V from hxV)
  apply Opens.mem_iSup.mpr
  refine ⟨⟨(⟨V, hV⟩, ⟨W, hW⟩), hWV⟩, ?_⟩
  simpa only [IsAffineOpen.opensRange_fromSpec] using hxW

end AlgebraicGeometry
