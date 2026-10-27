/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Sheaf.Paper.NativeAdicEncodingCore
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.SixFunctors.ProEtale.Adic.Constructible
import Sheaf.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import Sheaf.Paper.CondensedQbarLfpLocalTriviality
import WeilConjectures.SixFunctors.ProEtale.Adic.ExtensionByZero

/-!
# Constructibility under the native adic encoding

Source: Bhatt--Scholze, Definitions 6.8.3 and 6.8.8.
(blueprint: lem-sf-native-adic-encoding-constructibility)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale
variable {l : ℕ} [Fact l.Prime]

open MonoidalCategory MonObj Opposite Functor.LaxMonoidal Functor.OplaxMonoidal in
private lemma encoding_free_of_iso {X : Scheme.{u}}
    {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R]
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R}
    (h : Mod.IsFree R M) (e : M ≅ N) : Mod.IsFree R N := by
  obtain ⟨n, ⟨i⟩⟩ := h
  exact ⟨n, ⟨e.symm ≪≫ i⟩⟩

open MonoidalCategory MonObj Opposite Functor.LaxMonoidal Functor.OplaxMonoidal in
private lemma encoding_free_map {X Y : Scheme.{u}}
    {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    {S : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}} [MonObj R] [MonObj S]
    (F : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R ⥤
      Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) S)
    [F.Additive] [PreservesFiniteColimits F]
    (e : F.obj (Mod.regular R) ≅ Mod.regular S)
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R}
    (h : Mod.IsFree R M) : Mod.IsFree S (F.obj M) := by
  obtain ⟨n, ⟨i⟩⟩ := h
  exact ⟨n, ⟨F.mapIso i ≪≫ F.mapBiproduct (fun _ : Fin n ↦ Mod.regular R) ≪≫
    biproduct.mapIso (fun _ ↦ e)⟩⟩

open MonoidalCategory MonObj Opposite Functor.LaxMonoidal Functor.OplaxMonoidal in
private lemma encoding_free_comap {X : Scheme.{u}}
    {R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (φ : R ⟶ S) [IsMonHom φ] [IsIso φ]
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) S}
    (h : Mod.IsFree S M) : Mod.IsFree R ((Mod.comap φ).obj M) := by
  apply encoding_free_map (Mod.comap φ) _ h
  simpa using Mod.regularIsoOfIsIso (inv φ)

open MonoidalCategory MonObj Opposite Functor.LaxMonoidal Functor.OplaxMonoidal in
private lemma encoding_free_of_comap {X : Scheme.{u}}
    {R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (φ : R ⟶ S) [IsMonHom φ] [IsIso φ]
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) S}
    (h : Mod.IsFree R ((Mod.comap φ).obj M)) : Mod.IsFree S M := by
  exact encoding_free_of_iso (encoding_free_comap (inv φ) h)
    ((Mod.comapEquivalenceOfIsIso φ).unitIso.app M).symm

open MonoidalCategory MonObj Opposite Functor.LaxMonoidal Functor.OplaxMonoidal in
private lemma encoding_fp_of_free {X : Scheme.{u}}
    {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R]
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R}
    (hM : Mod.IsFree R M) : Mod.IsFinitelyPresented R M := by
  obtain ⟨n, ⟨i⟩⟩ := hM
  exact ⟨n, n, 0, ⟨i ≪≫ cokernelZeroIsoTarget.symm⟩⟩

private noncomputable def encoding_regular (T : Scheme.{u}) :
    (NativeEncoding.encoding l T).obj (AdicSheaf.unit l T) ≅
      Mod.regular (condensedRingObj (Profinite.padicAlgClRingObj l) T) := by
  let e : (AdicSheaf.forgetAb l T).obj (AdicSheaf.unit l T) ≅
      Mod.regular ((weilCoefficientsForgetAb l T).obj (adicConstantSheaf l T)) :=
    Mod.isoMk (Iso.refl _) (by simp only [Iso.refl_hom, Category.comp_id,
      MonoidalCategory.whiskerLeft_id, Category.id_comp])
  refine (Mod.comap (NativeEncoding.coefficientIso l T).hom).mapIso e ≪≫ ?_
  simpa only [IsIso.inv_inv] using
    Mod.regularIsoOfIsIso (inv (NativeEncoding.coefficientIso l T).hom)

private noncomputable def encoding_free (T : Scheme.{u}) (r : ℕ) :
    (NativeEncoding.encoding l T).obj (Mod.finiteFree (adicConstantSheaf l T) r) ≅
      Mod.finiteFree (condensedRingObj (Profinite.padicAlgClRingObj l) T) r :=
  (NativeEncoding.encoding l T).mapBiproduct _ ≪≫
    biproduct.mapIso (fun _ ↦ encoding_regular T)

private theorem encoding_lisse_iff {T : Scheme.{u}}
    [TopologicalSpace.NoetherianSpace T] (M : AdicSheaf l T) :
    IsAdicLisseSheaf M ↔
      IsLocallyFinitelyPresented (condensedRingObj (Profinite.padicAlgClRingObj l) T)
        ((NativeEncoding.encoding l T).obj M) := by
  classical
  constructor
  · intro hM
    obtain ⟨R, hR, h⟩ := hM
    obtain ⟨ι, V, f, rfl⟩ := R.exists_eq_ofArrows
    let D : Scheme.Cover.{u + 1} Scheme.proetalePrecoverage T :=
      { I₀ := ι, X := V, f := f, mem₀ := hR }
    let : Precoverage.Small.{u} Scheme.proetalePrecoverage :=
      inferInstanceAs (Precoverage.Small.{u} (Scheme.propQCPrecoverage (@WeaklyEtale)))
    let C := D.restrictIndexOfSmall.{u}
    refine ⟨C, fun i ↦ ?_⟩
    let j := Precoverage.ZeroHypercover.Small.restrictFun.{u} D i
    obtain ⟨r, ⟨e⟩⟩ := h (f j) (.mk j)
    have hfree : Mod.IsFree _
        ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) (C.f i)).obj
          ((NativeEncoding.encoding l T).obj M)) :=
      ⟨r, ⟨((NativeEncoding.pullComparison l (C.f i)).app M).symm ≪≫
        (NativeEncoding.encoding l (C.X i)).mapIso e ≪≫ encoding_free (C.X i) r⟩⟩
    let φ := condensedPullbackHom (Profinite.padicAlgClRingObj l) (C.f i)
    have hraw : Mod.IsFree _ ((Mod.comap (inv φ)).obj
        (((upperStar Ab.{u + 1} (C.f i)).mapMod _).obj
          ((NativeEncoding.encoding l T).obj M))) :=
      encoding_free_of_iso hfree ((Mod.extendScalarsIsoComapInv φ).app _)
    exact encoding_fp_of_free (encoding_free_of_comap (inv φ) hraw)
  · intro hM
    obtain ⟨C, hC⟩ := condensedQbar_lfp_locally_free l T _ hM
    refine ⟨C.presieve₀, C.mem₀, ?_⟩
    rintro _ _ ⟨i⟩
    obtain ⟨r, ⟨e⟩⟩ := hC i
    exact ⟨r, ⟨(NativeEncoding.encoding l (C.X i)).preimageIso
      (((NativeEncoding.pullComparison l (C.f i)).app M) ≪≫ e ≪≫
        (encoding_free (C.X i) r).symm)⟩⟩

/-- The normalized native encoding preserves and detects constructibility on a Noetherian
scheme.

Source: Bhatt--Scholze, Definitions 6.8.3 and 6.8.8; the finite-presentation
characterization in `condensedQbar_lfp_locally_free`.
(blueprint: lem-sf-native-adic-encoding-constructibility)

Proof: encoding identifies the regular modules and their finite biproducts. Its pullback
comparison transports native local finite-free trivializations to the condensed side.
Conversely local finite presentation has a finite-free refinement, and full faithfulness
lifts each trivialization back. On a Noetherian scheme native constructibility has a
finite global lisse stratification. Apply the local equivalence on each stratum and
transport local finite presentations along the invertible coefficient pullback map.
Conversely the same strata of a condensed constructible object give native lisse
restrictions, hence native constructibility. Empty covers, empty strata and rank zero
are included in the biproduct and covering constructions. -/
theorem encoding_constructible_iff {T : Scheme.{u}} [IsNoetherian T]
    (M : AdicSheaf l T) :
    IsAdicConstructibleSheaf M ↔
      IsConstructibleModuleObject (condensedRingObj (Profinite.padicAlgClRingObj l) T)
        ((NativeEncoding.encoding l T).obj M) := by
  classical
  have hrestriction (Z : Scheme.{u}) (i : Z ⟶ T) [IsImmersion i] :
      IsAdicLisseSheaf ((adicUpperStar l i).obj M) ↔
        IsLocallyFinitelyPresented
          ((upperStar Ab.{u + 1} i).obj
            (condensedRingObj (Profinite.padicAlgClRingObj l) T))
          (((upperStar Ab.{u + 1} i).mapMod _).obj
            ((NativeEncoding.encoding l T).obj M)) := by
    have : TopologicalSpace.NoetherianSpace Z :=
      i.isEmbedding.noetherianSpace
    rw [encoding_lisse_iff]
    let φ := condensedPullbackHom (Profinite.padicAlgClRingObj l) i
    let N := (((upperStar Ab.{u + 1} i).mapMod _).obj
      ((NativeEncoding.encoding l T).obj M))
    have e : (NativeEncoding.encoding l Z).obj ((adicUpperStar l i).obj M) ≅
        (Mod.comap (inv φ)).obj N :=
      (NativeEncoding.pullComparison l i).app M ≪≫
        (Mod.extendScalarsIsoComapInv φ).app N
    exact ⟨fun h ↦ localFinitePresentation_of_comap (inv φ)
        (localFinitePresentation_of_iso e h),
      fun h ↦ localFinitePresentation_of_iso e.symm
        (localFinitePresentation_comap (inv φ) h)⟩
  constructor
  · intro hM
    obtain ⟨ι, hι, Z, i, hi, hc, hcover, h⟩ := hM.isAdicStratifiedLisseSheaf
    let := hι
    let := Fintype.ofFinite ι
    let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
    let S : Scheme.Stratification T :=
      { n := Fintype.card ι
        stratum := fun r ↦ Set.range (i (e r))
        isLocallyClosed_stratum := fun r ↦ by
          have := hi (e r)
          exact (i (e r)).isLocallyClosed_range
        isConstructible_stratum := fun r ↦ hc (e r)
        iUnion_stratum_eq_univ := by
          apply Set.eq_univ_of_forall
          intro x
          obtain ⟨k, hk, -⟩ := hcover x
          refine Set.mem_iUnion.mpr ⟨e.symm k, ?_⟩
          dsimp only
          rw [e.apply_symm_apply]
          exact hk
        pairwise_disjoint_stratum := by
          intro r s hrs
          apply Set.disjoint_left.mpr
          intro x hxr hxs
          obtain ⟨k, -, hk⟩ := hcover x
          exact hrs (e.injective ((hk _ hxr).trans (hk _ hxs).symm))
        domain := fun r ↦ Z (e r)
        immersion := fun r ↦ i (e r)
        isImmersion := fun r ↦ hi (e r)
        range_immersion := fun _ ↦ rfl }
    exact ⟨S, fun r ↦ (hrestriction _ _).mp (h (e r))⟩
  · rintro ⟨S, hS⟩
    apply IsAdicStratifiedLisseSheaf.isAdicConstructibleSheaf
    refine ⟨Fin S.n, inferInstance, S.domain, S.immersion, S.isImmersion,
      fun i ↦ S.range_immersion i ▸ S.isConstructible_stratum i, ?_,
      fun i ↦ (hrestriction _ _).mpr (hS i)⟩
    intro x
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (S.iUnion_stratum_eq_univ.symm ▸ Set.mem_univ x)
    refine ⟨i, ?_, fun j hj ↦ ?_⟩
    · change x ∈ Set.range (S.immersion i)
      rwa [S.range_immersion i]
    · change x ∈ Set.range (S.immersion j) at hj
      by_contra hji
      exact Set.disjoint_left.mp (S.pairwise_disjoint_stratum hji) (by
        rwa [S.range_immersion j] at hj) hi

end AlgebraicGeometry.ProEtale
