/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Sheaf.Paper.CondensedConstantConstructibility
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import WeilConjectures.CategoryTheory.ModuleObjects.Monoidal
import Sheaf.Paper.ProfinitePointPullback

/-! # Comparison with finite constant models for locally free coefficients

Source: Bhatt--Scholze, Section 6.8, and the finite local presentation of a free module.
(blueprint: new-lem-sfb-lfp-free-constant-comparison)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory MonObj
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

private theorem fp_map
    {C D : Type*} [Category C] [Abelian C] [MonoidalCategory C]
    [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
    [Category D] [Abelian D] [MonoidalCategory D] [MonoidalPreadditive D]
    [SymmetricCategory D] [MonoidalClosed D]
    (R : C) [MonObj R] (S : D) [MonObj S]
    (F : Mod C R ⥤ Mod D S) [F.Additive] [PreservesFiniteColimits F]
    (e : F.obj (Mod.regular R) ≅ Mod.regular S)
    {M : Mod C R} (h : Mod.IsFinitelyPresented R M) :
    Mod.IsFinitelyPresented S (F.obj M) := by
  obtain ⟨n, m, f, ⟨i⟩⟩ := h
  let en (n : ℕ) : F.obj (Mod.finiteFree R n) ≅ Mod.finiteFree S n :=
    F.mapBiproduct (fun _ : Fin n ↦ Mod.regular R) ≪≫ biproduct.mapIso (fun _ ↦ e)
  let f' := (en m).inv ≫ F.map f ≫ (en n).hom
  exact ⟨n, m, f', ⟨F.mapIso i ≪≫ PreservesCokernel.iso F f ≪≫
    cokernel.mapIso (F.map f) f' (en m) (en n) (by simp [f'])⟩⟩

private theorem fp_iso
    {X : Scheme.{u}} {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R]
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R}
    (e : M ≅ N) (h : Mod.IsFinitelyPresented R M) : Mod.IsFinitelyPresented R N := by
  obtain ⟨n, m, f, ⟨i⟩⟩ := h
  exact ⟨n, m, f, ⟨e.symm ≪≫ i⟩⟩

private theorem fp_comap {X : Scheme.{u}}
    {R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (φ : R ⟶ S) [IsMonHom φ] [IsIso φ]
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) S}
    (h : Mod.IsFinitelyPresented S M) :
    Mod.IsFinitelyPresented R ((Mod.comap φ).obj M) := by
  exact fp_map S R (Mod.comap φ)
    (by simpa using Mod.regularIsoOfIsIso (inv φ)) h

private theorem lfp_comap {X : Scheme.{u}}
    {R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (φ : R ⟶ S) [IsMonHom φ] [IsIso φ]
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) S}
    (h : IsLocallyFinitelyPresented S M) :
    IsLocallyFinitelyPresented R ((Mod.comap φ).obj M) := by
  obtain ⟨U, hU⟩ := h
  refine ⟨U, fun i ↦ ?_⟩
  exact fp_iso (((upperStar Ab.{u + 1} (U.f i)).mapModComapIso φ).app M).symm
    (fp_comap ((upperStar Ab.{u + 1} (U.f i)).map φ) (hU i))

private theorem lfp_of_iso {X : Scheme.{u}}
    {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R]
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R}
    (e : M ≅ N) (h : IsLocallyFinitelyPresented R M) :
    IsLocallyFinitelyPresented R N := by
  obtain ⟨U, hU⟩ := h
  exact ⟨U, fun i ↦ fp_iso (((upperStar Ab.{u + 1} (U.f i)).mapMod R).mapIso e)
    (hU i)⟩

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

private instance point_colimits (X : Scheme.{u}) :
    PreservesFiniteColimits (upperStarFromPoint X) := by
  have : PreservesColimitsOfSize.{0, 0} pointUpperStar.{u} :=
    pointUpperStarLowerStarAdjunction.leftAdjoint_preservesColimits
  unfold upperStarFromPoint
  infer_instance

attribute [local instance] preservesBinaryBiproducts_of_preservesBinaryCoproducts

private instance point_additive (X : Scheme.{u}) : (upperStarFromPoint X).Additive := by
  exact Functor.additive_of_preservesBinaryBiproducts _

private noncomputable def pointFreeIso (X : Scheme.{u}) (n : ℕ) :
    ((upperStarFromPoint X).mapMod Λ).obj (Mod.finiteFree Λ n) ≅
      Mod.finiteFree (condensedRingObj Λ X) n :=
  ((upperStarFromPoint X).mapMod Λ).mapBiproduct (fun _ : Fin n ↦ Mod.regular Λ) ≪≫
    biproduct.mapIso (fun _ ↦ Mod.isoMk (Iso.refl _) (by simp [Mod.act]))

omit [IsCommMonObj Λ] in
private theorem fp_free (n : ℕ) : Mod.IsFinitelyPresented Λ (Mod.finiteFree Λ n) :=
  ⟨n, n, 0, ⟨cokernelZeroIsoTarget.symm⟩⟩

private theorem lfp_of_constantModel {X : Scheme.{u}}
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (h : HasFiniteConstantLocalModel Λ X M) :
    IsLocallyFinitelyPresented (condensedRingObj Λ X) M := by
  obtain ⟨U, hU⟩ := h
  refine ⟨U, fun i ↦ ?_⟩
  obtain ⟨P, hP, ⟨e⟩⟩ := hU i
  let φ := condensedPullbackHom Λ (U.f i)
  have hP' := fp_map Λ (condensedRingObj Λ (U.X i))
    ((upperStarFromPoint (U.X i)).mapMod Λ)
    (Mod.isoMk (Iso.refl _) (by simp [Mod.act])) hP
  have he := ((Mod.extendScalarsIsoComapInv φ).app
    (((upperStar Ab.{u + 1} (U.f i)).mapMod _).obj M))
  have hp := fp_comap φ (fp_iso e.symm hP')
  let e' := ((Mod.comap φ).mapIso he) ≪≫
    ((Mod.comapEquivalenceOfIsIso φ).counitIso.app
      (((upperStar Ab.{u + 1} (U.f i)).mapMod _).obj M))
  exact fp_iso e' hp


private theorem free_comap {X : Scheme.{u}}
    {R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (φ : R ⟶ S) [IsMonHom φ] [IsIso φ]
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) S}
    (h : Mod.IsFree S M) : Mod.IsFree R ((Mod.comap φ).obj M) := by
  obtain ⟨n, ⟨e⟩⟩ := h
  exact ⟨n, ⟨(Mod.comap φ).mapIso e ≪≫
    (Mod.comap φ).mapBiproduct (fun _ : Fin n ↦ Mod.regular S) ≪≫
      biproduct.mapIso (fun _ ↦ by simpa using Mod.regularIsoOfIsIso (inv φ))⟩⟩

private theorem constantLocalModel_of_locally_free {X : Scheme.{u}}
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (h : ∃ U : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i,
      Mod.IsFree ((upperStar Ab.{u + 1} (U.f i)).obj (condensedRingObj Λ X))
        (((upperStar Ab.{u + 1} (U.f i)).mapMod (condensedRingObj Λ X)).obj M)) :
    HasFiniteConstantLocalModel Λ X M := by
  obtain ⟨U, hU⟩ := h
  refine ⟨U, fun i ↦ ?_⟩
  let φ := condensedPullbackHom Λ (U.f i)
  obtain ⟨n, ⟨e⟩⟩ := free_comap (inv φ) (hU i)
  refine ⟨Mod.finiteFree Λ n, fp_free Λ n, ⟨?_⟩⟩
  exact ((Mod.extendScalarsIsoComapInv φ).app _ ≪≫ e) ≪≫ (pointFreeIso Λ (U.X i) n).symm

private theorem constantLocalModel_of_iso {X : Scheme.{u}}
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (e : M ≅ N) (h : HasFiniteConstantLocalModel Λ X M) :
    HasFiniteConstantLocalModel Λ X N := by
  obtain ⟨U, hU⟩ := h
  refine ⟨U, fun i ↦ ?_⟩
  obtain ⟨P, hP, ⟨eP⟩⟩ := hU i
  exact ⟨P, hP, ⟨((CondensedRing.upperStar Λ (U.f i)).mapIso e).symm ≪≫ eP⟩⟩

/-- If every locally finitely presented module is locally finite free, the source
constructibility predicate equals finite constant-model constructibility on Noetherian
qcqs schemes.

Source: Bhatt--Scholze, Section 6.8, finite local presentations and finite stratifications.
(blueprint: new-lem-sfb-lfp-free-constant-comparison)

Proof: on each constructibility stratum, use the stated local freeness and pullback of
the finite free module over the point to obtain a constant model. Conversely a finite
presentation over the point pulls back to a finite presentation on the cover. The
canonical coefficient isomorphisms identify raw inverse image of modules with the
coefficient-normalized pullback. Both constructions keep the original finite
stratification, and apply also to zero ranks and empty strata. -/
theorem constructible_eq_constantModels_of_lfp_locally_free
    (hLF : ∀ (Y : Scheme.{u}) [TopologicalSpace.NoetherianSpace Y]
      (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)),
      IsLocallyFinitelyPresented (condensedRingObj Λ Y) M →
      ∃ U : Scheme.Cover.{u} Scheme.proetalePrecoverage Y, ∀ i,
        Mod.IsFree ((upperStar Ab.{u + 1} (U.f i)).obj (condensedRingObj Λ Y))
          (((upperStar Ab.{u + 1} (U.f i)).mapMod (condensedRingObj Λ Y)).obj M))
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    [CompactSpace X] [QuasiSeparatedSpace X] :
    IsConstructibleModuleObject (condensedRingObj Λ X) =
      IsConstantModelConstructible Λ X := by
  funext M
  apply propext
  rw [IsConstantModelConstructible, if_pos ⟨inferInstance, inferInstance⟩]
  constructor
  · rintro ⟨S, hS⟩
    refine ⟨S, fun a ↦ ?_⟩
    have : TopologicalSpace.NoetherianSpace (S.domain a) :=
      (S.immersion a).isEmbedding.isInducing.noetherianSpace
    let φ := condensedPullbackHom Λ (S.immersion a)
    let N := (Mod.comap (inv φ)).obj
      (((upperStar Ab.{u + 1} (S.immersion a)).mapMod _).obj M)
    have hN : IsLocallyFinitelyPresented (condensedRingObj Λ (S.domain a)) N :=
      lfp_comap (inv φ) (hS a)
    exact constantLocalModel_of_iso Λ ((Mod.extendScalarsIsoComapInv φ).app _).symm
      (constantLocalModel_of_locally_free Λ N (hLF _ N hN))
  · rintro ⟨S, hS⟩
    refine ⟨S, fun a ↦ ?_⟩
    let φ := condensedPullbackHom Λ (S.immersion a)
    have h := lfp_comap φ (lfp_of_constantModel Λ _ (hS a))
    let e := ((Mod.comap φ).mapIso ((Mod.extendScalarsIsoComapInv φ).app
      (((upperStar Ab.{u + 1} (S.immersion a)).mapMod _).obj M))) ≪≫
      (Mod.comapEquivalenceOfIsIso φ).counitIso.app _
    exact lfp_of_iso e h


end AlgebraicGeometry.ProEtale
