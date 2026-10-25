/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.DeformationSpace.BaseChange
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import WeilConjectures.Mathlib.AlgebraicGeometry.PullbackCarrier
public import WeilConjectures.TraceFormula.OpenCover
public import WeilConjectures.TraceFormula.Specialization.DefectExchanges

/-!

# The vanishing of the defect of the specialization is local

Let `X` be a separated `k`-scheme of finite type, `Z = V(I) ⊆ X` a closed subscheme and
`g_a : V_a ⟶ X` finitely many open immersions covering `X`. This file shows that the defect
`C_{X,Z}(L)` of `ProEtale.CondensedRing.specializationDefect` vanishes as soon as every
`C_{V_a, g_a^* Z}(g_a^* L)` does
(`ProEtale.CondensedRing.isZero_specializationDefect_of_cover`): this is the reduction "the
assertion is local" in the proof of blueprint `det-sp-zero-section-vanishing`.

By the smooth exchange for the defect
(`ProEtale.CondensedRing.nonempty_specializationDefect_upperStar_iso`) the pullbacks of `C_{X,Z}(L)`
along the maps `N_⊥ (Z ∩ V_a) ⟶ N_⊥ Z` of special fibres of the constant families vanish, and we
conclude by the detection of zero objects along finite quasi-compact jointly surjective families.
For this we show the geometric facts:

* along an open immersion `h : X' ⟶ X`, the deformation space of `h^* I` is the base change
  `X' ×_X D_I X` (`Scheme.IdealSheafData.isPullback_deformationSpaceMap_of_isOpenImmersion`), and
  so are the total spaces and the special fibres over the trait
  (`ProEtale.CondensedRing.isPullback_deformationSpecialFibreMap_toBase`); in particular the map of
  special fibres is an open immersion
  (`ProEtale.CondensedRing.isOpenImmersion_deformationSpecialFibreMap_of_isOpenImmersion`);
* the restriction `Z ∩ V_a ⟶ Z` of `g_a` to the centre is the base change of `g_a`
  (`ProEtale.CondensedRing.isPullback_centreMap`).

-/

@[expose] public section

universe u

open CategoryTheory Limits ZeroObject

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- Along an open immersion `h : X' ⟶ X`, the deformation space of `J = h^* I` is the base change
`X' ×_X D_I X` of the deformation space of `I`. -/
lemma isPullback_deformationSpaceMap_of_isOpenImmersion {X X' : Scheme.{u}} (h : X' ⟶ X)
    [IsOpenImmersion h] (I : X.IdealSheafData) (J : X'.IdealSheafData)
    (hJ : ∀ ⦃U' : X'.AffineZariskiSite⦄ ⦃U : X.AffineZariskiSite⦄ (hU : U'.1 ≤ h ⁻¹ᵁ U.1),
      (I.siteIdeal U).map (h.appLE U.1 U'.1 hU).hom ≤ J.siteIdeal U')
    (hJI : J = I.comap h) :
    IsPullback (deformationSpaceMap h I J hJ) J.deformationSpaceProj I.deformationSpaceProj h := by
  refine (extendedReesPullbackData h I J hJ).isPullback_comparison _ _ fun x ↦ ?_
  obtain ⟨U, hU, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp X'.isBasis_affineOpens
    (show x ∈ (⊤ : X'.Opens) from trivial)
  exact ⟨⟨U, hU⟩, _, _, hx, isPushout_extendedReesPullbackData_imageSite _ _ _ _ hJI _⟩

end AlgebraicGeometry.Scheme.IdealSheafData

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-! ### Base change of the total space and of the special fibre -/

section Map

variable {k : Type u} [Field k] {X Y : Over (Spec (.of k))} (f : X ⟶ Y)
  {I : Y.left.IdealSheafData} {J : X.left.IdealSheafData}
  (hJ : ∀ ⦃U' : X.left.AffineZariskiSite⦄ ⦃U : Y.left.AffineZariskiSite⦄
    (hU : U'.1 ≤ f.left ⁻¹ᵁ U.1), (I.siteIdeal U).map (f.left.appLE U.1 U'.1 hU).hom ≤
      J.siteIdeal U')
  (k' : Type u) [Field k'] [Algebra k k']

/-- The total space `𝒳` of the deformation of `J` is the base change of the total space `𝒴` of
the deformation of `I` along the morphism of deformation spaces `D_J X ⟶ D_I Y`. -/
lemma isPullback_deformationTotalMap :
    IsPullback (deformationTotalMap f hJ k') (deformationTotalToSpace X J k')
      (deformationTotalToSpace Y I k') (IdealSheafData.deformationSpaceMap f.left I J hJ) :=
  IsPullback.of_right (by
      rw [deformationTotalMap_toTrait, deformationSpaceMap_deformationSpaceToAffineLine]
      exact (isPullback_deformationTotal X J k').flip)
    (deformationTotalMap_toSpace f hJ k') (isPullback_deformationTotal Y I k').flip

/-- The special fibre `𝒳_s` of the deformation of `J` is the base change of the special fibre
`𝒴_s` of the deformation of `I` along the morphism of total spaces `𝒳 ⟶ 𝒴`. -/
lemma isPullback_deformationSpecialFibreMap :
    IsPullback (deformationSpecialFibreMap f hJ k').left (deformationSpecialToTotal X J k')
      (deformationSpecialToTotal Y I k') (deformationTotalMap f hJ k') :=
  IsPullback.of_right (by
      rw [Over.w (deformationSpecialFibreMap f hJ k'), deformationTotalMap_toTrait]
      exact (isPullback_deformationSpecialFibre X J k').flip)
    (deformationSpecialFibreMap_toTotal f hJ k') (isPullback_deformationSpecialFibre Y I k').flip

/-- Along an open immersion `f : X ⟶ Y` and for `J = f^* I`, the special fibre `𝒳_s` of the
deformation of `J` is the base change `X ×_Y 𝒴_s` of the special fibre of the deformation of
`I`. -/
lemma isPullback_deformationSpecialFibreMap_toBase [IsOpenImmersion f.left]
    (hJI : J = I.comap f.left) :
    IsPullback (deformationSpecialFibreMap f hJ k').left
      (deformationSpecialToTotal X J k' ≫ deformationTotalToBase X J k')
      (deformationSpecialToTotal Y I k' ≫ deformationTotalToBase Y I k') f.left :=
  (isPullback_deformationSpecialFibreMap f hJ k').paste_vert
    ((isPullback_deformationTotalMap f hJ k').paste_vert
      (IdealSheafData.isPullback_deformationSpaceMap_of_isOpenImmersion f.left I J hJ hJI))

/-- Along an open immersion `f : X ⟶ Y` and for `J = f^* I`, the map of special fibres
`𝒳_s ⟶ 𝒴_s` is an open immersion. -/
lemma isOpenImmersion_deformationSpecialFibreMap_of_isOpenImmersion [IsOpenImmersion f.left]
    (hJI : J = I.comap f.left) : IsOpenImmersion (deformationSpecialFibreMap f hJ k').left :=
  (isPullback_deformationSpecialFibreMap_toBase f hJ k' hJI).isOpenImmersion_fst

/-- Along an open immersion `f : X ⟶ Y` and for `J = f^* I`, the image of the map of special
fibres `𝒳_s ⟶ 𝒴_s` is the inverse image of the image of `f` under `𝒴_s ⟶ Y`. -/
lemma range_deformationSpecialFibreMap_of_isOpenImmersion [IsOpenImmersion f.left]
    (hJI : J = I.comap f.left) :
    Set.range (deformationSpecialFibreMap f hJ k').left =
      (deformationSpecialToTotal Y I k' ≫ deformationTotalToBase Y I k') ⁻¹'
        Set.range f.left :=
  Scheme.range_snd_of_isPullback (isPullback_deformationSpecialFibreMap_toBase f hJ k' hJI).flip

end Map

/-! ### The restriction to the centre -/

section Centre

variable {k : Type u} [Field k] {X X' : Over (Spec (.of k))} (f : X' ⟶ X)
  (I : X.left.IdealSheafData) (k' : Type u) [Field k'] [Algebra k k']

/-- The restriction `f_Z : Z' = V(f^* I) ⟶ Z = V(I)` of `f` is the base change of `f` along the
closed immersion `Z ⟶ X`. -/
lemma isPullback_centreMap :
    IsPullback (centreMap f I).left (I.comap f.left).subschemeι I.subschemeι f.left := by
  have := (I.isPullback_comap f.left).flip
  rwa [IdealSheafData.comapIso_hom_snd] at this

instance [IsOpenImmersion f.left] : IsOpenImmersion (centreMap f I).left :=
  (isPullback_centreMap f I).isOpenImmersion_fst

/-- The image of the restriction `f_Z : V(f^* I) ⟶ V(I)` is the inverse image of the image
of `f`. -/
lemma range_centreMap :
    Set.range (centreMap f I).left = I.subschemeι ⁻¹' Set.range f.left :=
  Scheme.range_snd_of_isPullback (isPullback_centreMap f I).flip

instance [IsOpenImmersion f.left] : IsOpenImmersion (centreSpecialFibreMap f I k').left :=
  isOpenImmersion_deformationSpecialFibreMap_of_isOpenImmersion _ _ k'
    (IdealSheafData.comap_bot _).symm

instance [QuasiCompact X'.hom] [IsSeparated X.hom] :
    QuasiCompact (centreSpecialFibreMap f I k').left := by
  have : QuasiCompact ((centreSpecialFibreMap f I k').left ≫
      (deformationSpecialFibre (centre X I) ⊥ k').hom) := by
    rw [Over.w (centreSpecialFibreMap f I k')]
    infer_instance
  exact QuasiCompact.of_comp _ (deformationSpecialFibre (centre X I) ⊥ k').hom

/-- For an open immersion `f`, the image of the map `N_⊥ Z' ⟶ N_⊥ Z` of special fibres of the
constant families is the inverse image of the image of `f` under `N_⊥ Z ⟶ Z ⟶ X`. -/
lemma range_centreSpecialFibreMap [IsOpenImmersion f.left] :
    Set.range (centreSpecialFibreMap f I k').left =
      (deformationSpecialToTotal (centre X I) ⊥ k' ≫
        deformationTotalToBase (centre X I) ⊥ k' ≫ I.subschemeι) ⁻¹' Set.range f.left := by
  rw [centreSpecialFibreMap, range_deformationSpecialFibreMap_of_isOpenImmersion _ _ k'
    (IdealSheafData.comap_bot _).symm, range_centreMap]
  rfl

/-- The maps `N_⊥ (V(g_a^* I)) ⟶ N_⊥ V(I)` of special fibres of the constant families, for
open immersions `g_a` covering `X`, are jointly surjective. -/
lemma exists_mem_range_centreSpecialFibreMap {ι : Type*} {V : ι → Over (Spec (.of k))}
    (g : ∀ a, V a ⟶ X) [∀ a, IsOpenImmersion (g a).left]
    (hg : ⋃ a, Set.range (g a).left.base = Set.univ)
    (p : (deformationSpecialFibre (centre X I) ⊥ k').left) :
    ∃ a, p ∈ Set.range (centreSpecialFibreMap (g a) I k').left.base := by
  obtain ⟨a, ha⟩ := Set.mem_iUnion.mp (hg.symm ▸ Set.mem_univ
    ((deformationSpecialToTotal (centre X I) ⊥ k' ≫
      deformationTotalToBase (centre X I) ⊥ k' ≫ I.subschemeι) p))
  refine ⟨a, ?_⟩
  have := range_centreSpecialFibreMap (g a) I k'
  exact this.symm ▸ ha

end Centre

/-! ### Locality of the vanishing of the defect -/

variable {k : Type u} [Field k] {X : Over (Spec (.of k))} (I : X.left.IdealSheafData)
  (k' : Type u) [Field k'] [Algebra k k']
  {ℓ : ℕ} [Fact ℓ.Prime] [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

/-- **The vanishing of the defect is local** (the reduction "the assertion is local" in the proof
of blueprint `det-sp-zero-section-vanishing`): for finitely many open immersions `g_a : V_a ⟶ X`
covering `X`, if every defect `C_{V_a, g_a^* Z}(g_a^* L)` vanishes, then so does `C_{X,Z}(L)`. -/
theorem isZero_specializationDefect_of_cover {ι : Type*} [Finite ι] {V : ι → Over (Spec (.of k))}
    [∀ a, LocallyOfFiniteType (V a).hom] [∀ a, QuasiCompact (V a).hom]
    [∀ a, IsSeparated (V a).hom] (g : ∀ a, V a ⟶ X) [∀ a, IsOpenImmersion (g a).left]
    (hg : ⋃ a, Set.range (g a).left.base = Set.univ)
    (L : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (h : ∀ a, IsZero (specializationDefect (V a) (I.comap (g a).left) k'
      (Profinite.padicAlgClRingObj ℓ)
      ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (g a)).obj L).obj)) :
    IsZero (specializationDefect X I k' (Profinite.padicAlgClRingObj ℓ) L.obj) := by
  have hP := jointlyReflectIsomorphisms_leftDerivedUpperStar_of_cover
    (Profinite.padicAlgClRingObj ℓ) (fun a ↦ (centreSpecialFibreMap (g a) I k').left)
    (exists_mem_range_centreSpecialFibreMap I k' g hg)
  have (a : ι) : IsIso ((L(((centreSpecialFibreMap (g a) I k').left)^*⟦
      Profinite.padicAlgClRingObj ℓ⟧)).map
      (0 : specializationDefect X I k' (Profinite.padicAlgClRingObj ℓ) L.obj ⟶ 0)) := by
    obtain ⟨e⟩ := nonempty_specializationDefect_upperStar_iso (g a) I k' L
    exact ((h a).of_iso e.symm).isIso (Functor.map_isZero _ (isZero_zero _)) _
  exact ((isIsoZero_iff_source_target_isZero _ _).1 (hP.isIso
    (0 : specializationDefect X I k' (Profinite.padicAlgClRingObj ℓ) L.obj ⟶ 0))).1

end AlgebraicGeometry.ProEtale.CondensedRing
