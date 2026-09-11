/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.RingTheory.Localization.Finiteness
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Coherence of `M^~` on an affine scheme, and stability of coherence under pullback

For a commutative ring `R` and an `R`-module `M`, the quasi-coherent sheaf `M^~` on `Spec R` is
coherent as soon as `M` is a finite `R`-module, and conversely a finite family of global sections
generating `M^~` generates `M`.

## Main results

- `AlgebraicGeometry.tilde.epi_map_iff`: `M ↦ M^~` preserves and reflects epimorphisms.
- `AlgebraicGeometry.generatingSectionsTilde`: a generating family of `M` gives a family of
  global sections generating `M^~`.
- `AlgebraicGeometry.tilde.finite_of_generatingSections`: conversely, a finite family of global
  sections generating `M^~` exhibits `M` as a finite `R`-module.
- `AlgebraicGeometry.Scheme.Modules.isCoherent_of_finite`: a quasi-coherent sheaf of modules on
  `Spec R` whose module of global sections is finite is coherent.
- `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_pullback`,
  `AlgebraicGeometry.Scheme.Modules.isFiniteType_pullback` and
  `AlgebraicGeometry.Scheme.Modules.isCoherent_pullback`: quasi-coherence, finite type and
  hence coherence of sheaves of modules are stable under pullback along an arbitrary morphism
  of schemes. No Noetherian hypothesis is needed.
- `AlgebraicGeometry.tilde.finite_of_isFiniteType`: if `M^~` is of finite type, then `M` is a
  finite `R`-module. No Noetherian hypothesis is needed.
- `AlgebraicGeometry.tilde.isCoherent_iff` and `AlgebraicGeometry.Scheme.Modules.isCoherent_iff`:
  the resulting characterisation of coherence on an affine scheme.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory Limits SheafOfModules TopologicalSpace

namespace AlgebraicGeometry

variable {R : CommRingCat.{u}} {M N : ModuleCat.{u} R}

/-- `M ↦ M^~` preserves epimorphisms (it is a left adjoint) and reflects them (it is
faithful). -/
theorem tilde.epi_map_iff (f : M ⟶ N) : Epi (tilde.map f) ↔ Epi f := by
  constructor
  · intro _
    refine (tilde.functor R).epi_of_epi_map ?_
    change Epi (tilde.map f)
    infer_instance
  · intro _
    change Epi ((tilde.functor R).map f)
    infer_instance

/-- A family of generators of an `R`-module `M` gives a family of global sections
generating `M^~`. -/
@[simps I]
def generatingSectionsTilde (s : Set M) (hs : Submodule.span R s = ⊤) :
    (tilde M).GeneratingSections where
  I := s
  s := (tilde M).freeHomEquiv ((tildeFinsupp (R := R) s).inv ≫
    tilde.map (ModuleCat.ofHom (Finsupp.linearCombination R ((↑) : s → M))))
  epi := by
    rw [Equiv.symm_apply_apply]
    have hsurj : Function.Surjective (Finsupp.linearCombination R ((↑) : s → M)) := by
      rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination, Subtype.range_coe]
      exact hs
    have hepi : Epi (ModuleCat.ofHom (Finsupp.linearCombination R ((↑) : s → M))) := by
      rw [ModuleCat.epi_iff_surjective]
      exact hsurj
    have : Epi (tilde.map (ModuleCat.ofHom (Finsupp.linearCombination R ((↑) : s → M)))) :=
      (tilde.epi_map_iff _).mpr hepi
    infer_instance

instance (s : Set M) (hs : Submodule.span R s = ⊤) [Finite s] :
    (generatingSectionsTilde s hs).IsFiniteType where
  finite := inferInstanceAs (Finite s)

/-- **A finite family of global sections generating `M^~` generates `M`.** -/
theorem tilde.finite_of_generatingSections (G : (tilde M).GeneratingSections)
    [G.IsFiniteType] : Module.Finite R M := by
  have hG : Epi G.π := G.epi
  have hepi : Epi ((tildeFinsupp (R := R) G.I).hom ≫ G.π) := epi_comp _ _
  have hpre : Epi (tilde.map ((tilde.functor R).preimage
      ((tildeFinsupp (R := R) G.I).hom ≫ G.π))) := by
    change Epi ((tilde.functor R).map ((tilde.functor R).preimage _))
    rw [Functor.map_preimage]
    exact hepi
  have hsurj := (tilde.epi_map_iff _).mp hpre
  rw [ModuleCat.epi_iff_surjective] at hsurj
  exact Module.Finite.of_surjective _ hsurj

instance [Module.Finite R M] : (tilde M).IsFiniteType := by
  obtain ⟨s, hs⟩ := (Module.Finite.fg_top : (⊤ : Submodule R M).FG)
  have hs' : Submodule.span R (↑s : Set M) = ⊤ := hs
  have : Finite (↑s : Set M) := s.finite_toSet
  exact (generatingSectionsTilde (↑s : Set M) hs').isFiniteType

instance [Module.Finite R M] : (tilde M).IsCoherent where

/-- **A quasi-coherent sheaf of modules on an affine scheme with finite module of global
sections is coherent.** -/
theorem Scheme.Modules.isCoherent_of_finite (M : (Spec R).Modules) [M.IsQuasicoherent]
    [Module.Finite R (moduleSpecΓFunctor.obj M)] : M.IsCoherent := by
  have : IsIso M.fromTildeΓ := (isQuasicoherent_iff_isIso_fromTildeΓ M).mp inferInstance
  -- the source of `M.fromTildeΓ` is definitionally, but not syntactically, `moduleSpecΓFunctor`
  have : Module.Finite R ((modulesSpecToSheaf.obj M).presheaf.obj (.op ⊤)) := ‹_›
  exact ObjectProperty.prop_of_iso (isCoherent (Spec R).ringCatSheaf) (asIso M.fromTildeΓ)
    inferInstance

namespace Scheme.Modules

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)

set_option backward.isDefEq.respectTransparency false in
/-- A presentation of `M` over an open `U` of `Y` pulls back to a presentation of the pullback
of `M` over `f ⁻¹ᵁ U`. -/
def presentationPullbackOver {M : Y.Modules} (p : (M.over U).Presentation) :
    (((pullback f).obj M).over (f ⁻¹ᵁ U)).Presentation :=
  SheafOfModules.Presentation.ofIsIso (pullbackOverObjIso f U M).hom
    (p.map (pullbackOver f U) (pullbackOverUnitIso f U))

set_option backward.isDefEq.respectTransparency false in
/-- Sections generating `M` over an open `U` of `Y` pull back to sections generating the
pullback of `M` over `f ⁻¹ᵁ U`. -/
def generatingSectionsPullbackOver {M : Y.Modules} (G : (M.over U).GeneratingSections) :
    (((pullback f).obj M).over (f ⁻¹ᵁ U)).GeneratingSections :=
  (G.map (pullbackOver f U) (pullbackOverUnitIso f U)).ofEpi (pullbackOverObjIso f U M).hom

set_option backward.isDefEq.respectTransparency false in
instance {M : Y.Modules} (G : (M.over U).GeneratingSections) [G.IsFiniteType] :
    (generatingSectionsPullbackOver f U G).IsFiniteType := by
  unfold generatingSectionsPullbackOver
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- Quasi-coherent data for `M` pulls back to quasi-coherent data for the pullback of `M`,
on the preimage of the given covering. -/
def quasicoherentDataPullback {M : Y.Modules} (q : M.QuasicoherentData.{u}) :
    ((pullback f).obj M).QuasicoherentData.{u} where
  I := q.I
  X i := f ⁻¹ᵁ q.X i
  coversTop := Opens.coversTop_map f.base q.coversTop
  presentation i := presentationPullbackOver f _ (q.presentation i)

set_option backward.isDefEq.respectTransparency false in
/-- Local generators for `M` pull back to local generators for the pullback of `M`,
on the preimage of the given covering. -/
def localGeneratorsDataPullback {M : Y.Modules} (q : M.LocalGeneratorsData.{u}) :
    ((pullback f).obj M).LocalGeneratorsData.{u} where
  I := q.I
  X i := f ⁻¹ᵁ q.X i
  coversTop := Opens.coversTop_map f.base q.coversTop
  generators i := generatingSectionsPullbackOver f _ (q.generators i)

instance {M : Y.Modules} (q : M.LocalGeneratorsData.{u}) [q.IsFiniteType] :
    (localGeneratorsDataPullback f q).IsFiniteType where
  isFiniteType i := by
    have := ‹q.IsFiniteType›.isFiniteType i
    exact inferInstanceAs
      ((generatingSectionsPullbackOver f _ (q.generators i)).IsFiniteType)

/-- **Quasi-coherence is stable under pullback.** -/
instance isQuasicoherent_pullback (M : Y.Modules) [M.IsQuasicoherent] :
    ((pullback f).obj M).IsQuasicoherent :=
  (quasicoherentDataPullback f
    SheafOfModules.IsQuasicoherent.nonempty_quasicoherentData.some).isQuasicoherent

/-- **Being of finite type is stable under pullback.** -/
instance isFiniteType_pullback (M : Y.Modules) [M.IsFiniteType] :
    ((pullback f).obj M).IsFiniteType where
  exists_localGeneratorsData := by
    obtain ⟨q, hq⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData M
    exact ⟨localGeneratorsDataPullback f q, inferInstance⟩

/-- **Coherence is stable under pullback**, with no hypothesis on the schemes involved. -/
instance isCoherent_pullback (M : Y.Modules) [M.IsCoherent] :
    ((pullback f).obj M).IsCoherent where

end Scheme.Modules
variable {X : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- If `M.over W` is generated by a family of sections, then so is `M.restrict V.ι` for any
open `V ≤ W`. -/
lemma exists_generatingSections_restrict_of_over (M : X.Modules) {V W : X.Opens} (hVW : V ≤ W)
    (G : (M.over W).GeneratingSections) [G.IsFiniteType] :
    ∃ G' : (M.restrict V.ι).GeneratingSections, G'.IsFiniteType := by
  have : PreservesColimitsOfSize.{u, u} (restrictFunctor (X.homOfLE hVW)) := inferInstance
  let F := (overEquiv W).functor ⋙ restrictFunctor (X.homOfLE hVW)
  let iso : SheafOfModules.overFunctor X.ringCatSheaf W ⋙ F ≅ restrictFunctor V.ι :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (overFunctorEquiv W) _ ≪≫
      (restrictFunctorComp _ _).symm ≪≫ restrictFunctorCongr (by simp)
  exact ⟨(G.map F (restrictUnitIso _).symm).ofEpi (iso.app M).hom, inferInstance⟩

set_option backward.isDefEq.respectTransparency false in
/-- A family of generating sections of `M` restricts to a family of generating sections of
`M.restrict f`, for `f` an open immersion. -/
lemma exists_generatingSections_restrict {Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    (M : X.Modules) (G : M.GeneratingSections) [G.IsFiniteType] :
    ∃ G' : (M.restrict f).GeneratingSections, G'.IsFiniteType := by
  have : PreservesColimitsOfSize.{u, u} (restrictFunctor f) := inferInstance
  exact ⟨G.map (restrictFunctor.{u} f) (restrictUnitIso _).symm, inferInstance⟩

open TopologicalSpace in
set_option backward.isDefEq.respectTransparency false in
/-- **A sheaf of modules of finite type on `Spec R` is generated by finitely many sections over
each member of a finite family of basic opens covering `Spec R`.** -/
lemma exists_span_eq_top_generatingSections_restrict (M : (Spec R).Modules) [M.IsFiniteType] :
    ∃ (ι : Type u) (_ : Finite ι) (g : ι → R), Ideal.span (Set.range g) = ⊤ ∧
      ∀ i, ∃ G : (M.restrict (Spec.map (CommRingCat.ofHom
        (algebraMap R (Localization.Away (g i)))))).GeneratingSections, G.IsFiniteType := by
  obtain ⟨q, hq⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData (M := M)
  have hcov : IsOpenCover q.X := (Opens.coversTop_iff _ q.X).mp q.coversTop
  obtain ⟨s, hs⟩ := (_root_.PrimeSpectrum.isBasis_basic_opens (R := R)).isOpenCover_mem_and_le
    hcov |>.exists_finite_of_compactSpace
  choose g hg using fun j : s ↦ j.1.2.1
  refine ⟨s, inferInstance, g, ?_, fun j ↦ ?_⟩
  · rw [← _root_.PrimeSpectrum.iSup_basicOpen_eq_top_iff]
    simpa only [hg] using hs.iSup_eq_top
  · have hle : (_root_.PrimeSpectrum.basicOpen (g j) : (Spec R).Opens) ≤ q.X j.1.1.2 :=
      hg j ▸ j.1.2.2
    have := hq.isFiniteType j.1.1.2
    obtain ⟨G₁, hG₁⟩ := exists_generatingSections_restrict_of_over M hle (q.generators j.1.1.2)
    obtain ⟨G₂, hG₂⟩ := exists_generatingSections_restrict (basicOpenIsoSpecAway (g j)).inv _ G₁
    have he : (basicOpenIsoSpecAway (g j)).inv ≫ Scheme.Opens.ι (X := Spec R)
          (_root_.PrimeSpectrum.basicOpen (g j)) =
        Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (g j)))) := by
      simp [basicOpenIsoSpecAway]
    exact ⟨G₂.ofEpi (((restrictFunctorComp _ _).symm ≪≫ restrictFunctorCongr he).app M).hom,
      inferInstance⟩

set_option backward.isDefEq.respectTransparency false in
/-- If a quasi-coherent sheaf of modules on `Spec R` is generated by finitely many sections after
restriction along `ψ : Spec S ⟶ Spec R`, its sections over `Spec S` form a finite `S`-module. -/
lemma finite_of_generatingSections_restrict {S : CommRingCat.{u}} (ψ : Spec S ⟶ Spec R)
    [IsOpenImmersion ψ] (M : (Spec R).Modules) [M.IsQuasicoherent]
    (G : (M.restrict ψ).GeneratingSections) [G.IsFiniteType] :
    Module.Finite S Γ(M.restrict ψ, ⊤) := by
  have : IsIso (fromTildeΓ (R := S) (M.restrict ψ)) := inferInstance
  exact tilde.finite_of_generatingSections
    (G.ofEpi (CategoryTheory.inv (fromTildeΓ (R := S) (M.restrict ψ))))

/-- Sections over the image of an open immersion `ψ : Spec S ⟶ Spec R` are finite over
`Γ(Spec R, _)` as soon as they are finite over `S`. -/
lemma finite_sections_of_finite_restrict {S : CommRingCat.{u}} (ψ : Spec S ⟶ Spec R)
    [IsOpenImmersion ψ] (M : (Spec R).Modules) [Module.Finite S Γ(M.restrict ψ, ⊤)] :
    Module.Finite Γ(Spec R, ψ ''ᵁ ⊤) Γ(M, ψ ''ᵁ ⊤) := by
  let σ : S ⟶ Γ(Spec R, ψ ''ᵁ ⊤) := (Scheme.ΓSpecIso S).inv ≫ (ψ.appIso ⊤).inv
  have hσ : Function.Bijective σ.hom := ConcreteCategory.bijective_of_isIso σ
  have : RingHomSurjective σ.hom := ⟨hσ.surjective⟩
  refine (LinearMap.finite_iff_of_bijective
    ({ toFun := id, map_add' := fun _ _ ↦ rfl, map_smul' := ?_ } :
      Γ(M.restrict ψ, ⊤) →ₛₗ[σ.hom] Γ(M, ψ ''ᵁ ⊤))
    ⟨fun _ _ h ↦ h, fun y ↦ ⟨y, rfl⟩⟩).mp inferInstance
  intro a x
  change _ = σ.hom a • _
  rw [smul_Spec_def, Subsingleton.elim (⊤ : (Spec S).Opens).leTop (𝟙 _)]
  rfl

end Scheme.Modules

open _root_.PrimeSpectrum in
set_option backward.isDefEq.respectTransparency false in
/-- **A sheaf of modules of finite type on an affine scheme has finitely generated global
sections.** -/
theorem tilde.finite_of_isFiniteType (N : ModuleCat.{u} R) [(tilde N).IsFiniteType] :
    Module.Finite R N := by
  obtain ⟨ι, _, g, hspan, hG⟩ :=
    Scheme.Modules.exists_span_eq_top_generatingSections_restrict (tilde N)
  refine Module.Finite.of_localizationSpan' (Set.range g) hspan
    (Rₚ := fun x ↦ Γ(Spec R, basicOpen x.1)) (Mₚ := fun x ↦ Γ(tilde N, basicOpen x.1))
    (fun x ↦ (tilde.toOpen N (basicOpen x.1)).hom)
    (h₂ := fun x ↦ inferInstanceAs (IsLocalizedModule.Away x.1
      (tilde.toOpen N (basicOpen x.1)).hom)) (fun x ↦ ?_)
  obtain ⟨i, hi⟩ := x.2
  obtain ⟨G, hGft⟩ := hG i
  have him : Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (g i)))) ''ᵁ ⊤ =
      basicOpen (g i) := by simp
  have hloc := Scheme.Modules.finite_of_generatingSections_restrict _ (tilde N) G
  have h := Scheme.Modules.finite_sections_of_finite_restrict
    (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (g i))))) (tilde N)
  rw [him] at h
  rw [← hi]
  exact h

/-- **On an affine scheme, `M^~` is coherent if and only if `M` is a finite module.** -/
theorem tilde.isCoherent_iff (N : ModuleCat.{u} R) :
    (tilde N).IsCoherent ↔ Module.Finite R N :=
  ⟨fun _ ↦ tilde.finite_of_isFiniteType N, fun _ ↦ inferInstance⟩

set_option backward.isDefEq.respectTransparency false in
/-- **A quasi-coherent sheaf of modules on an affine scheme is coherent if and only if its module
of global sections is finite.** -/
theorem Scheme.Modules.isCoherent_iff (M : (Spec R).Modules) [M.IsQuasicoherent] :
    M.IsCoherent ↔ Module.Finite R (moduleSpecΓFunctor.obj M) := by
  refine ⟨fun _ ↦ ?_, fun _ ↦ isCoherent_of_finite M⟩
  have : IsIso M.fromTildeΓ := (isQuasicoherent_iff_isIso_fromTildeΓ M).mp inferInstance
  have : (tilde (moduleSpecΓFunctor.obj M)).IsFiniteType :=
    SheafOfModules.isFiniteType_of_iso.{u, u, u} (asIso M.fromTildeΓ).symm
  exact tilde.finite_of_isFiniteType _

end AlgebraicGeometry
