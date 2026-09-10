/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Coherence of `M^~` on an affine scheme, and quasi-coherence of a pushforward

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
- `AlgebraicGeometry.Scheme.Modules.nonempty_presentation_of_isAffine`: a quasi-coherent sheaf
  of modules on an affine scheme has a global presentation.
- `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_of_isAffineOpenCover`: quasi-coherence is
  local on the base, tested on a cover by affine opens.
- `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_pushforward`: quasi-coherence is stable
  under pushforward along an affine morphism, in particular along a closed immersion.
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

variable {X Y : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- A presentation of `M.restrict U.ι` gives a presentation of `M` over the open `U`. -/
def presentationOver (U : X.Opens) (M : X.Modules) (P : (M.restrict U.ι).Presentation) :
    (M.over U).Presentation :=
  have : PreservesColimitsOfSize.{u, u} ((overEquiv U).inverse) := inferInstance
  SheafOfModules.Presentation.ofIsIso (overEquivInverseRestrictIso U M).hom
    (P.map (overEquiv U).inverse (overEquivInverseUnitIso U))

set_option backward.isDefEq.respectTransparency false in
/-- A presentation of the restriction of `M` along an isomorphism of schemes gives a
presentation of `M`. -/
def presentationOfRestrictIsIso (f : X ⟶ Y) [IsIso f] (M : Y.Modules)
    (P : (M.restrict f).Presentation) : M.Presentation :=
  have : PreservesColimitsOfSize.{u, u} (restrictFunctor (inv f)) := inferInstance
  SheafOfModules.Presentation.ofIsIso (restrictFunctorCompInvIso.app M).hom
    (P.map (restrictFunctor (inv f)) (restrictUnitIso _).symm)

/-- **A quasi-coherent sheaf of modules on an affine scheme has a global presentation**: it is
the cokernel of a morphism between free sheaves of modules.

On `Spec R` this is the presentation of `Γ(M)^~` coming from a presentation of the `R`-module
`Γ(M)`; the general case follows by transporting it along `X ≅ Spec Γ(X, ⊤)`. -/
lemma nonempty_presentation_of_isAffine [IsAffine X] (M : X.Modules) [M.IsQuasicoherent] :
    Nonempty M.Presentation :=
  have : (M.restrict X.isoSpec.inv).IsQuasicoherent := inferInstance
  have : IsIso (M.restrict X.isoSpec.inv).fromTildeΓ := isIso_fromTildeΓ_of_isQuasicoherent _
  ⟨presentationOfRestrictIsIso X.isoSpec.inv M
    (SheafOfModules.Presentation.ofIsIso (M.restrict X.isoSpec.inv).fromTildeΓ
      (presentationTilde.{u} _ .univ (by simp) _ (Submodule.span_eq _)))⟩

/-- **Quasi-coherence is local on the base**: a sheaf of modules which is quasi-coherent after
restriction to each member of a cover of `X` by affine opens is quasi-coherent. -/
lemma isQuasicoherent_of_isAffineOpenCover (M : X.Modules) {ι : Type u} (U : ι → X.Opens)
    (hU : IsOpenCover U) (hU' : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, (M.restrict (U i).ι).IsQuasicoherent) : M.IsQuasicoherent := by
  refine SheafOfModules.QuasicoherentData.isQuasicoherent (M := M)
    { I := ι
      X := U
      coversTop := (Opens.coversTop_iff _ U).mpr hU
      presentation := fun i ↦ ?_ }
  have : IsAffine (U i).toScheme := hU' i
  exact presentationOver (U i) M (nonempty_presentation_of_isAffine _).some

/-- **Quasi-coherence is stable under pushforward along a morphism of affine spectra.** This is
`AlgebraicGeometry.isIso_fromTildeΓ_pushforward` combined with the characterisation of
quasi-coherence on an affine scheme. -/
instance isQuasicoherent_pushforward_specMap {S : CommRingCat.{u}} (φ : R ⟶ S)
    (M : (Spec S).Modules) [M.IsQuasicoherent] :
    ((pushforward (Spec.map φ)).obj M).IsQuasicoherent := by
  have : IsIso M.fromTildeΓ := isIso_fromTildeΓ_of_isQuasicoherent M
  rw [isQuasicoherent_iff_isIso_fromTildeΓ]
  exact isIso_fromTildeΓ_pushforward φ M

/-- Quasi-coherence may be checked after restricting along an isomorphism of schemes. -/
lemma isQuasicoherent_of_restrict_isIso (f : X ⟶ Y) [IsIso f] (M : Y.Modules)
    [(M.restrict f).IsQuasicoherent] : M.IsQuasicoherent := by
  refine (SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_of_iso
    ((restrictFunctorCompInvIso (f := f)).app M) ?_
  exact (inferInstance : ((M.restrict f).restrict (inv f)).IsQuasicoherent)

/-- **Quasi-coherence is stable under pushforward along an isomorphism.** -/
instance isQuasicoherent_pushforward_of_isIso (f : X ⟶ Y) [IsIso f] (M : X.Modules)
    [M.IsQuasicoherent] : ((pushforward f).obj M).IsQuasicoherent := by
  have h : (((pushforward f).obj M).restrict f).IsQuasicoherent := by
    refine (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      ((restrictFunctorAdjCounitIso f).app M).symm ?_
    exact (inferInstance : M.IsQuasicoherent)
  exact isQuasicoherent_of_restrict_isIso f _

/-- **Quasi-coherence is stable under pushforward along a morphism of affine schemes.** -/
lemma isQuasicoherent_pushforward_of_isAffine [IsAffine X] [IsAffine Y] (f : X ⟶ Y)
    (M : X.Modules) [M.IsQuasicoherent] : ((pushforward f).obj M).IsQuasicoherent := by
  have hf : X.isoSpec.hom ≫ Spec.map f.appTop ≫ Y.isoSpec.inv = f := by
    rw [Scheme.isoSpec_inv_naturality]
    simp
  have e : pushforward X.isoSpec.hom ⋙
      pushforward (Spec.map f.appTop) ⋙ pushforward Y.isoSpec.inv ≅ pushforward f :=
    Functor.isoWhiskerLeft _ (pushforwardComp _ _) ≪≫ pushforwardComp _ _ ≪≫
      pushforwardCongr hf
  refine (SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_of_iso (e.app M) ?_
  exact (inferInstance : ((pushforward Y.isoSpec.inv).obj ((pushforward (Spec.map f.appTop)).obj
    ((pushforward X.isoSpec.hom).obj M))).IsQuasicoherent)

/-- The restriction of `f _* M` to an affine open `U` of `Y` is quasi-coherent, if `f` is an
affine morphism and `M` is quasi-coherent. -/
lemma isQuasicoherent_restrict_pushforward (f : X ⟶ Y) [IsAffineHom f] (M : X.Modules)
    [M.IsQuasicoherent] {U : Y.Opens} (hU : IsAffineOpen U) :
    (((pushforward f).obj M).restrict U.ι).IsQuasicoherent := by
  have : IsAffine U.toScheme := hU
  have : IsAffine (f ⁻¹ᵁ U).toScheme := hU.preimage f
  have h : ((pushforward (f ∣_ U)).obj (M.restrict (f ⁻¹ᵁ U).ι)).IsQuasicoherent :=
    isQuasicoherent_pushforward_of_isAffine (f ∣_ U) (M.restrict (f ⁻¹ᵁ U).ι)
  exact (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).prop_of_iso
    ((pushforwardCompRestrictFunctorIso f U).app M).symm h

/-- **Quasi-coherence is stable under pushforward along an affine morphism**, in particular
along a closed immersion. -/
instance isQuasicoherent_pushforward (f : X ⟶ Y) [IsAffineHom f] (M : X.Modules)
    [M.IsQuasicoherent] : ((pushforward f).obj M).IsQuasicoherent :=
  isQuasicoherent_of_isAffineOpenCover _ (fun i ↦ (Y.affineOpenCover.f i).opensRange)
    Y.affineOpenCover.openCover.iSup_opensRange (fun _ ↦ isAffineOpen_opensRange _)
    fun _ ↦ isQuasicoherent_restrict_pushforward f M (isAffineOpen_opensRange _)

end Scheme.Modules

end AlgebraicGeometry
