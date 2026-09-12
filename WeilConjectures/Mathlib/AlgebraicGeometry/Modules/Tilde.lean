/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Module.LocalizedModule.Away
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Localization.Finiteness
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Coherence of `M^~` on an affine scheme, and affine-locality of coherence
# Coherence of `M^~` on an affine scheme, and quasi-coherence of a pushforward
# Coherence of `M^~` on an affine scheme, and stability of coherence under pullback

For a commutative ring `R` and an `R`-module `M`, the quasi-coherent sheaf `M^~` on `Spec R` is
coherent as soon as `M` is a finite `R`-module, and conversely a finite family of global sections
generating `M^~` generates `M`.

The second half of the file establishes that the sections of a quasi-coherent sheaf over a
basic open subset of an affine open are the corresponding localization, and deduces that its
stalk at a point of an affine open is the localization of the sections at the prime of that
point. This is what makes affine-local definitions in terms of the module of sections well
posed.
This file also proves that `M ↦ M^~` is exact, deduces that kernels and cokernels of morphisms
of quasi-coherent sheaves of modules on an affine scheme are quasi-coherent, and transfers all
of this to an arbitrary scheme: a sheaf of modules is coherent exactly when, on some cover by
affine opens, it is quasi-coherent with finitely generated module of sections.

## Main results

- `AlgebraicGeometry.tilde.epi_map_iff`: `M ↦ M^~` preserves and reflects epimorphisms.
- `AlgebraicGeometry.generatingSectionsTilde`: a generating family of `M` gives a family of
  global sections generating `M^~`.
- `AlgebraicGeometry.tilde.finite_of_generatingSections`: conversely, a finite family of global
  sections generating `M^~` exhibits `M` as a finite `R`-module.
- `AlgebraicGeometry.Scheme.Modules.isCoherent_of_finite`: a quasi-coherent sheaf of modules on
  `Spec R` whose module of global sections is finite is coherent.
- `AlgebraicGeometry.Scheme.Modules.exists_pow_smul_eq_res` and
  `AlgebraicGeometry.Scheme.Modules.exists_pow_smul_eq_zero`: the sections of a quasi-coherent
  sheaf over a basic open of an affine open are a localization of the sections over that open.
- `AlgebraicGeometry.Scheme.Modules.isLocalizedModule_germₗ`: the stalk of a quasi-coherent
  sheaf at a point of an affine open is the localization of the sections at the corresponding
  prime.
- `instance : PreservesFiniteLimits (AlgebraicGeometry.tilde.functor R)`: `M ↦ M^~` is exact.
- `AlgebraicGeometry.Scheme.Modules.kernelIsoTilde` and
  `AlgebraicGeometry.Scheme.Modules.cokernelIsoTilde`: on an affine scheme, kernels and
  cokernels of morphisms of quasi-coherent sheaves of modules are the sheaves associated to the
  kernel and the cokernel of the induced morphism of modules of global sections.
- `AlgebraicGeometry.Scheme.Modules.isCoherent_of_isOpenCover` and
  `AlgebraicGeometry.Scheme.Modules.exists_isOpenCover_finite`: coherence is affine-local.
- `AlgebraicGeometry.Scheme.Modules.nonempty_presentation_of_isAffine`: a quasi-coherent sheaf
  of modules on an affine scheme has a global presentation.
- `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_of_isAffineOpenCover`: quasi-coherence is
  local on the base, tested on a cover by affine opens.
- `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_pushforward`: quasi-coherence is stable
  under pushforward along an affine morphism, in particular along a closed immersion.
- `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_pullback`,
  `AlgebraicGeometry.Scheme.Modules.isFiniteType_pullback` and
  `AlgebraicGeometry.Scheme.Modules.isCoherent_pullback`: quasi-coherence, finite type and
  hence coherence of sheaves of modules are stable under pullback along an arbitrary morphism
  of schemes. No Noetherian hypothesis is needed.
- `AlgebraicGeometry.tilde.finite_of_isFiniteType`: if `M^~` is of finite type, then `M` is a
  finite `R`-module. No Noetherian hypothesis is needed.
- `AlgebraicGeometry.tilde.isCoherent_iff` and `AlgebraicGeometry.Scheme.Modules.isCoherent_iff`:
  the resulting characterisation of coherence on an affine scheme.
- `AlgebraicGeometry.Scheme.Modules.isFiniteType_restrictFunctor`: being of finite type is
  stable under restriction to an open subscheme.
- `AlgebraicGeometry.Scheme.Modules.isFiniteType_pushforward` and
  `AlgebraicGeometry.Scheme.Modules.isCoherent_pushforward_of_isClosedImmersion`: finite type
  and coherence of sheaves of modules are stable under pushforward along a closed immersion.
  No Noetherian hypothesis is needed.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory Limits Opposite SheafOfModules
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

section Localization

variable {X : Scheme.{u}} {U : X.Opens}

namespace Scheme.Modules

/-- The restriction map between sections of a sheaf of modules on `Spec R`, as an `R`-linear
map. -/
def resSpecₗ (G : (Spec R).Modules) {V W : (Spec R).Opens} (h : W ≤ V) :
    Γ(G, V) →ₗ[R] Γ(G, W) where
  toFun := G.presheaf.map (homOfLE h).op
  map_add' := map_add _
  map_smul' r x := map_smul_Spec _ r x

@[simp]
lemma resSpecₗ_apply (G : (Spec R).Modules) {V W : (Spec R).Opens} (h : W ≤ V) (x : Γ(G, V)) :
    resSpecₗ G h x = G.presheaf.map (homOfLE h).op x :=
  rfl

/-- **Sections of a quasi-coherent sheaf over a basic open subset of an affine scheme are a
localization** of the global sections. -/
theorem isLocalizedModule_resSpecₗ (G : (Spec R).Modules) [G.IsQuasicoherent] (g : R) :
    IsLocalizedModule.Away g
      (resSpecₗ G (le_top (a := (PrimeSpectrum.basicOpen g : (Spec R).Opens)))) := by
  have hiso : IsIso G.fromTildeΓ := inferInstance
  have h := Scheme.Modules.toOpen_fromTildeΓ_app G (PrimeSpectrum.basicOpen g)
  set N := (modulesSpecToSheaf.obj G).presheaf.obj (.op ⊤)
  have hφ : IsIso ((modulesSpecToSheaf.map G.fromTildeΓ).hom.app
      (.op (PrimeSpectrum.basicOpen g : (Spec R).Opens))) := inferInstance
  have key : resSpecₗ G (le_top (a := (PrimeSpectrum.basicOpen g : (Spec R).Opens))) =
      (asIso ((modulesSpecToSheaf.map G.fromTildeΓ).hom.app
        (.op (PrimeSpectrum.basicOpen g : (Spec R).Opens)))).toLinearEquiv.toLinearMap ∘ₗ
        (tilde.toOpen N (PrimeSpectrum.basicOpen g)).hom := by
    ext x
    exact (congr($h x)).symm
  have : IsLocalizedModule.Away g (tilde.toOpen N (PrimeSpectrum.basicOpen g)).hom :=
    inferInstance
  rw [key]
  exact IsLocalizedModule.of_linearEquiv _ _ _

variable (F : X.Modules)

/-- Restriction of scalars along `Γ(X, U) ≅ Γ(Spec Γ(X, U), ⊤) ⟶ Γ(Spec Γ(X, U), V)` agrees with
restriction of sections along `hU.fromSpec ''ᵁ V ≤ U`. -/
lemma ΓSpecIso_inv_map_appIso_inv (hU : IsAffineOpen U) (V : (Spec Γ(X, U)).Opens)
    (h : hU.fromSpec ''ᵁ V ≤ U) :
    (Scheme.ΓSpecIso Γ(X, U)).inv ≫ (Spec Γ(X, U)).presheaf.map V.leTop.op ≫
      (hU.fromSpec.appIso V).inv = X.presheaf.map (homOfLE h).op := by
  have h1 : (Scheme.ΓSpecIso Γ(X, U)).inv ≫ (Spec Γ(X, U)).presheaf.map V.leTop.op =
      hU.fromSpec.appLE U V (by simp) := by
    simp only [Scheme.Hom.appLE, hU.fromSpec_app_self, Category.assoc, ← Functor.map_comp,
      ← op_comp]
    congr 1
  rw [← Category.assoc, h1, Scheme.Hom.appLE_appIso_inv]

/-- The `Γ(X, U)`-action on the sections of the restriction of `F` to `Spec Γ(X, U)` is the
action of `Γ(X, U)` on sections of `F` by restriction. -/
lemma smul_restrict_fromSpec (hU : IsAffineOpen U) (V : (Spec Γ(X, U)).Opens)
    (h : hU.fromSpec ''ᵁ V ≤ U) (r : Γ(X, U)) (x : Γ(F.restrict hU.fromSpec, V)) :
    r • x = (X.presheaf.map (homOfLE h).op r) • (show Γ(F, hU.fromSpec ''ᵁ V) from x) := by
  have : r • x = ((hU.fromSpec.appIso V).inv
      ((Spec Γ(X, U)).presheaf.map V.leTop.op ((Scheme.ΓSpecIso Γ(X, U)).inv r)))
      • (show Γ(F, hU.fromSpec ''ᵁ V) from x) := rfl
  rw [this]
  congr 1
  exact ConcreteCategory.congr_hom (ΓSpecIso_inv_map_appIso_inv hU V h) r

variable {F}

/-- **Sections of a quasi-coherent sheaf over a basic open of an affine open are a
localization**: every section over `X.basicOpen g` becomes, after multiplication by a power of
`g`, the restriction of a section over `U`. -/
theorem exists_pow_smul_eq_res (hU : IsAffineOpen U) [F.IsQuasicoherent] (g : Γ(X, U))
    (s : Γ(F, X.basicOpen g)) :
    ∃ (n : ℕ) (t : Γ(F, U)), (X.presheaf.map (homOfLE (X.basicOpen_le g)).op g) ^ n • s =
      F.presheaf.map (homOfLE (X.basicOpen_le g)).op t := by
  have e₁ : U = hU.fromSpec ''ᵁ ⊤ := by
    rw [Scheme.Hom.image_top_eq_opensRange, hU.opensRange_fromSpec]
  have e₂ : hU.fromSpec ''ᵁ (PrimeSpectrum.basicOpen g) = X.basicOpen g :=
    hU.fromSpec_image_basicOpen g
  suffices H : ∀ (W : X.Opens) (_ : W = X.basicOpen g) (h : W ≤ U) (s : Γ(F, W)),
      ∃ (n : ℕ) (t : Γ(F, U)), (X.presheaf.map (homOfLE h).op g) ^ n • s =
        F.presheaf.map (homOfLE h).op t from H _ rfl _ s
  intro W hW h s
  obtain rfl : W = hU.fromSpec ''ᵁ (PrimeSpectrum.basicOpen g) := hW.trans e₂.symm
  have H := isLocalizedModule_resSpecₗ (F.restrict hU.fromSpec) g
  obtain ⟨⟨t', ⟨_, n, rfl⟩⟩, ht⟩ :=
    IsLocalizedModule.surj (Submonoid.powers g)
      ((F.restrict hU.fromSpec).resSpecₗ (le_top (a := (PrimeSpectrum.basicOpen g :
        (Spec Γ(X, U)).Opens)))) s
  refine ⟨n, F.presheaf.map (eqToHom e₁).op t', ?_⟩
  simp only [Submonoid.smul_def] at ht
  rw [← map_pow, ← smul_restrict_fromSpec F hU _ h (g ^ n) s, ht]
  change (F.restrict hU.fromSpec).presheaf.map (homOfLE le_top).op t' = _
  rw [Scheme.Modules.restrict_map, ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
  congr 2

/-- **Sections of a quasi-coherent sheaf over a basic open of an affine open are a
localization**: a section over `U` restricting to zero on `X.basicOpen g` is killed by a power
of `g`. -/
theorem exists_pow_smul_eq_zero (hU : IsAffineOpen U) [F.IsQuasicoherent] (g : Γ(X, U))
    (t : Γ(F, U)) (ht : F.presheaf.map (homOfLE (X.basicOpen_le g)).op t = 0) :
    ∃ n : ℕ, g ^ n • t = 0 := by
  have e₁ : hU.fromSpec ''ᵁ ⊤ = U := by
    rw [Scheme.Hom.image_top_eq_opensRange, hU.opensRange_fromSpec]
  have e₂ : hU.fromSpec ''ᵁ (PrimeSpectrum.basicOpen g) = X.basicOpen g :=
    hU.fromSpec_image_basicOpen g
  have H := isLocalizedModule_resSpecₗ (F.restrict hU.fromSpec) g
  have hinj : Function.Injective (F.presheaf.map (homOfLE e₁.le).op) := by
    have hiso : (homOfLE e₁.le : _ ⟶ _) = eqToHom e₁ := Subsingleton.elim _ _
    have : IsIso (F.presheaf.map (homOfLE e₁.le).op) := by
      rw [hiso, eqToHom_op]; infer_instance
    exact (ConcreteCategory.bijective_of_isIso _).1
  have key : F.presheaf.map (homOfLE e₁.le).op ≫
      (F.restrict hU.fromSpec).presheaf.map (homOfLE (le_top (a := (PrimeSpectrum.basicOpen g :
        (Spec Γ(X, U)).Opens)))).op =
      F.presheaf.map (homOfLE (X.basicOpen_le g)).op ≫ F.presheaf.map (homOfLE e₂.le).op := by
    rw [Scheme.Modules.restrict_map, ← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp]
    congr 2
  have hzero : (F.restrict hU.fromSpec).resSpecₗ (le_top (a := (PrimeSpectrum.basicOpen g :
      (Spec Γ(X, U)).Opens))) (F.presheaf.map (homOfLE e₁.le).op t) = 0 :=
    calc (F.restrict hU.fromSpec).presheaf.map (homOfLE le_top).op
            (F.presheaf.map (homOfLE e₁.le).op t)
        = (F.presheaf.map (homOfLE e₁.le).op ≫
            (F.restrict hU.fromSpec).presheaf.map (homOfLE le_top).op) t :=
          (ConcreteCategory.comp_apply _ _ t).symm
      _ = (F.presheaf.map (homOfLE (X.basicOpen_le g)).op ≫
            F.presheaf.map (homOfLE e₂.le).op) t := ConcreteCategory.congr_hom key t
      _ = F.presheaf.map (homOfLE e₂.le).op
            (F.presheaf.map (homOfLE (X.basicOpen_le g)).op t) :=
          ConcreteCategory.comp_apply _ _ t
      _ = 0 := by rw [ht, map_zero]
  obtain ⟨⟨_, n, rfl⟩, hn⟩ := (IsLocalizedModule.eq_zero_iff (Submonoid.powers g) _).mp hzero
  rw [Submonoid.smul_def, smul_restrict_fromSpec F hU ⊤ e₁.le (g ^ n) _] at hn
  refine ⟨n, hinj ?_⟩
  rw [map_zero, Scheme.Modules.map_smul]
  exact hn

/-- For a point `x` of an affine open `U`, a section `g : Γ(X, U)` is invertible at `x` exactly
when `x` lies in `X.basicOpen g`. -/
lemma mem_primeCompl_iff_mem_basicOpen (hU : IsAffineOpen U) (x : U) (g : Γ(X, U)) :
    g ∈ (hU.primeIdealOf x).asIdeal.primeCompl ↔ x.1 ∈ X.basicOpen g := by
  have hloc : IsLocalization.AtPrime (X.presheaf.stalk x.1) (hU.primeIdealOf x).asIdeal :=
    hU.isLocalization_stalk x
  rw [X.mem_basicOpen' g x, ← IsLocalization.AtPrime.isUnit_to_map_iff
    (X.presheaf.stalk x.1) (hU.primeIdealOf x).asIdeal g]
  rfl

variable (F) in
/-- **The stalk of a quasi-coherent sheaf at a point of an affine open is the localization of
its sections over that open** at the prime corresponding to the point. -/
theorem isLocalizedModule_germₗ (hU : IsAffineOpen U) [F.IsQuasicoherent] (x : U) :
    IsLocalizedModule (hU.primeIdealOf x).asIdeal.primeCompl (germₗ F x) := by
  have hloc : IsLocalization.AtPrime (X.presheaf.stalk x.1) (hU.primeIdealOf x).asIdeal :=
    hU.isLocalization_stalk x
  refine ⟨fun s ↦ ?_, fun y ↦ ?_, fun {t₁ t₂} h ↦ ?_⟩
  · rw [Module.End.isUnit_iff]
    have hu : IsUnit (algebraMap Γ(X, U) (X.presheaf.stalk x.1) s.1) :=
      IsLocalization.map_units _ s
    have h2 := hu.map (algebraMap (X.presheaf.stalk x.1)
      (Module.End (X.presheaf.stalk x.1) (F.presheaf.stalk x.1)))
    rw [Module.End.isUnit_iff] at h2
    have hfun : ⇑(algebraMap Γ(X, U) (Module.End Γ(X, U) (F.presheaf.stalk x.1)) s.1) =
        ⇑(algebraMap (X.presheaf.stalk x.1)
          (Module.End (X.presheaf.stalk x.1) (F.presheaf.stalk x.1))
          (algebraMap Γ(X, U) (X.presheaf.stalk x.1) s.1)) := by
      funext m
      rw [Module.algebraMap_end_apply, Module.algebraMap_end_apply,
        IsScalarTower.algebraMap_smul]
    rw [hfun]
    exact h2
  · obtain ⟨W, hWU, hxW, s, rfl⟩ := F.presheaf.exists_le_germ_eq y x.2
    obtain ⟨g, hgW, hxg⟩ := hU.exists_basicOpen_le ⟨x.1, hxW⟩ x.2
    obtain ⟨n, t, hnt⟩ := exists_pow_smul_eq_res hU g (F.presheaf.map (homOfLE hgW).op s)
    refine ⟨⟨t, ⟨g ^ n, pow_mem ((mem_primeCompl_iff_mem_basicOpen hU x g).mpr hxg) n⟩⟩, ?_⟩
    have := congr(F.presheaf.germ (X.basicOpen g) x.1 hxg $hnt)
    rw [germ_smul, map_pow] at this
    simpa [Submonoid.smul_def, TopCat.Presheaf.germ_res_apply, germₗ, smul_stalk_def]
      using this
  · obtain ⟨W, hxW, iU₁, iU₂, hW⟩ := F.presheaf.germ_eq x.1 x.2 x.2 t₁ t₂ h
    obtain ⟨g, hgW, hxg⟩ := hU.exists_basicOpen_le ⟨x.1, hxW⟩ x.2
    have hres : F.presheaf.map (homOfLE (X.basicOpen_le g)).op (t₁ - t₂) = 0 := by
      rw [map_sub, sub_eq_zero]
      calc F.presheaf.map (homOfLE (X.basicOpen_le g)).op t₁
          = F.presheaf.map (homOfLE hgW).op (F.presheaf.map iU₁.op t₁) := by
            rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
            congr 2
        _ = F.presheaf.map (homOfLE hgW).op (F.presheaf.map iU₂.op t₂) := by rw [hW]
        _ = F.presheaf.map (homOfLE (X.basicOpen_le g)).op t₂ := by
            rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
            congr 2
    obtain ⟨n, hn⟩ := exists_pow_smul_eq_zero hU g (t₁ - t₂) hres
    refine ⟨⟨g ^ n, pow_mem ((mem_primeCompl_iff_mem_basicOpen hU x g).mpr hxg) n⟩, ?_⟩
    rw [smul_sub, sub_eq_zero] at hn
    exact hn

end Scheme.Modules

end Localization
/-!
### Exactness of `M ↦ M^~`

`M ↦ M^~` is a left adjoint, hence right exact.  It is also left exact: a monomorphism of
`R`-modules is sent to a morphism which is injective on sections over each basic open, because
those sections are localisations, and hence injective on sections over every open, because
`M^~` is a sheaf.
-/

section Exactness

variable {A B : ModuleCat.{u} R}

open _root_.PrimeSpectrum in
/-- `M^~ ⟶ N^~` is injective on the sections over a basic open subset as soon as `M ⟶ N` is
injective, because those sections are localisations. -/
theorem tilde.injective_app_basicOpen (f : A ⟶ B) (hf : Function.Injective f.hom) (r : R) :
    Function.Injective
      ((modulesSpecToSheaf.map (tilde.map f)).1.app (op (basicOpen r))).hom := by
  have key (m : A) :
      ((modulesSpecToSheaf.map (tilde.map f)).1.app (op (basicOpen r))).hom
        ((tilde.toOpen A (basicOpen r)).hom m) = (tilde.toOpen B (basicOpen r)).hom (f.hom m) :=
    congr($(tilde.toOpen_map_app f (basicOpen r)).hom m)
  refine IsLocalizedModule.injective_of_map_zero (.powers r) (tilde.toOpen A (basicOpen r)).hom ?_
  intro m hm
  rw [key] at hm
  obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_zero_iff (.powers r) _).mp hm
  refine (IsLocalizedModule.eq_zero_iff (.powers r) _).mpr ⟨s, hf ?_⟩
  simpa [Submonoid.smul_def] using hs

open _root_.PrimeSpectrum in
/-- `M^~ ⟶ N^~` is injective on the sections over any open subset as soon as `M ⟶ N` is
injective. -/
theorem tilde.injective_app (f : A ⟶ B) (hf : Function.Injective f.hom) (U : (Spec R).Opens) :
    Function.Injective ((modulesSpecToSheaf.map (tilde.map f)).1.app (op U)).hom := by
  intro s t hst
  refine TopCat.Presheaf.IsSheaf.section_ext (modulesSpecToSheaf.obj (tilde A)).2 ?_
  intro x hxU
  obtain ⟨a, ⟨_, ⟨r, rfl⟩, rfl⟩, hxr, hrU : basicOpen _ ≤ _⟩ :=
    isBasis_basic_opens.exists_subset_of_mem_open hxU U.2
  refine ⟨_, hrU, hxr, ?_⟩
  refine tilde.injective_app_basicOpen f hf r ?_
  have h (y) : ((modulesSpecToSheaf.map (tilde.map f)).1.app (op (basicOpen r))).hom
        (((modulesSpecToSheaf.obj (tilde A)).obj.map (homOfLE hrU).op).hom y) =
      ((modulesSpecToSheaf.obj (tilde B)).obj.map (homOfLE hrU).op).hom
        (((modulesSpecToSheaf.map (tilde.map f)).1.app (op U)).hom y) :=
    congr($((modulesSpecToSheaf.map (tilde.map f)).1.naturality (homOfLE hrU).op).hom y)
  exact (h s).trans ((congrArg _ hst).trans (h t).symm)

instance : (tilde.functor R).PreservesMonomorphisms where
  preserves {A B} f hf := by
    have hinj : Function.Injective f.hom := (ModuleCat.mono_iff_injective f).mp hf
    refine modulesSpecToSheaf.mono_of_mono_map (f := tilde.map f) ?_
    refine (TopCat.Sheaf.forget (ModuleCat.{u} R) (Spec R)).mono_of_mono_map ?_
    suffices h : ∀ U, Mono (((TopCat.Sheaf.forget (ModuleCat.{u} R) (Spec R)).map
        (modulesSpecToSheaf.map (tilde.map f))).app U) from NatTrans.mono_of_mono_app _
    intro U
    exact (ModuleCat.mono_iff_injective _).mpr (tilde.injective_app f hinj U.unop)

/-- **`M ↦ M^~` is an exact functor.** -/
instance : PreservesFiniteLimits (tilde.functor R) := by
  rw [Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono]
  intro S hS
  have := hS.mono_f
  exact ⟨((Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi
    (tilde.functor R)).mp inferInstance S hS).1, inferInstance⟩

instance : (moduleSpecΓFunctor (R := R)).IsRightAdjoint := tilde.adjunction.isRightAdjoint

attribute [local instance] preservesBinaryBiproducts_of_preservesBinaryProducts in
instance : (moduleSpecΓFunctor (R := R)).Additive :=
  Functor.additive_of_preservesBinaryBiproducts _

-- `moduleSpecΓFunctor` is declared with source `(Spec (CommRingCat.of R)).Modules`, which is
-- definitionally but not syntactically the category `(Spec R).Modules` in which the sheaves of
-- modules below live; instance search does not bridge the two on its own.
instance : Functor.PreservesZeroMorphisms
    (C := (Spec R).Modules) (D := ModuleCat R) moduleSpecΓFunctor where
  map_zero X Y := Functor.map_zero moduleSpecΓFunctor X Y

end Exactness


/-!
### Kernels and cokernels of quasi-coherent sheaves on an affine scheme

Because `M ↦ M^~` is exact and identifies `ModuleCat R` with the quasi-coherent sheaves of
modules on `Spec R`, kernels and cokernels of morphisms of quasi-coherent sheaves on an affine
scheme are again quasi-coherent, and their modules of global sections are the kernel and the
cokernel of the induced morphism of modules.
-/

variable {M N : (Spec R).Modules}

namespace Scheme.Modules

/-- Naturality of the counit `M^~(Γ) ⟶ M` of the tilde-Gamma adjunction. -/
lemma fromTildeΓ_naturality (φ : M ⟶ N) :
    tilde.map (moduleSpecΓFunctor.map φ) ≫ N.fromTildeΓ = M.fromTildeΓ ≫ φ :=
  fromTildeΓNatTrans.naturality φ

variable [M.IsQuasicoherent] [N.IsQuasicoherent]

/-- A quasi-coherent sheaf of modules on an affine scheme is the sheaf associated to its module
of global sections. -/
noncomputable def isoTildeΓ (M : (Spec R).Modules) [M.IsQuasicoherent] :
    tilde (moduleSpecΓFunctor.obj M) ≅ M :=
  @asIso _ _ _ _ M.fromTildeΓ ((isQuasicoherent_iff_isIso_fromTildeΓ M).mp inferInstance)

lemma isoTildeΓ_hom (M : (Spec R).Modules) [M.IsQuasicoherent] :
    (isoTildeΓ M).hom = M.fromTildeΓ := rfl

/-- On an affine scheme, the kernel of a morphism of quasi-coherent sheaves of modules is the
sheaf associated to the kernel of the induced morphism of modules of global sections. -/
noncomputable def kernelIsoTilde (φ : M ⟶ N) :
    tilde (kernel (moduleSpecΓFunctor.map φ)) ≅ kernel φ :=
  PreservesKernel.iso (tilde.functor R) (moduleSpecΓFunctor.map φ) ≪≫
    kernel.mapIso (tilde.map (moduleSpecΓFunctor.map φ)) φ (isoTildeΓ M) (isoTildeΓ N)
      (fromTildeΓ_naturality φ)

/-- On an affine scheme, the cokernel of a morphism of quasi-coherent sheaves of modules is the
sheaf associated to the cokernel of the induced morphism of modules of global sections. -/
noncomputable def cokernelIsoTilde (φ : M ⟶ N) :
    tilde (cokernel (moduleSpecΓFunctor.map φ)) ≅ cokernel φ :=
  PreservesCokernel.iso (tilde.functor R) (moduleSpecΓFunctor.map φ) ≪≫
    cokernel.mapIso (tilde.map (moduleSpecΓFunctor.map φ)) φ (isoTildeΓ M) (isoTildeΓ N)
      (fromTildeΓ_naturality φ)

instance isQuasicoherent_kernel (φ : M ⟶ N) : (kernel φ).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso
    (kernelIsoTilde φ) inferInstance

instance isQuasicoherent_cokernel (φ : M ⟶ N) : (cokernel φ).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso
    (cokernelIsoTilde φ) inferInstance


/-- A quasi-coherent sheaf of modules on an affine scheme generated by finitely many global
sections has a finite module of global sections. -/
theorem finite_of_generatingSections (P : (Spec R).Modules) [P.IsQuasicoherent]
    (G : P.GeneratingSections) (hG : G.IsFiniteType) :
    Module.Finite R (moduleSpecΓFunctor.obj P) :=
  @tilde.finite_of_generatingSections _ _
    (SheafOfModules.GeneratingSections.equivOfIso (isoTildeΓ P).symm G) ⟨hG.finite⟩

/-- A quasi-coherent sheaf of modules on an affine scheme with finite module of global sections
is generated by finitely many global sections. -/
theorem exists_generatingSections_of_finite (P : (Spec R).Modules) [P.IsQuasicoherent]
    (h : Module.Finite R (moduleSpecΓFunctor.obj P)) :
    ∃ G : P.GeneratingSections, G.IsFiniteType := by
  have := h
  obtain ⟨s, hs⟩ := (Module.Finite.fg_top :
    (⊤ : Submodule R (moduleSpecΓFunctor.obj P)).FG)
  have hs' : Submodule.span R (↑s : Set (moduleSpecΓFunctor.obj P)) = ⊤ := hs
  have : Finite (↑s : Set (moduleSpecΓFunctor.obj P)) := s.finite_toSet
  exact ⟨SheafOfModules.GeneratingSections.equivOfIso (isoTildeΓ P)
    (generatingSectionsTilde (↑s : Set (moduleSpecΓFunctor.obj P)) hs'), ⟨‹Finite _›⟩⟩

/-- A quasi-coherent sheaf of modules on an affine scheme admits a global presentation. -/
theorem nonempty_presentation (P : (Spec R).Modules) [P.IsQuasicoherent] :
    Nonempty P.Presentation :=
  ⟨@SheafOfModules.Presentation.ofIsIso _ _ _ _ _ _ _ _ P.fromTildeΓ
    ((isQuasicoherent_iff_isIso_fromTildeΓ P).mp inferInstance)
    (presentationTilde.{u} _ .univ (by simp) _ (Submodule.span_eq _))⟩


/-- On an affine scheme, global sections of quasi-coherent sheaves of modules preserve
epimorphisms. -/
theorem epi_moduleSpecΓ_map (φ : M ⟶ N) [Epi φ] : Epi (moduleSpecΓFunctor.map φ) := by
  rw [← tilde.epi_map_iff]
  have h : tilde.map (moduleSpecΓFunctor.map φ) ≫ (isoTildeΓ N).hom =
      (isoTildeΓ M).hom ≫ φ := fromTildeΓ_naturality φ
  have h2 : tilde.map (moduleSpecΓFunctor.map φ) =
      (tilde.map (moduleSpecΓFunctor.map φ) ≫ (isoTildeΓ N).hom) ≫ (isoTildeΓ N).inv := by simp
  rw [h2, h]
  infer_instance


/-- On an affine scheme, if the outer terms of a short exact sequence of quasi-coherent sheaves
of modules have finite modules of global sections, then so does the middle term. -/
theorem finite_moduleSpecΓ_of_shortExact {S : ShortComplex (Spec R).Modules}
    (hS : S.ShortExact) [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent]
    (h₁ : Module.Finite R (moduleSpecΓFunctor.obj S.X₁))
    (h₃ : Module.Finite R (moduleSpecΓFunctor.obj S.X₃)) :
    Module.Finite R (moduleSpecΓFunctor.obj S.X₂) := by
  have e₁ : Module.Finite R (S.map moduleSpecΓFunctor).X₁ := h₁
  have e₃ : Module.Finite R (S.map moduleSpecΓFunctor).X₃ := h₃
  obtain ⟨hex, -⟩ := (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono
    moduleSpecΓFunctor).mp inferInstance S hS
  have hepi : Epi (moduleSpecΓFunctor.map S.g) := by
    have := hS.epi_g
    exact epi_moduleSpecΓ_map S.g
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hex
  exact Module.Finite.of_exact hex ((ModuleCat.epi_iff_surjective _).mp hepi)


/-- On an affine scheme, the cokernel of a morphism of quasi-coherent sheaves of modules whose
target has finite module of global sections again has finite module of global sections. -/
theorem finite_moduleSpecΓ_cokernel (φ : M ⟶ N)
    [Module.Finite R (moduleSpecΓFunctor.obj N)] :
    Module.Finite R (moduleSpecΓFunctor.obj (cokernel φ)) := by
  let C : ModuleCat.{u} R := cokernel (moduleSpecΓFunctor.map φ)
  have h₂ : Module.Finite R C :=
    Module.Finite.of_surjective (cokernel.π (moduleSpecΓFunctor.map φ)).hom
      ((ModuleCat.epi_iff_surjective _).mp inferInstance)
  exact h₂.equiv ((tilde.toTildeΓNatIso.app C ≪≫
    moduleSpecΓFunctor.mapIso (cokernelIsoTilde φ)).toLinearEquiv)

section Noetherian

variable [IsNoetherianRing R]

omit [M.IsQuasicoherent] [N.IsQuasicoherent] in
/-- Over a Noetherian affine scheme, the kernel of a morphism of sheaves of modules whose
source has finite module of global sections again has finite module of global sections. -/
theorem finite_moduleSpecΓ_kernel (φ : M ⟶ N)
    [Module.Finite R (moduleSpecΓFunctor.obj M)] :
    Module.Finite R (moduleSpecΓFunctor.obj (kernel φ)) := by
  have h₁ : IsNoetherian R (moduleSpecΓFunctor.obj M) := inferInstance
  let K : ModuleCat.{u} R := kernel (moduleSpecΓFunctor.map φ)
  have h₂ : Module.Finite R K :=
    Module.Finite.of_injective (kernel.ι (moduleSpecΓFunctor.map φ)).hom
      ((ModuleCat.mono_iff_injective _).mp inferInstance)
  exact h₂.equiv (PreservesKernel.iso moduleSpecΓFunctor φ).symm.toLinearEquiv

end Noetherian

end Scheme.Modules

/-!
### Restriction to open subschemes and to the slice site

`SheafOfModules.IsQuasicoherent` and `SheafOfModules.IsFiniteType` are defined through the
restrictions `M.over U` of `M` to the slice sites of the opens of a covering family, while the
affine theory above is phrased through the restrictions `M.restrict f` along open immersions.
The two are matched by `Scheme.Modules.overFunctorEquiv`; the transports of
`SheafOfModules.GeneratingSections` and `SheafOfModules.Presentation` along it are recorded here.
-/

namespace Scheme.Modules

open TopologicalSpace

variable {X : Scheme.{u}} (M : X.Modules)

/-- Transport of a presentation of a sheaf of modules along an isomorphism. -/
noncomputable def presentationOfIso {P Q : X.Modules} (e : P ≅ Q) (p : P.Presentation) :
    Q.Presentation :=
  @SheafOfModules.Presentation.ofIsIso _ _ _ _ _ _ _ _ e.hom e.isIso_hom p

/-- A morphism of sheaves of modules which is injective on sections over every open subset is
a monomorphism. -/
lemma mono_of_injective_app {M N : X.Modules} (φ : M ⟶ N)
    (h : ∀ U, Function.Injective (φ.app U)) : Mono φ := by
  refine (toPresheaf X).mono_of_mono_map ?_
  suffices h' : ∀ U, Mono (((toPresheaf X).map φ).app U) from NatTrans.mono_of_mono_app _
  intro U
  exact ConcreteCategory.mono_of_injective _ (h U.unop)

/-- A monomorphism of sheaves of modules is injective on sections over every open subset.

This is stated for `SheafOfModules X.ringCatSheaf` rather than for the definitionally equal
`X.Modules`, because instance search for `PreservesLimit` does not see through the latter. -/
lemma injective_app_of_mono {M N : SheafOfModules.{u} X.ringCatSheaf} (φ : M ⟶ N) (hφ : Mono φ)
    (U : X.Opens) :
    Function.Injective ((SheafOfModules.evaluation X.ringCatSheaf (op U)).map φ) := by
  have := hφ
  exact (ModuleCat.mono_iff_injective _).mp inferInstance

section restrict

variable {Y Z : Scheme.{u}} (f : Y ⟶ Z) [IsOpenImmersion f]

/-- `Scheme.Modules.restrictFunctor`, with its type spelled out in terms of `SheafOfModules`.
Instance search does not see through the `Category` instance on `Scheme.Modules`, so the
universe-explicit `PreservesColimitsOfSize` instance needed by
`SheafOfModules.GeneratingSections.map` has to be stated for this copy. -/
noncomputable def restrictFunctor' :
    SheafOfModules.{u} Z.ringCatSheaf ⥤ SheafOfModules.{u} Y.ringCatSheaf :=
  restrictFunctor f

instance : PreservesColimitsOfSize.{u, u, u, u, u + 1, u + 1} (restrictFunctor' f) :=
  inferInstanceAs (PreservesColimitsOfSize.{u, u, u, u, u + 1, u + 1} (restrictFunctor f))

attribute [local instance] preservesBinaryBiproducts_of_preservesBinaryCoproducts in
instance : (restrictFunctor f).Additive := Functor.additive_of_preservesBinaryBiproducts _

instance : (restrictFunctor f).PreservesMonomorphisms where
  preserves {M N} φ hφ := by
    refine mono_of_injective_app _ fun U ↦ ?_
    exact injective_app_of_mono (M := M) (N := N) φ hφ (f ''ᵁ U)

/-- **Restriction to an open subscheme is exact.** It preserves finite colimits because it is a
left adjoint, and it preserves monomorphisms because it only reindexes sections. -/
instance : PreservesFiniteLimits (restrictFunctor f) := by
  rw [Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono]
  intro S hS
  have := hS.mono_f
  exact ⟨((Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi
    (restrictFunctor f)).mp inferInstance S hS).1, inferInstance⟩

/-- The generating sections of `M.restrict f` obtained by restricting generating sections of `M`.
This is the `SheafOfModules.GeneratingSections` analogue of
`AlgebraicGeometry.Scheme.Modules.presentationRestrict`. -/
noncomputable def generatingSectionsRestrict {N : Z.Modules} (G : N.GeneratingSections) :
    (N.restrict f).GeneratingSections :=
  G.map (restrictFunctor' f) (restrictUnitIso f).symm

instance {N : Z.Modules} (G : N.GeneratingSections) [G.IsFiniteType] :
    (generatingSectionsRestrict f G).IsFiniteType :=
  ⟨‹G.IsFiniteType›.finite⟩

end restrict

section over

variable (U : X.Opens)

/-- The functor underlying `Scheme.Modules.overEquiv`, with its type spelled out in terms of
`SheafOfModules`; see `AlgebraicGeometry.Scheme.Modules.restrictFunctor'`. -/
noncomputable def overEquivFunctor :
    SheafOfModules.{u} (X.ringCatSheaf.over U) ⥤ SheafOfModules.{u} (U.toScheme).ringCatSheaf :=
  (overEquiv U).functor

/-- The inverse of `Scheme.Modules.overEquiv`, with its type spelled out in terms of
`SheafOfModules`; see `AlgebraicGeometry.Scheme.Modules.restrictFunctor'`. -/
noncomputable def overEquivInverse :
    SheafOfModules.{u} (U.toScheme).ringCatSheaf ⥤ SheafOfModules.{u} (X.ringCatSheaf.over U) :=
  (overEquiv U).inverse

instance : PreservesColimitsOfSize.{u, u, u, u, u + 1, u + 1} (overEquivFunctor U) :=
  inferInstanceAs (PreservesColimitsOfSize.{u, u, u, u, u + 1, u + 1} (overEquiv U).functor)

instance : PreservesColimitsOfSize.{u, u, u, u, u + 1, u + 1} (overEquivInverse U) :=
  inferInstanceAs (PreservesColimitsOfSize.{u, u, u, u, u + 1, u + 1} (overEquiv U).inverse)

/-- Under `Scheme.Modules.overEquiv`, the restriction of `M` to the slice site over `U`
corresponds to its restriction to the open subscheme `U`. -/
noncomputable def overIsoRestrict : (overEquivFunctor U).obj (M.over U) ≅ M.restrict U.ι :=
  (overFunctorEquiv U).app M

/-- The inverse form of `AlgebraicGeometry.Scheme.Modules.overIsoRestrict`. -/
noncomputable def restrictIsoOver : (overEquivInverse U).obj (M.restrict U.ι) ≅ M.over U :=
  (overEquiv U).inverse.mapIso (overIsoRestrict M U).symm ≪≫ ((overEquiv U).unitIso.app _).symm

/-- Generating sections of `M.over U` give generating sections of `M.restrict U.ι`. -/
noncomputable def generatingSectionsOfOver (G : (M.over U).GeneratingSections) :
    (M.restrict U.ι).GeneratingSections :=
  SheafOfModules.GeneratingSections.equivOfIso (overIsoRestrict M U)
    (G.map (overEquivFunctor U)
      (TopologicalSpace.Opens.sheafOfModulesEquivOverUnit U X.ringCatSheaf).symm)

instance (G : (M.over U).GeneratingSections) [G.IsFiniteType] :
    (generatingSectionsOfOver M U G).IsFiniteType :=
  ⟨‹G.IsFiniteType›.finite⟩

/-- Generating sections of `M.restrict U.ι` give generating sections of `M.over U`. -/
noncomputable def overGeneratingSections (G : (M.restrict U.ι).GeneratingSections) :
    (M.over U).GeneratingSections :=
  SheafOfModules.GeneratingSections.equivOfIso (restrictIsoOver M U)
    (G.map (overEquivInverse U)
      (TopologicalSpace.Opens.sheafOfModulesEquivOverInverseUnit U X.ringCatSheaf).symm)

instance (G : (M.restrict U.ι).GeneratingSections) [G.IsFiniteType] :
    (overGeneratingSections M U G).IsFiniteType :=
  ⟨‹G.IsFiniteType›.finite⟩

/-- A presentation of `M.restrict U.ι` gives a presentation of `M.over U`. -/
noncomputable def overPresentation (P : (M.restrict U.ι).Presentation) :
    (M.over U).Presentation :=
  SheafOfModules.Presentation.ofIsIso (restrictIsoOver M U).hom
    (P.map (overEquivInverse U)
      (TopologicalSpace.Opens.sheafOfModulesEquivOverInverseUnit U X.ringCatSheaf).symm)

end over

section le

variable {V W : X.Opens} (h : V ≤ W)

/-- Restricting to `V` factors through restricting to a larger open `W`. -/
noncomputable def restrictRestrictIso :
    (restrictFunctor' (X.homOfLE h)).obj (M.restrict W.ι) ≅ M.restrict V.ι :=
  ((restrictFunctorComp (X.homOfLE h) W.ι).app M).symm ≪≫
    (restrictFunctorCongr (X.homOfLE_ι h)).app M

/-- Generating sections restrict to smaller opens. -/
noncomputable def generatingSectionsRestrictLE (G : (M.restrict W.ι).GeneratingSections) :
    (M.restrict V.ι).GeneratingSections :=
  SheafOfModules.GeneratingSections.equivOfIso (restrictRestrictIso M h)
    (generatingSectionsRestrict (X.homOfLE h) G)

instance (G : (M.restrict W.ι).GeneratingSections) [G.IsFiniteType] :
    (generatingSectionsRestrictLE M h G).IsFiniteType :=
  ⟨‹G.IsFiniteType›.finite⟩

end le

section locality

open TopologicalSpace

variable {ι : Type u} (U : ι → X.Opens)

/-- **Being of finite type is local**: a sheaf of modules generated by finitely many sections
over each member of an open cover is of finite type. -/
theorem isFiniteType_of_generatingSections (hU : IsOpenCover U)
    (G : ∀ i, (M.restrict (U i).ι).GeneratingSections) (hG : ∀ i, (G i).IsFiniteType) :
    M.IsFiniteType :=
  SheafOfModules.LocalGeneratorsData.isFiniteType_of_forall (M := M)
    (.mk (M := M) ι U ((Opens.coversTop_iff _ U).mpr hU)
      fun i ↦ overGeneratingSections M (U i) (G i))
    fun i ↦ ⟨(hG i).finite⟩

/-- **Being quasi-coherent is local**: a sheaf of modules admitting a presentation over each
member of an open cover is quasi-coherent. -/
theorem isQuasicoherent_of_presentation (hU : IsOpenCover U)
    (P : ∀ i, (M.restrict (U i).ι).Presentation) : M.IsQuasicoherent :=
  SheafOfModules.QuasicoherentData.isQuasicoherent (M := M)
    (.mk (M := M) ι U ((Opens.coversTop_iff _ U).mpr hU)
      fun i ↦ overPresentation M (U i) (P i))

end locality

/-- A sheaf of modules of finite type is generated by finitely many sections over each member
of some cover by affine opens refining a given open cover. -/
theorem exists_isOpenCover_generatingSections_le [M.IsFiniteType] {κ : Type u} (V : κ → X.Opens)
    (hV : IsOpenCover V) :
    ∃ (ι : Type u) (U : ι → X.Opens) (r : ι → κ)
      (G : ∀ i, (M.restrict (U i).ι).GeneratingSections),
      IsOpenCover U ∧ (∀ i, IsAffineOpen (U i)) ∧ (∀ i, U i ≤ V (r i)) ∧
        ∀ i, (G i).IsFiniteType := by
  obtain ⟨⟨I, W, cov, gens⟩, hgens⟩ :=
    SheafOfModules.IsFiniteType.exists_localGeneratorsData (M := M)
  choose κ' hsub heq using fun p : I × κ ↦
    Opens.isBasis_iff_cover.mp X.isBasis_affineOpens (W p.1 ⊓ V p.2)
  have hle' (j : Σ p : I × κ, κ' p) : (j.2 : X.Opens) ≤ W j.1.1 ⊓ V j.1.2 := by
    rw [heq j.1]; exact le_sSup j.2.2
  refine ⟨Σ p : I × κ, κ' p, fun j ↦ j.2, fun j ↦ j.1.2,
    fun j ↦ generatingSectionsRestrictLE M ((hle' j).trans inf_le_left)
      (generatingSectionsOfOver M (W j.1.1) (gens j.1.1)), ?_, ?_, ?_, ?_⟩
  · rw [Opens.coversTop_iff, IsOpenCover] at cov
    rw [IsOpenCover] at hV
    have h₁ : (⨆ p : I × κ, W p.1 ⊓ V p.2) = ⊤ := by
      rw [← iSup_inf_iSup, cov, hV, top_inf_eq]
    rw [IsOpenCover, iSup_sigma, ← h₁]
    exact iSup_congr fun p ↦ by rw [heq p, sSup_eq_iSup']
  · exact fun j ↦ hsub _ j.2.2
  · exact fun j ↦ (hle' j).trans inf_le_right
  · intro j
    have := hgens.isFiniteType j.1.1
    infer_instance

/-- A sheaf of modules of finite type is generated by finitely many sections over each member
of some cover by affine opens. This is the `SheafOfModules.GeneratingSections` analogue of
`AlgebraicGeometry.Scheme.Modules.exists_isOpenCover_presentation`. -/
theorem exists_isOpenCover_generatingSections [M.IsFiniteType] :
    ∃ (ι : Type u) (U : ι → X.Opens) (G : ∀ i, (M.restrict (U i).ι).GeneratingSections),
      IsOpenCover U ∧ (∀ i, IsAffineOpen (U i)) ∧ ∀ i, (G i).IsFiniteType := by
  obtain ⟨ι, U, -, G, hU, hU', -, hG⟩ := exists_isOpenCover_generatingSections_le M
    (fun _ : PUnit.{u + 1} ↦ (⊤ : X.Opens)) (by simp [IsOpenCover])
  exact ⟨ι, U, G, hU, hU', hG⟩


section AffineLocal

/-!
### Coherence is affine-local

A sheaf of modules on a scheme is coherent exactly when, on some cover by affine opens, it is
quasi-coherent with finitely generated module of sections.
-/

variable {U : X.Opens} (hU : IsAffineOpen U)

/-- Restriction to the affine open `U`, transported along `U ≅ Spec Γ(X, U)`. -/
noncomputable def restrictFromSpecIso :
    (M.restrict U.ι).restrict hU.isoSpec.inv ≅ M.restrict hU.fromSpec :=
  ((restrictFunctorComp hU.isoSpec.inv U.ι).app M).symm ≪≫
    (restrictFunctorCongr hU.isoSpec_inv_ι).app M

/-- The inverse form of `AlgebraicGeometry.Scheme.Modules.restrictFromSpecIso`. -/
noncomputable def restrictIotaIso :
    (M.restrict hU.fromSpec).restrict hU.isoSpec.hom ≅ M.restrict U.ι :=
  ((restrictFunctorComp hU.isoSpec.hom hU.fromSpec).app M).symm ≪≫
    (restrictFunctorCongr hU.isoSpec_hom_fromSpec).app M


/-- **Coherence is affine-local**: a sheaf of modules which is quasi-coherent with finite module
of sections on each member of a cover by affine opens is coherent. -/
theorem isCoherent_of_isOpenCover {ι : Type u} (U : ι → X.Opens) (hU : IsOpenCover U)
    (hU' : ∀ i, IsAffineOpen (U i))
    (hqc : ∀ i, (M.restrict (hU' i).fromSpec).IsQuasicoherent)
    (hfin : ∀ i, Module.Finite Γ(X, U i)
      (moduleSpecΓFunctor.obj (M.restrict (hU' i).fromSpec))) : M.IsCoherent := by
  have hq : M.IsQuasicoherent := by
    refine isQuasicoherent_of_presentation M U hU fun i ↦ ?_
    have := hqc i
    exact presentationOfIso (restrictIotaIso M (hU' i))
      (presentationRestrict (hU' i).isoSpec.hom
        (nonempty_presentation (M.restrict (hU' i).fromSpec)).some)
  have h (i) : ∃ G : (M.restrict (U i).ι).GeneratingSections, G.IsFiniteType := by
    have := hqc i
    obtain ⟨G, hG⟩ := exists_generatingSections_of_finite (M.restrict (hU' i).fromSpec) (hfin i)
    exact ⟨SheafOfModules.GeneratingSections.equivOfIso (restrictIotaIso M (hU' i))
      (generatingSectionsRestrict (hU' i).isoSpec.hom G), ⟨hG.finite⟩⟩
  choose G hG using h
  have hf : M.IsFiniteType := isFiniteType_of_generatingSections M U hU G hG
  exact (SheafOfModules.isCoherent_iff M).mpr ⟨hq, hf⟩

/-- A quasi-coherent sheaf of modules generated by finitely many sections over an affine open
`U` has a finite module of sections over `U`. -/
theorem finite_of_generatingSections_restrict [M.IsQuasicoherent]
    (G : (M.restrict U.ι).GeneratingSections) (hG : G.IsFiniteType) :
    Module.Finite Γ(X, U) (moduleSpecΓFunctor.obj (M.restrict hU.fromSpec)) :=
  finite_of_generatingSections _
    (SheafOfModules.GeneratingSections.equivOfIso (restrictFromSpecIso M hU)
      (generatingSectionsRestrict hU.isoSpec.inv G)) ⟨hG.finite⟩

/-- A coherent sheaf of modules has finitely generated modules of sections on some cover by
affine opens. -/
theorem exists_isOpenCover_finite (hM : M.IsCoherent) :
    ∃ (ι : Type u) (U : ι → X.Opens) (hU' : ∀ i, IsAffineOpen (U i)), IsOpenCover U ∧
      ∀ i, Module.Finite Γ(X, U i)
        (moduleSpecΓFunctor.obj (M.restrict (hU' i).fromSpec)) := by
  obtain ⟨hq, hf⟩ := (SheafOfModules.isCoherent_iff M).mp hM
  obtain ⟨ι, U, G, hU, hU', hG⟩ := exists_isOpenCover_generatingSections M
  exact ⟨ι, U, hU', hU, fun i ↦ finite_of_generatingSections_restrict M (hU' i) (G i) (hG i)⟩

/-- Two coherent sheaves of modules have finitely generated modules of sections on a common
cover by affine opens. -/
theorem exists_isOpenCover_finite₂ (N : X.Modules) (hM : M.IsCoherent) (hN : N.IsCoherent) :
    ∃ (ι : Type u) (U : ι → X.Opens) (hU' : ∀ i, IsAffineOpen (U i)), IsOpenCover U ∧
      (∀ i, Module.Finite Γ(X, U i)
        (moduleSpecΓFunctor.obj (M.restrict (hU' i).fromSpec))) ∧
      ∀ i, Module.Finite Γ(X, U i)
        (moduleSpecΓFunctor.obj (N.restrict (hU' i).fromSpec)) := by
  obtain ⟨hMq, hMf⟩ := (SheafOfModules.isCoherent_iff M).mp hM
  obtain ⟨hNq, hNf⟩ := (SheafOfModules.isCoherent_iff N).mp hN
  obtain ⟨ι₁, U₁, -, G, hU₁, -, -, hG⟩ := exists_isOpenCover_generatingSections_le M
    (fun _ : PUnit.{u + 1} ↦ (⊤ : X.Opens)) (by simp [IsOpenCover])
  obtain ⟨ι, U, r, H, hU, hU', hle, hH⟩ := exists_isOpenCover_generatingSections_le N U₁ hU₁
  refine ⟨ι, U, hU', hU, fun i ↦ ?_, fun i ↦ finite_of_generatingSections_restrict N (hU' i)
    (H i) (hH i)⟩
  exact finite_of_generatingSections_restrict M (hU' i)
    (generatingSectionsRestrictLE M (hle i) (G (r i))) ⟨(hG (r i)).finite⟩


end AffineLocal

end Scheme.Modules

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

namespace Scheme.Modules

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
lemma finite_restrict_of_generatingSections {S : CommRingCat.{u}} (ψ : Spec S ⟶ Spec R)
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
  have hloc := Scheme.Modules.finite_restrict_of_generatingSections _ (tilde N) G
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

namespace Scheme.Modules

variable {X : Scheme.{u}}

/-- Sections over the image of an open immersion `ψ : Spec S ⟶ X` are finite over
`Γ(X, _)` as soon as they are finite over `S`. -/
lemma finite_sections_of_finite_restrict' {S : CommRingCat.{u}} (ψ : Spec S ⟶ X)
    [IsOpenImmersion ψ] (M : X.Modules) [Module.Finite S Γ(M.restrict ψ, ⊤)] :
    Module.Finite Γ(X, ψ ''ᵁ ⊤) Γ(M, ψ ''ᵁ ⊤) := by
  let σ : S ⟶ Γ(X, ψ ''ᵁ ⊤) := (Scheme.ΓSpecIso S).inv ≫ (ψ.appIso ⊤).inv
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

/-- **The stalk of a coherent sheaf of modules is a finite module over the local ring.** -/
theorem finite_stalk (M : X.Modules) [M.IsCoherent] (x : X) :
    Module.Finite (X.presheaf.stalk x) (M.presheaf.stalk x) := by
  obtain ⟨ι, U, hU', hcov, hfin⟩ := exists_isOpenCover_finite M inferInstance
  obtain ⟨i, hi⟩ := hcov.exists_mem x
  have him : (hU' i).fromSpec ''ᵁ ⊤ = U i := by
    ext y
    simp
  have haff : IsAffineOpen ((hU' i).fromSpec ''ᵁ ⊤) := by rw [him]; exact hU' i
  have hx : x ∈ (hU' i).fromSpec ''ᵁ ⊤ := by rw [him]; exact hi
  have hfin' : Module.Finite Γ(X, U i) Γ(M.restrict (hU' i).fromSpec, ⊤) := hfin i
  have hsec := finite_sections_of_finite_restrict' (hU' i).fromSpec M
  let _ : Algebra Γ(X, (hU' i).fromSpec ''ᵁ ⊤) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hx⟩
  let _ : Module Γ(X, (hU' i).fromSpec ''ᵁ ⊤) (M.presheaf.stalk x) :=
    module_section_stalk M ⟨x, hx⟩
  let _ : IsScalarTower Γ(X, (hU' i).fromSpec ''ᵁ ⊤) (X.presheaf.stalk x) (M.presheaf.stalk x) :=
    isScalarTower_section_stalk M ⟨x, hx⟩
  have hloc : IsLocalization.AtPrime (X.presheaf.stalk x)
      (haff.primeIdealOf ⟨x, hx⟩).asIdeal := haff.isLocalization_stalk ⟨x, hx⟩
  have hlm := isLocalizedModule_germₗ M haff ⟨x, hx⟩
  exact Module.Finite.of_isLocalizedModule (haff.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
    (germₗ M ⟨x, hx⟩)

/-- The `𝔪_x`-adic completion of the stalk of a sheaf of `𝒪_X`-modules at `x`. By
`AlgebraicGeometry.Scheme.Modules.finite_stalk` this is, for a coherent sheaf on a locally
noetherian scheme, the completion of a finite module over a noetherian local ring. -/
noncomputable abbrev completedStalk (M : X.Modules) (x : X) : Type u :=
  AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (M.presheaf.stalk x)

/-- The canonical map from the stalk of `M` at `x` to its `𝔪_x`-adic completion. -/
noncomputable abbrev toCompletedStalk (M : X.Modules) (x : X) :
    M.presheaf.stalk x →ₗ[X.presheaf.stalk x] completedStalk M x :=
  AdicCompletion.of _ _

end Scheme.Modules

/-!
### Finite type and coherence of a pushforward along a closed immersion

Unlike quasi-coherence, which is stable under pushforward along any affine morphism, finite type
requires the morphism to be a closed immersion: the argument on an affine chart `V` of the target
is that `Γ(M, f ⁻¹ᵁ V)` is a finite `Γ(X, f ⁻¹ᵁ V)`-module by
`AlgebraicGeometry.Scheme.Modules.isCoherent_iff`, and that this makes it a finite
`Γ(Y, V)`-module because `Γ(Y, V) ⟶ Γ(X, f ⁻¹ᵁ V)` is surjective. No Noetherian hypothesis is
needed anywhere.
-/

namespace Scheme.Modules

variable {S : CommRingCat.{u}} {X Y : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- **Being of finite type is stable under restriction to an open subscheme.** -/
instance isFiniteType_restrictFunctor (f : Y ⟶ X) [IsOpenImmersion f] (P : X.Modules)
    [P.IsFiniteType] : ((restrictFunctor f).obj P).IsFiniteType := by
  obtain ⟨q, hq⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData (M := P)
  set W : q.I → X.Opens := q.X with hW
  have h : ∀ i, ∃ G : ((P.restrict f).restrict (f ⁻¹ᵁ W i).ι).GeneratingSections,
      G.IsFiniteType := by
    intro i
    have := hq.isFiniteType i
    obtain ⟨G, hG⟩ := exists_generatingSections_restrict (f ∣_ W i) (P.restrict (W i).ι)
      (generatingSectionsOfOver P (W i) (q.generators i))
    exact ⟨G.ofEpi ((restrictFunctorCompMorphismRestrictIso f (W i)).app P).hom, inferInstance⟩
  choose G hG using h
  refine isFiniteType_of_generatingSections (P.restrict f) (fun i ↦ f ⁻¹ᵁ W i) ?_ G hG
  have hcov : IsOpenCover W := (Opens.coversTop_iff _ q.X).mp q.coversTop
  rw [IsOpenCover] at hcov ⊢
  rw [← Scheme.Hom.preimage_iSup, hcov, Scheme.Hom.preimage_top]

set_option backward.isDefEq.respectTransparency false in
/-- **A quasi-coherent sheaf of modules of finite type on an affine scheme has a finite module
of global sections.** This is the `SheafOfModules.IsQuasicoherent` plus
`SheafOfModules.IsFiniteType` form of `AlgebraicGeometry.Scheme.Modules.isCoherent_iff`. -/
theorem finite_moduleSpecΓ_of_isFiniteType (P : (Spec R).Modules) [P.IsQuasicoherent]
    [P.IsFiniteType] : Module.Finite R (moduleSpecΓFunctor.obj P) := by
  have : IsIso P.fromTildeΓ := (isQuasicoherent_iff_isIso_fromTildeΓ P).mp inferInstance
  have : (tilde (moduleSpecΓFunctor.obj P)).IsFiniteType :=
    SheafOfModules.isFiniteType_of_iso.{u, u, u} (asIso P.fromTildeΓ).symm
  exact tilde.finite_of_isFiniteType _

set_option backward.isDefEq.respectTransparency false in
/-- **A quasi-coherent sheaf of modules of finite type on an affine scheme is generated by
finitely many global sections.** -/
theorem exists_generatingSections_of_isAffine [IsAffine X] (P : X.Modules) [P.IsQuasicoherent]
    [P.IsFiniteType] : ∃ G : P.GeneratingSections, G.IsFiniteType := by
  obtain ⟨G, hG⟩ := exists_generatingSections_of_finite (P.restrict X.isoSpec.inv)
    (finite_moduleSpecΓ_of_isFiniteType _)
  obtain ⟨G', hG'⟩ := exists_generatingSections_restrict X.isoSpec.hom _ G
  exact ⟨G'.ofEpi ((restrictFunctorInvCompIso X.isoSpec).app P).hom, inferInstance⟩

open scoped ModuleCat.Algebra in
/-- **Being of finite type is stable under pushforward along a surjection of affine
spectra.** Surjectivity enters through `Module.Finite.trans`: the global sections are already
finite over `S`, and `S` is finite over `R` because it is a quotient of it. -/
theorem isFiniteType_pushforward_specMap (φ : R ⟶ S) (hφ : Function.Surjective φ.hom)
    (P : (Spec S).Modules) [P.IsQuasicoherent] [P.IsFiniteType] :
    ((pushforward (Spec.map φ)).obj P).IsFiniteType := by
  have hP : Module.Finite S (moduleSpecΓFunctor.obj P) := finite_moduleSpecΓ_of_isFiniteType P
  have h₁ : Module.Finite R
      ((ModuleCat.restrictScalars φ.hom).obj (moduleSpecΓFunctor.obj P)) := by
    algebraize [φ.hom]
    have hRS : Module.Finite R S := Module.Finite.of_surjective (Algebra.linearMap R S) hφ
    let _ : Module S ((ModuleCat.restrictScalars φ.hom).obj (moduleSpecΓFunctor.obj P)) :=
      inferInstanceAs (Module S (moduleSpecΓFunctor.obj P))
    have : IsScalarTower R S
        ((ModuleCat.restrictScalars φ.hom).obj (moduleSpecΓFunctor.obj P)) :=
      .of_algebraMap_smul fun _ _ ↦ rfl
    have : Module.Finite S
        ((ModuleCat.restrictScalars φ.hom).obj (moduleSpecΓFunctor.obj P)) :=
      inferInstanceAs (Module.Finite S (moduleSpecΓFunctor.obj P))
    exact Module.Finite.trans S _
  -- the source of `(moduleSpecΓPushforwardIso φ).app P` is spelled as a composite of functors
  have h₂ : Module.Finite R
      ((moduleSpecΓFunctor ⋙ ModuleCat.restrictScalars φ.hom).obj P) := h₁
  have hfin : Module.Finite R
      (moduleSpecΓFunctor.obj ((pushforward (Spec.map φ)).obj P)) :=
    Module.Finite.equiv ((moduleSpecΓPushforwardIso φ).app P).symm.toLinearEquiv
  -- the source of `fromTildeΓ` is definitionally, but not syntactically, `moduleSpecΓFunctor`
  have : Module.Finite R ((modulesSpecToSheaf.obj
    ((pushforward (Spec.map φ)).obj P)).presheaf.obj (.op ⊤)) := ‹_›
  have : IsIso P.fromTildeΓ := isIso_fromTildeΓ_of_isQuasicoherent P
  have hiso : IsIso ((pushforward (Spec.map φ)).obj P).fromTildeΓ :=
    isIso_fromTildeΓ_pushforward φ P
  exact SheafOfModules.isFiniteType_of_iso.{u, u, u}
    (asIso ((pushforward (Spec.map φ)).obj P).fromTildeΓ)

/-- Being of finite type may be checked after restricting along an isomorphism of schemes. -/
lemma isFiniteType_of_restrict_isIso (f : X ⟶ Y) [IsIso f] (P : Y.Modules)
    [(P.restrict f).IsFiniteType] : P.IsFiniteType := by
  have : ((restrictFunctor f ⋙ restrictFunctor (inv f)).obj P).IsFiniteType :=
    inferInstanceAs ((P.restrict f).restrict (inv f)).IsFiniteType
  exact SheafOfModules.isFiniteType_of_iso.{u, u, u} ((restrictFunctorCompInvIso (f := f)).app P)

/-- **Being of finite type is stable under pushforward along an isomorphism.** -/
instance isFiniteType_pushforward_of_isIso (f : X ⟶ Y) [IsIso f] (P : X.Modules)
    [P.IsFiniteType] : ((pushforward f).obj P).IsFiniteType := by
  have h₀ : ((𝟭 X.Modules).obj P).IsFiniteType := inferInstanceAs P.IsFiniteType
  have h : (((pushforward f).obj P).restrict f).IsFiniteType :=
    SheafOfModules.isFiniteType_of_iso.{u, u, u} ((restrictFunctorAdjCounitIso f).app P).symm
  exact isFiniteType_of_restrict_isIso f _

/-- **Being of finite type is stable under pushforward along a closed immersion of affine
schemes.** -/
theorem isFiniteType_pushforward_of_isAffine [IsAffine X] [IsAffine Y] (f : X ⟶ Y)
    [IsClosedImmersion f] (P : X.Modules) [P.IsQuasicoherent] [P.IsFiniteType] :
    ((pushforward f).obj P).IsFiniteType := by
  have hφ : Function.Surjective f.appTop.hom :=
    (IsClosedImmersion.isAffine_surjective_of_isAffine f).2
  have hf : X.isoSpec.hom ≫ Spec.map f.appTop ≫ Y.isoSpec.inv = f := by
    rw [Scheme.isoSpec_inv_naturality]
    simp
  have e : pushforward X.isoSpec.hom ⋙
      pushforward (Spec.map f.appTop) ⋙ pushforward Y.isoSpec.inv ≅ pushforward f :=
    Functor.isoWhiskerLeft _ (pushforwardComp _ _) ≪≫ pushforwardComp _ _ ≪≫
      pushforwardCongr hf
  have h : ((pushforward (Spec.map f.appTop)).obj
      ((pushforward X.isoSpec.hom).obj P)).IsFiniteType :=
    isFiniteType_pushforward_specMap f.appTop hφ _
  have h' : ((pushforward X.isoSpec.hom ⋙ pushforward (Spec.map f.appTop) ⋙
      pushforward Y.isoSpec.inv).obj P).IsFiniteType :=
    inferInstanceAs ((pushforward Y.isoSpec.inv).obj ((pushforward (Spec.map f.appTop)).obj
      ((pushforward X.isoSpec.hom).obj P))).IsFiniteType
  exact SheafOfModules.isFiniteType_of_iso.{u, u, u} (e.app P)

/-- The restriction of `f _* M` to an affine open `V` of `Y` is of finite type, if `f` is a
closed immersion and `M` is quasi-coherent of finite type. -/
lemma isFiniteType_restrict_pushforward (f : X ⟶ Y) [IsClosedImmersion f] (P : X.Modules)
    [P.IsQuasicoherent] [P.IsFiniteType] {V : Y.Opens} (hV : IsAffineOpen V) :
    (((pushforward f).obj P).restrict V.ι).IsFiniteType := by
  have : IsAffine V.toScheme := hV
  have : IsAffine (f ⁻¹ᵁ V).toScheme := hV.preimage f
  have h₀ : ((pushforward (f ∣_ V)).obj (P.restrict (f ⁻¹ᵁ V).ι)).IsFiniteType :=
    isFiniteType_pushforward_of_isAffine (f ∣_ V) (P.restrict (f ⁻¹ᵁ V).ι)
  have h : ((restrictFunctor (f ⁻¹ᵁ V).ι ⋙ pushforward (f ∣_ V)).obj P).IsFiniteType :=
    inferInstanceAs ((pushforward (f ∣_ V)).obj (P.restrict (f ⁻¹ᵁ V).ι)).IsFiniteType
  exact SheafOfModules.isFiniteType_of_iso.{u, u, u}
    ((pushforwardCompRestrictFunctorIso f V).app P).symm

/-- **Being of finite type is stable under pushforward along a closed immersion.**

Quasi-coherence of `M` is part of the hypotheses because the proof reads off the sections of `M`
over an affine open, which only finite type together with quasi-coherence controls; no Noetherian
hypothesis on `Y` is needed. -/
instance isFiniteType_pushforward (f : X ⟶ Y) [IsClosedImmersion f] (P : X.Modules)
    [P.IsQuasicoherent] [P.IsFiniteType] : ((pushforward f).obj P).IsFiniteType := by
  have h : ∀ i, ∃ G : (((pushforward f).obj P).restrict
      (Y.affineOpenCover.f i).opensRange.ι).GeneratingSections, G.IsFiniteType := by
    intro i
    have hV : IsAffineOpen (Y.affineOpenCover.f i).opensRange := isAffineOpen_opensRange _
    have : IsAffine (Y.affineOpenCover.f i).opensRange.toScheme := hV
    have := isFiniteType_restrict_pushforward f P hV
    exact exists_generatingSections_of_isAffine _
  choose G hG using h
  exact isFiniteType_of_generatingSections _ (fun i ↦ (Y.affineOpenCover.f i).opensRange)
    Y.affineOpenCover.openCover.iSup_opensRange G hG

/-- **Coherence is stable under pushforward along a closed immersion**, with no Noetherian
hypothesis on the schemes involved. -/
instance isCoherent_pushforward_of_isClosedImmersion (f : X ⟶ Y) [IsClosedImmersion f]
    (P : X.Modules)
    [P.IsCoherent] : ((pushforward f).obj P).IsCoherent where

end Scheme.Modules

end AlgebraicGeometry
