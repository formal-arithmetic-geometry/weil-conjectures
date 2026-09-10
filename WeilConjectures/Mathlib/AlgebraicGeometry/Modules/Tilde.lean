/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Module.LocalizedModule.Away
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Coherence of `M^~` on an affine scheme

For a commutative ring `R` and an `R`-module `M`, the quasi-coherent sheaf `M^~` on `Spec R` is
coherent as soon as `M` is a finite `R`-module, and conversely a finite family of global sections
generating `M^~` generates `M`.

The second half of the file establishes that the sections of a quasi-coherent sheaf over a
basic open subset of an affine open are the corresponding localization, and deduces that its
stalk at a point of an affine open is the localization of the sections at the prime of that
point. This is what makes affine-local definitions in terms of the module of sections well
posed.

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
-/

@[expose] public noncomputable section

universe u

open CategoryTheory Limits SheafOfModules

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

end AlgebraicGeometry
