/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P1
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Sheaf.Paper.DerivedHomMayerVietoris
public import Mathlib.Algebra.Module.LocalizedModule.Away
public import Mathlib.RingTheory.Finiteness.Projective
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.RingTheory.FiniteProjectiveStandardFreeCover

/-! # Finite local freeness from finite projective principal localizations

Source: Stacks Project, Tag 00NX, (2) implies (7), and Tag 08EG, local freeness paragraph.
(blueprint: lem-sc-principal-open-finite-projective-tilde).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
private theorem sectionsLocalizationEquiv (R : CommRingCat.{u}) (M : ModuleCat.{u} R)
    (r : R) :
    Nonempty ((moduleSpecΓFunctor (R := CommRingCat.of (Localization.Away r))).obj
      ((tilde M).restrict (Spec.map
        (show R ⟶ .of (Localization.Away r) from
          CommRingCat.ofHom (algebraMap R (Localization.Away r)))))
      ≃ₗ[Localization.Away r] LocalizedModule.Away r M) := by
  let S : CommRingCat.{u} := .of (Localization.Away r)
  let φ : R ⟶ S := CommRingCat.ofHom (algebraMap R (Localization.Away r))
  let j := Spec.map φ
  let H := tilde M
  let N := H.restrict j
  have hU : j ''ᵁ ⊤ = PrimeSpectrum.basicOpen r := by
    rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.opensRange_localizationAway]
  let X : ModuleCat S := moduleSpecΓFunctor.obj N
  let : Module R X := Module.compHom X φ.hom
  have : IsScalarTower R (Localization.Away r) X := ⟨fun a s x ↦ by
    rw [Algebra.smul_def, mul_smul]
    rfl⟩
  let ι₀ : (modulesSpecToSheaf.obj H).obj.obj (Opposite.op (j ''ᵁ ⊤)) ≃ₗ[R] X :=
    { toFun x := x
      invFun x := x
      map_add' _ _ := rfl
      map_smul' a x := (Scheme.Modules.restrictAppIso_smul_Spec (M := H) φ a
        (x : N.val.obj (Opposite.op ⊤))).symm
      left_inv _ := rfl
      right_inv _ := rfl }
  let ρ := (tilde.toOpen M (j ''ᵁ ⊤)).hom
  have hρ : IsLocalizedModule (.powers r) ρ := by
    dsimp [ρ]
    rw [hU]
    infer_instance
  have : IsLocalizedModule (.powers r) (ι₀.toLinearMap ∘ₗ ρ) :=
    IsLocalizedModule.of_linearEquiv (.powers r) _ ι₀
  let e := IsLocalizedModule.iso (.powers r) (ι₀.toLinearMap ∘ₗ ρ)
  exact ⟨(e.extendScalarsOfIsLocalization (.powers r) (Localization.Away r)).symm⟩

private theorem exists_free_neighborhood_of_projective_sections
    (R : CommRingCat.{u}) (N : (Spec R).Modules) [N.IsQuasicoherent]
    [Module.Finite R (moduleSpecΓFunctor.obj N)]
    [Module.Projective R ((moduleSpecΓFunctor (R := R)).obj N)] (x : Spec R) :
    ∃ (Y : Scheme.{u}) (j : Y ⟶ Spec R) (_ : IsOpenImmersion j) (κ : Type u)
      (_ : Finite κ), x ∈ j.opensRange ∧
      Nonempty (N.restrict j ≅ SheafOfModules.free κ) := by
  classical
  let P := moduleSpecΓFunctor.obj N
  obtain ⟨n, g, hg, hfree⟩ := Module.exists_standardFreeCover_of_finite_projective R P
  have hcov : ⨆ i, PrimeSpectrum.basicOpen (g i) = ⊤ :=
    PrimeSpectrum.iSup_basicOpen_eq_top_iff.mpr hg
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (hcov.ge (Set.mem_univ x))
  have := (hfree i).1
  have := (hfree i).2
  let κ := Module.Free.ChooseBasisIndex (Localization.Away (g i))
    (LocalizedModule.Away (g i) P)
  let j := Spec.map (show R ⟶ .of (Localization.Away (g i)) from
    CommRingCat.ofHom (algebraMap R (Localization.Away (g i))))
  refine ⟨_, j, inferInstance, κ, inferInstance, ?_, ?_⟩
  · rwa [Scheme.Hom.opensRange_localizationAway]
  · exact Scheme.Modules.nonempty_restrict_iso_free_of_localizedModule N (g i)
      (Module.Free.chooseBasis (Localization.Away (g i))
        (LocalizedModule.Away (g i) P)).repr

set_option backward.isDefEq.respectTransparency false in
/-- A module whose principal localizations inside an open are finite projective has
finite locally free associated sheaf on that open.
Source: Stacks Project, Tag 00NX, (2) implies (7); Tag 08EG, local freeness paragraph.
(blueprint: lem-sc-principal-open-finite-projective-tilde).

Proof: For each point x of U choose a principal open D(f) containing x and contained
in U. Its ring is A_f and the associated sheaf restricts to the sheaf associated with
M_f, by the localization description of tilde. The hypothesis makes M_f finite
projective. Apply lem-weil-pbc-finite-projective-standard-free-cover to M_f over A_f.
The resulting finitely many standard opens D(g) cover Spec A_f; each corresponding
localized module is finite free. Under D(f) = Spec A_f these are open neighbourhoods
in U, and localization of associated sheaves identifies their restrictions with free
sheaves of the same finite ranks. Compose their open immersions with D(f) into U.
The resulting family over all x covers U. The sheaf definition of finite local freeness
then supplies the conclusion, with no common rank required. Empty U has the empty
cover; the zero module has rank zero; no finiteness of M on all of Spec A is assumed.
-/
theorem finiteLocallyFree_restrict_tilde_of_principalOpen_projective
    (A : Type u) [CommRing A] (U : (Spec (.of A)).Opens) (M : ModuleCat.{u} A)
    (h : ∀ f : A, PrimeSpectrum.basicOpen f ≤ U →
      Module.Finite (Localization.Away f) (LocalizedModule.Away f M) ∧
        Module.Projective (Localization.Away f) (LocalizedModule.Away f M)) :
    SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (((@id (ModuleCat.{u} A ⥤
          SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
          (tilde.functor (.of A))) ⋙
        SheafOfModules.overFunctor (moduleRings (Spec (.of A)).toRingedSpace) U ⋙
        Equivalence.functor
          (C := SheafOfModules.{u} ((moduleRings (Spec (.of A)).toRingedSpace).over U))
          (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
          (Scheme.Modules.overEquiv U)).obj M) := by
  classical
  let H := tilde (R := CommRingCat.of A) M
  let F := H.restrict U.ι
  have key (x : U.toScheme) :
      ∃ (Y : Scheme.{u}) (j : Y ⟶ U.toScheme) (_ : IsOpenImmersion j) (κ : Type u)
        (_ : Finite κ), x ∈ j.opensRange ∧
        Nonempty (F.restrict j ≅ SheafOfModules.free κ) := by
    obtain ⟨_, ⟨_, ⟨f, rfl⟩, rfl⟩, hxf, hf⟩ :=
      PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open x.2 U.2
    let R : CommRingCat.{u} := .of (Localization.Away f)
    let a : CommRingCat.of A ⟶ R :=
      CommRingCat.ofHom (algebraMap A (Localization.Away f))
    let j₀ := Spec.map a
    have hrange : Set.range j₀ ⊆ Set.range U.ι := by
      intro y hy
      have hy' : y ∈ j₀.opensRange := hy
      rw [show j₀.opensRange = PrimeSpectrum.basicOpen f from
        Scheme.Hom.opensRange_localizationAway (R := CommRingCat.of A) f] at hy'
      exact ⟨⟨y, hf hy'⟩, rfl⟩
    let j₁ := IsOpenImmersion.lift U.ι j₀ hrange
    have hj₁ : j₁ ≫ U.ι = j₀ := IsOpenImmersion.lift_fac _ _ _
    have : IsOpenImmersion j₁ := by
      apply IsOpenImmersion.of_comp j₁ U.ι
    let N := H.restrict j₀
    obtain ⟨e⟩ := sectionsLocalizationEquiv (.of A) M f
    have : Module.Finite (Localization.Away f) (LocalizedModule.Away f M) := (h f hf).1
    have hfin : Module.Finite R ((moduleSpecΓFunctor (R := R)).obj N) :=
      Module.Finite.equiv e.symm
    have hproj : Module.Projective R ((moduleSpecΓFunctor (R := R)).obj N) := by
      have := (h f hf).2
      exact Module.Projective.of_equiv e.symm
    have hx₀ : x.1 ∈ j₀.opensRange := by
      rw [show j₀.opensRange = PrimeSpectrum.basicOpen f from
        Scheme.Hom.opensRange_localizationAway (R := CommRingCat.of A) f]
      exact hxf
    obtain ⟨z, hz⟩ := hx₀
    obtain ⟨Y, j₂, hj₂, κ, hκ, hz₂, ⟨e₂⟩⟩ :=
      exists_free_neighborhood_of_projective_sections R N z
    refine ⟨Y, j₂ ≫ j₁, inferInstance, κ, hκ, ?_, ⟨?_⟩⟩
    · obtain ⟨y, hy⟩ := hz₂
      refine ⟨y, ?_⟩
      apply Subtype.ext
      change U.ι ((j₂ ≫ j₁) y) = x.1
      rw [Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply j₁ U.ι, hj₁, hy, hz]
    · exact ((Scheme.Modules.restrictFunctorComp (j₂ ≫ j₁) U.ι).app H).symm ≪≫
        (Scheme.Modules.restrictFunctorCongr (by simp [Category.assoc, hj₁])).app H ≪≫
        (Scheme.Modules.restrictFunctorComp j₂ j₀).app H ≪≫ e₂
  choose Y j hj κ hκ hx e using key
  have : ∀ x, IsOpenImmersion (j x) := hj
  have : ∀ x, Finite (κ x) := hκ
  have hF : F.IsFiniteLocallyFree :=
    Scheme.Modules.isFiniteLocallyFree_of_restrict_iso_free F j
      (eq_top_iff.mpr fun x _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hx x⟩) κ e
  exact SheafOfModules.IsFiniteLocallyFree.of_iso.{u, u, u}
    ((Scheme.Modules.overFunctorEquiv U).app H).symm

end AlgebraicGeometry
