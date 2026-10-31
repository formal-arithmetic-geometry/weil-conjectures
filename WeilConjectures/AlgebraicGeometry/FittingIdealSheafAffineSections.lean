/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoherentFiniteType
public import WeilConjectures.AlgebraicGeometry.FittingIdealSheaf
public import WeilConjectures.RingTheory.PresentationFittingIdeal
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import WeilConjectures.AlgebraicGeometry.Modules.ClosedImmersion
import Mathlib.RingTheory.Finiteness.Cardinality

/-!
# Affine sections of the Fitting ideal sheaf

Source: Stacks Project, Divisors, Tag 0C3C, first paragraph; More on Algebra,
Tag 07ZA(3) (blueprint: lem-trf-fitting-ideal-sheaf-affine-sections).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

private theorem presentationSup_eq {R M : Type u} [CommRing R] [AddCommGroup M]
    [Module R M] [Module.Finite R M] (r : ℕ) {n : ℕ}
    (π : (Fin n → R) →ₗ[R] M) (hπ : Function.Surjective π) :
    (⨆ (n' : ℕ) (π' : (Fin n' → R) →ₗ[R] M) (_hπ' : Function.Surjective π'),
      π'.presentationFittingIdeal r) = π.presentationFittingIdeal r := by
  apply le_antisymm
  · refine iSup_le fun n' ↦ iSup_le fun π' ↦ iSup_le fun hπ' ↦ ?_
    exact ((LinearMap.presentationFittingIdeal_independence_baseChange.{u, u, u}
      r π hπ).1 n' π' hπ').ge
  · exact le_iSup_of_le n (le_iSup_of_le π (le_iSup_of_le hπ le_rfl))

private theorem presentationFittingIdeal_postcomp {R M N : Type u} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {n : ℕ} (π : (Fin n → R) →ₗ[R] M) (e : M ≃ₗ[R] N) (r : ℕ) :
    (e.toLinearMap.comp π).presentationFittingIdeal r = π.presentationFittingIdeal r := by
  unfold LinearMap.presentationFittingIdeal
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, EmbeddingLike.map_eq_zero_iff]

private theorem presentationSup_basicOpen {S : Scheme.{u}} (F : S.Modules)
    [F.IsFiniteType] [F.IsQuasicoherent] (r : ℕ) (U : S.affineOpens) (f : Γ(S, U.1)) :
    Ideal.map (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom
      (⨆ (n : ℕ) (π : (Fin n → Γ(S, U.1)) →ₗ[Γ(S, U.1)] Γ(F, U.1))
        (_hπ : Function.Surjective π), π.presentationFittingIdeal r) =
      ⨆ (n : ℕ)
        (π : (Fin n → Γ(S, S.basicOpen f)) →ₗ[Γ(S, S.basicOpen f)] Γ(F, S.basicOpen f))
        (_hπ : Function.Surjective π), π.presentationFittingIdeal r := by
  have := finite_sections_of_finiteType F U.2
  have := finite_sections_of_finiteType F (U.2.basicOpen f)
  let : Module Γ(S, U.1) Γ(F, S.basicOpen f) :=
    Module.compHom _ (algebraMap Γ(S, U.1) Γ(S, S.basicOpen f))
  have : IsScalarTower Γ(S, U.1) Γ(S, S.basicOpen f) Γ(F, S.basicOpen f) :=
    ⟨fun a b m ↦ mul_smul _ _ _⟩
  let ρ : Γ(F, U.1) →ₗ[Γ(S, U.1)] Γ(F, S.basicOpen f) :=
    { toFun := F.presheaf.map (homOfLE (S.basicOpen_le f)).op
      map_add' := map_add _
      map_smul' := map_smul F _ }
  have := U.2.isLocalization_basicOpen f
  have := isLocalizedModule_basicOpen F U.2 f
  let e := (IsLocalizedModule.isBaseChange (.powers f) Γ(S, S.basicOpen f) ρ).equiv
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' Γ(S, U.1) Γ(F, U.1)
  have hb := (π.presentationFittingIdeal_independence_baseChange r hπ).2.1
    Γ(S, S.basicOpen f)
  rw [presentationSup_eq r π hπ,
    presentationSup_eq r (e.toLinearMap.comp (π.baseChangePresentation Γ(S, S.basicOpen f)))
      (e.surjective.comp hb.1), presentationFittingIdeal_postcomp, hb.2]
  rfl

private theorem fittingIdealSheaf_ideal_eq {S : Scheme.{u}} (F : S.Modules)
    [F.IsFiniteType] [F.IsQuasicoherent] (r : ℕ) (U : S.affineOpens) (n : ℕ)
    (π : (Fin n → Γ(S, U.1)) →ₗ[Γ(S, U.1)] Γ(F, U.1))
    (hπ : Function.Surjective π) :
    (fittingIdealSheaf F r).ideal U = π.presentationFittingIdeal r := by
  let J : S.IdealSheafData :=
    { ideal V := ⨆ (m : ℕ) (p : (Fin m → Γ(S, V.1)) →ₗ[Γ(S, V.1)] Γ(F, V.1))
        (_hp : Function.Surjective p), p.presentationFittingIdeal r
      map_ideal_basicOpen := presentationSup_basicOpen F r }
  have h : fittingIdealSheaf F r = J := IdealSheafData.ofIdeals_ideal J
  rw [h]
  have := finite_sections_of_finiteType F U.2
  exact presentationSup_eq r π hπ

private theorem ideal_restrict_tilde {S : Scheme.{u}} (J : S.IdealSheafData)
    (U : S.affineOpens) :
    ∃ e : tilde (ModuleCat.of Γ(S, U.1) (J.ideal U)) ≅ J.toModules.restrict U.2.fromSpec,
      e.hom ≫ (restrictFunctor U.2.fromSpec).map J.toModulesι ≫
          (restrictUnitIso U.2.fromSpec).hom =
        tilde.map (ModuleCat.ofHom (J.ideal U).subtype) ≫
          (tildeSelf (R := Γ(S, U.1))).hom := by
  have := SheafOfModules.isQuasicoherent_unit (R := J.subscheme.ringCatSheaf)
  have := SheafOfModules.isQuasicoherent_unit (R := S.ringCatSheaf)
  have : SheafOfModules.IsQuasicoherent (R := S.ringCatSheaf)
      ((SheafOfModules.pushforward J.subschemeι.toRingCatSheafHom).obj
        (SheafOfModules.unit J.subscheme.ringCatSheaf)) :=
    isQuasicoherent_pushforward_of_isClosedImmersion J.subschemeι _
  have : J.toModules.IsQuasicoherent := isQuasicoherent_kernel J.toPushforwardSubscheme
  let N := J.toModules.restrict U.2.fromSpec
  have : N.IsQuasicoherent := isQuasicoherent_restrictFunctor U.2.fromSpec J.toModules
  have : IsIso N.fromTildeΓ := isIso_fromTildeΓ_of_isQuasicoherent N
  let A := ModuleCat.of Γ(S, U.1) (J.ideal U)
  let l : Γ(J.toModules, U.1) →ₗ[Γ(S, U.1)] J.ideal U :=
    (J.toModulesι.val.app (.op U.1)).hom.codRestrict (J.ideal U) fun x ↦
      (J.range_toModulesι_app U).subset ⟨x, rfl⟩
  have hl : Function.Bijective l := by
    constructor
    · intro x y h
      apply J.injective_toModulesι_app U.1
      exact congrArg Subtype.val h
    · intro x
      obtain ⟨y, hy⟩ := (J.range_toModulesι_app U).symm.subset x.property
      exact ⟨y, Subtype.ext hy⟩
  let q := (LinearEquiv.ofBijective l hl).symm
  have hq (x : J.ideal U) : J.toModulesι.app U.1 (q x) = (x : Γ(S, U.1)) :=
    congrArg Subtype.val ((LinearEquiv.ofBijective l hl).apply_symm_apply x)
  let d := q.trans (sectionsTopRestrictFromSpecEquiv J.toModules U.2).symm
  let e : tilde A ≅ N := (tilde.functor Γ(S, U.1)).mapIso d.toModuleIso ≪≫
    asIso N.fromTildeΓ
  have he (x : A) : e.hom.app ⊤ (tilde.toOpen A ⊤ x) = d x := by
    change N.fromTildeΓ.app ⊤ ((tilde.map d.toModuleIso.hom).app ⊤
      (tilde.toOpen A ⊤ x)) = d x
    have hm := congr($(tilde.toOpen_map_app d.toModuleIso.hom ⊤) x)
    change (tilde.map d.toModuleIso.hom).app ⊤ (tilde.toOpen A ⊤ x) =
      tilde.toOpen (moduleSpecΓFunctor.obj N) ⊤ (d x) at hm
    rw [hm]
    have h := congr($(toOpen_fromTildeΓ_app N ⊤) (d x))
    refine h.trans ?_
    change N.presheaf.map (𝟙 _) (d x) = d x
    rw [CategoryTheory.Functor.map_id]
    rfl
  refine ⟨e, ?_⟩
  apply (tilde.adjunction.homEquiv _ _).injective
  ext x
  change ((e.hom ≫ (restrictFunctor U.2.fromSpec).map J.toModulesι ≫
    (restrictUnitIso U.2.fromSpec).hom).app ⊤) (tilde.toOpen A ⊤ x) =
      ((tilde.map (ModuleCat.ofHom (J.ideal U).subtype) ≫
        (tildeSelf (R := Γ(S, U.1))).hom).app ⊤) (tilde.toOpen A ⊤ x)
  simp only [Hom.comp_app, ConcreteCategory.comp_apply, he]
  have hm := congr($(tilde.toOpen_map_app (ModuleCat.ofHom (J.ideal U).subtype) ⊤) x)
  change (tilde.map (ModuleCat.ofHom (J.ideal U).subtype)).app ⊤
      (tilde.toOpen A ⊤ x) = tilde.toOpen (ModuleCat.of Γ(S, U.1) Γ(S, U.1)) ⊤
        (x : Γ(S, U.1)) at hm
  rw [hm]
  change (U.2.fromSpec.appIso ⊤).hom
      (J.toModulesι.app (U.2.fromSpec ''ᵁ ⊤)
        (J.toModules.presheaf.map (homOfLE (U.2.fromSpec_image_le ⊤)).op (q x))) =
    (Scheme.ΓSpecIso Γ(S, U.1)).inv (x : Γ(S, U.1))
  have hn := congr($(J.toModulesι.mapPresheaf.naturality
    (homOfLE (U.2.fromSpec_image_le ⊤)).op) (q x))
  change J.toModulesι.app (U.2.fromSpec ''ᵁ ⊤)
      (J.toModules.presheaf.map (homOfLE (U.2.fromSpec_image_le ⊤)).op (q x)) =
    S.presheaf.map (homOfLE (U.2.fromSpec_image_le ⊤)).op
      (J.toModulesι.app U.1 (q x)) at hn
  rw [hn, hq]
  apply (ConcreteCategory.bijective_of_isIso (U.2.fromSpec.appIso ⊤).inv).1
  rw [Iso.hom_inv_id_apply]
  have hr := congr($(U.2.ΓSpecIso_inv_map_appIso_inv ⊤) (x : Γ(S, U.1)))
  simpa only [ConcreteCategory.comp_apply, show
    (TopologicalSpace.Opens.leTop (⊤ : (Spec Γ(S, U.1)).Opens)).op = 𝟙 _ from rfl,
    CategoryTheory.Functor.map_id, ConcreteCategory.id_apply] using hr.symm

/-- The largest bounded quasi-coherent ideal construction has the kernel-minor ideal as
its sections on every affine open. Its restriction is the tilde of that ideal, with the
isomorphism commuting with the inclusions into the structure sheaf. The affine open is
identified with its canonical spectrum by `U.2.fromSpec`.
Source: Stacks Project, Divisors, Tag 0C3C, first paragraph; More on Algebra, Tag 07ZA(3).
(blueprint: lem-trf-fitting-ideal-sheaf-affine-sections)

Proof:
1. On each affine open V, `lem-weil-pbc-quasi-coherent-finite-type-affine` makes F(V)
   finitely generated, so a finite free surjection exists. By
   `lem-trf-fitting-ideal-independence-base-change` (1), all its presentation ideals
   are one ideal L_V. The nonempty supremum J_V used in
   `def-trf-fitting-ideal-sheaf` is therefore L_V; in particular J_U = I_r(pi).
2. For f in O(V), `lem-weil-pbc-affine-ideals-closed-subscheme` (0) identifies V_f
   as affine with localized section ring. The counit of
   `lem-weil-pbc-affine-tilde-gamma-adjunction` (3), normalized by its unit (2), and
   `lem-weil-pbc-spec-module-tilde-sections` identify F(V_f) with F(V)_f and section
   restriction with m -> m/1. Localizing a presentation and applying
   `lem-trf-fitting-ideal-independence-base-change` (2) gives J_(V_f) = J_V O(V_f).
   Composing with this module isomorphism leaves the presentation kernel unchanged.
3. Apply `lem-weil-pbc-affine-ideals-closed-subscheme` (1) to the compatible family
   J_V. It gives a closed immersion with kernel ideal sheaf K and K(V) = J_V.
   By `def-sbc-closed-immersion-ideal-sheaf`, K is quasi-coherent and its restriction
   to U is the associated ideal subsheaf of J_U. No finite presentation or hypothesis
   on intersections of affine opens is needed.
4. K satisfies the bounds defining `fittingIdealSheaf`, so maximality gives K <= Fit.
   The upper bound gives J_V = K(V) <= Fit(V) <= J_V on every affine V.
   Hence Fit(U) = I_r(pi). On arbitrary opens, equality follows by restricting to
   affine covers and applying the subsheaf gluing axiom, so Fit = K. Restrict to U
   and use step 3 to obtain the displayed isomorphism over the structure sheaf.
-/
theorem fittingIdealSheaf_affine_sections {S : Scheme.{u}} (F : S.Modules)
    [F.IsFiniteType] [F.IsQuasicoherent] (r : ℕ) (U : S.affineOpens) (n : ℕ)
    (π : (Fin n → Γ(S, U.1)) →ₗ[Γ(S, U.1)] Γ(F, U.1))
    (hπ : Function.Surjective π) :
    (fittingIdealSheaf F r).ideal U = π.presentationFittingIdeal r ∧
      ∃ e : tilde (ModuleCat.of Γ(S, U.1) (π.presentationFittingIdeal r)) ≅
          (fittingIdealSheaf F r).toModules.restrict U.2.fromSpec,
        e.hom ≫ (restrictFunctor U.2.fromSpec).map (fittingIdealSheaf F r).toModulesι ≫
            (restrictUnitIso U.2.fromSpec).hom =
          tilde.map (ModuleCat.ofHom (π.presentationFittingIdeal r).subtype) ≫
            (tildeSelf (R := Γ(S, U.1))).hom := by
  have h := fittingIdealSheaf_ideal_eq F r U n π hπ
  refine ⟨h, ?_⟩
  rw [← h]
  exact ideal_restrict_tilde (fittingIdealSheaf F r) U

end AlgebraicGeometry.Scheme.Modules
