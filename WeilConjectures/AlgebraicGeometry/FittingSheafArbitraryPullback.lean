/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoherentFiniteType
public import WeilConjectures.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.FittingIdealSheaf
public import WeilConjectures.RingTheory.PresentationFittingIdeal
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import WeilConjectures.AlgebraicGeometry.ModulePullbackFiniteType
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections
import WeilConjectures.AlgebraicGeometry.FittingIdealSheafAffineSections
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Affine
import WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeAffine

/-!
# Fitting ideals and finite generators under arbitrary pullback

Source: Stacks Project, Divisors, Tag 0C3D; Schemes, Tags 01I9 and 01IA;
More on Algebra, Tag 07ZA(3) (blueprint: lem-trf-fitting-sheaf-arbitrary-pullback).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite TopologicalSpace
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.Modules

/-- The module `B ⊗_A F(U)` for the ring map induced by the specified affine pair.
This merely applies Mathlib's extension of scalars to the section module.
Source: Stacks, Schemes, Tag 01I9(1)
(blueprint: lem-trf-fitting-sheaf-arbitrary-pullback). -/
noncomputable def affinePullbackTensor {T S : Scheme.{u}} (g : T ⟶ S) (F : S.Modules)
    (U : S.affineOpens) (V : T.affineOpens) (h : V.1 ≤ g ⁻¹ᵁ U.1) :
    ModuleCat Γ(T, V.1) :=
  (ModuleCat.extendScalars (g.appLE U.1 V.1 h).hom).obj (ModuleCat.of Γ(S, U.1) Γ(F, U.1))

/-- The section `1 ⊗ m` of the affine tensor module, using the extension-of-scalars unit.
Source: Stacks, Schemes, Tag 01I9(1)
(blueprint: lem-trf-fitting-sheaf-arbitrary-pullback). -/
noncomputable def affinePullbackOneTensor {T S : Scheme.{u}} (g : T ⟶ S) (F : S.Modules)
    (U : S.affineOpens) (V : T.affineOpens) (h : V.1 ≤ g ⁻¹ᵁ U.1)
    (m : Γ(F, U.1)) : affinePullbackTensor g F U V h :=
  (ModuleCat.extendRestrictScalarsAdj (g.appLE U.1 V.1 h).hom).unit.app
    (ModuleCat.of Γ(S, U.1) Γ(F, U.1)) m

/-- The specified generating presentation after tensoring with `B`, using the already
recorded `LinearMap.baseChangePresentation` and its canonical finite-free identification.
Source: Stacks, More on Algebra, Tag 07ZA(3)
(blueprint: lem-trf-fitting-sheaf-arbitrary-pullback). -/
noncomputable def affinePullbackPresentation {T S : Scheme.{u}} (g : T ⟶ S)
    (F : S.Modules) (U : S.affineOpens) (V : T.affineOpens)
    (h : V.1 ≤ g ⁻¹ᵁ U.1) {n : ℕ}
    (π : (Fin n → Γ(S, U.1)) →ₗ[Γ(S, U.1)] Γ(F, U.1)) :
    (Fin n → Γ(T, V.1)) →ₗ[Γ(T, V.1)] affinePullbackTensor g F U V h :=
  letI : Algebra Γ(S, U.1) Γ(T, V.1) := (g.appLE U.1 V.1 h).hom.toAlgebra
  π.baseChangePresentation Γ(T, V.1)

private theorem presentationFittingIdeal_comp_equiv {R M N : Type u} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {n : ℕ} (π : (Fin n → R) →ₗ[R] M) (e : M ≃ₗ[R] N) (r : ℕ) :
    (e.toLinearMap.comp π).presentationFittingIdeal r = π.presentationFittingIdeal r := by
  simp only [LinearMap.presentationFittingIdeal, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.map_eq_zero_iff]

private theorem affinePullback_span {T S : Scheme.{u}} (g : T ⟶ S) (F : S.Modules)
    (U : S.affineOpens) (V : T.affineOpens) (h : V.1 ≤ g ⁻¹ᵁ U.1)
    (n : ℕ) (m : Fin n → Γ(F, U.1))
    (hm : Submodule.span Γ(S, U.1) (Set.range m) = ⊤) :
    Submodule.span Γ(T, V.1)
      (Set.range (fun i ↦ affinePullbackOneTensor g F U V h (m i))) = ⊤ := by
  let : Algebra Γ(S, U.1) Γ(T, V.1) := (g.appLE U.1 V.1 h).hom.toAlgebra
  have ht := congrArg (Submodule.baseChange Γ(T, V.1)) hm
  rw [Submodule.baseChange_span, Submodule.baseChange_top, ← Set.range_comp] at ht
  exact ht

private theorem affinePullback_equiv {T S : Scheme.{u}} (g : T ⟶ S) (F : S.Modules)
    [F.IsQuasicoherent] (U : S.affineOpens) (V : T.affineOpens)
    (h : V.1 ≤ g ⁻¹ᵁ U.1) :
    ∃ e : affinePullbackTensor g F U V h ≃ₗ[Γ(T, V.1)]
        Γ((tensorPullback g).obj F, V.1),
      ∀ m : Γ(F, U.1), e (affinePullbackOneTensor g F U V h m) =
        ((tensorPullback g).obj F).presheaf.map (homOfLE h).op
          (tensorPullbackSection g F U.1 m) := by
  classical
  let : Algebra Γ(S, U.1) Γ(T, V.1) := (g.appLE U.1 V.1 h).hom.toAlgebra
  let : ∀ G : S.Modules, Module Γ(S, U.1) Γ((tensorPullback g).obj G, V.1) :=
    fun G ↦ Module.compHom _ (g.appLE U.1 V.1 h).hom
  obtain ⟨c, hbij, hsmul, hpure, _⟩ := exists_tensorPullback_affine_sections g U V h
  let swap := TensorProduct.comm Γ(S, U.1) Γ(F, U.1) Γ(T, V.1)
  let d : Γ(T, V.1) ⊗[Γ(S, U.1)] Γ(F, U.1) →ₗ[Γ(T, V.1)]
      Γ((tensorPullback g).obj F, V.1) :=
    { toFun := fun x ↦ c F inferInstance (swap.symm x)
      map_add' := by intros; simp only [map_add]
      map_smul' := by
        intro b x
        simpa only [swap, LinearEquiv.apply_symm_apply, RingHom.id_apply] using
          hsmul F inferInstance b (swap.symm x) }
  let e := LinearEquiv.ofBijective d ((hbij F inferInstance).comp swap.symm.bijective)
  refine ⟨e, ?_⟩
  intro m
  change c F inferInstance (TensorProduct.tmul Γ(S, U.1) m 1) = _
  rw [hpure, one_smul]
  congr 1
  exact Classical.choose_spec (exists_tensorPullbackAdjunction g) F (op U.1) m

private theorem affinePullback_sheaf_iso {T S : Scheme.{u}} (g : T ⟶ S) (F : S.Modules)
    [((tensorPullback g).obj F).IsQuasicoherent]
    (U : S.affineOpens) (V : T.affineOpens) (h : V.1 ≤ g ⁻¹ᵁ U.1)
    (e : affinePullbackTensor g F U V h ≃ₗ[Γ(T, V.1)]
      Γ((tensorPullback g).obj F, V.1)) :
    Nonempty (((tensorPullback g).obj F).restrict V.1.ι ≅
      (tilde (affinePullbackTensor g F U V h)).restrict V.2.isoSpec.hom) := by
  let G := (tensorPullback g).obj F
  let a := sectionsRestrictFromSpecLinearEquiv G V.2
  let b : G.restrict V.2.fromSpec ≅ tilde (affinePullbackTensor g F U V h) :=
    (asIso (G.restrict V.2.fromSpec).fromTildeΓ).symm ≪≫
      (tilde.functor Γ(T, V.1)).mapIso (a.trans e.symm).toModuleIso
  exact ⟨(restrictFunctorCongr V.2.isoSpec_hom_fromSpec.symm).app G ≪≫
    (restrictFunctorComp V.2.isoSpec.hom V.2.fromSpec).app G ≪≫
      (restrictFunctor V.2.isoSpec.hom).mapIso b⟩

/-- Arbitrary pullback preserves finite type and quasi-coherence, identifies affine
pullback with the associated tensor sheaf, carries every finite generating family to
its tensors with `1`, and extends all Fitting ideals, on affine charts and globally.
The Fitting ideal of a finite module is rendered by every surjective finite-free
presentation, using presentation independence; no finite relation module is required.
Source: Stacks, Divisors, Tag 0C3D; Schemes, Tags 01I9 and 01IA; More on Algebra, 07ZA(3).
(blueprint: lem-trf-fitting-sheaf-arbitrary-pullback)

Proof plan:
1. Apply lem-weil-pbc-module-pullback-finite-type and
   lem-weil-pbc-module-pullback-quasi-coherent to g and F. By
   lem-weil-pbc-quasi-coherent-finite-type-affine, F(U) has finite generators on each
   affine U, hence a finite-free surjection, with no finiteness claimed for its kernel.
2. Apply lem-weil-pbc-module-pullback-affine-sections to U,V. Interchanging tensor
   factors gives the B-linear equivalence e, taking 1 tensor m to the actual pulled-back
   section restricted to V. The tilde functor and counit isomorphism of
   lem-weil-pbc-affine-tilde-gamma-adjunction give the displayed sheaf isomorphism.
3. Write m as a finite linear combination of the given generators. The balancing
   relation expresses b tensor m as the corresponding B-linear combination of their
   tensors with 1, as in def-weil-module-base-change. This includes the empty family.
4. Use lem-trf-fitting-ideal-sheaf-affine-sections for F and its pullback, and
   lem-trf-fitting-ideal-independence-base-change for the original presentation.
   Tensor right exactness supplies the surjectivity after tensoring. Composing with e
   does not change its kernel, so presentation independence gives both affine ideal
   equalities. For r at least the number of generators both ideals are the unit ideal.
5. Pull back the ideal inclusion and compose with the structure-sheaf comparison of
   lem-weil-pbc-module-pullback-structure-sheaf. Its image is quasi-coherent by
   lem-weil-pbc-quasi-coherent-module-cokernel-image and is the ideal locally generated
   by the inverse-image ideal. The structure sheaf is quasi-coherent by the rank-one
   case of lem-weil-pbc-spec-tilde-free-module. On affine V its image is precisely the
   extended ideal, by the natural affine section formula. Step 4 therefore identifies
   the ideals on affine opens lying over affine opens. Such opens cover every open of
   T; equality of subsheaves follows by the sheaf condition. No injectivity of the
   pulled-back ideal inclusion is used.
-/
theorem fittingSheaf_arbitrary_pullback {T S : Scheme.{u}} (g : T ⟶ S) (F : S.Modules)
    [F.IsFiniteType] [F.IsQuasicoherent] (r : ℕ) :
    ∃ (hft : ((tensorPullback g).obj F).IsFiniteType)
      (hqc : ((tensorPullback g).obj F).IsQuasicoherent),
      (∀ (U : S.affineOpens) (V : T.affineOpens) (h : V.1 ≤ g ⁻¹ᵁ U.1),
        Nonempty (((tensorPullback g).obj F).restrict V.1.ι ≅
          (tilde (affinePullbackTensor g F U V h)).restrict V.2.isoSpec.hom) ∧
        ∃ e : affinePullbackTensor g F U V h ≃ₗ[Γ(T, V.1)]
            Γ((tensorPullback g).obj F, V.1),
          (∀ m : Γ(F, U.1), e (affinePullbackOneTensor g F U V h m) =
            ((tensorPullback g).obj F).presheaf.map (homOfLE h).op
              (tensorPullbackSection g F U.1 m)) ∧
          (∀ (n : ℕ) (m : Fin n → Γ(F, U.1)),
            Submodule.span Γ(S, U.1) (Set.range m) = ⊤ →
            Submodule.span Γ(T, V.1)
              (Set.range (fun i ↦ affinePullbackOneTensor g F U V h (m i))) = ⊤) ∧
          (∀ (n : ℕ) (π : (Fin n → Γ(S, U.1)) →ₗ[Γ(S, U.1)] Γ(F, U.1)),
            Function.Surjective π →
            (fittingIdealSheaf F r).ideal U = π.presentationFittingIdeal r ∧
            Function.Surjective (affinePullbackPresentation g F U V h π) ∧
            (@fittingIdealSheaf T ((tensorPullback g).obj F) hft hqc r).ideal V =
              (affinePullbackPresentation g F U V h π).presentationFittingIdeal r ∧
            (affinePullbackPresentation g F U V h π).presentationFittingIdeal r =
              Ideal.map (g.appLE U.1 V.1 h).hom ((fittingIdealSheaf F r).ideal U))) ∧
      @fittingIdealSheaf T ((tensorPullback g).obj F) hft hqc r =
        (fittingIdealSheaf F r).comap g := by
  classical
  let hft := (tensorPullback_isFiniteType T S g F).1
  let k := (tensorPullbackSectionAdjunction g).leftAdjointUniq (pullbackPushforwardAdjunction g)
  let hqc : ((tensorPullback g).obj F).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent T.ringCatSheaf).prop_of_iso (k.app F).symm
      (by infer_instance)
  have hcharts :
    (∀ (U : S.affineOpens) (V : T.affineOpens) (h : V.1 ≤ g ⁻¹ᵁ U.1),
        Nonempty (((tensorPullback g).obj F).restrict V.1.ι ≅
          (tilde (affinePullbackTensor g F U V h)).restrict V.2.isoSpec.hom) ∧
        ∃ e : affinePullbackTensor g F U V h ≃ₗ[Γ(T, V.1)]
            Γ((tensorPullback g).obj F, V.1),
          (∀ m : Γ(F, U.1), e (affinePullbackOneTensor g F U V h m) =
            ((tensorPullback g).obj F).presheaf.map (homOfLE h).op
              (tensorPullbackSection g F U.1 m)) ∧
          (∀ (n : ℕ) (m : Fin n → Γ(F, U.1)),
            Submodule.span Γ(S, U.1) (Set.range m) = ⊤ →
            Submodule.span Γ(T, V.1)
              (Set.range (fun i ↦ affinePullbackOneTensor g F U V h (m i))) = ⊤) ∧
          (∀ (n : ℕ) (π : (Fin n → Γ(S, U.1)) →ₗ[Γ(S, U.1)] Γ(F, U.1)),
            Function.Surjective π →
            (fittingIdealSheaf F r).ideal U = π.presentationFittingIdeal r ∧
            Function.Surjective (affinePullbackPresentation g F U V h π) ∧
            (@fittingIdealSheaf T ((tensorPullback g).obj F) hft hqc r).ideal V =
              (affinePullbackPresentation g F U V h π).presentationFittingIdeal r ∧
            (affinePullbackPresentation g F U V h π).presentationFittingIdeal r =
              Ideal.map (g.appLE U.1 V.1 h).hom ((fittingIdealSheaf F r).ideal U))) := by
    intro U V h
    obtain ⟨e, he⟩ := affinePullback_equiv g F U V h
    refine ⟨affinePullback_sheaf_iso g F U V h e, e, he,
      affinePullback_span g F U V h, ?_⟩
    intro n π hπ
    let : Algebra Γ(S, U.1) Γ(T, V.1) := (g.appLE U.1 V.1 h).hom.toAlgebra
    let := finite_sections_of_finiteType F U.2
    have hs := (π.presentationFittingIdeal_independence_baseChange r hπ).2.1 Γ(T, V.1)
    have hsource := (fittingIdealSheaf_affine_sections F r U n π hπ).1
    let ρ := e.toLinearMap.comp (affinePullbackPresentation g F U V h π)
    have hρ : Function.Surjective ρ := e.surjective.comp hs.1
    have htarget := (fittingIdealSheaf_affine_sections
      ((tensorPullback g).obj F) r V n ρ hρ).1
    rw [presentationFittingIdeal_comp_equiv] at htarget
    exact ⟨hsource, hs.1, htarget, hs.2.trans (congrArg
      (Ideal.map (g.appLE U.1 V.1 h).hom) hsource.symm)⟩
  refine ⟨hft, hqc, hcharts, ?_⟩
  let ι := Σ' (U : S.affineOpens) (V : T.affineOpens), V.1 ≤ g ⁻¹ᵁ U.1
  apply IdealSheafData.ext_of_iSup_eq_top (ι := ι) (fun i ↦ i.2.1)
  · rw [eq_top_iff]
    intro x _
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, _⟩ :=
      S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (g x)) isOpen_univ
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
      T.isBasis_affineOpens.exists_subset_of_mem_open (a := x) (ou := (g ⁻¹ᵁ U).2) hxU
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨U, hU⟩, ⟨V, hV⟩, hVU⟩, hxV⟩
  · rintro ⟨U, V, h⟩
    obtain ⟨_, _, _, _, hpres⟩ := hcharts U V h
    let := finite_sections_of_finiteType F U.2
    obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' Γ(S, U.1) Γ(F, U.1)
    obtain ⟨_, _, htarget, hmap⟩ := hpres n π hπ
    rw [IdealSheafData.ideal_comap_appLE _ g U V h]
    exact htarget.trans hmap

end AlgebraicGeometry.Scheme.Modules
