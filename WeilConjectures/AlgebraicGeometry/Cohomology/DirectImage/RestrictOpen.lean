/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Topology.Sheaves.Flasque
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import WeilConjectures.AlgebraicGeometry.Cohomology.Exact
public import WeilConjectures.AlgebraicGeometry.Cohomology.InjectiveFlasque
public import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Higher direct images and restriction to an open subscheme of the base

Let `g : T' ⟶ T` be an open immersion and let `f' : X' ⟶ T'`, `g' : X' ⟶ X` be the base change
of `f : X ⟶ T` along `g`. Then `R^q f'_* (g'^* ℱ) ≅ (R^q f_* ℱ)|_{T'}` for every `𝒪_X`-module
`ℱ` (`AlgebraicGeometry.Scheme.Modules.nonempty_higherDirectImage_iso_restrict_of_isPullback`).

The pushforward commutes with restriction to opens,
`f'_* (ℱ|_{X'}) ≅ (f_* ℱ)|_{T'}` (`AlgebraicGeometry.Scheme.Modules.pushforwardRestrictIso`).
The restriction of an injective resolution `ℱ → I` is a resolution `ℱ|_{X'} → I|_{X'}` by flasque
modules, which are acyclic for `f'_*`, so `R^q f'_* (ℱ|_{X'})` is the cohomology of
`f'_* (I|_{X'}) ≅ (f_* I)|_{T'}`; restriction to `T'` is exact, so this is `(R^q f_* ℱ)|_{T'}`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

variable {X T X' T' : Scheme.{u}} {f : X ⟶ T} {g : T' ⟶ T} {g' : X' ⟶ X} {f' : X' ⟶ T'}
  [IsOpenImmersion g] [IsOpenImmersion g']

/-- In a cartesian square with `g` an open immersion, `f⁻¹(g(V)) = g'(f'⁻¹(V))`. -/
lemma preimage_image_eq_image_preimage_of_isPullback (sq : IsPullback g' f' f g)
    (V : T'.Opens) : f ⁻¹ᵁ (g ''ᵁ V) = g' ''ᵁ (f' ⁻¹ᵁ V) := by
  ext x
  simp only [Scheme.Hom.coe_preimage, Scheme.Hom.coe_image, Set.mem_preimage, Set.mem_image,
    SetLike.mem_coe]
  constructor
  · rintro ⟨v, hv, hvx⟩
    obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback x v hvx.symm
    refine ⟨sq.isoPullback.inv z, ?_, ?_⟩
    · rw [← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_snd, hz₂]
      exact hv
    · rw [← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_fst, hz₁]
  · rintro ⟨y, hy, rfl⟩
    refine ⟨f' y, hy, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, sq.w]

variable (f g g' f') in
/-- The comparison of the two composites `T'.Opens ⥤ X.Opens`, `V ↦ f⁻¹(g(V)) = g'(f'⁻¹(V))`. -/
noncomputable def opensFunctorCompMapIso (sq : IsPullback g' f' f g) :
    g.opensFunctor ⋙ TopologicalSpace.Opens.map f.base ≅
      TopologicalSpace.Opens.map f'.base ⋙ g'.opensFunctor :=
  NatIso.ofComponents (fun V ↦ eqToIso (preimage_image_eq_image_preimage_of_isPullback sq V))
    fun _ ↦ rfl

/-- The ring maps of the two composites `T'.Opens ⥤ X.Opens` agree: on `V ⊆ T'`, the map
`Γ(T', V) ≅ Γ(T, g(V)) → Γ(X, f⁻¹(g(V))) = Γ(X, g'(f'⁻¹(V)))` is
`Γ(T', V) → Γ(X', f'⁻¹(V)) ≅ Γ(X, g'(f'⁻¹(V)))`. -/
lemma appIso_inv_app_map_eq_app_appIso_inv (sq : IsPullback g' f' f g) (V : T'.Opens) :
    (g.appIso V).inv ≫ f.app (g ''ᵁ V) ≫
      X.presheaf.map (eqToHom (preimage_image_eq_image_preimage_of_isPullback sq V).symm).op =
    f'.app V ≫ (g'.appIso (f' ⁻¹ᵁ V)).inv := by
  rw [← cancel_mono (g'.appIso (f' ⁻¹ᵁ V)).hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [Scheme.Hom.appIso_hom']
  rw [Scheme.Hom.map_appLE, ← Scheme.Hom.comp_appLE]
  simp only [sq.w]
  rw [Scheme.Hom.comp_appLE, Scheme.Hom.appIso_inv_app_assoc, Scheme.Hom.map_appLE,
    Scheme.Hom.appLE_eq_app]

set_option backward.isDefEq.respectTransparency.types false in
/-- **The pushforward commutes with restriction to an open subscheme of the base.** In a cartesian
square with `g` an open immersion, `(f_* ℱ)|_{T'} ≅ f'_* (ℱ|_{X'})`. -/
noncomputable def pushforwardRestrictIso (sq : IsPullback g' f' f g) :
    pushforward f ⋙ restrictFunctor g ≅ restrictFunctor g' ⋙ pushforward f' := by
  letI := Functor.isContinuous_comp.{u} g.opensFunctor (TopologicalSpace.Opens.map f.base)
    (Opens.grothendieckTopology T') (Opens.grothendieckTopology T) (Opens.grothendieckTopology X)
  letI := Functor.isContinuous_comp.{u} (TopologicalSpace.Opens.map f'.base) g'.opensFunctor
    (Opens.grothendieckTopology T') (Opens.grothendieckTopology X')
    (Opens.grothendieckTopology X)
  refine SheafOfModules.pushforwardComp _ _ ≪≫
    SheafOfModules.pushforwardCongr₂ _ (opensFunctorCompMapIso f g g' f' sq).symm ?_ ≪≫
      (SheafOfModules.pushforwardComp _ _).symm
  ext V x
  exact congr($(appIso_inv_app_map_eq_app_appIso_inv sq V.unop).hom x)

section Flasque

variable {Y S : Scheme.{u}}

/-- An `𝒪_Y`-module whose underlying abelian sheaf is flasque. -/
abbrev IsFlasqueModule (M : Y.Modules) : Prop :=
  TopCat.Presheaf.IsFlasque ((toAb Y).obj M).obj

/-- The restriction of a flasque module along an open immersion is flasque. -/
lemma isFlasqueModule_restrict (j : Y ⟶ S) [IsOpenImmersion j] {M : S.Modules}
    (hM : IsFlasqueModule M) : IsFlasqueModule (M.restrict j) where
  epi i := hM.epi (j.opensFunctor.op.map i)

/-- **Flasque modules are acyclic for the pushforward.** In a short exact sequence
`0 ⟶ M₁ ⟶ M₂ ⟶ M₃ ⟶ 0` with `M₁` flasque, `M₂ ⟶ M₃` is surjective on all sections, so the
pushforward keeps it short exact; flasque modules are stable under cokernels of monomorphisms
between them and injective modules are flasque, so flasque modules are `h_*`-acyclic. -/
lemma rightAcyclic_pushforward_of_isFlasqueModule (h : Y ⟶ S) [HasInjectiveResolutions Y.Modules]
    {M : Y.Modules} (hM : IsFlasqueModule M) : (pushforward h).rightAcyclic M := by
  have : PreservesFiniteLimits (pushforward h) :=
    have := (pullbackPushforwardAdjunction h).rightAdjoint_preservesLimits.{0, 0}
    inferInstance
  refine Functor.rightAcyclic_of_epi_map_g (pushforward h) (fun M ↦ IsFlasqueModule M)
    (fun I _ ↦ isFlasque_of_injective I) (fun S hS h₁ h₂ ↦ ?_) (fun S hS h₁ ↦ ?_) hM
  · have hS' := hS.map_of_exact (toAb Y)
    have : TopCat.Sheaf.IsFlasque (S.map (toAb Y)).X₁ := h₁
    have : TopCat.Sheaf.IsFlasque (S.map (toAb Y)).X₂ := h₂
    exact TopCat.Sheaf.IsFlasque.of_shortExact_of_isFlasque₁₂ hS'
  · have hS' := hS.map_of_exact (toAb Y)
    have : TopCat.Sheaf.IsFlasque (S.map (toAb Y)).X₁ := h₁
    refine epi_of_forall_exists_app_eq _ fun W y x hx ↦ ⟨W, le_rfl, hx, ?_⟩
    obtain ⟨z, hz⟩ := (AddCommGrpCat.epi_iff_surjective _).1
      (TopCat.Sheaf.IsFlasque.epi_of_shortExact (U := h ⁻¹ᵁ W) hS') y
    refine ⟨z, ?_⟩
    rw [show homOfLE (le_refl W) = 𝟙 W from rfl, op_id, CategoryTheory.Functor.map_id]
    exact hz

end Flasque

/-- **The higher direct images commute with restriction to an open subscheme of the base.** Let
`g : T' ⟶ T` be an open immersion and let `f' : X' ⟶ T'`, `g' : X' ⟶ X` be the base change of
`f : X ⟶ T` along `g`. Then `R^q f'_* (ℱ|_{X'}) ≅ (R^q f_* ℱ)|_{T'}` for every `𝒪_X`-module `ℱ`.

For an injective resolution `ℱ → I`, the restriction `ℱ|_{X'} → I|_{X'}` is a resolution by
flasque, hence `f'_*`-acyclic, modules, so `R^q f'_* (ℱ|_{X'})` is the cohomology of
`f'_* (I|_{X'}) ≅ (f_* I)|_{T'}`, which is `(R^q f_* ℱ)|_{T'}` since restriction is exact. -/
theorem nonempty_higherDirectImage_restrict_iso_of_isPullback (sq : IsPullback g' f' f g)
    [HasInjectiveResolutions X.Modules] [HasInjectiveResolutions X'.Modules] (ℱ : X.Modules)
    (q : ℕ) :
    Nonempty ((higherDirectImage f' q).obj (ℱ.restrict g') ≅
      ((higherDirectImage f q).obj ℱ).restrict g) := by
  have : PreservesFiniteLimits (pushforward f) :=
    have := (pullbackPushforwardAdjunction f).rightAdjoint_preservesLimits.{0, 0}
    inferInstance
  have : PreservesFiniteLimits (pushforward f') :=
    have := (pullbackPushforwardAdjunction f').rightAdjoint_preservesLimits.{0, 0}
    inferInstance
  let I := injectiveResolution ℱ
  let K := ((restrictFunctor g').mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
  let ι' : (CochainComplex.single₀ _).obj ((restrictFunctor g').obj ℱ) ⟶ K :=
    (HomologicalComplex.singleMapHomologicalComplex (restrictFunctor g') (ComplexShape.up ℕ)
      0).inv.app ℱ ≫ ((restrictFunctor g').mapHomologicalComplex _).map I.ι
  have : QuasiIso ι' := inferInstance
  have hK (n : ℕ) : (pushforward f').rightAcyclic (K.X n) :=
    rightAcyclic_pushforward_of_isFlasqueModule f'
      (isFlasqueModule_restrict g' (isFlasque_of_injective (I.cocomplex.X n)))
  let e₁ := (pushforward f').rightDerivedObjIsoOfResolution ι' hK q
  let e₂ : ((pushforward f').mapHomologicalComplex _).obj K ≅
      ((restrictFunctor g).mapHomologicalComplex _).obj
        (((pushforward f).mapHomologicalComplex _).obj I.cocomplex) :=
    (NatIso.mapHomologicalComplex (pushforwardRestrictIso sq).symm _).app I.cocomplex
  let L := ((pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
  let e₃ : (((restrictFunctor g).mapHomologicalComplex _).obj L).homology q ≅
      (restrictFunctor g).obj (L.homology q) :=
    (L.sc q).mapHomologyIso (restrictFunctor g)
  exact ⟨e₁ ≪≫ (HomologicalComplex.homologyFunctor _ _ q).mapIso e₂ ≪≫ e₃ ≪≫
    (restrictFunctor g).mapIso (I.isoRightDerivedObj (pushforward f) q).symm⟩

end AlgebraicGeometry.Scheme.Modules
