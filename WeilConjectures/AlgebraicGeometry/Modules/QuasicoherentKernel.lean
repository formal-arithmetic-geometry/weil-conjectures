/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Localization.Finiteness
public import WeilConjectures.AlgebraicGeometry.Modules.FreeGenerator
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
# Kernels and finite coproducts of quasi-coherent modules

Let `X` be a scheme. We show that the category of quasi-coherent `𝒪_X`-modules is closed under
kernels and coproducts, and that on a locally Noetherian scheme the kernel of a morphism from a
module of finite presentation to a quasi-coherent module is of finite presentation. Along the
way we show that the sections of a module of finite presentation over an affine open are a finite
module.

The proofs reduce to affine opens `U`, through the open immersions `Spec Γ(X, U) ⟶ X`. Restriction
along an open immersion preserves limits and colimits, and on `Spec R` a module `M` is
quasi-coherent if and only if it is localizing, i.e. `M ≅ Γ(M)^~`; localization is exact, so the
kernel of a morphism of localizing modules is localizing.

## Main statements

- `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_kernel`: the kernel of a morphism of
  quasi-coherent modules is quasi-coherent.
- `AlgebraicGeometry.Scheme.Modules.finite_sections_of_isFinitePresentation`: the sections of a
  module of finite presentation over an affine open `U` form a finite `Γ(X, U)`-module.
- `AlgebraicGeometry.Scheme.Modules.isFinitePresentation_kernel`: on a locally Noetherian scheme,
  the kernel of a morphism from a module of finite presentation to a quasi-coherent module is of
  finite presentation.
- `AlgebraicGeometry.Scheme.Modules.epi_of_surjective_app`: a morphism into a quasi-coherent
  module which is surjective on sections over an affine open cover is an epimorphism.
- `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_sigma` and `isFinitePresentation_sigma`: a
  coproduct of quasi-coherent modules is quasi-coherent, and a finite coproduct of modules of
  finite presentation is of finite presentation.

## Auxiliary results

- `IsLocalizedModule.of_injective_of_exact`: localization commutes with taking kernels.
- `CategoryTheory.Limits.isColimitCokernelCoforkSigmaMap`: a coproduct of cokernels is a
  cokernel.
- `SheafOfModules.Presentation.sigma`: a presentation of a coproduct of sheaves of modules from
  presentations of the summands.
- `AlgebraicGeometry.Scheme.Modules.preservesLimitsOfSize_restrictFunctor`: restriction along an
  open immersion preserves limits.
-/

@[expose] public section

universe u v' u'

open CategoryTheory Limits Opposite TopologicalSpace

/-- **Localization commutes with kernels.** Let `0 → K → M → N` and `K' → M' → N'` be exact
sequences of `R`-modules with `K' → M'` injective, compatible with maps `K → K'`, `M → M'`,
`N → N'`, the last two of which are localizations at `S`. If the elements of `S` act invertibly on
`K'`, then `K → K'` is a localization at `S`. -/
lemma IsLocalizedModule.of_injective_of_exact {R : Type*} [CommRing R] (S : Submonoid R)
    {K M N K' M' N' : Type*} [AddCommGroup K] [AddCommGroup M] [AddCommGroup N]
    [AddCommGroup K'] [AddCommGroup M'] [AddCommGroup N'] [Module R K] [Module R M] [Module R N]
    [Module R K'] [Module R M'] [Module R N'] {ι : K →ₗ[R] M} {φ : M →ₗ[R] N}
    {ι' : K' →ₗ[R] M'} {φ' : M' →ₗ[R] N'} (lK : K →ₗ[R] K') (lM : M →ₗ[R] M')
    (lN : N →ₗ[R] N') [IsLocalizedModule S lM] [IsLocalizedModule S lN]
    (hι : Function.Injective ι) (hex : Function.Exact ι φ) (hι' : Function.Injective ι')
    (hφι' : ∀ y, φ' (ι' y) = 0) (h₁ : ∀ k, lM (ι k) = ι' (lK k))
    (h₂ : ∀ m, lN (φ m) = φ' (lM m)) (hu : ∀ s : S, IsUnit (algebraMap R (Module.End R K') s)) :
    IsLocalizedModule S lK where
  map_units := hu
  surj y := by
    obtain ⟨⟨m, s⟩, hm⟩ := IsLocalizedModule.surj S lM (ι' y)
    dsimp only at hm
    rw [Submonoid.smul_def] at hm
    have h0 : lN (φ m) = lN 0 := by
      rw [h₂, ← hm, map_zero, map_smul, hφι', smul_zero]
    obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := S) h0
    rw [smul_zero, Submonoid.smul_def, ← map_smul] at hc
    obtain ⟨k, hk⟩ := (hex _).mp hc
    refine ⟨⟨k, c * s⟩, hι' ?_⟩
    rw [← h₁, hk, Submonoid.smul_def, map_smul, map_smul, ← hm, smul_smul, Submonoid.coe_mul]
  exists_of_eq {k₁ k₂} h := by
    have : lM (ι k₁) = lM (ι k₂) := by rw [h₁, h₁, h]
    obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := S) this
    refine ⟨c, hι ?_⟩
    rw [Submonoid.smul_def, Submonoid.smul_def, map_smul, map_smul]
    exact hc

namespace CategoryTheory.Limits

/-- A coproduct of cokernels is a cokernel: if each `g i : B i ⟶ Z i` is a cokernel of
`f i : A i ⟶ B i`, then `Sigma.map g` is a cokernel of `Sigma.map f`. -/
noncomputable def isColimitCokernelCoforkSigmaMap {C : Type*} [Category C] [Preadditive C]
    {ι : Type*} {A B Z : ι → C} [HasCoproduct A] [HasCoproduct B] [HasCoproduct Z]
    (f : ∀ i, A i ⟶ B i) (g : ∀ i, B i ⟶ Z i) (w : ∀ i, f i ≫ g i = 0)
    (h : ∀ i, IsColimit (CokernelCofork.ofπ (g i) (w i))) :
    IsColimit (CokernelCofork.ofπ (Sigma.map g) (show Sigma.map f ≫ Sigma.map g = 0 by
      ext i
      simp [reassoc_of% (w i)])) :=
  CokernelCofork.IsColimit.ofπ _ _
    (fun k hk ↦ Sigma.desc fun i ↦ (h i).desc (CokernelCofork.ofπ (Sigma.ι B i ≫ k) (by
      rw [← Sigma.ι_map_assoc, hk, comp_zero])))
    (fun k hk ↦ by
      ext i
      simp only [Sigma.ι_map_assoc, colimit.ι_desc, Cofan.mk_ι_app]
      exact (h i).fac _ WalkingParallelPair.one)
    (fun k hk m hm ↦ by
      ext i
      simp only [colimit.ι_desc, Cofan.mk_ι_app]
      refine Cofork.IsColimit.hom_ext (h i) ?_
      refine Eq.trans ?_
        ((h i).fac (CokernelCofork.ofπ (Sigma.ι B i ≫ k) _) WalkingParallelPair.one).symm
      simp [← hm])

end CategoryTheory.Limits

namespace SheafOfModules

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **A presentation of a coproduct.** Presentations of the sheaves of modules `M i` give a
presentation of `∐ M`, with generators and relations the disjoint unions of those of the `M i`:
the cokernel of `∐ free (relations i) ⟶ ∐ free (generators i)` is `∐ M`. -/
noncomputable def Presentation.sigma {ι : Type u} (M : ι → SheafOfModules.{u} R)
    (P : ∀ i, (M i).Presentation) : (∐ M).Presentation :=
  letI eI := (freeFunctor (R := R)).mapIso (Types.coproductIso fun i ↦ (P i).generators.I).symm ≪≫
    PreservesCoproduct.iso (freeFunctor (R := R)) fun i ↦ (P i).generators.I
  letI eJ := (freeFunctor (R := R)).mapIso (Types.coproductIso fun i ↦ (P i).relations.I).symm ≪≫
    PreservesCoproduct.iso (freeFunctor (R := R)) fun i ↦ (P i).relations.I
  presentationOfIsCokernelFree
    (eJ.hom ≫ Limits.Sigma.map (fun i ↦ (freeHomEquiv _).symm (P i).relations.s ≫ kernel.ι _) ≫
      eI.inv)
    (eI.hom ≫ Limits.Sigma.map fun i ↦ (P i).generators.π) (by
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      rw [Sigma.map_comp_map]
      convert comp_zero
      exact Sigma.hom_ext _ _ fun i ↦ by simp)
    (IsCokernel.ofIso _ (isColimitCokernelCoforkSigmaMap _ _ _ fun i ↦ (P i).isColimit) _ eJ.symm
      eI.symm (Iso.refl _) (by simp) (by simp))

instance Presentation.isFinite_sigma {ι : Type u} [Finite ι] (M : ι → SheafOfModules.{u} R)
    (P : ∀ i, (M i).Presentation) [∀ i, (P i).IsFinite] : (Presentation.sigma M P).IsFinite where
  isFiniteType_generators := ⟨inferInstanceAs (Finite (Σ i, (P i).generators.I))⟩
  isFiniteType_relations := ⟨inferInstanceAs (Finite (Σ i, (P i).relations.I))⟩

end SheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

/-- On `Spec R`, the kernel of a morphism of localizing modules is localizing: its sections are the
kernels of the sections, and localization is exact. -/
theorem isLocalizing_kernel {R : CommRingCat.{u}} {M N : (Spec R).Modules}
    (hM : IsLocalizing (modulesSpecToSheaf.obj M)) (hN : IsLocalizing (modulesSpecToSheaf.obj N))
    (φ : M ⟶ N) : IsLocalizing (modulesSpecToSheaf.obj (kernel φ)) := by
  intro f
  have := hM f
  have := hN f
  let D := PrimeSpectrum.basicOpen f
  let ι (U : (Spec R).Opens) := ((modulesSpecToSheaf.map (kernel.ι φ)).hom.app (op U)).hom
  let φ' (U : (Spec R).Opens) := ((modulesSpecToSheaf.map φ).hom.app (op U)).hom
  have hinj (U : (Spec R).Opens) : Function.Injective (ι U) := injective_map_kernelι U φ
  have hex (U : (Spec R).Opens) : Function.Exact (ι U) (φ' U) := fun y ↦
    (Set.ext_iff.mp (range_map_kernelι U φ) y).symm
  have hu : ∀ s : Submonoid.powers f, IsUnit (algebraMap R
      (Module.End R ((modulesSpecToSheaf.obj (kernel φ)).obj.obj (op D))) s) := by
    rintro ⟨_, n, rfl⟩
    rw [map_pow]
    exact (isUnit_algebraMap_end_of_le_basicOpen (M := kernel φ) f le_rfl).pow n
  have h₁ (k : (modulesSpecToSheaf.obj (kernel φ)).obj.obj (op ⊤)) :
      ((modulesSpecToSheaf.obj M).obj.map D.leTop.op).hom (ι ⊤ k) =
        ι D (((modulesSpecToSheaf.obj (kernel φ)).obj.map D.leTop.op).hom k) := by
    have := (modulesSpecToSheaf.map (kernel.ι φ)).hom.naturality D.leTop.op
    exact (LinearMap.congr_fun (congrArg ModuleCat.Hom.hom this) k).symm
  have h₂ (k : (modulesSpecToSheaf.obj M).obj.obj (op ⊤)) :
      ((modulesSpecToSheaf.obj N).obj.map D.leTop.op).hom (φ' ⊤ k) =
        φ' D (((modulesSpecToSheaf.obj M).obj.map D.leTop.op).hom k) := by
    have := (modulesSpecToSheaf.map φ).hom.naturality D.leTop.op
    exact (LinearMap.congr_fun (congrArg ModuleCat.Hom.hom this) k).symm
  exact IsLocalizedModule.of_injective_of_exact (.powers f) _ _ _ (hinj ⊤) (hex ⊤) (hinj D)
    (fun y ↦ (hex D _).mpr ⟨y, rfl⟩) h₁ h₂ hu

variable {X Y : Scheme.{u}}

/-- Restriction along an open immersion `f` preserves limits: the underlying presheaf of abelian
groups of `M.restrict f` is the presheaf of `M` precomposed with `f.opensFunctor`, and the forgetful
functor to presheaves of abelian groups preserves and reflects limits. -/
noncomputable instance preservesLimitsOfSize_restrictFunctor (f : X ⟶ Y) [IsOpenImmersion f] :
    PreservesLimitsOfSize.{u, u} (restrictFunctor f) := by
  have : PreservesLimitsOfSize.{u, u}
      ((Functor.whiskeringLeft X.Opensᵒᵖ Y.Opensᵒᵖ Ab.{u}).obj f.opensFunctor.op) :=
    preservesLimits_of_evaluation _ fun U ↦ inferInstanceAs
      (PreservesLimitsOfSize.{u, u}
        ((CategoryTheory.evaluation _ _).obj (f.opensFunctor.op.obj U)))
  have : PreservesLimitsOfSize.{u, u} (restrictFunctor f ⋙ toPresheaf X) :=
    inferInstanceAs (PreservesLimitsOfSize.{u, u}
      (toPresheaf Y ⋙ (Functor.whiskeringLeft _ _ _).obj f.opensFunctor.op))
  have : ReflectsLimitsOfSize.{u, u} (toPresheaf X) := reflectsLimits_of_reflectsIsomorphisms
  exact preservesLimits_of_reflects_of_preserves (restrictFunctor f) (toPresheaf X)

/-- A presentation of a module `M` on `Spec R` with `M ≅ Γ(M)^~`, coming from the presentation of
the `R`-module `Γ(M)` by all its elements and all their relations. -/
noncomputable def presentationOfIsIsoFromTildeΓ {R : CommRingCat.{u}} (M : (Spec R).Modules)
    [IsIso M.fromTildeΓ] : M.Presentation :=
  haveI : IsIso (C := SheafOfModules.{u} (Spec R).ringCatSheaf) M.fromTildeΓ := ‹_›
  (presentationTilde ((modulesSpecToSheaf.obj M).presheaf.obj (.op ⊤)) .univ (by simp) _
    (Submodule.span_eq _)).ofIsIso M.fromTildeΓ

/-- An `𝒪_X`-module whose restrictions to the members of an open cover have global presentations
is quasi-coherent. This is the quasi-coherent analogue of
`AlgebraicGeometry.Scheme.Modules.isFinitePresentation_of_isOpenCover`. -/
theorem isQuasicoherent_of_isOpenCover (M : X.Modules) {ι : Type u}
    {U : ι → X.Opens} (hU : IsOpenCover U) (P : ∀ i, (M.restrict (U i).ι).Presentation) :
    M.IsQuasicoherent :=
  SheafOfModules.QuasicoherentData.isQuasicoherent (M := M)
    (SheafOfModules.QuasicoherentData.mk.{u, u, u, u} (I := ι) (X := U)
      ((Opens.coversTop_iff _ U).mpr hU) (fun i ↦ presentationOverOfRestrict (U i) (P i)))

/-- An `𝒪_X`-module whose restrictions along a family of open immersions covering `X` have global
presentations is quasi-coherent. -/
theorem isQuasicoherent_of_iSup_opensRange_eq_top (M : X.Modules)
    {ι : Type u} {Y : ι → Scheme.{u}} (f : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (f i)]
    (hf : ⨆ i, (f i).opensRange = ⊤) (P : ∀ i, (M.restrict (f i)).Presentation) :
    M.IsQuasicoherent :=
  isQuasicoherent_of_isOpenCover M (U := fun i ↦ (f i).opensRange) hf
    (fun i ↦ presentationRestrictOpensRange (f i) (P i))

/-- The open immersions `Spec Γ(X, U) ⟶ X` for the affine opens `U` of `X` cover `X`. -/
theorem iSup_opensRange_fromSpec_eq_top :
    ⨆ U : {U : X.Opens // IsAffineOpen U}, U.2.fromSpec.opensRange = ⊤ := by
  refine eq_top_iff.mpr fun x _ ↦ ?_
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  exact Opens.mem_iSup.mpr ⟨⟨V, hV⟩, by rwa [IsAffineOpen.opensRange_fromSpec]⟩

/-- **The kernel of a morphism of quasi-coherent modules is quasi-coherent.** On an affine open
`U`, restriction along `Spec Γ(X, U) ⟶ X` commutes with kernels, and on `Spec Γ(X, U)` the kernel of
a morphism of localizing modules is localizing (`isLocalizing_kernel`). -/
theorem isQuasicoherent_kernel {M N : X.Modules}
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) M]
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) N] (φ : M ⟶ N) :
    SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) (kernel φ) := by
  refine isQuasicoherent_of_iSup_opensRange_eq_top (kernel φ)
    (fun U : {U : X.Opens // IsAffineOpen U} ↦ U.2.fromSpec) iSup_opensRange_fromSpec_eq_top
    fun U ↦ ?_
  have : IsIso (kernel ((restrictFunctor U.2.fromSpec).map φ)).fromTildeΓ :=
    (isIso_fromTildeΓ_iff_isLocalizing _).mpr (isLocalizing_kernel
      ((isIso_fromTildeΓ_iff_isLocalizing _).mp inferInstance)
      ((isIso_fromTildeΓ_iff_isLocalizing _).mp inferInstance) _)
  let e := PreservesKernel.iso (restrictFunctor U.2.fromSpec) φ
  haveI : IsIso (C := SheafOfModules.{u} (Spec Γ(X, U.1)).ringCatSheaf) e.inv :=
    (inferInstance : IsIso e.inv)
  exact (presentationOfIsIsoFromTildeΓ _).ofIsIso e.inv

/-- A module `M ≅ Γ(M)^~` on `Spec R` generated by finitely many global sections has finite global
sections: the generating sections give an epimorphism `(R^I)^~ ⟶ Γ(M)^~`, which comes from a
surjection `R^I → Γ(M)` since `M ↦ M^~` is fully faithful. -/
theorem finite_sections_top_of_isIso_fromTildeΓ {R : CommRingCat.{u}} (M : (Spec R).Modules)
    [hM : IsIso M.fromTildeΓ] (σ : M.GeneratingSections) [Finite σ.I] :
    Module.Finite R Γ(M, ⊤) := by
  have : @Epi (Spec R).Modules _ _ _ σ.π := σ.epi
  let e := @asIso _ _ _ _ M.fromTildeΓ hM
  let ψ : (tilde.functor R).obj (ModuleCat.of R (σ.I →₀ R)) ⟶
      (tilde.functor R).obj ((modulesSpecToSheaf.obj M).presheaf.obj (op ⊤)) :=
    (tildeFinsupp σ.I).hom ≫ σ.π ≫ e.inv
  have : Epi ((tilde.functor R).map ((tilde.functor R).preimage ψ)) := by
    rw [Functor.map_preimage]
    exact @epi_comp _ _ _ _ _ _ (@IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_hom _)) _
      (@epi_comp _ _ _ _ _ _ this _ (@IsIso.epi_of_iso _ _ _ _ e.inv (Iso.isIso_inv e)))
  have hg := (tilde.functor R).epi_of_epi_map this
  exact Module.Finite.of_surjective _ ((ModuleCat.epi_iff_surjective _).mp hg)

/-- If the global sections of the restriction of `F` along `Spec Γ(X, V) ⟶ X` are finite over
`Γ(X, V)`, so are the sections of `F` over the affine open `V`. -/
theorem finite_sections_of_finite_sections_restrict_fromSpec (F : X.Modules) {V : X.Opens}
    (hV : IsAffineOpen V) [Module.Finite Γ(X, V) Γ(F.restrict hV.fromSpec, ⊤)] :
    Module.Finite Γ(X, V) Γ(F, V) := by
  have hW' : V ≤ hV.fromSpec ''ᵁ ⊤ := by
    rw [Hom.image_top_eq_opensRange, hV.opensRange_fromSpec]
  have hid : (homOfLE (hV.fromSpec_image_le ⊤)).op ≫ (homOfLE hW').op =
      𝟙 (Opposite.op V) := Subsingleton.elim _ _
  let L : Γ(F.restrict hV.fromSpec, ⊤) →ₗ[Γ(X, V)] Γ(F, V) :=
    { toFun x := F.presheaf.map (homOfLE hW').op ((F.restrictAppIso hV.fromSpec ⊤).hom x)
      map_add' x y := by simp only [map_add]
      map_smul' r x := by
        rw [restrictAppIso_fromSpec_smul, map_smul, ← Functor.map_comp_apply, hid,
          CategoryTheory.Functor.map_id, ConcreteCategory.id_apply, RingHom.id_apply] }
  refine Module.Finite.of_surjective L fun y ↦ ⟨(F.restrictAppIso hV.fromSpec ⊤).inv
    (F.presheaf.map (homOfLE (hV.fromSpec_image_le ⊤)).op y), ?_⟩
  simp only [L, LinearMap.coe_mk, AddHom.coe_mk, Iso.inv_hom_id_apply, ← Functor.map_comp_apply,
    hid, CategoryTheory.Functor.map_id, ConcreteCategory.id_apply]

/-- A presentation of `M.over W` gives a presentation of the restriction of `M` along any open
immersion `f` with image in `W`. -/
noncomputable def presentationRestrictOfOver {M : X.Modules} {W : X.Opens}
    (P : (M.over W).Presentation) (f : Y ⟶ X) [IsOpenImmersion f] (hf : f.opensRange ≤ W) :
    (M.restrict f).Presentation :=
  let u : Y ⟶ W.toScheme := IsOpenImmersion.lift W.ι f (by
    rw [Scheme.Opens.range_ι]
    exact hf)
  haveI : IsOpenImmersion (u ≫ W.ι) := by
    rw [IsOpenImmersion.lift_fac]
    infer_instance
  haveI : IsOpenImmersion u := IsOpenImmersion.of_comp u W.ι
  haveI : PreservesColimitsOfSize.{u, u} (restrictFunctor u) := inferInstance
  let F := (overEquiv W).functor ⋙ restrictFunctor u
  let iso : SheafOfModules.overFunctor X.ringCatSheaf W ⋙ F ≅ restrictFunctor f :=
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight (overFunctorEquiv W) _ ≪≫
      (restrictFunctorComp u W.ι).symm ≪≫ restrictFunctorCongr (IsOpenImmersion.lift_fac _ _ _)
  SheafOfModules.Presentation.ofIsIso.{u, u, u} (iso.app M).hom
    (P.map F (restrictUnitIso _).symm)

instance isFinite_presentationRestrictOfOver {M : X.Modules} {W : X.Opens}
    (P : (M.over W).Presentation) [P.IsFinite] (f : Y ⟶ X) [IsOpenImmersion f]
    (hf : f.opensRange ≤ W) : (presentationRestrictOfOver P f hf).IsFinite := by
  dsimp [presentationRestrictOfOver]
  infer_instance

/-- **The sections of a module of finite presentation over an affine open are finite.** Let `F` be
an `𝒪_X`-module of finite presentation and `U` an affine open. Then `Γ(F, U)` is a finite
`Γ(X, U)`-module: `U` is covered by basic opens `D(g)` over which `F` has a finite presentation, so
that `Γ(F, D(g))` is finite over `Γ(X, D(g))`, and finiteness descends along the localizations
`Γ(F, U) → Γ(F, D(g))`. -/
theorem finite_sections_of_isFinitePresentation (F : X.Modules)
    [SheafOfModules.IsFinitePresentation (R := X.ringCatSheaf) F] {U : X.Opens}
    (hU : IsAffineOpen U) : Module.Finite Γ(X, U) Γ(F, U) := by
  obtain ⟨q, hq⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData
    (R := X.ringCatSheaf) F
  have hcov : IsOpenCover q.X := (Opens.coversTop_iff _ q.X).mp q.coversTop
  let s : Set Γ(X, U) := {g | Module.Finite Γ(X, X.basicOpen g) Γ(F, X.basicOpen g)}
  have hs : Ideal.span s = ⊤ := by
    rw [← hU.self_le_iSup_basicOpen_iff]
    intro x hx
    obtain ⟨i, hi⟩ := hcov.exists_mem x
    obtain ⟨g, hgW, hxg⟩ := hU.exists_basicOpen_le ⟨x, hi⟩ hx
    have hV := hU.basicOpen g
    let P := presentationRestrictOfOver (q.presentation i) hV.fromSpec
      (hV.opensRange_fromSpec.le.trans hgW)
    have : IsIso (F.restrict hV.fromSpec).fromTildeΓ :=
      isIso_fromTildeΓ_of_isQuasicoherent _
    have : Module.Finite Γ(X, X.basicOpen g) Γ(F.restrict hV.fromSpec, ⊤) :=
      finite_sections_top_of_isIso_fromTildeΓ _ P.generators
    exact Opens.mem_iSup.mpr ⟨⟨g, finite_sections_of_finite_sections_restrict_fromSpec F hV⟩, hxg⟩
  let _ (r : s) : Module Γ(X, U) Γ(F, X.basicOpen r.1) :=
    Module.compHom _ (algebraMap Γ(X, U) Γ(X, X.basicOpen r.1))
  have _ (r : s) := isLocalizedModule_basicOpen F hU r.1
  have _ (r : s) := hU.isLocalization_basicOpen r.1
  have _ (r : s) : IsScalarTower Γ(X, U) Γ(X, X.basicOpen r.1) Γ(F, X.basicOpen r.1) :=
    ⟨fun a b m ↦ mul_smul _ _ _⟩
  exact Module.Finite.of_localizationSpan' s hs
    (Rₚ := fun r : s ↦ Γ(X, X.basicOpen r.1)) (fun r ↦
      { toFun := F.presheaf.map (homOfLE (X.basicOpen_le r.1)).op
        map_add' := map_add _
        map_smul' := map_smul F _ }) fun r ↦ r.2

/-- **Kernels of modules of finite presentation on a locally Noetherian scheme.** Let `X` be
locally Noetherian and `φ : M ⟶ N` a morphism from a module of finite presentation to a
quasi-coherent module. Then `kernel φ` is of finite presentation: it is quasi-coherent, and over an
affine open `U` its sections are a submodule of the finite module `Γ(M, U)` over the Noetherian ring
`Γ(X, U)`. -/
theorem isFinitePresentation_kernel [IsLocallyNoetherian X] {M N : X.Modules}
    [SheafOfModules.IsFinitePresentation (R := X.ringCatSheaf) M]
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) N] (φ : M ⟶ N) :
    SheafOfModules.IsFinitePresentation (R := X.ringCatSheaf) (kernel φ) := by
  have := isQuasicoherent_kernel φ
  have hfin (U : {U : X.Opens // IsAffineOpen U}) :
      Module.Finite Γ(X, U.1) Γ((kernel φ).restrict U.2.fromSpec, ⊤) := by
    have := IsLocallyNoetherian.component_noetherian ⟨U.1, U.2⟩
    have := finite_sections_of_isFinitePresentation (M.restrict U.2.fromSpec)
      (isAffineOpen_top (Spec Γ(X, U.1)))
    have := finite_sections_top_of_finite (M.restrict U.2.fromSpec)
    have : _root_.IsNoetherian Γ(X, U.1) Γ(M.restrict U.2.fromSpec, ⊤) :=
      isNoetherian_of_isNoetherianRing_of_finite _ _
    have : _root_.IsNoetherian Γ(X, U.1)
        ((modulesSpecToSheaf.obj (M.restrict U.2.fromSpec)).obj.obj (op ⊤)) :=
      inferInstanceAs (_root_.IsNoetherian Γ(X, U.1) Γ(M.restrict U.2.fromSpec, ⊤))
    exact Module.Finite.of_injective ((modulesSpecToSheaf.map
      ((restrictFunctor U.2.fromSpec).map (kernel.ι φ))).hom.app (op ⊤)).hom
      (injective_map_kernelι _ φ)
  choose P hP using fun U : {U : X.Opens // IsAffineOpen U} ↦
    have := IsLocallyNoetherian.component_noetherian ⟨U.1, U.2⟩
    exists_presentation_isFinite (R := Γ(X, U.1)) ((kernel φ).restrict U.2.fromSpec)
  exact isFinitePresentation_of_iSup_opensRange_eq_top (kernel φ) _
    iSup_opensRange_fromSpec_eq_top P

/-- **A coproduct of quasi-coherent modules is quasi-coherent.** -/
theorem isQuasicoherent_sigma {ι : Type u} (M : ι → X.Modules)
    [∀ i, SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) (M i)] :
    SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) (∐ M) :=
  isQuasicoherent_of_iSup_opensRange_eq_top (∐ M) (fun U : {U : X.Opens // IsAffineOpen U} ↦
    U.2.fromSpec) iSup_opensRange_fromSpec_eq_top fun U ↦
      (SheafOfModules.Presentation.sigma _ fun i ↦ presentationOfIsIsoFromTildeΓ
        ((M i).restrict U.2.fromSpec)).ofIsIso
        (PreservesCoproduct.iso (restrictFunctor U.2.fromSpec) M).inv

/-- **A finite coproduct of modules of finite presentation is of finite presentation.** Every point
has an affine neighbourhood over which all the summands have finite presentations. -/
theorem isFinitePresentation_sigma {ι : Type u} [Finite ι] (M : ι → X.Modules)
    [∀ i, SheafOfModules.IsFinitePresentation (R := X.ringCatSheaf) (M i)] :
    SheafOfModules.IsFinitePresentation (R := X.ringCatSheaf) (∐ M) := by
  choose q hq using fun i ↦ SheafOfModules.IsFinitePresentation.exists_quasicoherentData
    (R := X.ringCatSheaf) (M i)
  choose j hj using fun (x : X) (i : ι) ↦
    ((Opens.coversTop_iff _ (q i).X).mp (q i).coversTop).exists_mem x
  have hV (x : X) : ∃ V : X.Opens, IsAffineOpen V ∧ x ∈ V ∧ ∀ i, V ≤ (q i).X (j x i) := by
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVle⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_iInter.mpr fun i ↦ hj x i) (isOpen_iInter_of_finite fun i ↦ ((q i).X (j x i)).2)
    exact ⟨V, hV, hxV, fun i ↦ (hVle.trans (Set.iInter_subset _ i) :)⟩
  choose V hV hxV hVle using hV
  let P (x : X) : ((∐ M).restrict (hV x).fromSpec).Presentation :=
    (SheafOfModules.Presentation.sigma _ fun i ↦ presentationRestrictOfOver
      ((q i).presentation (j x i)) (hV x).fromSpec
      (by rw [(hV x).opensRange_fromSpec]; exact hVle x i)).ofIsIso
      (PreservesCoproduct.iso (restrictFunctor (hV x).fromSpec) M).inv
  refine isFinitePresentation_of_iSup_opensRange_eq_top (∐ M) (fun x ↦ (hV x).fromSpec) ?_ P
  refine eq_top_iff.mpr fun x _ ↦ Opens.mem_iSup.mpr ⟨x, ?_⟩
  rw [(hV x).opensRange_fromSpec]
  exact hxV x

section Epi

variable {X : Scheme.{u}}

/-- A morphism of `𝒪_X`-modules is an epimorphism as soon as every section of the target is,
locally, in the image. -/
lemma epi_of_forall_exists_app_eq {M N : X.Modules} (φ : M ⟶ N)
    (h : ∀ (W : X.Opens) (y : Γ(N, W)) (x : X), x ∈ W → ∃ (V : X.Opens) (hVW : V ≤ W),
      x ∈ V ∧ ∃ z : Γ(M, V), φ.app V z = N.presheaf.map (homOfLE hVW).op y) :
    Epi φ := by
  have h₁ : TopCat.Presheaf.IsLocallySurjective ((toPresheaf X).map φ) := by
    rw [TopCat.Presheaf.isLocallySurjective_iff]
    intro W y x hx
    obtain ⟨V, hVW, hxV, z, hz⟩ := h W y x hx
    exact ⟨V, hVW, ⟨z, hz⟩, hxV⟩
  have : Sheaf.IsLocallySurjective ((SheafOfModules.toSheaf X.ringCatSheaf).map φ) := h₁
  exact (SheafOfModules.toSheaf X.ringCatSheaf).epi_of_epi_map
    (Sheaf.epi_of_isLocallySurjective _)

/-- **Surjectivity on an affine cover gives an epimorphism.** Let `𝒩` be quasi-coherent and let
`(Uᵢ)` be affine opens covering `X`. If `φ : ℳ ⟶ 𝒩` is surjective on sections over every `Uᵢ`,
then `φ` is an epimorphism: a section of `𝒩` near `x ∈ Uᵢ` is, on a basic open `D(g) ∋ x` of
`Uᵢ`, `g⁻ᵏ` times the restriction of a section over `Uᵢ`. -/
lemma epi_of_surjective_app {M N : X.Modules}
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) N] (φ : M ⟶ N) {ι : Type*}
    (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i)) (hcov : ⨆ i, U i = ⊤)
    (h : ∀ i, Function.Surjective (φ.app (U i))) : Epi φ := by
  refine epi_of_forall_exists_app_eq φ fun W y x hx ↦ ?_
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (show x ∈ ⨆ i, U i by rw [hcov]; trivial)
  obtain ⟨g, hgU, hxg⟩ := (hU i).exists_basicOpen_le ⟨x, hx⟩ hi
  obtain ⟨k, t, ht⟩ := exists_map_eq_pow_smul_of_isAffineOpen N (hU i) g
    (N.presheaf.map (homOfLE hgU).op y)
  obtain ⟨z, rfl⟩ := h i t
  have hu : IsUnit ((X.presheaf.map (homOfLE (X.basicOpen_le g)).op g) ^ k) :=
    (X.toRingedSpace.isUnit_res_basicOpen g).pow k
  refine ⟨_, hgU, hxg, hu.unit⁻¹.1 • M.presheaf.map (homOfLE (X.basicOpen_le g)).op z, ?_⟩
  rw [Hom.app_smul, Hom.app_presheaf_map, ht, smul_smul, IsUnit.val_inv_mul, one_smul]

end Epi

end AlgebraicGeometry.Scheme.Modules
