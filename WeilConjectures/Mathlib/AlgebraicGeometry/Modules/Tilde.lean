/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

/-!
# Coherence of `M^~` on an affine scheme, and affine-locality of coherence

For a commutative ring `R` and an `R`-module `M`, the quasi-coherent sheaf `M^~` on `Spec R` is
coherent as soon as `M` is a finite `R`-module, and conversely a finite family of global sections
generating `M^~` generates `M`.

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
- `instance : PreservesFiniteLimits (AlgebraicGeometry.tilde.functor R)`: `M ↦ M^~` is exact.
- `AlgebraicGeometry.Scheme.Modules.kernelIsoTilde` and
  `AlgebraicGeometry.Scheme.Modules.cokernelIsoTilde`: on an affine scheme, kernels and
  cokernels of morphisms of quasi-coherent sheaves of modules are the sheaves associated to the
  kernel and the cokernel of the induced morphism of modules of global sections.
- `AlgebraicGeometry.Scheme.Modules.isCoherent_of_isOpenCover` and
  `AlgebraicGeometry.Scheme.Modules.exists_isOpenCover_finite`: coherence is affine-local.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory Limits Opposite SheafOfModules

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

end AlgebraicGeometry
