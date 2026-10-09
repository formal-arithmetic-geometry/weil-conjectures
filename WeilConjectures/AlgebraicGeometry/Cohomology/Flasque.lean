/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.AlgebraicGeometry.Cohomology.LongExact
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic
public import WeilConjectures.Mathlib.Topology.Sheaves.Flasque

/-!
# Flasque sheaves of modules

An `𝒪_X`-module is *flasque* if its underlying abelian sheaf is, i.e. if all its restriction maps
are surjective. Injective `𝒪_X`-modules are flasque, and flasque modules are acyclic for the
pushforward along any morphism of schemes, for the functors of sections, and for the sheaf
cohomology `AlgebraicGeometry.Scheme.Modules.H`. Flasque modules are stable under pushforward
and restriction to open subschemes.

This is the bridge between the right derived functors computed inside `X.Modules` (for instance
the higher direct images) and the sheaf cohomology `H`, which is an `Ext`-group of abelian sheaves:
an injective resolution in `X.Modules` is a flasque resolution of the underlying abelian sheaf.

## Main definitions

- `AlgebraicGeometry.Scheme.Modules.IsFlasque`: flasque `𝒪_X`-modules.
- `AlgebraicGeometry.Scheme.Modules.sectionsFunctor`: the sections over an open, as a functor to
  abelian groups.

## Main statements

- `AlgebraicGeometry.Scheme.Modules.isFlasque_of_injective`: injective modules are flasque.
- `AlgebraicGeometry.Scheme.Modules.rightAcyclic_pushforward_of_isFlasque`,
  `rightAcyclic_sectionsFunctor_of_isFlasque` and `subsingleton_H_of_isFlasque`: flasque modules
  are acyclic for the pushforward, for the sections and for the sheaf cohomology.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

/-- An `𝒪_X`-module is **flasque** if all its restriction maps are surjective, i.e. if its
underlying abelian sheaf is flasque. -/
abbrev IsFlasque (M : X.Modules) : Prop :=
  TopCat.Presheaf.IsFlasque ((toAb X).obj M).obj

lemma IsFlasque.surjective {M : X.Modules} (hM : M.IsFlasque) {U V : X.Opens} (h : V ≤ U) :
    Function.Surjective (M.presheaf.map (homOfLE h).op) :=
  (AddCommGrpCat.epi_iff_surjective _).1 (hM.epi (homOfLE h).op)

lemma IsFlasque.of_surjective {M : X.Modules}
    (h : ∀ {U V : X.Opens} (h : V ≤ U), Function.Surjective (M.presheaf.map (homOfLE h).op)) :
    M.IsFlasque where
  epi i := (AddCommGrpCat.epi_iff_surjective _).2 (h (leOfHom i.unop))

lemma IsFlasque.of_iso {M N : X.Modules} (e : M ≅ N) (hM : M.IsFlasque) : N.IsFlasque where
  epi {U V} i := by
    let φ := (sheafToPresheaf _ _).mapIso ((toAb X).mapIso e)
    have h : ((toAb X).obj N).obj.map i =
        φ.inv.app U ≫ ((toAb X).obj M).obj.map i ≫ φ.hom.app V := by
      erw [φ.hom.naturality i, Iso.inv_hom_id_app_assoc]
      rfl
    have := hM.epi i
    rw [h]
    infer_instance

section Injective

variable (X) in
/-- The sheafified free `𝒪_X`-module `𝒪_W` on the representable presheaf of an open `W`. -/
noncomputable abbrev freeYoneda : X.Opens ⥤ X.Modules :=
  yoneda ⋙ PresheafOfModules.free X.ringCatSheaf.obj ⋙
    PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)

/-- Morphisms `𝒪_W ⟶ M` are the sections of `M` over `W`. -/
noncomputable def freeYonedaHomEquiv (M : X.Modules) (W : X.Opens) :
    ((freeYoneda X).obj W ⟶ M) ≃ Γ(M, W) :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv _ _).trans
    PresheafOfModules.freeYonedaEquiv

lemma freeYonedaHomEquiv_naturality (M : X.Modules) {V W : X.Opens} (i : V ⟶ W)
    (b : (freeYoneda X).obj W ⟶ M) :
    freeYonedaHomEquiv M V ((freeYoneda X).map i ≫ b) =
      M.presheaf.map i.op (freeYonedaHomEquiv M W b) := by
  have h₁ : (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv _ _
      ((freeYoneda X).map i ≫ b) = (PresheafOfModules.free X.ringCatSheaf.obj).map
        (yoneda.map i) ≫ (PresheafOfModules.sheafificationAdjunction
          (𝟙 X.ringCatSheaf.obj)).homEquiv _ _ b :=
    Adjunction.homEquiv_naturality_left _ _ _
  change PresheafOfModules.freeYonedaEquiv
      ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv _ _
        ((freeYoneda X).map i ≫ b)) = _
  rw [h₁]
  have h₂ := Adjunction.homEquiv_naturality_left (PresheafOfModules.freeAdjunction
    X.ringCatSheaf.obj) (yoneda.map i) ((PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)).homEquiv _ _ b)
  rw [PresheafOfModules.freeAdjunction_homEquiv] at h₂
  change yonedaEquiv (PresheafOfModules.freeHomEquiv
    ((PresheafOfModules.free X.ringCatSheaf.obj).map (yoneda.map i) ≫
      (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv _ _ b)) = _
  exact (congrArg yonedaEquiv h₂).trans (yonedaEquiv_naturality _ _).symm

instance (V W : X.Opens) (i : V ⟶ W) : Mono ((freeYoneda X).map i) := by
  have : Mono ((PresheafOfModules.free X.ringCatSheaf.obj).map (yoneda.map i)) := by
    refine PresheafOfModules.mono_of_injective ?_
    intro T
    by_cases h : Nonempty (T.unop ⟶ V)
    · obtain ⟨g⟩ := h
      have hb : Function.Bijective ((yoneda.map i).app T) :=
        ⟨fun _ _ _ ↦ Subsingleton.elim (α := T.unop ⟶ V) _ _,
          fun _ ↦ ⟨g, Subsingleton.elim (α := T.unop ⟶ W) _ _⟩⟩
      have : IsIso ((yoneda.map i).app T) := (isIso_iff_bijective _).2 hb
      exact (ConcreteCategory.bijective_of_isIso
        ((ModuleCat.free (X.ringCatSheaf.obj.obj T)).map ((yoneda.map i).app T))).1
    · have : IsEmpty (T.unop ⟶ V) := not_nonempty_iff.1 h
      intro a b _
      exact Subsingleton.elim (α := (T.unop ⟶ V) →₀ X.ringCatSheaf.obj.obj T) a b
  exact (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map_mono _

/-- **Injective `𝒪_X`-modules are flasque.** -/
theorem isFlasque_of_injective (I : X.Modules) [Injective I] : I.IsFlasque := by
  refine IsFlasque.of_surjective fun {U V} h x ↦ ?_
  refine ⟨freeYonedaHomEquiv I U (Injective.factorThru ((freeYonedaHomEquiv I V).symm x)
    ((freeYoneda X).map (homOfLE h))), ?_⟩
  rw [← freeYonedaHomEquiv_naturality, Injective.comp_factorThru, Equiv.apply_symm_apply]

end Injective

/-- In a short exact sequence `0 ⟶ M₁ ⟶ M₂ ⟶ M₃ ⟶ 0` of `𝒪_X`-modules with `M₁` flasque, the
map `M₂ ⟶ M₃` is surjective on the sections over every open. -/
lemma surjective_app_of_isFlasque {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (h : S.X₁.IsFlasque) (U : X.Opens) : Function.Surjective (S.g.app U) := by
  have hS' := shortExact_map_toSheaf hS
  have : TopCat.Presheaf.IsFlasque (S.map (toAb X)).X₁.obj := h
  exact (AddCommGrpCat.epi_iff_surjective _).1
    (TopCat.Sheaf.IsFlasque.epi_of_shortExact (U := U) hS')

/-- In a short exact sequence `0 ⟶ M₁ ⟶ M₂ ⟶ M₃ ⟶ 0` of `𝒪_X`-modules with `M₁` and `M₂`
flasque, `M₃` is flasque. -/
lemma isFlasque_X₃ {S : ShortComplex X.Modules} (hS : S.ShortExact) (h₁ : S.X₁.IsFlasque)
    (h₂ : S.X₂.IsFlasque) : S.X₃.IsFlasque := by
  have hS' := shortExact_map_toSheaf hS
  have : TopCat.Presheaf.IsFlasque (S.map (toAb X)).X₁.obj := h₁
  have : TopCat.Presheaf.IsFlasque (S.map (toAb X)).X₂.obj := h₂
  exact TopCat.Sheaf.IsFlasque.of_shortExact_of_isFlasque₁₂ hS'

/-- A morphism of `𝒪_X`-modules which is surjective on the sections over every open is an
epimorphism. -/
lemma epi_of_forall_surjective_app {M N : X.Modules} (φ : M ⟶ N)
    (h : ∀ U : X.Opens, Function.Surjective (φ.app U)) : Epi φ :=
  (SheafOfModules.forget _).epi_of_epi_map
    (PresheafOfModules.epi_of_surjective fun U ↦ h U.unop)

/-- The pushforward of a flasque module is flasque. -/
lemma IsFlasque.pushforward {M : X.Modules} (hM : M.IsFlasque) (f : X ⟶ Y) :
    ((pushforward f).obj M).IsFlasque :=
  IsFlasque.of_surjective fun {_ _} h ↦ hM.surjective (f.preimage_mono h)

/-- The restriction of a flasque module to an open subscheme is flasque. -/
lemma IsFlasque.restrict {M : Y.Modules} (hM : M.IsFlasque) (f : X ⟶ Y) [IsOpenImmersion f] :
    (M.restrict f).IsFlasque :=
  IsFlasque.of_surjective fun {_ _} h ↦ hM.surjective (f.image_mono h)

/-- The pullback of a flasque module along an open immersion is flasque. -/
lemma IsFlasque.pullback {M : Y.Modules} (hM : M.IsFlasque) (f : X ⟶ Y) [IsOpenImmersion f] :
    ((Modules.pullback f).obj M).IsFlasque :=
  (hM.restrict f).of_iso ((restrictFunctorIsoPullback f).app M)

/-- The pushforward of a short exact sequence `0 ⟶ M₁ ⟶ M₂ ⟶ M₃ ⟶ 0` with `M₁` flasque is right
exact: `f_* M₂ ⟶ f_* M₃` is an epimorphism. -/
lemma epi_pushforward_map_g {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (h : S.X₁.IsFlasque) (f : X ⟶ Y) : Epi ((pushforward f).map S.g) :=
  epi_of_forall_surjective_app _ fun U ↦ surjective_app_of_isFlasque hS h (f ⁻¹ᵁ U)

instance (f : X ⟶ Y) : PreservesFiniteLimits (pushforward f) :=
  have := (pullbackPushforwardAdjunction f).rightAdjoint_preservesLimits.{0, 0}
  inferInstance

/-- **Flasque modules are acyclic for the pushforward.** -/
theorem rightAcyclic_pushforward_of_isFlasque [HasInjectiveResolutions X.Modules] (f : X ⟶ Y)
    {M : X.Modules} (hM : M.IsFlasque) : (pushforward f).rightAcyclic M :=
  Functor.rightAcyclic_of_epi_map IsFlasque (fun I _ ↦ isFlasque_of_injective I)
    (fun _ hS h₁ h₂ ↦ isFlasque_X₃ hS h₁ h₂) (fun _ hS h ↦ epi_pushforward_map_g hS h f) hM

variable (X) in
/-- The sections over an open `U`, as a functor from `𝒪_X`-modules to abelian groups. -/
noncomputable abbrev sectionsFunctor (U : X.Opens) : X.Modules ⥤ AddCommGrpCat.{u} :=
  toAb X ⋙ sheafToPresheaf _ _ ⋙ (evaluation _ _).obj (op U)

instance (U : X.Opens) : PreservesFiniteLimits (sectionsFunctor X U) := by
  dsimp only [sectionsFunctor]
  infer_instance

instance (U : X.Opens) : (sectionsFunctor X U).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- **Flasque modules are acyclic for the sections over an open.** -/
theorem rightAcyclic_sectionsFunctor_of_isFlasque [HasInjectiveResolutions X.Modules]
    (U : X.Opens) {M : X.Modules} (hM : M.IsFlasque) : (sectionsFunctor X U).rightAcyclic M :=
  Functor.rightAcyclic_of_epi_map IsFlasque (fun I _ ↦ isFlasque_of_injective I)
    (fun _ hS h₁ h₂ ↦ isFlasque_X₃ hS h₁ h₂)
    (fun _ hS h ↦ (AddCommGrpCat.epi_iff_surjective _).2
      (surjective_app_of_isFlasque hS h U)) hM

/-- **Flasque modules have vanishing higher cohomology.** -/
theorem subsingleton_H_of_isFlasque {M : X.Modules} (hM : M.IsFlasque) (n : ℕ) :
    Subsingleton (M.H (n + 1)) :=
  have : TopCat.Presheaf.IsFlasque ((toAb X).obj M).obj := hM
  TopCat.Sheaf.IsFlasque.subsingleton_H ((toAb X).obj M) n

end AlgebraicGeometry.Scheme.Modules
