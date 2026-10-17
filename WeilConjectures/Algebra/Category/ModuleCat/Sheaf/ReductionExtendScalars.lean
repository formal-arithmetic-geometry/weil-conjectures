/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Reduction
public import WeilConjectures.CategoryTheory.Abelian.Flat.PreservesFlat
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Defs
public import WeilConjectures.CategoryTheory.Sites.SheafComposeMonoidal

/-!
# Extension of scalars of sheaves of modules along a quotient map

Let `f : A →+* A'` be a surjective morphism of commutative rings whose kernel is the principal
ideal `(a)`, and `(C, J)` an essentially small site. Extension of scalars
`A' ⊗_A - : Sh(J, A) ⥤ Sh(J, A')`, the sheafified objectwise extension of scalars, is a strong
monoidal left adjoint of restriction of scalars. We show:

- it is a reduction datum (`CategoryTheory.Sheaf.extendScalarsReductionDatum`), being
  isomorphic to the reduction `F ↦ F / a F` of `CategoryTheory.Sheaf.reductionDatum`, so that
  it sends quasi-isomorphisms between K-flat complexes to quasi-isomorphisms and computes the
  derived base change on K-flat complexes;
- with scalars restricted back to `A`, it is the tensor product with the constant sheaf
  `A ⧸ (a)` (`CategoryTheory.Sheaf.extendScalarsCompRestrictScalarsIso`);
- it preserves flat objects (`CategoryTheory.Sheaf.preservesFlat_extendScalars`): with
  scalars restricted to `A`, tensoring with `A' ⊗_A P` is tensoring with `P`.

We first show that the functor of a reduction datum along a fully faithful functor is a left
adjoint (`CategoryTheory.Functor.ReductionDatum.adjunction`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace CategoryTheory.Functor.ReductionDatum

variable {𝒜 𝒜' : Type*} [Category 𝒜] [Abelian 𝒜] [IsGrothendieckAbelian.{u} 𝒜]
  [MonoidalCategory 𝒜] [MonoidalPreadditive 𝒜] [MonoidalClosed 𝒜] [BraidedCategory 𝒜]
  [Abelian.HasFunctorialFlatResolution 𝒜] [HasDerivedCategory 𝒜]
  [Category 𝒜'] [Abelian 𝒜'] [HasDerivedCategory 𝒜']
  {res : 𝒜' ⥤ 𝒜} [res.Additive] [PreservesFiniteLimits res] [PreservesFiniteColimits res]
  {σ : 𝟭 𝒜 ⟶ 𝟭 𝒜} (D : ReductionDatum res σ) [res.Full] [res.Faithful]

/-- A morphism `F ⟶ res M` factors uniquely through the reduction `F ⟶ res Φ(F)`. -/
lemma bijective_r_app_comp_map (F : 𝒜) (M : 𝒜') :
    Function.Bijective fun g : D.Φ.obj F ⟶ M ↦ D.r.app F ≫ res.map g := by
  have := D.epi_r F
  refine ⟨fun g₁ g₂ h ↦ res.map_injective ((cancel_epi (D.r.app F)).1 h), fun h ↦ ?_⟩
  have hσ : σ.app F ≫ h = 0 := by
    have := σ.naturality h
    dsimp at this
    rw [← this, D.σ_app_obj, comp_zero]
  have := (D.exact F).gIsCokernel
  obtain ⟨g, hg⟩ := CokernelCofork.IsColimit.desc' this h hσ
  exact ⟨res.preimage g, by simpa using hg⟩

/-- The functor `Φ` of a reduction datum along a fully faithful `res` is left adjoint to `res`,
the unit being the reduction map. -/
noncomputable def adjunction : D.Φ ⊣ res :=
  Adjunction.mkOfHomEquiv
    { homEquiv F M := Equiv.ofBijective _ (D.bijective_r_app_comp_map F M)
      homEquiv_naturality_left_symm {F F' M} f g := by
        apply (Equiv.ofBijective _ (D.bijective_r_app_comp_map F' M)).injective
        rw [Equiv.apply_symm_apply]
        simp only [Equiv.ofBijective_apply, Functor.map_comp]
        have := D.r.naturality f
        dsimp at this
        rw [reassoc_of% this]
        exact congrArg (f ≫ ·)
          ((Equiv.ofBijective _ (D.bijective_r_app_comp_map F M)).apply_symm_apply g).symm
      homEquiv_naturality_right f g := by simp }

@[simp]
lemma adjunction_unit_app (F : 𝒜) : D.adjunction.unit.app F = D.r.app F := by
  simp [adjunction]

end CategoryTheory.Functor.ReductionDatum

namespace CategoryTheory.Sheaf

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (J : GrothendieckTopology C) {A A' : Type (u + 1)} [CommRing A] [CommRing A'] (f : A →+* A')

/-- Extension of scalars `A' ⊗_A -` of sheaves of modules along `f : A →+* A'`: the
sheafification of the objectwise extension of scalars. -/
noncomputable abbrev extendScalars :
    Sheaf J (ModuleCat.{u + 1} A) ⥤ Sheaf J (ModuleCat.{u + 1} A') :=
  Sheaf.composeAndSheafify J (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} f)

/-- Extension of scalars of sheaves of modules is left adjoint to restriction of scalars. -/
noncomputable def extendScalarsAdjunction : extendScalars J f ⊣ restrictScalars J f :=
  Sheaf.adjunction J (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} f)

/-- Extension of scalars of sheaves of modules is strong monoidal. -/
noncomputable instance monoidal_extendScalars : (extendScalars J f).Monoidal :=
  composeAndSheafifyMonoidal J (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} f)

instance : (extendScalars J f).IsLeftAdjoint := (extendScalarsAdjunction J f).isLeftAdjoint

instance : (extendScalars J f).Additive := (extendScalarsAdjunction J f).left_adjoint_additive

variable {f} (hf : Function.Surjective f) {a : A} (ha : RingHom.ker f = Ideal.span {a})

/-- The reduction `F ↦ F / a F` is left adjoint to restriction of scalars. -/
noncomputable def reductionAdjunction : reductionFunctor J f hf ⊣ restrictScalars J f :=
  have := restrictScalars_full J f hf
  (reductionDatum J f hf a ha).adjunction

/-- Extension of scalars along a surjective `f` is the reduction `F ↦ F / a F`. -/
noncomputable def extendScalarsIsoReductionFunctor :
    extendScalars J f ≅ reductionFunctor J f hf :=
  (extendScalarsAdjunction J f).leftAdjointUniq (reductionAdjunction J hf ha)

include ha in
/-- The unit of the extension of scalars is the reduction map, up to the identification of
`CategoryTheory.Sheaf.extendScalarsIsoReductionFunctor`. -/
lemma extendScalarsAdjunction_unit_app (F : Sheaf J (ModuleCat.{u + 1} A)) :
    (extendScalarsAdjunction J f).unit.app F =
      (reductionNatTrans J f hf).app F ≫
        (restrictScalars J f).map ((extendScalarsIsoReductionFunctor J hf ha).inv.app F) := by
  have h := (extendScalarsAdjunction J f).unit_leftAdjointUniq_hom_app
    (reductionAdjunction J hf ha) F
  have := restrictScalars_full J f hf
  rw [reductionAdjunction, Functor.ReductionDatum.adjunction_unit_app] at h
  rw [← h, Category.assoc, ← Functor.map_comp]
  simp [extendScalarsIsoReductionFunctor]

/-- With scalars restricted back to `A`, the extension of scalars of `F` is
`F ⊗ A ⧸ ker f`. -/
noncomputable def extendScalarsCompRestrictScalarsIso :
    extendScalars J f ⋙ restrictScalars J f ≅
      tensorRight ((constantSheaf J (ModuleCat.{u + 1} A)).obj
        (ModuleCat.of A (A ⧸ RingHom.ker f))) :=
  Functor.isoWhiskerRight (extendScalarsIsoReductionFunctor J hf ha) _ ≪≫
    reductionFunctorCompRestrictScalarsIso J f hf

/-- Restriction of scalars along a surjective ring morphism reflects isomorphisms. -/
lemma reflectsIsomorphisms_restrictScalars : (restrictScalars J f).ReflectsIsomorphisms :=
  have := restrictScalars_full J f hf
  reflectsIsomorphisms_of_full_and_faithful _

/-- The counit `A' ⊗_A M ⟶ M` of extension of scalars is an isomorphism, restriction of scalars
along a surjective ring morphism being fully faithful. -/
lemma isIso_extendScalarsAdjunction_counit : IsIso (extendScalarsAdjunction J f).counit :=
  have := restrictScalars_full J f hf
  (extendScalarsAdjunction J f).counit_isIso_of_R_fully_faithful

/-- The extension of scalars along a surjective ring morphism with principal kernel `(a)` is a
reduction datum for restriction of scalars and the multiplication by `a`, its reduction map
being the unit of the adjunction. -/
noncomputable def extendScalarsReductionDatum :
    Functor.ReductionDatum (restrictScalars J f) (smulNatTrans J a) where
  Φ := extendScalars J f
  r := (extendScalarsAdjunction J f).unit
  σ_app_obj := smulNatTrans_app_restrictScalars_obj J ha
  σ_comp_r F := by
    have h₀ : a • 𝟙 ((restrictScalars J f).obj ((extendScalars J f).obj F)) = 0 :=
      smulNatTrans_app_restrictScalars_obj J ha _
    change (a • 𝟙 F) ≫ _ = 0
    rw [Linear.smul_comp, Category.id_comp,
      ← Category.comp_id ((extendScalarsAdjunction J f).unit.app F), ← Linear.comp_smul, h₀,
      comp_zero]
  epi_r F := by
    rw [extendScalarsAdjunction_unit_app J hf ha]
    have := epi_reductionNatTrans_app J hf F
    infer_instance
  exact F := by
    refine (ShortComplex.exact_iff_of_iso ?_).1 (exact_reductionNatTrans_app J hf ha F)
    exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _)
      ((restrictScalars J f).mapIso ((extendScalarsIsoReductionFunctor J hf ha).app F).symm)
      (by simp) (by simp [extendScalarsAdjunction_unit_app J hf ha])
  quasiIso_map φ _ h₁ h₂ := by
    have := reflectsIsomorphisms_restrictScalars J hf
    exact CochainComplex.quasiIso_map_of_iso_tensorRight _ _
      (extendScalarsCompRestrictScalarsIso J hf ha) φ h₁ h₂

include ha in
/-- With scalars restricted to `A`, tensoring with the extension of scalars `A' ⊗_A P` is
tensoring with `P`: `Res((A' ⊗_A P) ⊗ M) ≅ Res(A' ⊗_A (P ⊗ Res M)) ≅ (P ⊗ Res M) ⊗ A ⧸ (a)`,
and `Res M ⊗ A ⧸ (a) ≅ Res(A' ⊗_A Res M) ≅ Res M`. -/
lemma nonempty_tensorLeft_extendScalars_obj_comp_restrictScalars_iso
    (P : Sheaf J (ModuleCat.{u + 1} A)) :
    Nonempty (tensorLeft ((extendScalars J f).obj P) ⋙ restrictScalars J f ≅
      restrictScalars J f ⋙ tensorLeft P) := by
  have := isIso_extendScalarsAdjunction_counit J hf
  let Fe := extendScalars J f
  let Res := restrictScalars J f
  let c := (constantSheaf J (ModuleCat.{u + 1} A)).obj (ModuleCat.of A (A ⧸ RingHom.ker f))
  let T : Fe ⋙ Res ≅ tensorRight c := extendScalarsCompRestrictScalarsIso J hf ha
  let ε : Res ⋙ Fe ≅ 𝟭 _ := asIso (extendScalarsAdjunction J f).counit
  let assoc : tensorLeft P ⋙ tensorRight c ≅ tensorRight c ⋙ tensorLeft P :=
    NatIso.ofComponents (fun X ↦ α_ P X c) (fun g ↦ by simp)
  let e₁ : Fe ⋙ tensorLeft (Fe.obj P) ⋙ Res ≅ tensorLeft P ⋙ tensorRight c :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (Functor.Monoidal.commTensorLeft Fe P) Res ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft (tensorLeft P) T
  let e₂ : Res ⋙ tensorRight c ≅ Res :=
    Functor.isoWhiskerLeft Res T.symm ≪≫ (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight ε Res ≪≫ Functor.leftUnitor Res
  exact ⟨(Functor.leftUnitor _).symm ≪≫ Functor.isoWhiskerRight ε.symm _ ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft Res (e₁ ≪≫ assoc) ≪≫
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight e₂ (tensorLeft P)⟩

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits in
include ha in
/-- Extension of scalars along a surjective ring morphism with principal kernel preserves flat
objects. -/
lemma preservesFlat_extendScalars : (extendScalars J f).PreservesFlat where
  flat_obj {P} hP := by
    have := reflectsIsomorphisms_restrictScalars J hf
    have := hP.tensorLeft.preservesFiniteLimits
    have := hP.tensorLeft.preservesFiniteColimits
    obtain ⟨e⟩ := nonempty_tensorLeft_extendScalars_obj_comp_restrictScalars_iso J hf ha P
    have : PreservesFiniteLimits
        (tensorLeft ((extendScalars J f).obj P) ⋙ restrictScalars J f) :=
      preservesFiniteLimits_of_natIso e.symm
    have : PreservesFiniteColimits
        (tensorLeft ((extendScalars J f).obj P) ⋙ restrictScalars J f) :=
      preservesFiniteColimits_of_natIso e.symm
    have hL : PreservesFiniteLimits (tensorLeft ((extendScalars J f).obj P)) :=
      preservesFiniteLimits_of_reflects_of_preserves _ (restrictScalars J f)
    have hC : PreservesFiniteColimits (tensorLeft ((extendScalars J f).obj P)) :=
      preservesFiniteColimits_of_reflects_of_preserves _ (restrictScalars J f)
    let β' : tensorLeft ((extendScalars J f).obj P) ≅ tensorRight ((extendScalars J f).obj P) :=
      NatIso.ofComponents (fun Y ↦ β_ _ Y) (fun g ↦ by simp)
    exact ⟨(exactFunctor_iff _).2 ⟨hL, hC⟩, (exactFunctor_iff _).2
      ⟨preservesFiniteLimits_of_natIso β', preservesFiniteColimits_of_natIso β'⟩⟩

end CategoryTheory.Sheaf
