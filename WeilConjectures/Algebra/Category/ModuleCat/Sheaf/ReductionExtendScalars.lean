/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ExtendScalarsFlat
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
  `A ⧸ (a)` (`CategoryTheory.Sheaf.extendScalarsCompRestrictScalarsQuotientIso`);
- it preserves flat objects (`CategoryTheory.Sheaf.preservesFlat_extendScalars`, an instance
  form of `CategoryTheory.Sheaf.flat_extendScalars_obj`).

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

omit [Abelian.HasFunctorialFlatResolution 𝒜] [HasDerivedCategory 𝒜] [HasDerivedCategory 𝒜']
  [res.Additive] [PreservesFiniteLimits res] [PreservesFiniteColimits res] in
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
      homEquiv_naturality_left_symm f g := by
        rw [Equiv.symm_apply_eq]
        simp only [Equiv.ofBijective_apply, Functor.map_comp]
        have h := D.r.naturality f
        dsimp at h
        rw [← reassoc_of% h]
        congr 1
        exact ((Equiv.ofBijective _ (D.bijective_r_app_comp_map _ _)).apply_symm_apply g).symm
      homEquiv_naturality_right f g := by simp }

set_option linter.unusedSectionVars false in
@[simp]
lemma adjunction_unit_app (F : 𝒜) : D.adjunction.unit.app F = D.r.app F := by
  simp [adjunction]

end CategoryTheory.Functor.ReductionDatum

-- Make instance search produce the braiding `SymmetricCategory.toBraidedCategory` of `ModuleCat`,
-- as used by the derived tensor product of étale sheaves (`AlgebraicGeometry.Etale.derivedTensor`),
-- so that the monoidal statements below can be compared cheaply with those about derived tensor
-- products.
attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] GrothendieckTopology.braidedCategory_sheaf_of_essentiallySmall

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

/-- With scalars restricted back to `A`, the extension of scalars of `F` is
`F ⊗ A ⧸ ker f`: the form of `CategoryTheory.Sheaf.extendScalarsCompRestrictScalarsIso` for a
surjective `f` with principal kernel, obtained through the reduction functor. -/
noncomputable def extendScalarsCompRestrictScalarsQuotientIso :
    extendScalars J f ⋙ restrictScalars J f ≅
      tensorRight ((constantSheaf J (ModuleCat.{u + 1} A)).obj
        (ModuleCat.of A (A ⧸ RingHom.ker f))) :=
  Functor.isoWhiskerRight (extendScalarsIsoReductionFunctor J hf ha) _ ≪≫
    reductionFunctorCompRestrictScalarsIso J f hf

/-- Extension of scalars of sheaves of modules preserves flat objects
(`CategoryTheory.Sheaf.flat_extendScalars_obj`). -/
instance preservesFlat_extendScalars : (extendScalars J f).PreservesFlat where
  flat_obj hP := flat_extendScalars_obj J f hP

end CategoryTheory.Sheaf
