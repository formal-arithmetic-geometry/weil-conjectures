/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.DeformationSpace.BaseChange
public import WeilConjectures.AlgebraicGeometry.DeformationSpace.NormalConeMap

/-!

# Functoriality of the morphisms of deformation spaces and normal cones

The morphisms of deformation spaces `D_J X' ⟶ D_I X` compose for arbitrary morphisms of schemes
(`AlgebraicGeometry.Scheme.IdealSheafData.deformationSpaceMap_comp`), not only over open
immersions, and so do the morphisms of normal cones `N_J X' ⟶ N_I X`
(`AlgebraicGeometry.Scheme.IdealSheafData.normalConeMap_comp`), the restrictions of the former to
the special fibres.

-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

namespace Scheme.AffineZariskiSite

variable {X : Scheme.{u}} {F : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat.{u}}
  {α : (toOpensFunctor X).op ⋙ X.presheaf ⟶ F} (H : α.Coequifibered)
  (P : X.AffineZariskiSite → Prop) (hP : ∀ x : X, ∃ U, P U ∧ x ∈ U.1)

/-- The open cover of the relative spectrum `Spec_X F` by the charts `Spec F(U)` for the affine
opens `U` satisfying a property `P`, provided these opens cover `X`. -/
noncomputable def coverOfProp : (relativeGluingData H).glued.OpenCover where
  I₀ := {U // P U}
  X U := (relativeGluingData H).functor.obj U.1
  f U := colimit.ι (relativeGluingData H).functor U.1
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    refine ⟨fun z ↦ ?_, fun U ↦ (relativeGluingData H).cover.map_prop U.1⟩
    obtain ⟨U, hU, hz⟩ := hP ((relativeGluingData H).toBase z)
    refine ⟨⟨U, hU⟩, ?_⟩
    have hz' : z ∈ (relativeGluingData H).toBase ⁻¹ᵁ U.1 := hz
    rw [toBase_preimage] at hz'
    exact hz'

include hP in
/-- Two morphisms out of the relative spectrum `Spec_X F` agree if they agree on the charts
`Spec F(U)` for the affine opens `U` satisfying a property `P`, provided these cover `X`. -/
lemma hom_ext_of_prop {Y : Scheme.{u}} {f g : (relativeGluingData H).glued ⟶ Y}
    (hfg : ∀ U, P U → colimit.ι (relativeGluingData H).functor U ≫ f =
      colimit.ι (relativeGluingData H).functor U ≫ g) : f = g :=
  (coverOfProp H P hP).hom_ext _ _ fun U ↦ hfg U.1 U.2

end Scheme.AffineZariskiSite

/-- The morphisms of deformation spaces compose. -/
lemma Scheme.IdealSheafData.deformationSpaceMap_comp
    {X₁ X₂ X₃ : Scheme.{u}} (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃)
    {I₃ : X₃.IdealSheafData} {I₂ : X₂.IdealSheafData} {I₁ : X₁.IdealSheafData}
    (hf : ∀ ⦃U' : X₁.AffineZariskiSite⦄ ⦃U : X₂.AffineZariskiSite⦄ (hU : U'.1 ≤ f ⁻¹ᵁ U.1),
      (I₂.siteIdeal U).map (f.appLE U.1 U'.1 hU).hom ≤ I₁.siteIdeal U')
    (hg : ∀ ⦃U' : X₂.AffineZariskiSite⦄ ⦃U : X₃.AffineZariskiSite⦄ (hU : U'.1 ≤ g ⁻¹ᵁ U.1),
      (I₃.siteIdeal U).map (g.appLE U.1 U'.1 hU).hom ≤ I₂.siteIdeal U')
    (hfg : ∀ ⦃U' : X₁.AffineZariskiSite⦄ ⦃U : X₃.AffineZariskiSite⦄
      (hU : U'.1 ≤ (f ≫ g) ⁻¹ᵁ U.1),
      (I₃.siteIdeal U).map ((f ≫ g).appLE U.1 U'.1 hU).hom ≤ I₁.siteIdeal U') :
    IdealSheafData.deformationSpaceMap f I₂ I₁ hf ≫ IdealSheafData.deformationSpaceMap g I₃ I₂ hg =
      IdealSheafData.deformationSpaceMap (f ≫ g) I₃ I₁ hfg := by
  refine AffineZariskiSite.hom_ext_of_prop I₁.coequifibered_toReesPresheaf
    (fun U₁ ↦ ∃ (U₂ : X₂.AffineZariskiSite) (U₃ : X₃.AffineZariskiSite),
      U₁.1 ≤ f ⁻¹ᵁ U₂.1 ∧ U₂.1 ≤ g ⁻¹ᵁ U₃.1) (fun x ↦ ?_) fun U₁ ⟨U₂, U₃, h₁, h₂⟩ ↦ ?_
  · obtain ⟨U₃, hU₃, hx₃, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
      X₃.isBasis_affineOpens (show g (f x) ∈ (⊤ : X₃.Opens) from trivial)
    obtain ⟨U₂, hU₂, hx₂, h₂⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
      X₂.isBasis_affineOpens (show f x ∈ g ⁻¹ᵁ U₃ from hx₃)
    obtain ⟨U₁, hU₁, hx₁, h₁⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
      X₁.isBasis_affineOpens (show x ∈ f ⁻¹ᵁ U₂ from hx₂)
    exact ⟨⟨U₁, hU₁⟩, ⟨⟨U₂, hU₂⟩, ⟨U₃, hU₃⟩, h₁, h₂⟩, hx₁⟩
  have hU : U₁.1 ≤ (f ≫ g) ⁻¹ᵁ U₃.1 := fun x hx ↦ by
    have := h₂ (h₁ hx)
    simpa using this
  rw [IdealSheafData.deformationSpaceMap, IdealSheafData.deformationSpaceMap,
    IdealSheafData.deformationSpaceMap, AffineZariskiSite.PullbackData.ι_comparison_assoc _ _ _ h₁,
    AffineZariskiSite.PullbackData.ι_comparison _ _ _ h₂,
    AffineZariskiSite.PullbackData.ι_comparison _ _ _ hU, ← Spec.map_comp_assoc]
  congr 2
  ext : 1
  simp only [IdealSheafData.extendedReesPullbackData_map, CommRingCat.hom_comp,
    CommRingCat.hom_ofHom]
  rw [Ideal.extendedReesAlgebraMap_comp]
  congr 1
  rw [← CommRingCat.hom_comp, Scheme.Hom.appLE_comp_appLE]

/-- Blueprint `lemma-naturality-under-base-change-etale--8`, the geometric part: *the morphisms
of normal cones compose.* For `f : X₁ ⟶ X₂` and `g : X₂ ⟶ X₃` with ideal sheaves pulled back
into each other, the morphism of normal cones `N_{I₁} X₁ ⟶ N_{I₃} X₃` induced by `f ≫ g` is the
composite of those induced by `f` and `g`. In particular the identifications of normal cones and
deformation spaces attached to base changes and étale maps of pairs respect composition and
commute with each other. -/
@[reassoc]
lemma Scheme.IdealSheafData.normalConeMap_comp
    {X₁ X₂ X₃ : Scheme.{u}} (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃)
    {I₃ : X₃.IdealSheafData} {I₂ : X₂.IdealSheafData} {I₁ : X₁.IdealSheafData}
    (hf : ∀ ⦃U' : X₁.AffineZariskiSite⦄ ⦃U : X₂.AffineZariskiSite⦄ (hU : U'.1 ≤ f ⁻¹ᵁ U.1),
      (I₂.siteIdeal U).map (f.appLE U.1 U'.1 hU).hom ≤ I₁.siteIdeal U')
    (hg : ∀ ⦃U' : X₂.AffineZariskiSite⦄ ⦃U : X₃.AffineZariskiSite⦄ (hU : U'.1 ≤ g ⁻¹ᵁ U.1),
      (I₃.siteIdeal U).map (g.appLE U.1 U'.1 hU).hom ≤ I₂.siteIdeal U')
    (hfg : ∀ ⦃U' : X₁.AffineZariskiSite⦄ ⦃U : X₃.AffineZariskiSite⦄
      (hU : U'.1 ≤ (f ≫ g) ⁻¹ᵁ U.1),
      (I₃.siteIdeal U).map ((f ≫ g).appLE U.1 U'.1 hU).hom ≤ I₁.siteIdeal U') :
    IdealSheafData.normalConeMap f I₂ I₁ hf ≫ IdealSheafData.normalConeMap g I₃ I₂ hg =
      IdealSheafData.normalConeMap (f ≫ g) I₃ I₁ hfg := by
  rw [← cancel_mono I₃.normalConeToDeformationSpace, Category.assoc,
    IdealSheafData.normalConeMap_normalConeToDeformationSpace,
    IdealSheafData.normalConeMap_normalConeToDeformationSpace_assoc,
    IdealSheafData.deformationSpaceMap_comp f g hf hg hfg,
    IdealSheafData.normalConeMap_normalConeToDeformationSpace]

end AlgebraicGeometry
