/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.KunnethGeneric
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionIhom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriekLocalizing
public import WeilConjectures.TraceFormula.Specialization.TraitModelEmbedding
public import WeilConjectures.TraceFormula.Specialization.TraitProductRestrict

/-!

# Gabber's Künneth formula for nearby cycles: passing to proper closures

Let `P` be the product over the trait `S = Spec k'⟦t⟧` of models `M`, `N` of finite type over `S`
along `qM : 𝒳 ⟶ S`, `qN : 𝒴 ⟶ S`, whose identifications factor through the total spaces,
`ε_M = j ≫ e_M`, `ε_N = j ≫ e_N`, and whose second projection is compatible with the structure
morphisms of the geometric generic fibres to `Spec Ω`. Given open immersions `𝒳 ⟶ 𝒳̄`,
`𝒴 ⟶ 𝒴̄` over `S` into proper `S`-schemes, this file shows that Gabber's Künneth formula for the
product `𝒳̄ ×_S 𝒴̄` of the standard models of `𝒳̄`, `𝒴̄` implies it for `P`
(`AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.isIso_kunnethMap_of_closure`):

* the Künneth map is natural in the coefficients
  (`NearbyCyclesModel.kunnethMap_naturality`);
* the Künneth map of `P` is the Künneth map of the models of the total spaces, applied to
  `Le_M^* A`, `Le_N^* B` (`NearbyCyclesModel.isIso_kunnethMap_of_toGeometricGeneric`); these
  models are restrictions of the standard models of `𝒳̄`, `𝒴̄`, `𝒳̄ ×_S 𝒴̄` along open immersions
  with cartesian squares of geometric generic fibres;
* by the restriction of the Künneth map to opens
  (`NearbyCyclesModel.isIso_map_kunnethMap_iff_of_isKunnethRestriction`) applied to the
  extensions by zero `u_! A`, `u_! B` (with `Lu^* u_! ≅ 𝟭`), the Künneth map of the models of the
  total spaces is invertible if the one of the closures is.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

section Abstract

variable {CM CN CP SM SN T : Type*} [Category CM] [Category CN] [Category CP] [Category SM]
  [Category SN] [Category T] [MonoidalCategory CP] [MonoidalCategory T]
  {ΨM : CM ⥤ SM} {ΨN : CN ⥤ SN} {ΨP : CP ⥤ T} {s₁ : SM ⥤ T} {s₂ : SN ⥤ T} {g₁ : CM ⥤ CP}
  {g₂ : CN ⥤ CP}

/-- Naturality of a Künneth map `(α₁ ⊗ α₂) ≫ μ`, for abstract functors. -/
lemma kunnethMap_naturality_aux (α₁ : ΨM ⋙ s₁ ⟶ g₁ ⋙ ΨP) (α₂ : ΨN ⋙ s₂ ⟶ g₂ ⋙ ΨP)
    (μ : ∀ U V, ΨP.obj U ⊗ ΨP.obj V ⟶ ΨP.obj (U ⊗ V))
    (hμ : ∀ {U U' V V' : CP} (x : U ⟶ U') (y : V ⟶ V'),
      (ΨP.map x ⊗ₘ ΨP.map y) ≫ μ U' V' = μ U V ≫ ΨP.map (x ⊗ₘ y))
    {A A' : CM} {B B' : CN} (a : A ⟶ A') (b : B ⟶ B') :
    ((α₁.app A ⊗ₘ α₂.app B) ≫ μ _ _) ≫ ΨP.map (g₁.map a ⊗ₘ g₂.map b) =
      (s₁.map (ΨM.map a) ⊗ₘ s₂.map (ΨN.map b)) ≫ (α₁.app A' ⊗ₘ α₂.app B') ≫ μ _ _ := by
  have h₁ := α₁.naturality a
  have h₂ := α₂.naturality b
  simp only [Functor.comp_map] at h₁ h₂
  rw [Category.assoc, ← hμ, tensorHom_comp_tensorHom_assoc, ← h₁, ← h₂,
    tensorHom_comp_tensorHom_assoc]

end Abstract

section General

variable {X X' Y Y' Z Z' : Scheme.{u}} {M : NearbyCyclesModel X X'} {N : NearbyCyclesModel Y Y'}
  {P : NearbyCyclesModel Z Z'} {f₁ : Z ⟶ X} {f₁' : Z' ⟶ X'} {f₂ : Z ⟶ Y} {f₂' : Z' ⟶ Y'}

/-- The Künneth map `Π_{A,B}` is natural in `A` and `B`. -/
lemma kunnethMap_naturality (φ₁ : P.Hom M f₁ f₁') (φ₂ : P.Hom N f₂ f₂')
    {A A' : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))}
    {B B' : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y))} (a : A ⟶ A') (b : B ⟶ B') :
    kunnethMap Λ φ₁ φ₂ A B ≫
        (P.nearbyCycles Λ).map (L((f₁)^*⟦Λ⟧).map a ⊗ₘ L((f₂)^*⟦Λ⟧).map b) =
      (L((f₁')^*⟦Λ⟧).map ((M.nearbyCycles Λ).map a) ⊗ₘ
          L((f₂')^*⟦Λ⟧).map ((N.nearbyCycles Λ).map b)) ≫ kunnethMap Λ φ₁ φ₂ A' B' := by
  exact kunnethMap_naturality_aux (φ₁.pullbackExchange Λ) (φ₂.pullbackExchange Λ)
    (P.tensorMap Λ) (fun x y ↦ P.tensorMap_natural Λ x y) a b

/-- The Künneth map `Π_{A,B}` is invertible if `Π_{A',B'}` is, for `A ≅ A'` and `B ≅ B'`. -/
lemma isIso_kunnethMap_of_iso (φ₁ : P.Hom M f₁ f₁') (φ₂ : P.Hom N f₂ f₂')
    {A A' : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))}
    {B B' : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y))} (a : A ≅ A') (b : B ≅ B')
    (h : IsIso (kunnethMap Λ φ₁ φ₂ A' B')) : IsIso (kunnethMap Λ φ₁ φ₂ A B) := by
  have e := kunnethMap_naturality Λ φ₁ φ₂ a.hom b.hom
  have : IsIso (kunnethMap Λ φ₁ φ₂ A B ≫
      (P.nearbyCycles Λ).map (L((f₁)^*⟦Λ⟧).map a.hom ⊗ₘ L((f₂)^*⟦Λ⟧).map b.hom)) := by
    rw [e]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    ((P.nearbyCycles Λ).map (L((f₁)^*⟦Λ⟧).map a.hom ⊗ₘ L((f₂)^*⟦Λ⟧).map b.hom))

/-- The inclusion `M.geometric ⟶ M` of the geometric model of the total space into a model whose
identification factors as `ε = j ≫ e`, over `e` and `𝟙 X'`. -/
@[simps]
def geometricHom (M : NearbyCyclesModel X X') {e : M.total ⟶ X} (he : M.j ≫ e = M.ε) :
    M.geometric.Hom M e (𝟙 X') where
  total := 𝟙 _
  generic := 𝟙 _
  comm_j := by simp [geometric]
  comm_i := by simp [geometric]
  comm_ε := by simp [geometric, he]

/-- The morphism `M.geometric.toGeneric ⟶ M` of models over `ε` and `𝟙 X'`. -/
@[simps]
def toGenericHom (M : NearbyCyclesModel X X') : M.geometric.toGeneric.Hom M M.ε (𝟙 X') where
  total := 𝟙 _
  generic := 𝟙 _
  comm_j := by simp [geometric]
  comm_i := by simp [geometric]
  comm_ε := by simp [geometric]

/-- A morphism of models `φ : P ⟶ M` induces a morphism
`P.geometric.toGeneric ⟶ M.geometric` over `j_P ≫ φ.total`. -/
@[simps]
def Hom.toGeometricGeneric (φ : P.Hom M f₁ f₁') :
    P.geometric.toGeneric.Hom M.geometric (P.j ≫ φ.total) f₁' where
  total := φ.total
  generic := φ.generic
  comm_j := φ.comm_j
  comm_i := φ.comm_i
  comm_ε := by simpa [geometric] using φ.comm_j

/-- The inclusions of the models of the total spaces are restriction data of the Künneth map. -/
lemma isKunnethRestriction_toGeometricGeneric (φ₁ : P.Hom M f₁ f₁') (φ₂ : P.Hom N f₂ f₂')
    {eM : M.total ⟶ X} (heM : M.j ≫ eM = M.ε) {eN : N.total ⟶ Y} (heN : N.j ≫ eN = N.ε) :
    IsKunnethRestriction φ₁ φ₂ φ₁.toGeometricGeneric φ₂.toGeometricGeneric (M.geometricHom heM)
      (N.geometricHom heN) P.toGenericHom where
  htot₁ := by simp
  hgen₁ := by simp
  htot₂ := by simp
  hgen₂ := by simp
  hb₁ := by
    simp only [Category.assoc]
    rw [← reassoc_of% φ₁.comm_j, heM, φ₁.comm_ε]
  hs₁ := by simp
  hb₂ := by
    simp only [Category.assoc]
    rw [← reassoc_of% φ₂.comm_j, heN, φ₂.comm_ε]
  hs₂ := by simp
  isOpenImmersion_M := inferInstanceAs (IsOpenImmersion (𝟙 _))
  isOpenImmersion_N := inferInstanceAs (IsOpenImmersion (𝟙 _))
  isOpenImmersion_P := inferInstanceAs (IsOpenImmersion (𝟙 _))
  isPullback_M :=
    have : IsIso (M.geometricHom heM).generic := inferInstanceAs (IsIso (𝟙 _))
    have : IsIso (M.geometricHom heM).total := inferInstanceAs (IsIso (𝟙 _))
    IsPullback.of_horiz_isIso ⟨by simp [geometric]⟩
  isPullback_N :=
    have : IsIso (N.geometricHom heN).generic := inferInstanceAs (IsIso (𝟙 _))
    have : IsIso (N.geometricHom heN).total := inferInstanceAs (IsIso (𝟙 _))
    IsPullback.of_horiz_isIso ⟨by simp [geometric]⟩
  isPullback_P :=
    have : IsIso P.toGenericHom.generic := inferInstanceAs (IsIso (𝟙 _))
    have : IsIso P.toGenericHom.total := inferInstanceAs (IsIso (𝟙 _))
    IsPullback.of_horiz_isIso ⟨by simp [geometric]⟩

/-- **Reduction to the models of the total spaces**: for models whose identifications factor
through the total spaces, `ε_M = j ≫ e_M`, `ε_N = j ≫ e_N`, the Künneth map `Π_{A,B}` is
invertible if the Künneth map `Π_{Le_M^* A, Le_N^* B}` of the models `M.geometric`,
`N.geometric`, `P.geometric.toGeneric` is. -/
theorem isIso_kunnethMap_of_toGeometricGeneric (φ₁ : P.Hom M f₁ f₁') (φ₂ : P.Hom N f₂ f₂')
    {eM : M.total ⟶ X} (heM : M.j ≫ eM = M.ε) {eN : N.total ⟶ Y} (heN : N.j ≫ eN = N.ε)
    (A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y)))
    (h : IsIso (kunnethMap Λ φ₁.toGeometricGeneric φ₂.toGeometricGeneric
      (L((eM)^*⟦Λ⟧).obj A) (L((eN)^*⟦Λ⟧).obj B))) :
    IsIso (kunnethMap Λ φ₁ φ₂ A B) := by
  have := (isIso_map_kunnethMap_iff_of_isKunnethRestriction Λ
    (isKunnethRestriction_toGeometricGeneric φ₁ φ₂ heM heN) A B).2 h
  exact (NatIso.isIso_map_iff (leftDerivedUpperStarId Λ Z') _).1 this

end General

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
