/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AffineCoordinateComparisonData
import WeilConjectures.AlgebraicGeometry.AffineCoordinateComparisonFamilyBase
import WeilConjectures.AlgebraicGeometry.AffineCoordinateComparisonChartCocycle

/-! # Composition of affine-coordinate comparisons
Source: Stacks Project, Tags 08DW, 06Y1 and 0D5S. -/

@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable [∀ X : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]

/-- Naturality form of one object triangle: propagation of any supplied identification
(Stacks, Tag 0D5S). -/
def AffineComparisonTransportTriangle
    {D T V : Type*} [Category D] [Category T] [Category V]
    (L : D ⥤ T) (B : T ⥤ V) (N : D ⥤ V) (κ : L ⋙ B ≅ N)
    {U : D} {J : T} {K : V}
    (δ₁ : J ≅ L.obj U) (δ₂ : K ≅ N.obj U) (t : K ≅ B.obj J) : Prop :=
  ∀ (U' : D) (a : U ≅ U') (J' : T) (K' : V)
    (e₁ : J' ≅ L.obj U') (e₂ : K' ≅ N.obj U') (e₁₂ : K' ≅ B.obj J'),
    B.mapIso e₁.symm ≪≫ e₁₂.symm = κ.app U' ≪≫ e₂.symm →
    t ≪≫ B.mapIso (δ₁ ≪≫ L.mapIso a ≪≫ e₁.symm) ≪≫ e₁₂.symm =
      δ₂ ≪≫ N.mapIso a ≪≫ e₂.symm

omit [∀ X : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))] in
private theorem affineComparisonTransportTriangle_of_comp
    {D T V : Type*} [Category D] [Category T] [Category V]
    (L : D ⥤ T) (B : T ⥤ V) (N : D ⥤ V) (κ : L ⋙ B ≅ N)
    {U : D} {J : T} {K : V}
    (δ₁ : J ≅ L.obj U) (δ₂ : K ≅ N.obj U) (t : K ≅ B.obj J)
    (hδ : t ≪≫ B.mapIso δ₁ ≪≫ κ.app U = δ₂) :
    AffineComparisonTransportTriangle L B N κ δ₁ δ₂ t := by
  intro U' a J' K' e₁ e₂ e₁₂ he
  apply Iso.ext
  have hd := congrArg Iso.hom hδ
  have hh := congrArg Iso.hom he
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_hom] at hd hh ⊢
  simp only [Functor.map_comp, Category.assoc] at hd hh ⊢
  rw [hh]
  have hn := κ.hom.naturality a.hom
  dsimp only [Functor.comp_map] at hn
  rw [← Category.assoc (B.map (L.map a.hom)), hn]
  simpa only [Category.assoc] using
    congrArg (fun v ↦ v ≫ N.map a.hom ≫ e₂.inv) hd

/-- Affine-coordinate comparisons can be made simultaneously and respect composition
(Stacks, Tags 08DW, 06Y1 and 0D5S). -/
theorem exists_affineCoordinateComparisonFamily :
    ∃ δ : AffineCoordinateComparisonFamily.{u, w},
      ∀ (a b c : AffineComparisonCoordinate.{u, w})
        (φ : a.A →+* b.A) (ψ : b.A →+* c.A) (χ : a.A →+* c.A)
        (hc : χ = ψ.comp φ) (p : b.X ⟶ a.X) (q : c.X ⟶ b.X) (r : c.X ⟶ a.X)
        (hr : q ≫ p = r)
        (hp : b.σ.hom ≫ p = Spec.map (CommRingCat.ofHom φ) ≫ a.σ.hom)
        (hq : c.σ.hom ≫ q = Spec.map (CommRingCat.ofHom ψ) ≫ b.σ.hom)
        (hs : c.σ.hom ≫ r = Spec.map (CommRingCat.ofHom χ) ≫ a.σ.hom)
        (M N : CochainComplex (ModuleCat.{u} a.A) ℤ)
        (hM : AffineComparisonKFlat a.A M) (hN : AffineComparisonKFlat a.A N),
        (c.H.mapIso
          (eqToIso (congrArg (fun t ↦
              ((ModuleCat.extendScalars t).mapHomologicalComplex (.up ℤ)).obj
                M) hc) ≪≫
            (NatIso.mapHomologicalComplex (ModuleCat.extendScalarsComp φ ψ) (.up ℤ)).app
              M) ≪≫
          (δ b c ψ q hq
            (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj M)
            (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj N)
            (CochainComplex.acyclic_mapBifunctor_extendScalars_of_kFlat φ M hM)
            (CochainComplex.acyclic_mapBifunctor_extendScalars_of_kFlat φ N hN)).app true ≪≫
          (derivedPullback q).mapIso ((δ a b φ p hp M N hM hN).app true) ≪≫
          (perfectHomComposition q p).app (a.H.obj M) ≪≫
          (eqToIso (congrArg (fun t ↦ derivedPullback t) hr)).app
            (a.H.obj M) =
          (δ a c χ r hs M N hM hN).app true) ∧
        (c.H.mapIso
          (eqToIso (congrArg (fun t ↦
              ((ModuleCat.extendScalars t).mapHomologicalComplex (.up ℤ)).obj
                N) hc) ≪≫
            (NatIso.mapHomologicalComplex (ModuleCat.extendScalarsComp φ ψ) (.up ℤ)).app
              N) ≪≫
          (δ b c ψ q hq
            (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj M)
            (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj N)
            (CochainComplex.acyclic_mapBifunctor_extendScalars_of_kFlat φ M hM)
            (CochainComplex.acyclic_mapBifunctor_extendScalars_of_kFlat φ N hN)).app false ≪≫
          (derivedPullback q).mapIso ((δ a b φ p hp M N hM hN).app false) ≪≫
          (perfectHomComposition q p).app (a.H.obj N) ≪≫
          (eqToIso (congrArg (fun t ↦ derivedPullback t) hr)).app
            (a.H.obj N) =
          (δ a c χ r hs M N hM hN).app false) := by
  obtain ⟨δ, hδ⟩ := exists_affineCoordinateComparisonFamilyBase.{u, w}
  refine ⟨δ, ?_⟩
  intro a b c φ ψ χ hc p q r hr hp hq hs M N hM hN
  constructor
  · simpa only [hδ a b φ p hp M N hM hN true,
      hδ b c ψ q hq _ _ _ _ true,
      hδ a c χ r hs M N hM hN true, Bool.cond_true] using
      affineCoordinateChartObjectComparison_cocycle a b c φ ψ χ hc p q r hr hp hq hs M hM
  · simpa only [hδ a b φ p hp M N hM hN false,
      hδ b c ψ q hq _ _ _ _ false,
      hδ a c χ r hs M N hM hN false, Bool.cond_false] using
      affineCoordinateChartObjectComparison_cocycle a b c φ ψ χ hc p q r hr hp hq hs N hN


/-- Affine-coordinate comparisons with the naturality form of their composition law
(Stacks, Tags 08DW, 06Y1 and 0D5S). -/
theorem exists_affineCoordinateComparisonTransportFamily :
    ∃ δ : AffineCoordinateComparisonFamily.{u, w},
      ∀ (a b c : AffineComparisonCoordinate.{u, w})
        (φ : a.A →+* b.A) (ψ : b.A →+* c.A) (χ : a.A →+* c.A)
        (hc : χ = ψ.comp φ) (p : b.X ⟶ a.X) (q : c.X ⟶ b.X) (r : c.X ⟶ a.X)
        (hr : q ≫ p = r)
        (hp : b.σ.hom ≫ p = Spec.map (CommRingCat.ofHom φ) ≫ a.σ.hom)
        (hq : c.σ.hom ≫ q = Spec.map (CommRingCat.ofHom ψ) ≫ b.σ.hom)
        (hs : c.σ.hom ≫ r = Spec.map (CommRingCat.ofHom χ) ≫ a.σ.hom)
        (M N : CochainComplex (ModuleCat.{u} a.A) ℤ)
        (hM : AffineComparisonKFlat a.A M) (hN : AffineComparisonKFlat a.A N),
        AffineComparisonTransportTriangle (derivedPullback p) (derivedPullback q)
          (derivedPullback r)
          (perfectHomComposition q p ≪≫ eqToIso (congrArg (fun t ↦ derivedPullback t) hr))
          ((δ a b φ p hp M N hM hN).app true)
          ((δ a c χ r hs M N hM hN).app true)
          (c.H.mapIso
            (eqToIso (congrArg (fun t ↦
                ((ModuleCat.extendScalars t).mapHomologicalComplex (.up ℤ)).obj M) hc) ≪≫
              (NatIso.mapHomologicalComplex (ModuleCat.extendScalarsComp φ ψ) (.up ℤ)).app
                M) ≪≫
            (δ b c ψ q hq
              (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj M)
              (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj N)
              (CochainComplex.acyclic_mapBifunctor_extendScalars_of_kFlat φ M hM)
              (CochainComplex.acyclic_mapBifunctor_extendScalars_of_kFlat φ N hN)).app true) ∧
        AffineComparisonTransportTriangle (derivedPullback p) (derivedPullback q)
          (derivedPullback r)
          (perfectHomComposition q p ≪≫ eqToIso (congrArg (fun t ↦ derivedPullback t) hr))
          ((δ a b φ p hp M N hM hN).app false)
          ((δ a c χ r hs M N hM hN).app false)
          (c.H.mapIso
            (eqToIso (congrArg (fun t ↦
                ((ModuleCat.extendScalars t).mapHomologicalComplex (.up ℤ)).obj N) hc) ≪≫
              (NatIso.mapHomologicalComplex (ModuleCat.extendScalarsComp φ ψ) (.up ℤ)).app
                N) ≪≫
            (δ b c ψ q hq
              (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj M)
              (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj N)
              (CochainComplex.acyclic_mapBifunctor_extendScalars_of_kFlat φ M hM)
              (CochainComplex.acyclic_mapBifunctor_extendScalars_of_kFlat φ N hN)).app false)
      := by
  obtain ⟨δ, hδ⟩ := exists_affineCoordinateComparisonFamily.{u, w}
  refine ⟨δ, ?_⟩
  intro a b c φ ψ χ hc p q r hr hp hq hs M N hM hN
  have hh := hδ a b c φ ψ χ hc p q r hr hp hq hs M N hM hN
  constructor
  · apply affineComparisonTransportTriangle_of_comp
    simpa only [NatIso.trans_app, Iso.trans_assoc, Functor.comp_obj,
      inducedFunctor_obj, Bool.cond_true, Bool.cond_false] using hh.1
  · apply affineComparisonTransportTriangle_of_comp
    simpa only [NatIso.trans_app, Iso.trans_assoc, Functor.comp_obj,
      inducedFunctor_obj, Bool.cond_true, Bool.cond_false] using hh.2

end AlgebraicGeometry
