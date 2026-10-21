module

public import WeilConjectures.AlgebraicGeometry.AffineModelCoherentObjectComparisons
public import WeilConjectures.AlgebraicGeometry.PerfectHomTransport
public import WeilConjectures.AlgebraicGeometry.PerfectHomTransportExtension
public import WeilConjectures.Algebra.Homology.ScalarExtensionHom
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.CategoryTheory.InducedCategory
public import WeilConjectures.Algebra.Homology.KFlatModuleBaseChange
public import WeilConjectures.AlgebraicGeometry.AffineCoordinateComparisonChartCocycle
public import WeilConjectures.AlgebraicGeometry.PerfectHomComparisonTriangle

/-! Declarations of ours that lived in the upstream file `WeilConjectures.AlgebraicGeometry.AffineModelCoherentObjectComparisons` (moved out by the scheduled sync, tools/upstream_verbatim.py, 2026-10-20: upstream files are verbatim in live). -/

/-! # Coherent affine object comparisons
Source: Stacks Project, Tags 09RE, 06Y1 and 0D5S.
(blueprint: lem-pc-affine-model-coherent-object-comparisons). -/

@[expose] public section
universe u v w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {I : Type u} [Preorder I]
    (R : I ⥤ CommRingCat.{u}) (c : Cocone R)
    (i : I) (Y : Scheme.{u}) [IsAffine Y] (s : Y ⟶ Spec (R.obj i))
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    (P Q : schemeDerivedCategory Y)
    (F : Set.Ici i ⥤ CommRingCat.{u}) (C : Cocone F)
    (E K : CochainComplex (ModuleCat.{u} (F.obj ⟨i, le_rfl⟩)) ℤ)
    (d : ∀ j : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i),
          schemeDerivedCategory (Spec (F.obj j.val)) ≌
            schemeDerivedCategory (pullback s (Spec.map (R.map (homOfLE j.val.property)))))
      (dlim : schemeDerivedCategory (Spec (C.pt)) ≌
        schemeDerivedCategory (pullback s (Spec.map (c.ι.app i))))

end


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
attribute [local irreducible] DerivedCategory DerivedCategory.Q limit.cone
attribute [local irreducible] perfectHomComposition affineModelLocalizedTilde



section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
/-- Naturality form of one object triangle: propagation of any supplied identification.
Source: Stacks Project, Tag 0D5S, and naturality of the composition comparison.
(blueprint: lem-pc-affine-model-coherent-object-comparisons). -/
@[no_expose] private def affineModelTransportTriangle
    {D T V : Type*} [Category D] [Category T] [Category V]
    (L : D ⥤ T) (B : T ⥤ V) (N : D ⥤ V) (κ : L ⋙ B ≅ N)
    {U : D} {J : T} {K K₀ : V}
    (δ₁ : J ≅ L.obj U) (δ₂ : K ≅ N.obj U)
    (μ : K ≅ K₀) (t : K₀ ≅ B.obj J) : Prop :=
  ∀ (U' : D) (a : U ≅ U') (J' : T) (K' : V)
    (e₁ : J' ≅ L.obj U') (e₂ : K' ≅ N.obj U') (e₁₂ : K' ≅ B.obj J'),
    B.mapIso e₁.symm ≪≫ e₁₂.symm = κ.app U' ≪≫ e₂.symm →
    μ ≪≫ t ≪≫ B.mapIso (δ₁ ≪≫ L.mapIso a ≪≫ e₁.symm) ≪≫ e₁₂.symm =
      δ₂ ≪≫ N.mapIso a ≪≫ e₂.symm

private theorem affineModelTransportTriangle_of_comp
    {D T V : Type*} [Category D] [Category T] [Category V]
    (L : D ⥤ T) (B : T ⥤ V) (N : D ⥤ V) (κ : L ⋙ B ≅ N)
    {U : D} {J : T} {K K₀ : V}
    (δ₁ : J ≅ L.obj U) (δ₂ : K ≅ N.obj U)
    (μ : K ≅ K₀) (t : K₀ ≅ B.obj J)
    (hδ : μ ≪≫ t ≪≫ B.mapIso δ₁ ≪≫ κ.app U = δ₂) :
    affineModelTransportTriangle L B N κ δ₁ δ₂ μ t := by
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

end

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The one-model object comparison, with geometric projection objects fixed explicitly.
Source: chart comparison and projection composition, Stacks Tags 09RE and 0D5S.
(blueprint: lem-pc-affine-model-coherent-object-comparisons). -/
@[irreducible, no_expose] private noncomputable def affineModelComparisonObject
    [∀ X : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (a b : AffineComparisonCoordinate.{u, w}) (φ : a.A →+* b.A) (p : b.X ⟶ a.X)
    (hp : b.σ.hom ≫ p = Spec.map (CommRingCat.ofHom φ) ≫ a.σ.hom)
    (M : CochainComplex (ModuleCat.{u} a.A) ℤ) (hM : AffineComparisonKFlat a.A M)
    (Z : Scheme.{u}) (f₀ : a.X ⟶ Z) (f₁ : b.X ⟶ Z) (P : schemeDerivedCategory Z)
    (a₀ : a.H.obj M ≅ (derivedPullback f₀).obj P)
    (ε : (derivedPullback f₁).obj P ≅
      (derivedPullback p).obj ((derivedPullback f₀).obj P)) :
    b.H.obj (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj M) ≅
      (derivedPullback f₁).obj P :=
  affineCoordinateChartObjectComparison a b φ p hp M hM ≪≫
    (derivedPullback p).mapIso a₀ ≪≫ ε.symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Transport the one-model chart cocycle through an arbitrary bottom identification.
Source: Stacks Project, Tag 0D5S, and the chart cocycle.
(blueprint: lem-pc-affine-model-coherent-object-comparisons). -/
@[no_expose] private def affineModelChartTransportEquation
    [∀ X : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (a b c : AffineComparisonCoordinate.{u, w})
    (φ : a.A →+* b.A) (ψ : b.A →+* c.A) (χ : a.A →+* c.A)
    (hc : χ = ψ.comp φ) (p : b.X ⟶ a.X) (q : c.X ⟶ b.X) (r : c.X ⟶ a.X)
    (_hr : q ≫ p = r)
    (hp : b.σ.hom ≫ p = Spec.map (CommRingCat.ofHom φ) ≫ a.σ.hom)
    (hq : c.σ.hom ≫ q = Spec.map (CommRingCat.ofHom ψ) ≫ b.σ.hom)
    (hs : c.σ.hom ≫ r = Spec.map (CommRingCat.ofHom χ) ≫ a.σ.hom)
    (M : CochainComplex (ModuleCat.{u} a.A) ℤ)
    (hM : AffineComparisonKFlat a.A M)
    (Z : Scheme.{u}) (f₀ : a.X ⟶ Z) (f₁ : b.X ⟶ Z) (f₂ : c.X ⟶ Z)
    (P : schemeDerivedCategory Z)
    (a₀ : a.H.obj M ≅ (derivedPullback f₀).obj P)
    (e₁ : (derivedPullback f₁).obj P ≅
      (derivedPullback p).obj ((derivedPullback f₀).obj P))
    (e₂ : (derivedPullback f₂).obj P ≅
      (derivedPullback r).obj ((derivedPullback f₀).obj P))
    (e₁₂ : (derivedPullback f₂).obj P ≅
      (derivedPullback q).obj ((derivedPullback f₁).obj P)) : Prop :=
    c.H.mapIso (affineModelScalarAssocIso φ ψ χ hc M) ≪≫
      affineCoordinateChartObjectComparison b c ψ q hq
        (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj M)
        (CochainComplex.acyclic_mapBifunctor_extendScalars_of_kFlat φ M hM) ≪≫
      (derivedPullback q).mapIso
        (affineModelComparisonObject a b φ p hp M hM Z f₀ f₁ P a₀ e₁) ≪≫ e₁₂.symm =
      affineModelComparisonObject a c χ r hs M hM Z f₀ f₂ P a₀ e₂

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Folded geometric equation for transport along one affine chart triangle.
Source: the object triangle of Stacks Project, Tag 0D5S.
(blueprint: lem-pc-affine-model-coherent-object-comparisons). -/
private theorem affineModelChartTransportTriangle
    [∀ X : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (a b c : AffineComparisonCoordinate.{u, w})
    (φ : a.A →+* b.A) (ψ : b.A →+* c.A) (χ : a.A →+* c.A)
    (hc : χ = ψ.comp φ) (p : b.X ⟶ a.X) (q : c.X ⟶ b.X) (r : c.X ⟶ a.X)
    (hr : q ≫ p = r)
    (hp : b.σ.hom ≫ p = Spec.map (CommRingCat.ofHom φ) ≫ a.σ.hom)
    (hq : c.σ.hom ≫ q = Spec.map (CommRingCat.ofHom ψ) ≫ b.σ.hom)
    (hs : c.σ.hom ≫ r = Spec.map (CommRingCat.ofHom χ) ≫ a.σ.hom)
    (M : CochainComplex (ModuleCat.{u} a.A) ℤ)
    (hM : AffineComparisonKFlat a.A M)
    (Z : Scheme.{u}) (f₀ : a.X ⟶ Z) (f₁ : b.X ⟶ Z) (f₂ : c.X ⟶ Z)
    (P : schemeDerivedCategory Z)
    (a₀ : a.H.obj M ≅ (derivedPullback f₀).obj P)
    (e₁ : (derivedPullback f₁).obj P ≅
      (derivedPullback p).obj ((derivedPullback f₀).obj P))
    (e₂ : (derivedPullback f₂).obj P ≅
      (derivedPullback r).obj ((derivedPullback f₀).obj P))
    (e₁₂ : (derivedPullback f₂).obj P ≅
      (derivedPullback q).obj ((derivedPullback f₁).obj P))
    (he : (derivedPullback q).mapIso e₁.symm ≪≫ e₁₂.symm =
      (perfectHomComposition q p ≪≫
        eqToIso (congrArg (fun t ↦ derivedPullback t) hr)).app
          ((derivedPullback f₀).obj P) ≪≫ e₂.symm) :
    affineModelChartTransportEquation a b c φ ψ χ hc p q r hr hp hq hs
      M hM Z f₀ f₁ f₂ P a₀ e₁ e₂ e₁₂ := by
  have hδ := affineCoordinateChartObjectComparison_cocycle
    a b c φ ψ χ hc p q r hr hp hq hs M hM
  have hh := affineModelTransportTriangle_of_comp
    (derivedPullback p) (derivedPullback q) (derivedPullback r)
    (perfectHomComposition q p ≪≫ eqToIso (congrArg (fun t ↦ derivedPullback t) hr))
    (affineCoordinateChartObjectComparison a b φ p hp M hM)
    (affineCoordinateChartObjectComparison a c χ r hs M hM)
    (c.H.mapIso (affineModelScalarAssocIso φ ψ χ hc M))
    (affineCoordinateChartObjectComparison b c ψ q hq
      (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj M)
      (CochainComplex.acyclic_mapBifunctor_extendScalars_of_kFlat φ M hM))
    (by simpa only [affineModelScalarAssocIso, NatIso.trans_app, Functor.comp_obj,
      Iso.trans_assoc] using hδ)
  unfold affineModelChartTransportEquation affineModelComparisonObject
  exact hh _ a₀ _ _ e₁ e₂ e₁₂ he

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Object transport retaining the actual comparison on both labelled models.
Source: the full two-label affine comparison, Stacks Tags 09RE and 0D5S.
(blueprint: lem-pc-affine-model-coherent-object-comparisons). -/
@[no_expose] private def affineModelLabelledTransportEquation
    [∀ X : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (a b c : AffineComparisonCoordinate.{u, w})
    (φ : a.A →+* b.A) (ψ : b.A →+* c.A) (χ : a.A →+* c.A)
    (hc : χ = ψ.comp φ) (p : b.X ⟶ a.X) (q : c.X ⟶ b.X) (r : c.X ⟶ a.X)
    (_hr : q ≫ p = r)
    (hp : b.σ.hom ≫ p = Spec.map (CommRingCat.ofHom φ) ≫ a.σ.hom)
    (hq : c.σ.hom ≫ q = Spec.map (CommRingCat.ofHom ψ) ≫ b.σ.hom)
    (hs : c.σ.hom ≫ r = Spec.map (CommRingCat.ofHom χ) ≫ a.σ.hom)
    (E K : CochainComplex (ModuleCat.{u} a.A) ℤ)
    (hE : AffineComparisonKFlat a.A E) (hK : AffineComparisonKFlat a.A K)
    (t : Bool) (hM : AffineComparisonKFlat a.A (cond t E K))
    (Z : Scheme.{u}) (f₀ : a.X ⟶ Z) (f₁ : b.X ⟶ Z) (f₂ : c.X ⟶ Z)
    (P : schemeDerivedCategory Z)
    (a₀ : a.H.obj (cond t E K) ≅ (derivedPullback f₀).obj P)
    (e₁ : (derivedPullback f₁).obj P ≅
      (derivedPullback p).obj ((derivedPullback f₀).obj P))
    (e₂ : (derivedPullback f₂).obj P ≅
      (derivedPullback r).obj ((derivedPullback f₀).obj P))
    (e₁₂ : (derivedPullback f₂).obj P ≅
      (derivedPullback q).obj ((derivedPullback f₁).obj P)) : Prop := by
  cases t
  · exact c.H.mapIso (affineModelScalarAssocIso φ ψ χ hc (K)) ≪≫
        (affineCoordinateDerivedComparison b c ψ q hq
          (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj E)
          (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj K)
          (CochainComplex.acyclic_mapBifunctor_extendScalars_of_kFlat φ E hE)
          (CochainComplex.acyclic_mapBifunctor_extendScalars_of_kFlat φ K hK)).app false ≪≫
        (derivedPullback q).mapIso
          (affineModelComparisonObject a b φ p hp (K) hM Z f₀ f₁ P a₀ e₁) ≪≫ e₁₂.symm =
        affineModelComparisonObject a c χ r hs (K) hM Z f₀ f₂ P a₀ e₂
  · exact c.H.mapIso (affineModelScalarAssocIso φ ψ χ hc (E)) ≪≫
        (affineCoordinateDerivedComparison b c ψ q hq
          (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj E)
          (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj K)
          (CochainComplex.acyclic_mapBifunctor_extendScalars_of_kFlat φ E hE)
          (CochainComplex.acyclic_mapBifunctor_extendScalars_of_kFlat φ K hK)).app true ≪≫
        (derivedPullback q).mapIso
          (affineModelComparisonObject a b φ p hp (E) hM Z f₀ f₁ P a₀ e₁) ≪≫ e₁₂.symm =
        affineModelComparisonObject a c χ r hs (E) hM Z f₀ f₂ P a₀ e₂

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Object transport retaining the actual comparison on both labelled models.
Source: the full two-label affine comparison, Stacks Tags 09RE and 0D5S.
(blueprint: lem-pc-affine-model-coherent-object-comparisons). -/
private theorem affineModelLabelledTransportTriangle
    [∀ X : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (a b c : AffineComparisonCoordinate.{u, w})
    (φ : a.A →+* b.A) (ψ : b.A →+* c.A) (χ : a.A →+* c.A)
    (hc : χ = ψ.comp φ) (p : b.X ⟶ a.X) (q : c.X ⟶ b.X) (r : c.X ⟶ a.X)
    (hr : q ≫ p = r)
    (hp : b.σ.hom ≫ p = Spec.map (CommRingCat.ofHom φ) ≫ a.σ.hom)
    (hq : c.σ.hom ≫ q = Spec.map (CommRingCat.ofHom ψ) ≫ b.σ.hom)
    (hs : c.σ.hom ≫ r = Spec.map (CommRingCat.ofHom χ) ≫ a.σ.hom)
    (E K : CochainComplex (ModuleCat.{u} a.A) ℤ)
    (hE : AffineComparisonKFlat a.A E) (hK : AffineComparisonKFlat a.A K)
    (t : Bool) (hM : AffineComparisonKFlat a.A (cond t E K))
    (Z : Scheme.{u}) (f₀ : a.X ⟶ Z) (f₁ : b.X ⟶ Z) (f₂ : c.X ⟶ Z)
    (P : schemeDerivedCategory Z)
    (a₀ : a.H.obj (cond t E K) ≅ (derivedPullback f₀).obj P)
    (e₁ : (derivedPullback f₁).obj P ≅
      (derivedPullback p).obj ((derivedPullback f₀).obj P))
    (e₂ : (derivedPullback f₂).obj P ≅
      (derivedPullback r).obj ((derivedPullback f₀).obj P))
    (e₁₂ : (derivedPullback f₂).obj P ≅
      (derivedPullback q).obj ((derivedPullback f₁).obj P))
    (he : (derivedPullback q).mapIso e₁.symm ≪≫ e₁₂.symm =
      (perfectHomComposition q p ≪≫
        eqToIso (congrArg (fun t ↦ derivedPullback t) hr)).app
          ((derivedPullback f₀).obj P) ≪≫ e₂.symm) :
    affineModelLabelledTransportEquation a b c φ ψ χ hc p q r hr hp hq hs
      E K hE hK t hM Z f₀ f₁ f₂ P a₀ e₁ e₂ e₁₂ := by
  cases t
  · change affineModelChartTransportEquation a b c φ ψ χ hc p q r hr hp hq hs
      K hK Z f₀ f₁ f₂ P a₀ e₁ e₂ e₁₂
    exact affineModelChartTransportTriangle a b c φ ψ χ hc p q r hr hp hq hs
      K hK Z f₀ f₁ f₂ P a₀ e₁ e₂ e₁₂ he
  · change affineModelChartTransportEquation a b c φ ψ χ hc p q r hr hp hq hs
      E hE Z f₀ f₁ f₂ P a₀ e₁ e₂ e₁₂
    exact affineModelChartTransportTriangle a b c φ ψ χ hc p q r hr hp hq hs
      E hE Z f₀ f₁ f₂ P a₀ e₁ e₂ e₁₂ he

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The projection comparison component, retaining its geometric object types.
Source: the fixed projection comparison, Stacks Tag 0D5S.
(blueprint: lem-pc-affine-model-coherent-object-comparisons). -/
@[irreducible, no_expose] private noncomputable def affineModelProjectionComparison
    [∀ X : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    {X S : Scheme.{u}} (s : X ⟶ S) {T T' : Over S} (g : T' ⟶ T)
    (P : schemeDerivedCategory X) :
    (derivedPullback (pullback.fst s T'.hom)).obj P ≅
      (derivedPullback (baseChangeMap s g)).obj
        ((derivedPullback (pullback.fst s T.hom)).obj P) :=
  (perfectHomComparison s g).app P

attribute [local irreducible] perfectHomComparison ModuleCat.extendScalars
  Functor.mapHomologicalComplex

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
end AlgebraicGeometry
