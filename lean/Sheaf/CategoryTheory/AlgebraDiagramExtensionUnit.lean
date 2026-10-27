/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Sheaf.CategoryTheory.AlgebraDiagramPullbackData
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import all Sheaf.CategoryTheory.DerivedCategory.CokernelAdjointExchange
import all Sheaf.CategoryTheory.AlgebraDiagramOrdinaryUnitNaturality
import all Sheaf.Paper.PullbackTensorCanonicalShiftUnit
import all Sheaf.Paper.KFlatScalarComparisonNormalization
/-! # Units of normalized scalar-association comparisons

Source: Stacks 03EL and 07A4
(blueprint: lem-pur-algebra-diagram-extension-unit).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance 100000] CategoryTheory.hasSheafCompose_of_preservesLimitsOfSize
open CategoryTheory CategoryTheory.Limits CategoryTheory.CochainPullback
open SheafOfModules.PullbackTensorCanonical
universe u₀ v₀ w₀
section
variable {A B A' B' : Type u₀}
  [Category.{v₀} A] [Category.{v₀} B] [Category.{v₀} A'] [Category.{v₀} B']
  [Abelian A] [Abelian B] [Abelian A'] [Abelian B']
  [HasDerivedCategory.{w₀} A] [HasDerivedCategory.{w₀} B]
  [HasDerivedCategory.{w₀} A'] [HasDerivedCategory.{w₀} B']
  (E : A ⥤ B) (E' : A' ⥤ B') [E.Additive] [E'.Additive]
  (R : B ⥤ A) (R' : B' ⥤ A') [R.Additive] [R'.Additive]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R]
  [PreservesFiniteLimits R'] [PreservesFiniteColimits R']
  (a : E ⊣ R) (a' : E' ⊣ R')
  (L : DerivedCategory A ⥤ DerivedCategory B)
  (L' : DerivedCategory A' ⥤ DerivedCategory B')
  (ad : L ⊣ R.mapDerivedCategory.{w₀, w₀}) (ad' : L' ⊣ R'.mapDerivedCategory.{w₀, w₀})
  (ε : DerivedCategory.Q.{w₀} ⋙ L ⟶ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q.{w₀})
  (ε' : DerivedCategory.Q.{w₀} ⋙ L' ⟶ E'.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q.{w₀})
  (F : A ⥤ A') (G : B ⥤ B') [F.Additive] [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  (ρ : R ⋙ F ≅ G ⋙ R') (e : E ⋙ G ≅ F ⋙ E')
  (β : F.mapDerivedCategory.{w₀, w₀} ⋙ L' ⟶ L ⋙ G.mapDerivedCategory.{w₀, w₀})
  (hβ : ∀ X, ad'.unit.app (F.mapDerivedCategory.{w₀, w₀}.obj X) ≫
    R'.mapDerivedCategory.{w₀, w₀}.map (β.app X) =
    F.mapDerivedCategory.{w₀, w₀}.map (ad.unit.app X) ≫
      (CategoryTheory.Functor.mapDerivedCategorySquareIso ρ).hom.app (L.obj X))
  (P : CochainComplex A ℤ)
  (hunit : ad.unit.app (DerivedCategory.Q.{w₀}.obj P) ≫
    R.mapDerivedCategory.{w₀, w₀}.map (ε.app P) ≫
    R.mapDerivedCategoryFactors.{w₀, w₀}.hom.app ((E.mapHomologicalComplex (.up ℤ)).obj P) =
    DerivedCategory.Q.{w₀}.map ((a.mapHomologicalComplex (.up ℤ)).unit.app P))
  (hunit' : ad'.unit.app (DerivedCategory.Q.{w₀}.obj ((F.mapHomologicalComplex (.up ℤ)).obj P)) ≫
    R'.mapDerivedCategory.{w₀, w₀}.map (ε'.app ((F.mapHomologicalComplex (.up ℤ)).obj P)) ≫
    R'.mapDerivedCategoryFactors.{w₀, w₀}.hom.app
      ((E'.mapHomologicalComplex (.up ℤ)).obj ((F.mapHomologicalComplex (.up ℤ)).obj P)) =
    DerivedCategory.Q.{w₀}.map ((a'.mapHomologicalComplex (.up ℤ)).unit.app
      ((F.mapHomologicalComplex (.up ℤ)).obj P)))
  (he : ∀ X, F.map (a.unit.app X) ≫ ρ.hom.app (E.obj X) ≫
    R'.map (e.hom.app X) = a'.unit.app (F.obj X))
include hβ hunit hunit' he in
private theorem mate_computes_resolving :
    β.app (DerivedCategory.Q.{w₀}.obj P) ≫
      G.mapDerivedCategory.{w₀, w₀}.map (ε.app P) ≫
      G.mapDerivedCategoryFactors.{w₀, w₀}.hom.app ((E.mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.{w₀}.map ((NatIso.mapHomologicalComplex e (.up ℤ)).hom.app P) =
    L'.map (F.mapDerivedCategoryFactors.{w₀, w₀}.hom.app P) ≫
      ε'.app ((F.mapHomologicalComplex (.up ℤ)).obj P) := by
  let Ec := E.mapHomologicalComplex (.up ℤ)
  let E'c := E'.mapHomologicalComplex (.up ℤ)
  let Fc := F.mapHomologicalComplex (.up ℤ)
  let Gc := G.mapHomologicalComplex (.up ℤ)
  let Rc := R.mapHomologicalComplex (.up ℤ)
  let R'c := R'.mapHomologicalComplex (.up ℤ)
  let ρd := CategoryTheory.Functor.mapDerivedCategorySquareIso ρ
  let ρc := NatIso.mapHomologicalComplex ρ (.up ℤ)
  let ec := NatIso.mapHomologicalComplex e (.up ℤ)
  have hec : Fc.map ((a.mapHomologicalComplex (.up ℤ)).unit.app P) ≫
      ρc.hom.app (Ec.obj P) ≫ R'c.map (ec.hom.app P) =
        (a'.mapHomologicalComplex (.up ℤ)).unit.app (Fc.obj P) := by
    apply HomologicalComplex.Hom.ext
    funext i
    exact he (P.X i)
  apply (ad'.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, CategoryTheory.Functor.map_comp]
  apply (cancel_mono
    (R'.mapDerivedCategoryFactors.{w₀, w₀}.hom.app (E'c.obj (Fc.obj P)))).1
  simp only [Category.assoc]
  rw [← Category.assoc, ← Category.assoc, ← Category.assoc, hβ]
  simp only [Category.assoc]
  rw [← reassoc_of% (ρd.hom.naturality (ε.app P))]
  erw [R'.mapDerivedCategoryFactors.{w₀, w₀}.hom.naturality (ec.hom.app P)]
  erw [reassoc_of% (square_factors R F G R' ρ (Ec.obj P))]
  simp only [← CategoryTheory.Functor.map_comp_assoc]
  rw [hunit]
  rw [reassoc_of% (F.mapDerivedCategoryFactors.{w₀, w₀}.hom.naturality
    ((a.mapHomologicalComplex (.up ℤ)).unit.app P))]
  simp only [← CategoryTheory.Functor.map_comp_assoc]
  change F.mapDerivedCategoryFactors.{w₀, w₀}.hom.app P ≫
    DerivedCategory.Q.{w₀}.map (Fc.map ((a.mapHomologicalComplex (.up ℤ)).unit.app P) ≫
      ρc.hom.app (Ec.obj P)) ≫ DerivedCategory.Q.{w₀}.map (R'c.map (ec.hom.app P)) = _
  rw [← CategoryTheory.Functor.map_comp]
  erw [Category.assoc, hec]
  simp only [CategoryTheory.Functor.map_comp]
  simp only [Category.assoc]
  erw [← reassoc_of% (ad'.unit.naturality (F.mapDerivedCategoryFactors.{w₀, w₀}.hom.app P))]
  erw [hunit']
end

universe u w
attribute [local irreducible] DerivedCategory.Q Functor.mapDerivedCategory
attribute [local irreducible] CategoryTheory.CochainPullback.extensionFunctor
attribute [local irreducible] CategoryTheory.CochainPullback.scalarAssociation
attribute [local irreducible] Functor.curry SheafOfModules.monoidalCategory
namespace CategoryTheory.AlgebraDiagramPullback
variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  {K : GrothendieckTopology C} {L : GrothendieckTopology D}
  {R : Sheaf K CommRingCat.{u}} {S : Sheaf L CommRingCat.{u}}
section
variable {B : Sheaf K CommRingCat.{u}} (a : R ⟶ B)
  [HasDerivedCategory.{w} (Modules.{u, u, u} R)]
  [HasDerivedCategory.{w} (Modules.{u, u, u} B)] [ExactRestriction a]
private def actualCounit (s : ScalarDerivedPresentation.{u, w} a) :
    DerivedCategory.Q.{w} ⋙ s.model.T ⟶ extend a ⋙ DerivedCategory.Q.{w} :=
  s.model.ε ≫ Functor.whiskerRight
    (NatIso.mapHomologicalComplex s.ordinary (.up ℤ)).hom DerivedCategory.Q.{w}
private theorem actualCounit_unit (s : ScalarDerivedPresentation.{u, w} a)
    (P : CategoryTheory.CochainPullback.Complex.{u, u, u} R)
    (hp : P.IsKFlatIndependentCoefficients)
    (hf : ∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := K) (R := R) (P.X n)) :
    s.adj.unit.app (DerivedCategory.Q.{w}.obj P) ≫
      (restrictionFunctor.{u, u, u, u} a).mapDerivedCategory.{w, w}.map
        ((actualCounit a s).app P) ≫
      (restrictionFunctor.{u, u, u, u} a).mapDerivedCategoryFactors.{w, w}.hom.app
        ((extend a).obj P) =
      DerivedCategory.Q.{w}.map
        (((extensionAdjunction a).mapHomologicalComplex (.up ℤ)).unit.app P) := by
  simp only [actualCounit, NatTrans.comp_app, Functor.whiskerRight_app, Functor.map_comp,
    Category.assoc]
  erw [← Category.assoc,
    (restrictionFunctor.{u, u, u, u} a).mapDerivedCategoryFactors.{w, w}.hom.naturality]
  have hu : (scalarCochainUnit a).app P =
      (((extensionAdjunction a).mapHomologicalComplex (.up ℤ)).unit.app P) := by
    ext n : 1
    simp only [Adjunction.mapHomologicalComplex, scalarCochainUnit,
      Functor.mapHomologicalComplexCompIso,
      NatTrans.comp_app, HomologicalComplex.comp_f,
      Functor.mapHomologicalComplexIdIso_inv_app_f,
      NatIso.mapHomologicalComplex_inv_app_f,
      Iso.refl_inv, NatTrans.id_app, NatTrans.mapHomologicalComplex_app_f]
    dsimp only [Functor.mapHomologicalComplex, Iso.app, Iso.symm, Iso.trans,
      NatTrans.vcomp, NatTrans.id, NatTrans.mapHomologicalComplex,
      HomologicalComplex.Hom.isoOfComponents, NatIso.ofComponents]
    simp only [Category.comp_id]
    erw [Category.id_comp]
  simpa only [Category.assoc, Functor.comp_map, hu] using s.unit_model P hp hf
end
attribute [local irreducible] Functor.mapHomologicalComplex
section
variable (f : RingedPullback.{u, u, u, u, u} R S)
  (k : Comparison.{u, u, u, u, u} f) (d : CoefficientSquare.{u, u, u, u, u} f)
  (k' : Comparison.{u, u, u, u, u} (changed f d))
  [IsIso f.coefficient]
  [HasDerivedCategory.{w} (Modules.{u, u, u} R)]
  [HasDerivedCategory.{w} (Modules.{u, u, u} S)]
  [HasDerivedCategory.{w} (Modules.{u, u, u} d.R')]
  [HasDerivedCategory.{w} (Modules.{u, u, u} d.S')]
  [ExactPullback f] [ExactPullback (changed f d)]
  [ExactRestriction d.sourceMap] [ExactRestriction d.targetMap]
  (s : ScalarDerivedPresentation.{u, w} d.sourceMap)
  (t : ScalarDerivedPresentation.{u, w} d.targetMap)
  (b : restrictionFunctor.{u, u, u, u} d.sourceMap ⋙ f.L ≅
    (changed f d).L ⋙ restrictionFunctor.{u, u, u, u} d.targetMap)
  (hb : ∀ (H : Modules.{u, u, u} d.R') (Z : Sheaf K (Type u))
    (x : Z ⟶ (underlying.{u, u, u} d.R').obj H),
    generator f k x ≫ (underlying.{u, u, u} S).map (b.hom.app H) =
      generator (changed f d) k' x)
  (e : ExtensionComparison.{u, w} f d s t)
  (he : IsNormalizedExtension.{u, w} f k d k' s t e)
  (hflat : ∀ (P : CategoryTheory.CochainPullback.Complex.{u, u, u} R),
    P.IsKFlatIndependentCoefficients →
    (∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := K) (R := R) (P.X n)) →
    CochainComplex.IsKFlatIndependentCoefficients ((pull f).obj P) ∧
      ∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := L) (R := S) (((pull f).obj P).X n))
omit [IsIso f.coefficient] in
include he in
private theorem actualCounit_extension
    (P : CategoryTheory.CochainPullback.Complex.{u, u, u} R)
    (hp : P.IsKFlatIndependentCoefficients)
    (hf : ∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := K) (R := R) (P.X n)) :
    (changed f d).L.mapDerivedCategory.{w, w}.map ((actualCounit d.sourceMap s).app P) ≫
      (changed f d).L.mapDerivedCategoryFactors.{w, w}.hom.app ((extend d.sourceMap).obj P) ≫
      DerivedCategory.Q.{w}.map ((kappa f k d k' P).hom) =
    e.hom.app (DerivedCategory.Q.{w}.obj P) ≫
      t.model.T.map (f.L.mapDerivedCategoryFactors.{w, w}.hom.app P) ≫
      (actualCounit d.targetMap t).app ((pull f).obj P) := by
  dsimp only [ExtensionComparison] at e
  apply (cancel_mono (DerivedCategory.Q.{w}.map
    ((NatIso.mapHomologicalComplex t.ordinary (.up ℤ)).inv.app ((pull f).obj P)))).mp
  simp only [actualCounit, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.map_comp, Category.assoc]
  have hn := (changed f d).L.mapDerivedCategoryFactors.{w, w}.hom.naturality
    ((NatIso.mapHomologicalComplex s.ordinary (.up ℤ)).hom.app P)
  simp only [Functor.comp_map] at hn
  erw [reassoc_of% hn]
  repeat' erw [← (DerivedCategory.Q.{w} (C := Modules.{u, u, u} d.S')).map_comp]
  simp only [Iso.hom_inv_id_app, Functor.map_id]
  erw [Category.comp_id]
  simpa only [Functor.map_comp, Category.assoc, pull] using he P hp hf

include hb he hflat in
/-- The normalized scalar-association comparison carries scalar units to scalar
units. On resolving representatives this is the ordinary generator unit square;
the adjunction mate calculation and resolving-class descent extend it to all
unbounded objects. Source: Stacks 03EL and 07A4
(blueprint: lem-pur-algebra-diagram-extension-unit). -/
theorem extension_unit (M : DerivedCategory (Modules.{u, u, u} R)) :
    f.L.mapDerivedCategory.{w, w}.map (s.adj.unit.app M) ≫
      (CategoryTheory.Functor.mapDerivedCategorySquareIso b).hom.app (s.model.T.obj M) ≫
      (restrictionFunctor.{u, u, u, u} d.targetMap).mapDerivedCategory.{w, w}.map (e.hom.app M) =
    t.adj.unit.app (f.L.mapDerivedCategory.{w, w}.obj M) := by
  dsimp only [ExtensionComparison] at e
  let β : f.L.mapDerivedCategory.{w, w} ⋙ t.model.T ⟶
      s.model.T ⋙ (changed f d).L.mapDerivedCategory.{w, w} :=
    SheafOfModules.ScalarPullback.mate s.adj t.adj
    (CategoryTheory.Functor.mapDerivedCategorySquareIso b).hom
  have hm (X : DerivedCategory (Modules.{u, u, u} R)) :
      t.adj.unit.app (f.L.mapDerivedCategory.{w, w}.obj X) ≫
        (restrictionFunctor d.targetMap).mapDerivedCategory.{w, w}.map (β.app X) =
      f.L.mapDerivedCategory.{w, w}.map (s.adj.unit.app X) ≫
        (CategoryTheory.Functor.mapDerivedCategorySquareIso b).hom.app (s.model.T.obj X) := by
    exact (unit_mateEquiv_symm s.adj t.adj
      (TwoSquare.mk _ _ _ _ (CategoryTheory.Functor.mapDerivedCategorySquareIso b).hom) X).symm
  have hβ : β ≫ e.hom = 𝟙 _ := by
    apply derivedNatTrans_ext (R := R) (S := d.S')
    intro P hp hf
    obtain ⟨hp', hf'⟩ := hflat P hp hf
    have h := mate_computes_resolving.{u + 1, u, w}
      (A := Modules.{u, u, u} R) (B := Modules.{u, u, u} d.R')
      (A' := Modules.{u, u, u} S) (B' := Modules.{u, u, u} d.S')
      (extensionFunctor.{u, u, u} d.sourceMap) (extensionFunctor.{u, u, u} d.targetMap)
      (restrictionFunctor.{u, u, u, u} d.sourceMap)
      (restrictionFunctor.{u, u, u, u} d.targetMap)
      (extensionAdjunction.{u, u, u} d.sourceMap)
      (extensionAdjunction.{u, u, u} d.targetMap)
      s.model.T t.model.T s.adj t.adj
      (actualCounit d.sourceMap s) (actualCounit d.targetMap t)
      f.L (changed f d).L b (scalarAssociation.{u, u, u, u, u} f k d k') β hm P
      (actualCounit_unit d.sourceMap s P hp hf)
      (actualCounit_unit d.targetMap t ((pull f).obj P) hp' hf')
      (ordinary_unit_square f k d k' b hb)
    have hn := actualCounit_extension f k d k' s t e he P hp hf
    have : IsIso ((actualCounit d.targetMap t).app ((pull f).obj P)) := by
      have := t.model.computes ((pull f).obj P) hp'
      dsimp only [actualCounit, NatTrans.comp_app, Functor.whiskerRight_app]
      infer_instance
    let v := t.model.T.map (f.L.mapDerivedCategoryFactors.{w, w}.hom.app P) ≫
      (actualCounit d.targetMap t).app ((pull f).obj P)
    have : IsIso v := by dsimp only [v]; infer_instance
    apply (cancel_mono v).mp
    change (β.app (DerivedCategory.Q.{w}.obj P) ≫ e.hom.app (DerivedCategory.Q.{w}.obj P)) ≫ v =
      𝟙 _ ≫ v
    rw [Category.id_comp, Category.assoc]
    rw [← hn]
    dsimp only [v, kappa, pull, extend, extensionPullback, Iso.app_hom] at h ⊢
    unfold Functor.mapHomologicalComplex at h ⊢
    exact h
  erw [← Category.assoc, ← hm, Category.assoc,
    ← (restrictionFunctor d.targetMap).mapDerivedCategory.{w, w}.map_comp]
  have hh := NatTrans.congr_app hβ M
  change β.app M ≫ e.hom.app M = 𝟙 _ at hh
  rw [hh]
  erw [Functor.map_id, Category.comp_id]
end
end CategoryTheory.AlgebraDiagramPullback
