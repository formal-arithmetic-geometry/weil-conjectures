/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Sheaf.CategoryTheory.AlgebraDiagramPullbackData
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import all Sheaf.Paper.PullbackTensorCanonicalShiftUnit
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all Sheaf.CategoryTheory.DerivedExactSquareComposition
import Sheaf.Algebra.Homology.ExactPullbackSignedComparison
/-! # Derived normalized comparison maps

Source: Stacks 03EL and 07A4.
(blueprint: lem-pur-algebra-diagram-derived-comparisons).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance 100000] CategoryTheory.hasSheafCompose_of_preservesLimitsOfSize
attribute [local irreducible] DerivedCategory.Q CategoryTheory.Functor.mapDerivedCategory
universe u w v v' v'' u' u''
open CategoryTheory CategoryTheory.Limits CategoryTheory.CochainPullback
open scoped ZeroObject
namespace CategoryTheory.AlgebraDiagramPullback
variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  {K : GrothendieckTopology C} {L : GrothendieckTopology D}
  {R : Sheaf K CommRingCat.{u}} {S : Sheaf L CommRingCat.{u}}
section
variable (f : RingedPullback.{u, u, u, u, u} R S)
  (k : Comparison.{u, u, u, u, u} f) (d : CoefficientSquare.{u, u, u, u, u} f)
  [HasDerivedCategory.{w} (Modules.{u, u, u} R)]
  [HasDerivedCategory.{w} (Modules.{u, u, u} S)]
  [HasDerivedCategory.{w} (Modules.{u, u, u} d.R')]
  [HasDerivedCategory.{w} (Modules.{u, u, u} d.S')]
  [ExactPullback f] [ExactPullback (changed f d)]
  [ExactRestriction d.sourceMap] [ExactRestriction d.targetMap]
/-- Localizing the ordinary restriction square gives its representative formula.
Source: exact localization (Stacks 06YU)
(blueprint: lem-pur-algebra-diagram-derived-comparisons). -/
theorem restriction_descent
    (b : restrictionFunctor.{u, u, u, u} d.sourceMap ⋙ f.L ≅
      (changed f d).L ⋙ restrictionFunctor.{u, u, u, u} d.targetMap) :
    ∀ H : CategoryTheory.CochainPullback.Complex.{u, u, u} d.R',
        f.L.mapDerivedCategory.{w, w}.map
          ((restrictionFunctor.{u, u, u, u} d.sourceMap).mapDerivedCategoryFactors.{w, w}.hom.app
            H) ≫
          f.L.mapDerivedCategoryFactors.{w, w}.hom.app
            ((restrictComplex.{u, u, u, u} d.sourceMap).obj H) ≫
          DerivedCategory.Q.{w}.map
            ((Functor.mapHomologicalComplexCompIso b (.up ℤ)).hom.app H ≫
              (Functor.mapHomologicalComplexCompIso
                (Iso.refl ((changed f d).L ⋙ restrictionFunctor.{u, u, u, u} d.targetMap))
                (.up ℤ)).inv.app H) =
        (CategoryTheory.Functor.mapDerivedCategorySquareIso b).hom.app
          (DerivedCategory.Q.{w}.obj H) ≫
          (restrictionFunctor.{u, u, u, u} d.targetMap).mapDerivedCategory.{w, w}.map
            ((changed f d).L.mapDerivedCategoryFactors.{w, w}.hom.app H) ≫
          (restrictionFunctor.{u, u, u, u} d.targetMap).mapDerivedCategoryFactors.{w, w}.hom.app
            ((pull.{u, u, u, u, u} (changed f d)).obj H) := by
  intro H
  have h := (Functor.exactSquare_fac b H).symm
  simpa only [Functor.mapHomologicalComplexCompIso, NatIso.mapHomologicalComplex,
    Iso.app_hom, Iso.app_inv, Iso.refl_hom, Iso.refl_inv,
    NatTrans.mapHomologicalComplex_id, NatTrans.id_app, Category.comp_id] using h
include k in
/-- The normalized ambient comparison supplied by canonical tensor pullback.
Source: Stacks 07A4 (blueprint: lem-pur-algebra-diagram-derived-comparisons). -/
theorem ambient_exists :
    ∃ e : SheafOfModules.PullbackTensorCanonical.Phi f.L.mapDerivedCategory.{w, w} ≅
      SheafOfModules.PullbackTensorCanonical.Psi f.L.mapDerivedCategory.{w, w},
      SheafOfModules.PullbackTensorCanonical.IsNormalized f k f.L.mapDerivedCategory
        f.L.mapDerivedCategoryFactors.hom e.hom := by
  have hL : f.L.mapDerivedCategory.{w, w}.IsLeftDerivedFunctor
      f.L.mapDerivedCategoryFactors.hom
      (HomologicalComplex.quasiIso (Modules.{u, u, u} R) (.up ℤ)) := by
    exact Functor.isLeftDerivedFunctor_of_inverts _ _ f.L.mapDerivedCategoryFactors
  obtain ⟨_, _, _, _, _, _, _, e, he, _⟩ :=
    SheafOfModules.PullbackTensorCanonical.pullback_tensor_canonical_shift_unit
      f k f.L.mapDerivedCategory f.L.mapDerivedCategoryFactors.hom hL
  exact ⟨e, he⟩
include k in
/-- Exact geometric pullback preserves flat-term K-flat resolving representatives.
Source: Stacks 0G7E (blueprint: lem-pur-algebra-diagram-derived-comparisons). -/
theorem pullback_resolving
    (P : CategoryTheory.CochainPullback.Complex.{u, u, u} R)
    (hp : P.IsKFlatIndependentCoefficients)
    (hf : ∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := K) (R := R) (P.X n)) :
    CochainComplex.IsKFlatIndependentCoefficients ((pull f).obj P) ∧
      ∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := L) (R := S) (((pull f).obj P).X n) := by
  have hL : f.L.mapDerivedCategory.{w, w}.IsLeftDerivedFunctor
      f.L.mapDerivedCategoryFactors.hom
      (HomologicalComplex.quasiIso (Modules.{u, u, u} R) (.up ℤ)) :=
    Functor.isLeftDerivedFunctor_of_inverts _ _ f.L.mapDerivedCategoryFactors
  obtain ⟨_, _, _, _, _, _, _, _, _, hres, _⟩ :=
    SheafOfModules.ExactPullbackSigned.exact_pullback_signed_comparison
      f k f.L.mapDerivedCategory f.L.mapDerivedCategoryFactors.hom hL
  exact hres P hp hf
end

private def fixedSecond {A : Type u} [Category.{v} A] (Y : A) : A ⥤ A × A where
  obj X := (X, Y)
  map f := (f, 𝟙 Y)

private theorem unary_descent
    {A : Type u} [Category.{v} A] {B : Type u'} [Category.{v'} B]
    {E : Type u''} [Category.{v''} E] (q : A ⥤ B) (X₀ : A)
    (ff : ((Functor.whiskeringLeft (A × A) (B × B) E).obj (q.prod q)).FullyFaithful)
    {F G : B ⥤ E} (e : q ⋙ F ≅ q ⋙ G) :
    ∃ t : F ≅ G, ∀ X, t.app (q.obj X) = e.app X := by
  let fstA : A × A ⥤ A := Prod.fst _ _
  let fstB : B × B ⥤ B := Prod.fst _ _
  let ee : (q.prod q) ⋙ (fstB ⋙ F) ≅ (q.prod q) ⋙ (fstB ⋙ G) :=
    Functor.isoWhiskerLeft fstA e
  let tt : fstB ⋙ F ≅ fstB ⋙ G := ff.preimageIso ee
  let t : F ≅ G := Functor.isoWhiskerLeft (fixedSecond (q.obj X₀)) tt
  refine ⟨t, ?_⟩
  intro X
  apply Iso.ext
  exact NatTrans.congr_app (ff.map_preimage ee.hom) (X, X₀)


/-- Descend balanced scalar association from the resolving class. The source and
inverse target counits give the comparison on representatives; full faithfulness
of the resolving localization gives the derived isomorphism and its formula.
Source: Stacks 03EL, 06YU and 07A4
(blueprint: lem-pur-algebra-diagram-derived-comparisons). -/
theorem extension_descent
    (f : RingedPullback.{u, u, u, u, u} R S)
    (k : Comparison.{u, u, u, u, u} f) (d : CoefficientSquare.{u, u, u, u, u} f)
    (k' : Comparison.{u, u, u, u, u} (changed f d))
    [HasDerivedCategory.{w} (Modules.{u, u, u} R)]
    [HasDerivedCategory.{w} (Modules.{u, u, u} S)]
    [HasDerivedCategory.{w} (Modules.{u, u, u} d.R')]
    [HasDerivedCategory.{w} (Modules.{u, u, u} d.S')]
    [ExactPullback f] [ExactPullback (changed f d)]
    [ExactRestriction d.sourceMap] [ExactRestriction d.targetMap]
    (source : ScalarDerivedPresentation.{u, w} d.sourceMap)
    (target : ScalarDerivedPresentation.{u, w} d.targetMap)
    (hflat : ∀ P : CategoryTheory.CochainPullback.Complex.{u, u, u} R,
      P.IsKFlatIndependentCoefficients →
      (∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := K) (R := R) (P.X n)) →
      CochainComplex.IsKFlatIndependentCoefficients ((pull f).obj P)) :
    ∃ e : ExtensionComparison f d source target,
      IsNormalizedExtension f k d k' source target e := by
  let PR := SheafOfModules.PullbackTensorCanonical.resolvingProperty (R := R)
  let EY := source.model.E.mapHomologicalComplex (.up ℤ)
  let EX := target.model.E.mapHomologicalComplex (.up ℤ)
  let DY := (changed f d).L.mapDerivedCategory.{w, w}
  let DX := f.L.mapDerivedCategory.{w, w}
  let a : PR.ι ⋙ DerivedCategory.Q ⋙ source.model.T ⋙ DY ≅
      PR.ι ⋙ EY ⋙ DerivedCategory.Q ⋙ DY :=
    NatIso.ofComponents (fun P ↦ by
      have := source.model.computes P.obj P.property.1
      exact DY.mapIso (asIso (source.model.ε.app P.obj))) (by
        intro P Q g
        simpa only [Functor.map_comp, Functor.comp_map, Functor.mapIso_hom,
          asIso_hom, ObjectProperty.ι_map] using
            congrArg DY.map (source.model.ε.naturality g.hom))
  let b : PR.ι ⋙ DerivedCategory.Q ⋙ DX ⋙ target.model.T ≅
      PR.ι ⋙ pull f ⋙ EX ⋙ DerivedCategory.Q :=
    NatIso.ofComponents (fun P ↦ by
      have := target.model.computes ((pull f).obj P.obj)
        (hflat P.obj P.property.1 P.property.2)
      exact target.model.T.mapIso (f.L.mapDerivedCategoryFactors.app P.obj) ≪≫
        asIso (target.model.ε.app ((pull f).obj P.obj))) (by
      intro P Q g
      simp only [Iso.trans_hom, Functor.mapIso_hom, asIso_hom, Functor.comp_map,
        ObjectProperty.ι_map, Category.assoc]
      dsimp only [DX, EX]
      have hn := target.model.ε.naturality ((pull f).map g.hom)
      dsimp only [Functor.comp_map] at hn
      rw [← hn]
      rw [← target.model.T.map_comp_assoc]
      erw [f.L.mapDerivedCategoryFactors.hom.naturality]
      rw [target.model.T.map_comp, Category.assoc]
      rfl)
  let c : EY ⋙ pull (changed f d) ≅ pull f ⋙ EX :=
    Functor.mapHomologicalComplexCompIso
      (Functor.isoWhiskerRight source.ordinary (changed f d).L ≪≫
        scalarAssociation f k d k' ≪≫
        Functor.isoWhiskerLeft f.L target.ordinary.symm) (.up ℤ)
  let e : PR.ι ⋙ DerivedCategory.Q ⋙ (source.model.T ⋙ DY) ≅
      PR.ι ⋙ DerivedCategory.Q ⋙ (DX ⋙ target.model.T) :=
    a ≪≫ Functor.isoWhiskerLeft (PR.ι ⋙ EY) (changed f d).L.mapDerivedCategoryFactors ≪≫
      Functor.isoWhiskerLeft PR.ι (Functor.isoWhiskerRight c DerivedCategory.Q) ≪≫ b.symm
  obtain ⟨ff⟩ := SheafOfModules.PullbackTensorCanonical.resolving_fullyFaithful
    (R := R) (S := d.S')
  obtain ⟨P₀, p₀, hp₀, hq₀⟩ :=
    SheafOfModules.PullbackTensorCanonical.exists_resolving (R := R)
      (0 : CochainComplex (Modules.{u, u, u} R) ℤ)
  obtain ⟨z, hz⟩ := unary_descent (PR.ι ⋙ DerivedCategory.Q) ⟨P₀, hp₀⟩ ff
    (Functor.associator PR.ι DerivedCategory.Q (source.model.T ⋙ DY) ≪≫ e ≪≫
      (Functor.associator PR.ι DerivedCategory.Q (DX ⋙ target.model.T)).symm)
  refine ⟨z, ?_⟩
  intro P hp hf
  have h := congrArg Iso.hom (hz ⟨P, hp, hf⟩)
  simp only [NatIso.trans_app, Iso.trans_hom, Iso.app_hom, Iso.symm_hom,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.comp_id, Category.id_comp] at h
  dsimp only [Functor.comp_obj, ObjectProperty.ι_obj] at h
  erw [Category.id_comp] at h
  change z.hom.app (DerivedCategory.Q.obj P) = e.hom.app ⟨P, hp, hf⟩ at h
  erw [h]
  simp only [e, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    a, b, NatIso.ofComponents_hom_app, NatIso.ofComponents_inv_app, Iso.trans_inv,
    Iso.symm_hom, Functor.mapIso_inv, asIso_inv, asIso_hom, Functor.mapIso_hom,
    Category.assoc]
  simp only [Functor.associator_inv_app, Category.id_comp, Category.comp_id,
    ObjectProperty.ι_obj, Functor.comp_obj, IsIso.inv_hom_id_assoc,
    ← target.model.T.map_comp_assoc, Iso.inv_hom_id_app,
    target.model.T.map_id, Category.comp_id]
  have := target.model.computes ((pull f).obj P) (hflat P hp hf)
  dsimp only [DY, EY]
  simp only [Iso.app_inv, ← target.model.T.map_comp_assoc,
    Iso.inv_hom_id_app, target.model.T.map_id, Category.id_comp,
    IsIso.inv_hom_id, Category.comp_id, Category.assoc]
  congr 2
  erw [target.model.T.map_id]
  simp only [Category.id_comp, IsIso.inv_hom_id, Category.comp_id]
  apply DerivedCategory.Q.congr_map
  ext n : 1
  simp only [c, Functor.mapHomologicalComplexCompIso, Iso.trans_hom,
    NatTrans.mapHomologicalComplex_comp, NatTrans.comp_app,
    HomologicalComplex.comp_f, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    NatTrans.mapHomologicalComplex_app_f, kappa]
  dsimp only [NatIso.mapHomologicalComplex, Iso.app, Iso.trans, Iso.symm,
    NatTrans.mapHomologicalComplex, NatTrans.vcomp, Functor.isoWhiskerRight,
    Functor.isoWhiskerLeft, Functor.whiskerRight, Functor.whiskerLeft,
    pull, extend, Functor.mapHomologicalComplex]
  rfl

end CategoryTheory.AlgebraDiagramPullback
