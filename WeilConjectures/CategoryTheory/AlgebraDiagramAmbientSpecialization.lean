/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.AlgebraDiagramPullbackData
/-! # Specializing the ambient tensor comparison to coefficients

Source: Stacks 07A4 (blueprint: lem-pur-algebra-diagram-ambient-specialization).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance 100000] CategoryTheory.hasSheafCompose_of_preservesLimitsOfSize
universe u v u' v' w
open CategoryTheory CategoryTheory.Limits CategoryTheory.CochainPullback
open SheafOfModules.PullbackTensorCanonical
namespace CategoryTheory.AlgebraDiagramPullback
/-- Fixing the second tensor argument preserves a tensor pullback isomorphism.
Naturality is the original square applied to a morphism and an identity.
Source: Stacks 07A4
(blueprint: lem-pur-algebra-diagram-ambient-specialization). -/
def fixedTensorIso
    {A : Type u} [Category.{v} A] {B : Type u'} [Category.{v'} B]
    (T : A ⥤ A ⥤ A) (U : B ⥤ B ⥤ B) (F : A ⥤ B)
    (a : Functor.uncurry.obj T ⋙ F ≅ F.prod F ⋙ Functor.uncurry.obj U) (N : A) :
    T.flip.obj N ⋙ F ≅ F ⋙ U.flip.obj (F.obj N) :=
  NatIso.ofComponents (fun M ↦ a.app (M, N)) (by
    intro M M' h
    have hn := a.hom.naturality (Prod.mkHom h (𝟙 N))
    change F.map ((T.map h).app N ≫ (T.obj M').map (𝟙 N)) ≫ a.hom.app (M', N) =
      a.hom.app (M, N) ≫ ((U.map (F.map h)).app (F.obj N) ≫
        (U.obj (F.obj M')).map (F.map (𝟙 N))) at hn
    simpa only [Iso.app_hom, Functor.comp_map, Functor.uncurry_obj_map, Functor.prod_map,
      Functor.map_id, NatTrans.id_app, Category.comp_id, Category.id_comp,
      Functor.flip_obj_map, Functor.flip_obj_obj] using hn)
variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  {K : GrothendieckTopology C} {L : GrothendieckTopology D}
  {R : Sheaf K CommRingCat.{u}} {S : Sheaf L CommRingCat.{u}}
  (f : RingedPullback.{u, u, u, u, u} R S)
  (d : CoefficientSquare.{u, u, u, u, u} f)
  [HasDerivedCategory.{w} (Modules.{u, u, u} R)]
  [HasDerivedCategory.{w} (Modules.{u, u, u} S)]
  [HasDerivedCategory.{w} (Modules.{u, u, u} d.R')]
  [HasDerivedCategory.{w} (Modules.{u, u, u} d.S')]
  [ExactPullback f] [ExactPullback (changed f d)]
  [ExactRestriction d.sourceMap] [ExactRestriction d.targetMap]
  (source : ScalarDerivedPresentation.{u, w} d.sourceMap)
  (target : ScalarDerivedPresentation.{u, w} d.targetMap)
  (ambient : Phi f.L.mapDerivedCategory.{w, w} ≅ Psi f.L.mapDerivedCategory.{w, w})
  (beta : f.L.obj (coefficient d.sourceMap) ≅ coefficient d.targetMap)
/-- Specialize the independently constructed ambient comparison to the coefficient
module and transport through the normalized scalar presentations. All its data are
explicit composites of the given isomorphisms. Source: Stacks 07A4
(blueprint: lem-pur-algebra-diagram-ambient-specialization). -/
def ambientSpecialization :
    (source.model.T ⋙ (restrictionFunctor.{u, u, u, u} d.sourceMap).mapDerivedCategory) ⋙
      f.L.mapDerivedCategory.{w, w} ≅
    f.L.mapDerivedCategory.{w, w} ⋙ target.model.T ⋙
      (restrictionFunctor.{u, u, u, u} d.targetMap).mapDerivedCategory :=
  Functor.isoWhiskerRight (source.underlyingIso ≪≫ scalarTensorComparison d.sourceMap)
      f.L.mapDerivedCategory ≪≫
    fixedTensorIso (canonicalDerivedTensor R) (canonicalDerivedTensor S)
      f.L.mapDerivedCategory ambient (DerivedCategory.Q.obj (coefficientComplex d.sourceMap)) ≪≫
    Functor.isoWhiskerLeft f.L.mapDerivedCategory
      ((canonicalDerivedTensor S).flip.mapIso (derivedCoefficientIso f d beta)) ≪≫
    Functor.isoWhiskerLeft f.L.mapDerivedCategory
      ((scalarTensorComparison d.targetMap).symm ≪≫ target.underlyingIso.symm)
omit [ExactPullback (changed f d)] in
/-- Component formula for specialization. Source: Stacks 07A4
(blueprint: lem-pur-algebra-diagram-ambient-specialization). -/
theorem ambientSpecialization_hom (M : DerivedCategory (Modules.{u, u, u} R)) :
    (ambientSpecialization f d source target ambient beta).hom.app M =
      f.L.mapDerivedCategory.map (source.underlyingIso.hom.app M) ≫
        f.L.mapDerivedCategory.map ((scalarTensorComparison d.sourceMap).hom.app M) ≫
        ambient.hom.app (M, DerivedCategory.Q.obj (coefficientComplex d.sourceMap)) ≫
        (Functor.uncurry.obj (canonicalDerivedTensor S)).map
          (Prod.mkHom (𝟙 (f.L.mapDerivedCategory.obj M)) (derivedCoefficientIso f d beta).hom) ≫
        (scalarTensorComparison d.targetMap).inv.app (f.L.mapDerivedCategory.obj M) ≫
        target.underlyingIso.inv.app (f.L.mapDerivedCategory.obj M) := by
  dsimp only [ambientSpecialization, fixedTensorIso]
  simp only [ NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Iso.trans_hom, Functor.map_comp, Functor.mapIso_hom, Iso.symm_hom,
    fixedTensorIso, NatIso.ofComponents_hom_app, Iso.app_hom,
    Functor.uncurry_obj_map, Functor.map_id, NatTrans.id_app, Category.id_comp,
    Functor.flip_map_app, Category.assoc]
  dsimp only [Functor.prod_obj]
  simp only [Functor.map_id, NatTrans.id_app, Category.id_comp]
  repeat' erw [Category.id_comp]
end CategoryTheory.AlgebraDiagramPullback
