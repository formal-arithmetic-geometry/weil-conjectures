/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y3
-/
module

public import Sheaf.AlgebraicGeometry.FlatBaseChangeOpenChoices

/-! # Naturality of the concrete higher-direct-image resolution section map

Source: Stacks Project, Cohomology, Tags 01E1 and 01E4.
(blueprint: lem-pc-higher-direct-image-resolution-naturality).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
attribute [local instance] Scheme.Modules.enoughInjectives
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The canonical section-class map computed from a specified resolution.
Source: Stacks Project, Cohomology, Lemma 20.7.3, Tag 01E4.
(blueprint: lem-pc-higher-direct-image-resolution-naturality). -/
noncomputable def higherDirectImageResolutionSectionMap
    {X Y : Scheme.{u}} (f : X ⟶ Y) (p : ℕ) (V : Y.Opens)
    {N : SheafOfModules.{u} (moduleRings X.toRingedSpace)} (I : InjectiveResolution N) :
    ((RingedSpace.openModuleSections X.toRingedSpace (f ⁻¹ᵁ V)).rightDerived p).obj N ⟶
      ((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerived p ⋙
        RingedSpace.openModuleSections Y.toRingedSpace V).obj N :=
    let K : CochainComplex Y.Modules ℕ :=
      ((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).mapHomologicalComplex
        (.up ℕ)).obj I.cocomplex
    let L := ((SheafOfModules.forget Y.ringCatSheaf).mapHomologicalComplex (.up ℕ)).obj K
    let E := PresheafOfModules.toPresheaf Y.ringCatSheaf.obj ⋙
      (evaluation Y.Opensᵒᵖ AddCommGrpCat.{u}).obj (Opposite.op V)
    (I.isoRightDerivedObj
      (RingedSpace.openModuleSections X.toRingedSpace (f ⁻¹ᵁ V)) p).hom ≫
      ((L.sc p).mapHomologyIso E).hom ≫
      ((PresheafOfModules.toPresheaf Y.ringCatSheaf.obj).map
        (Scheme.Modules.sectionCohomologyTheta K p ≫
          (SheafOfModules.forget Y.ringCatSheaf).map
            (I.isoRightDerivedObj
              (RingedSpace.moduleDirectImage f.toLRSHom.toShHom) p).inv)).app
                (Opposite.op V)

/-- Exact left adjoints give a natural comparison from presheaf homology. -/
private theorem adjoint_homology_naturality
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    (S : D ⥤ C) (U : C ⥤ D) [S.PreservesZeroMorphisms] [U.PreservesZeroMorphisms]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S] (adj : S ⊣ U)
    {K K' : CochainComplex C ℕ} (g : K ⟶ K') (p : ℕ) :
    let L := (U.mapHomologicalComplex (.up ℕ)).obj K
    let L' := (U.mapHomologicalComplex (.up ℕ)).obj K'
    let ε := adj.counit.mapHomologicalComplex (.up ℕ)
    HomologicalComplex.homologyMap ((U.mapHomologicalComplex (.up ℕ)).map g) p ≫
        adj.homEquiv _ _ (((L'.sc p).mapHomologyIso S).inv ≫
          HomologicalComplex.homologyMap (ε.app K') p) =
      adj.homEquiv _ _ (((L.sc p).mapHomologyIso S).inv ≫
          HomologicalComplex.homologyMap (ε.app K) p) ≫
        U.map (HomologicalComplex.homologyMap g p) := by
  dsimp only
  apply adj.homEquiv_naturality_left_square
  have hm := ShortComplex.mapHomologyIso_inv_naturality
    ((HomologicalComplex.shortComplexFunctor _ (.up ℕ) p).map
      ((U.mapHomologicalComplex (.up ℕ)).map g)) S
  have hc := congrArg (HomologicalComplex.homologyFunctor C (.up ℕ) p).map
    ((adj.counit.mapHomologicalComplex (.up ℕ)).naturality g)
  simp only [Functor.map_comp] at hc
  rw [← Category.assoc]
  erw [hm]
  simp only [Category.assoc]
  exact congrArg (((((U.mapHomologicalComplex (.up ℕ)).obj K).sc p).mapHomologyIso S).inv ≫ ·)
    hc

set_option maxHeartbeats 800000 in
-- Specializing the adjunction requires comparing the identity restriction of scalars.
/-- The sheafification comparison is natural before choosing a resolution. -/
private theorem sectionCohomologyTheta_naturality
    {Y : Scheme.{u}} {K K' : CochainComplex Y.Modules ℕ} (g : K ⟶ K') (p : ℕ) :
    HomologicalComplex.homologyMap
        ((SheafOfModules.forget Y.ringCatSheaf).mapHomologicalComplex (.up ℕ) |>.map g) p ≫
      Scheme.Modules.sectionCohomologyTheta K' p =
    Scheme.Modules.sectionCohomologyTheta K p ≫
      (SheafOfModules.forget Y.ringCatSheaf).map
        (HomologicalComplex.homologyMap g p) := by
  exact adjoint_homology_naturality
    (PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj))
    (SheafOfModules.forget Y.ringCatSheaf)
    (PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)) g p

set_option maxHeartbeats 800000 in
-- The naturality squares compare several termwise composite functors.
/-- The canonical resolution-section map commutes with coefficient maps.

Source: Stacks Project, Cohomology, Lemma 20.7.3, Tag 01E4.
(blueprint: lem-pc-higher-direct-image-resolution-naturality).

Proof: Lift a to a cochain map g from I to J preserving the augmentations.
The isoRightDerivedObj_hom_naturality formula moves the derived sections map past
the source resolution isomorphism. Exact evaluation preserves homology, and its
mapHomologyIso is natural for g. Theta is adjoint to the homology comparison for
exact sheafification followed by the counit on the complex; naturality of both
mapHomologyIso and the counit, and naturality of the adjunction homEquiv, show that
theta commutes with f_*g. Finally isoRightDerivedObj_inv_naturality moves f_*g past
the inverse target comparison. Compose these three equalities and reassociate to
obtain the displayed square. Different lifts are homotopic and additive functors
preserve homotopies, so all such lifts give the same homology maps. This does not
use the comparison between restriction cohomology and derived open sections, and
requires neither properness nor an affine basis. It applies also for p = 0 and for
an empty inverse-image open. -/
theorem higherDirectImage_resolution_naturality
    {X Y : Scheme.{u}} (f : X ⟶ Y) (p : ℕ) (V : Y.Opens)
    {M N : SheafOfModules.{u} (moduleRings X.toRingedSpace)} (a : M ⟶ N)
    (I : InjectiveResolution M) (J : InjectiveResolution N) :
  ((RingedSpace.openModuleSections X.toRingedSpace (f ⁻¹ᵁ V)).rightDerived p).map a ≫
      higherDirectImageResolutionSectionMap f p V J =
        higherDirectImageResolutionSectionMap f p V I ≫
        ((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerived p ⋙
          RingedSpace.openModuleSections Y.toRingedSpace V).map a := by
  let A := RingedSpace.openModuleSections X.toRingedSpace (f ⁻¹ᵁ V)
  let D := RingedSpace.moduleDirectImage f.toLRSHom.toShHom
  let U := SheafOfModules.forget Y.ringCatSheaf
  let E := PresheafOfModules.toPresheaf Y.ringCatSheaf.obj ⋙
    (evaluation Y.Opensᵒᵖ AddCommGrpCat.{u}).obj (Opposite.op V)
  let g := InjectiveResolution.desc a J I
  have hg := InjectiveResolution.desc_commutes_zero a J I
  have hA := InjectiveResolution.isoRightDerivedObj_hom_naturality a I J g hg A p
  have hD := InjectiveResolution.isoRightDerivedObj_inv_naturality a I J g hg D p
  have hE := ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor _ (.up ℕ) p).map
      ((U.mapHomologicalComplex (.up ℕ)).map
        ((D.mapHomologicalComplex (.up ℕ)).map g))) E
  let LI := (U.mapHomologicalComplex (.up ℕ)).obj
    ((D.mapHomologicalComplex (.up ℕ)).obj I.cocomplex)
  let LJ := (U.mapHomologicalComplex (.up ℕ)).obj
    ((D.mapHomologicalComplex (.up ℕ)).obj J.cocomplex)
  change HomologicalComplex.homologyMap
      ((A.mapHomologicalComplex (.up ℕ)).map g) p ≫
        ((LJ.sc p).mapHomologyIso E).hom =
      ((LI.sc p).mapHomologyIso E).hom ≫
        E.map (HomologicalComplex.homologyMap
          ((U.mapHomologicalComplex (.up ℕ)).map
            ((D.mapHomologicalComplex (.up ℕ)).map g)) p) at hE
  have hθ := sectionCohomologyTheta_naturality
    ((D.mapHomologicalComplex (.up ℕ)).map g) p
  have hθE := congrArg E.map hθ
  have hDE := congrArg (U ⋙ E).map hD
  simp only [Functor.map_comp, E, Functor.comp_map] at hθE hDE
  dsimp only [higherDirectImageResolutionSectionMap]
  change (A.rightDerived p).map a ≫ _ = _
  simp only [Functor.map_comp, NatTrans.comp_app, Category.assoc]
  rw [reassoc_of% hA]
  erw [reassoc_of% hE]
  erw [reassoc_of% hθE]
  erw [← hDE]
  rfl

end AlgebraicGeometry
