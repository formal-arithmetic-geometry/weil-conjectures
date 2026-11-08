/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Submission.WeilConjectures.AlgebraicGeometry.FlatBaseChangeOpenChoices
public import Submission.WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

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

end AlgebraicGeometry
