/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F2
-/
module

public import Sheaf.AlgebraicGeometry.SchemeDerivedBaseChangeMap
public import Sheaf.AlgebraicGeometry.ModuleBaseChangeMapOpenRestriction
public import Sheaf.AlgebraicGeometry.Picard.CanonicalSingleDirectImageComparison
import Sheaf.AlgebraicGeometry.CanonicalSingleBaseChangeComparison

/-! # Tensor exchange on single complexes

Source: Stacks Project, Cohomology, Remark 08HY.
(blueprint: lem-sc-picard-tensor-single-base-change-square).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.Modules

set_option maxHeartbeats 800000 in
-- Naturality unfolds localized single complexes and the pinned derived functors.
/-- The pinned tensor comparisons commute with ordinary exchange before taking homology.
No flatness or invertibility of any comparison is assumed.
Source: Stacks Project, Cohomology, Remark 08HY; the single-complex specialization
of derivedBaseChange_unit_compatibility.
(blueprint: lem-sc-picard-tensor-single-base-change-square).

Proof: Apply canonicalSingleBaseChangeComparison to G. Write t_g and t_v for
its adjunction-preserving isomorphisms from tensor pullback to ordinary pullback.
By definition canonicalSinglePullbackMap is the pinned tensor comparison followed
by single(t.hom). Naturality of canonicalSingleDirectImageMap along t_v.hom is
proved from naturality of the right-derived unit and the inverse single-complex
comparison for pushforward. Postcompose the desired tensor square by the
invertible Rf'_*(single(t_v.hom)). This naturality identifies its left side with
the ordinary comparison's right side after cancelling single(t_g.hom) followed
by single(t_g.inv). Its right side is the ordinary comparison's left side by
functoriality and the definition of canonicalSinglePullbackMap. Cancel the
postcomposed isomorphism. No flatness or cancellation of a base-change map or
derived-to-ordinary comparison is used, so zero modules and empty schemes need
no separate case. -/
theorem tensorSingleBaseChangeSquare
    [∀ Y : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X S X' T : Scheme.{u}} (f : X ⟶ S) (f' : X' ⟶ T)
    (g : T ⟶ S) (v : X' ⟶ X) (h : v ≫ f = f' ≫ g)
    [(tensorPullback g).Additive] [(tensorPullback v).Additive] (G : X.Modules) :
    let εg := (Classical.choose (Classical.choose_spec
      exists_derivedPullbackComposition.{u, w})) g
    let εv := (Classical.choose (Classical.choose_spec
      exists_derivedPullbackComposition.{u, w})) v
    let cg := εg.app ((HomotopyCategory.singleFunctor _ 0).obj ((pushforward f).obj G)) ≫
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex
          (tensorPullback g) (ComplexShape.up ℤ) 0).hom.app ((pushforward f).obj G)))
    let cv := εv.app ((HomotopyCategory.singleFunctor _ 0).obj G) ≫
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex
          (tensorPullback v) (ComplexShape.up ℤ) 0).hom.app G))
    cg ≫ (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings T.toRingedSpace)) 0).map
          (moduleBaseChangeMap f f' g v h G) ≫
        canonicalSingleDirectImageMap f' ((tensorPullback v).obj G) =
      (derivedPullback g).map (canonicalSingleDirectImageMap f G) ≫
        schemeDerivedBaseChangeMap f f' g v h ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj G) ≫
        (schemeDerivedDirectImage f').map cv := by
  dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at *
  classical
  let tv := (Classical.choose (exists_tensorPullbackAdjunction v)).leftAdjointUniq
    (pullbackPushforwardAdjunction v)
  have hn : canonicalSingleDirectImageMap f' ((tensorPullback v).obj G) ≫
      (schemeDerivedDirectImage f').map ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings X'.toRingedSpace)) 0).map (tv.hom.app G)) =
    (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings T.toRingedSpace)) 0).map
        ((pushforward f').map (tv.hom.app G)) ≫
      canonicalSingleDirectImageMap f' ((pullback v).obj G) := by
    let β := (RingedSpace.moduleDirectImage f'.toLRSHom.toShHom).rightDerivedFunctorUnit
    have hβ := β.naturality ((HomotopyCategory.singleFunctor _ 0).map (tv.hom.app G))
    have hc := (HomologicalComplex.singleMapHomologicalComplex
      (pushforward f') (ComplexShape.up ℤ) 0).inv.naturality (tv.hom.app G)
    simp only [canonicalSingleDirectImageMap,
      DerivedCategory.singleFunctor, DerivedCategory.singleFunctors,
      HomotopyCategory.singleFunctor, HomotopyCategory.singleFunctors,
      SingleFunctors.postcomp, Functor.comp_map, Functor.comp_obj,
      Category.assoc] at hβ ⊢
    erw [← hβ]
    erw [Functor.mapHomotopyCategory_map]
    erw [← Functor.map_comp_assoc, ← Functor.map_comp]
    erw [← Functor.map_comp_assoc, ← Functor.map_comp]
    congr 1
    congr 2
    simp only [Functor.comp_map] at hc
    exact hc.symm
  have hs := canonicalSingleBaseChangeComparison.{u, w} f f' g v h G
  apply (cancel_mono ((schemeDerivedDirectImage f').map
    ((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings X'.toRingedSpace)) 0).map (tv.hom.app G)))).mp
  simp only [Category.assoc, hn]
  dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at hs
  simp only [canonicalSinglePullbackMap, Functor.map_comp, Category.assoc] at hs
  simp only [← Functor.map_comp_assoc] at hs
  simpa only [Scheme.Modules, Scheme.ringCatSheaf, ← Functor.map_comp_assoc,
    Category.assoc, Iso.hom_inv_id_app_assoc, tv]
    using hs.symm

end AlgebraicGeometry.Scheme.Modules
