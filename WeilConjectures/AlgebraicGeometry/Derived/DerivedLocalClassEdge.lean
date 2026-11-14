/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Derived.DerivedSingleAdjunctionTranspose
import WeilConjectures.AlgebraicGeometry.Derived.DerivedResolutionEdgeLocal
import WeilConjectures.AlgebraicGeometry.Derived.DerivedResolutionEdgeSingle
import WeilConjectures.AlgebraicGeometry.Derived.DerivedSingleDirectImageUnitIso

/-! # The natural local-class edge and its single-complex normalization
Source: Stacks Project, cohomology.tex, Tags 0BKJ, 0D5X and 079W.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory
noncomputable section
namespace AlgebraicGeometry

variable [∀ X : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]

/-- Sheafifying the local Leray/class maps gives a natural module edge, normalized on
single complexes by the right-derived unit.
Source: Stacks Project, cohomology.tex, Tags 0BKJ and 0D5X (local classes and Leray),
and Tag 079W (the right-derived unit on the same resolution). -/
theorem exists_topEdgeLocalClassEdge {T S : Scheme.{u}} (g : T ⟶ S) (q : ℤ) :
    let HS := DerivedCategory.homologyFunctor.{w, u, u + 1}
      (SheafOfModules.{u} (moduleRings S.toRingedSpace)) q
    let HT := DerivedCategory.homologyFunctor.{w, u, u + 1}
      (SheafOfModules.{u} (moduleRings T.toRingedSpace)) q
    ∃ e : ∀ K : schemeDerivedCategory T,
        HS.obj ((schemeDerivedDirectImage g).obj K) ⟶
          (Scheme.Modules.pushforward g).obj (HT.obj K),
      (∀ (K : schemeDerivedCategory T) (V : (TopologicalSpace.Opens S)ᵒᵖ),
        (RingedSpace.topEdgeLocalClass S.toRingedSpace q
          ((schemeDerivedDirectImage g).obj K)).app V ≫
            ((SheafOfModules.toSheaf (moduleRings S.toRingedSpace)).map (e K)).hom.app V =
          (RingedSpace.topEdgeLocalLeray g.toLRSHom.toShHom q K).hom.app V ≫
            (RingedSpace.topEdgeInverseLocalClass g.toLRSHom.toShHom q K).app V) ∧
      (∀ {K K' : schemeDerivedCategory T} (k : K ⟶ K'),
        HS.map ((schemeDerivedDirectImage g).map k) ≫ e K' =
          e K ≫ (Scheme.Modules.pushforward g).map (HT.map k)) ∧
      (∀ M : T.Modules,
        IsIso (HS.map (topEdgeSingleDirectImageMap g q M)) ∧
        HS.map (topEdgeSingleDirectImageMap g q M) ≫
            e ((DerivedCategory.singleFunctor
              (SheafOfModules.{u} (moduleRings T.toRingedSpace)) q).obj M) =
          (DerivedCategory.singleFunctorCompHomologyFunctorIso
            (SheafOfModules.{u} (moduleRings S.toRingedSpace)) q).hom.app
              ((Scheme.Modules.pushforward g).obj M) ≫
            (Scheme.Modules.pushforward g).map
              ((DerivedCategory.singleFunctorCompHomologyFunctorIso
                (SheafOfModules.{u} (moduleRings T.toRingedSpace)) q).inv.app M)) := by
  refine ⟨resolutionLocalClassEdge g q, ?_, ?_, ?_⟩
  · exact resolutionLocalClassEdge_local g q
  · intro K K' k
    exact resolutionLocalClassEdge_naturality g q k
  · intro M
    exact ⟨topEdgeSingleDirectImageMap_isIso_homology g q M,
      resolutionLocalClassEdge_single g q M⟩

end AlgebraicGeometry
