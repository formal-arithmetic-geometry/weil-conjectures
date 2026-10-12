/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U1
-/
module

public import Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Topology.Sheaves.Stalks
public import Mathlib.CategoryTheory.Sites.LeftExact
import Sheaf.Topology.PresheafModuleStalkFunctor

/-! # Sheafification of cohomology over open subsets

Source: Stacks Project, Cohomology, Lemma 20.32.3, Tag 0BKJ
(blueprint: lem-pc-ringed-space-sheafification-cohomology).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace AlgebraicGeometry.RingedSpace

/-- Cohomology of sections of the functorial K-injective replacement descends to the
unbounded derived category. Its sheafification is naturally the cohomology sheaf.
The comparison with that sheaf is the sheafification unit followed by this isomorphism;
it represents every stalk element locally, detects zero locally, and commutes with
morphisms on germs.

Source: Stacks Project, Tag 0BKJ
(blueprint: lem-pc-ringed-space-sheafification-cohomology).

Proof:
1. Resolve by `CochainComplex.kInjectiveResolutionFunctor`, as in
   `def-pc-ringed-spaces-derived-direct-image`. A quasi-isomorphism between the resulting
   K-injective complexes is a homotopy equivalence. Taking sections and then cohomology
   therefore inverts quasi-isomorphisms and descends to the derived category.
2. Compute cycles, boundaries and their quotient sectionwise. Exact sheafification
   (`lem-weil-pbc-ringed-site-module-sheafification-exact`) identifies their sheafifications
   with the cycles, boundaries and cohomology sheaf of the resolution. The resolution
   quasi-isomorphism identifies the latter with the derived cohomology sheaf. This is
   natural in chain maps and hence, by localization, in all derived morphisms.
3. The sheafification unit is an isomorphism on stalks
   (`lem-weil-pbc-stalk-sheafification-space`). The stalk is the filtered colimit over
   neighborhoods (`def-weil-pbc-module-stalk`), so every element is represented locally
   and a zero germ vanishes on a smaller neighborhood. Naturality of the comparison
   gives the asserted compatibility for the germ of the image of a section. -/
theorem sheafification_cohomology (X : RingedSpace.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X))] (q : ℤ) :
    ∃ P : DerivedCategory (SheafOfModules.{u} (moduleRings X)) ⥤
        ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}),
      Nonempty (DerivedCategory.Q ⋙ P ≅
        CochainComplex.kInjectiveResolutionFunctor.{u}
            (SheafOfModules.{u} (moduleRings X)) ⋙
          (Functor.mapHomologicalComplex
            (SheafOfModules.toSheaf (moduleRings X) ⋙
            sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
            (ComplexShape.up ℤ)) ⋙
          HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) q) ∧
      ∃ e : P ⋙ presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ≅
          DerivedCategory.homologyFunctor (SheafOfModules.{u} (moduleRings X)) q ⋙
            SheafOfModules.toSheaf (moduleRings X),
        ∃ θ : P ⟶
            DerivedCategory.homologyFunctor (SheafOfModules.{u} (moduleRings X)) q ⋙
              SheafOfModules.toSheaf (moduleRings X) ⋙
                sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u},
          θ = Functor.whiskerLeft P
              (sheafificationAdjunction (Opens.grothendieckTopology X)
                AddCommGrpCat.{u}).unit ≫
            Functor.whiskerRight e.hom
              (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) ∧
          (∀ (K : DerivedCategory (SheafOfModules.{u} (moduleRings X))) (x : X)
            (t : ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj
              ((DerivedCategory.homologyFunctor
                (SheafOfModules.{u} (moduleRings X)) q ⋙
                  SheafOfModules.toSheaf (moduleRings X) ⋙
                    sheafToPresheaf (Opens.grothendieckTopology X)
                      AddCommGrpCat.{u}).obj K))),
            ∃ (U : Opens X) (hx : x ∈ U) (s : (P.obj K).obj (op U)),
              (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) _ U x hx)
                ((θ.app K).app (op U) s) = t) ∧
          (∀ (K : DerivedCategory (SheafOfModules.{u} (moduleRings X)))
            (U : Opens X) (x : X) (hx : x ∈ U) (s : (P.obj K).obj (op U)),
            (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) _ U x hx) ((θ.app K).app (op U) s) = 0 →
              ∃ (V : Opens X) (_hxV : x ∈ V) (i : V ⟶ U),
                (P.obj K).map i.op s = 0) ∧
          (∀ (K L : DerivedCategory (SheafOfModules.{u} (moduleRings X)))
            (f : K ⟶ L) (U : Opens X) (x : X) (hx : x ∈ U)
            (s : (P.obj K).obj (op U)),
            (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) _ U x hx)
                ((θ.app L).app (op U) ((P.map f).app (op U) s)) =
              ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
                ((DerivedCategory.homologyFunctor
                  (SheafOfModules.{u} (moduleRings X)) q ⋙
                    SheafOfModules.toSheaf (moduleRings X) ⋙
                      sheafToPresheaf (Opens.grothendieckTopology X)
                        AddCommGrpCat.{u}).map f))
                  ((TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) _ U x hx)
                    ((θ.app K).app (op U) s))) := by
  sorry

end AlgebraicGeometry.RingedSpace
