/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryHomologyNatIso
import WeilConjectures.Algebra.Homology.ShortComplex.MapHomologyIsoComp
import Mathlib.CategoryTheory.Localization.Predicate

/-!
# Normalized cohomology comparisons for exact derived functors

The comparisons are `Functor.mapDerivedCategoryHomologyFunctorIso`. Their normalization on
representatives is `Functor.mapDerivedCategoryHomologyFunctorIso_hom_app_Q`: the inverse complex
homology comparison, transported through `homologyFunctorFactors` and
`mapDerivedCategoryFactors`.

## References

* Stacks Project, Tag 015F.
-/

@[expose] public section

set_option autoImplicit false

universe uA vA wA uB vB wB uC vC wC

open CategoryTheory Limits

namespace CategoryTheory.Functor

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
  {C : Type uC} [Category.{vC} C] [Abelian C] [HasDerivedCategory.{wC} C]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The normalized cohomology comparisons for exact functors respect the termwise
compositor and every natural isomorphism from the composite to another exact functor.

Here theta is `mapDerivedCategoryHomologyFunctorIso`, c is `mapDerivedCategoryCompIso`,
and d is c inverse followed by `mapDerivedCategoryNatIso eta`.

Stacks Project, Tag 015F. -/
theorem exactDerivedCohomologyCoherence
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (a : ℤ) :
    (∀ K : DerivedCategory A,
      (@mapDerivedCategoryHomologyFunctorIso A C _ _ _ _ _ _ (F ⋙ G) _
        (comp_preservesFiniteLimits F G) (comp_preservesFiniteColimits F G) a).hom.app K ≫
          (DerivedCategory.homologyFunctor C a).map
            ((mapDerivedCategoryCompIso F G).inv.app K) =
        G.map ((F.mapDerivedCategoryHomologyFunctorIso a).hom.app K) ≫
          (G.mapDerivedCategoryHomologyFunctorIso a).hom.app (F.mapDerivedCategory.obj K)) ∧
    (∀ (L : A ⥤ C) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
      (eta : F ⋙ G ≅ L) (K : DerivedCategory A),
      G.map ((F.mapDerivedCategoryHomologyFunctorIso a).hom.app K) ≫
          (G.mapDerivedCategoryHomologyFunctorIso a).hom.app (F.mapDerivedCategory.obj K) ≫
          (DerivedCategory.homologyFunctor C a).map
            ((mapDerivedCategoryCompIso F G ≪≫
              @mapDerivedCategoryNatIso A C _ _ _ _ _ _ (F ⋙ G) L _ _
                (comp_preservesFiniteLimits F G) (comp_preservesFiniteColimits F G)
                _ _ eta).hom.app K) =
        eta.hom.app ((DerivedCategory.homologyFunctor A a).obj K) ≫
          (L.mapDerivedCategoryHomologyFunctorIso a).hom.app K) := by
  let := comp_preservesFiniteLimits F G
  let := comp_preservesFiniteColimits F G
  have hcomplex (X : CochainComplex A ℤ) :
      ((F ⋙ G).mapHomologicalComplexHomologyIso (.up ℤ) a).inv.app X =
        G.map ((F.mapHomologicalComplexHomologyIso (.up ℤ) a).inv.app X) ≫
          (G.mapHomologicalComplexHomologyIso (.up ℤ) a).inv.app
            ((F.mapHomologicalComplex (.up ℤ)).obj X) := by
    have he (H : A ⥤ C) [H.Additive] [H.PreservesHomology] :
        (H.mapHomologicalComplexHomologyIso (.up ℤ) a).app X =
          (X.sc a).mapHomologyIso H :=
      Iso.ext (mapHomologicalComplexHomologyIso_hom_app_eq _ _ _ _)
    have heF : (F.mapHomologicalComplexHomologyIso (.up ℤ) a).app X =
        (X.sc a).mapHomologyIso F :=
      Iso.ext (mapHomologicalComplexHomologyIso_hom_app_eq _ _ _ _)
    have heG : (G.mapHomologicalComplexHomologyIso (.up ℤ) a).app
        ((F.mapHomologicalComplex (.up ℤ)).obj X) =
          ((X.sc a).map F).mapHomologyIso G :=
      Iso.ext (mapHomologicalComplexHomologyIso_hom_app_eq _ _ _ _)
    simp only [← Iso.app_inv, he, heF, heG, ShortComplex.mapHomologyIso_comp,
      Iso.trans_inv, Functor.mapIso_inv]
  have hcomp :
      ((F ⋙ G).mapDerivedCategoryHomologyFunctorIso a).hom ≫
          whiskerRight (mapDerivedCategoryCompIso F G).inv
            (DerivedCategory.homologyFunctor C a) =
        whiskerRight (F.mapDerivedCategoryHomologyFunctorIso a).hom G ≫
          whiskerLeft F.mapDerivedCategory (G.mapDerivedCategoryHomologyFunctorIso a).hom := by
    refine Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso A (.up ℤ)) (fun X ↦ ?_)
    have hc : (mapDerivedCategoryCompIso F G).inv.app (DerivedCategory.Q.obj X) ≫
        G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app X) ≫
          G.mapDerivedCategoryFactors.hom.app
            ((F.mapHomologicalComplex (.up ℤ)).obj X) =
        (F ⋙ G).mapDerivedCategoryFactors.hom.app X := by
      have h := mapDerivedCategoryCompIso_fac F G X
      have hid : (mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).hom.app X =
          𝟙 _ := rfl
      rw [hid] at h
      erw [DerivedCategory.Q.map_id, Category.comp_id] at h
      exact h
    have hfac : (F ⋙ G).mapDerivedCategoryFactors.inv.app X ≫
        (mapDerivedCategoryCompIso F G).inv.app (DerivedCategory.Q.obj X) =
        G.mapDerivedCategoryFactors.inv.app ((F.mapHomologicalComplex (.up ℤ)).obj X) ≫
          G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.inv.app X) := by
      apply (cancel_mono (G.mapDerivedCategory.map
        (F.mapDerivedCategoryFactors.hom.app X) ≫
          G.mapDerivedCategoryFactors.hom.app
            ((F.mapHomologicalComplex (.up ℤ)).obj X))).1
      simp only [Category.assoc, hc, Iso.inv_hom_id_app]
      erw [← G.mapDerivedCategory.map_comp_assoc, Iso.inv_hom_id_app]
      erw [G.mapDerivedCategory.map_id, Category.id_comp, Iso.inv_hom_id_app]
      rfl
    simp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app]
    rw [mapDerivedCategoryHomologyFunctorIso_hom_app_Q,
      mapDerivedCategoryHomologyFunctorIso_hom_app_Q]
    simp only [Functor.comp_map, Functor.map_comp, Category.assoc]
    rw [← Functor.map_comp, hfac, Functor.map_comp]
    have hn := (G.mapDerivedCategoryHomologyFunctorIso a).hom.naturality
      (F.mapDerivedCategoryFactors.inv.app X)
    dsimp only [Functor.comp_map] at hn
    erw [hn]
    dsimp only [Functor.comp_obj]
    erw [mapDerivedCategoryHomologyFunctorIso_hom_app_Q]
    simp only [Category.assoc]
    erw [← G.map_comp_assoc
      ((DerivedCategory.homologyFunctorFactors B a).inv.app _)
      ((DerivedCategory.homologyFunctorFactors B a).hom.app _),
      Iso.inv_hom_id_app, G.map_id, Category.id_comp]
    rw [hcomplex]
    simp only [Category.assoc]
    rfl
  refine ⟨fun K ↦ congr_app hcomp K, ?_⟩
  intro L _ _ _ eta K
  have hk := congr_app hcomp K
  simp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app] at hk
  rw [← Category.assoc, ← hk]
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.map_comp,
    Category.assoc]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app, Functor.map_id, Category.id_comp]
  exact (mapDerivedCategoryHomologyFunctorIso_hom_app_naturality eta a K).symm

end CategoryTheory.Functor
