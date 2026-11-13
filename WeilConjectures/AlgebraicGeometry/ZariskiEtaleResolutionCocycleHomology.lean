/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Abelian.Injective.Ext
import WeilConjectures.AlgebraicGeometry.ZariskiEtaleResolutionCocycleEquivalences
import WeilConjectures.AlgebraicGeometry.ZariskiEtaleResolutionCocycleCompatibility

/-! # Cocycle comparisons for object cohomology

## References

* [Stacks Project, Tag 01FT](https://stacks.math.columbia.edu/tag/01FT)
* [Stacks Project, Tag 06XR](https://stacks.math.columbia.edu/tag/06XR)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

/-- Termwise section evaluation respects the cocycle computation of Ext. -/
theorem zariski_etale_resolution_cocycle_homology
    {X : Scheme.{u + 1}}
    (i : X.Opens ⥤ X.Etale)
    (hi : i.IsContinuous (Opens.grothendieckTopology X.carrier)
      X.smallEtaleTopology)
    [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u + 1}]
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [HasExt
      (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u + 1})]
    [HasExt (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (I : InjectiveResolution F)
    (R : InjectiveResolution ((i.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology).obj F))
    (b : R.cocomplex ⟶
      ((i.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj I.cocomplex)
    (q : ℕ) (V : X.Opens) :
    ∃ (e₁ : Sheaf.H' ((i.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology).obj F) q V ≃+
        ↑(HomologicalComplex.homology
          (((sheafToPresheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u + 1} ⋙
            (evaluation X.Opensᵒᵖ AddCommGrpCat.{u + 1}).obj (op V)).mapHomologicalComplex
               (ComplexShape.up ℕ)).obj R.cocomplex) q))
      (e₂ : Sheaf.H' F q (i.obj V) ≃+
        ↑(HomologicalComplex.homology
          (((sheafToPresheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u + 1} ⋙
            (evaluation X.Opensᵒᵖ AddCommGrpCat.{u + 1}).obj (op V)).mapHomologicalComplex
               (ComplexShape.up ℕ)).obj
                (((i.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
                  (Opens.grothendieckTopology X.carrier)
                    X.smallEtaleTopology).mapHomologicalComplex
                       (ComplexShape.up ℕ)).obj I.cocomplex)) q)),
      ∀ (a : (presheafToSheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u + 1}).obj
        (yoneda.obj V ⋙ AddCommGrpCat.free) ⟶ R.cocomplex.X q)
        (ha : a ≫ R.cocomplex.d q (q + 1) = 0)
        (c : (presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (yoneda.obj (i.obj V) ⋙ AddCommGrpCat.free) ⟶ I.cocomplex.X q)
        (hc : c ≫ I.cocomplex.d q (q + 1) = 0),
        (b.f q).hom.app (op V) ((a.hom.app (op V)).hom
          (((toSheafify (Opens.grothendieckTopology X.carrier)
            (yoneda.obj V ⋙ AddCommGrpCat.free)).app (op V)).hom
              (FreeAbelianGroup.of (𝟙 V)))) =
        ((c.hom.app (op (i.obj V))).hom
          (((toSheafify X.smallEtaleTopology
            (yoneda.obj (i.obj V) ⋙ AddCommGrpCat.free)).app (op (i.obj V))).hom
              (FreeAbelianGroup.of (𝟙 (i.obj V))))) →
        e₂ (I.extMk c (q + 1) rfl hc) =
        (HomologicalComplex.homologyMap
          (((sheafToPresheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u + 1} ⋙
            (evaluation X.Opensᵒᵖ AddCommGrpCat.{u + 1}).obj (op V)).mapHomologicalComplex
               (ComplexShape.up ℕ)).map b) q).hom (e₁ (R.extMk a (q + 1) rfl ha)) := by
  set_option backward.isDefEq.respectTransparency false in
    obtain ⟨e₁, h₁⟩ := objectCohomology_resolution_cocycle_equivalence
      (Opens.grothendieckTopology X.carrier) _ R q V
    obtain ⟨e₂, h₂⟩ := objectCohomology_resolution_cocycle_equivalence
      X.smallEtaleTopology F I q (i.obj V)
    refine ⟨e₁, e₂, ?_⟩
    intro a ha c hc h
    erw [h₁ a ha, h₂ c hc]
    exact (zariski_etale_resolution_cocycle_compatibility
      (((sheafToPresheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u + 1} ⋙
        (evaluation X.Opensᵒᵖ AddCommGrpCat.{u + 1}).obj (op V)).mapHomologicalComplex
          (.up ℕ)).map b) q
      (sheafCocycleSection _ R.cocomplex q V a)
      (sheafCocycleSection_closed _ R.cocomplex q V a ha)
      (sheafCocycleSection X.smallEtaleTopology I.cocomplex q (i.obj V) c)
      (sheafCocycleSection_closed X.smallEtaleTopology I.cocomplex q (i.obj V) c hc) h).symm
