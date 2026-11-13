/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Abelian.RightDerived
import WeilConjectures.AlgebraicGeometry.ZariskiEtaleResolutionCocycleHomology
import WeilConjectures.AlgebraicGeometry.ZariskiEtaleResolutionPullbackCocycle

/-! # Resolution comparison bridge

## References

* [Stacks Project, Tag 01FB](https://stacks.math.columbia.edu/tag/01FB)
* [Stacks Project, Tag 013P](https://stacks.math.columbia.edu/tag/013P)
* [Stacks Project, Tag 015B](https://stacks.math.columbia.edu/tag/015B)
* [Stacks Project, Tag 0730](https://stacks.math.columbia.edu/tag/0730)
* [Stacks Project, Tag 0733](https://stacks.math.columbia.edu/tag/0733)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.Functor.sheafPullbackConstruction

private noncomputable def resolutionSectionEquiv
    {C : Type*} [Category.{u + 1} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{u + 1}] (V : C)
    (A : Sheaf J AddCommGrpCat.{u + 1}) :
    ((presheafToSheaf J AddCommGrpCat.{u + 1}).obj
      (yoneda.obj V ⋙ AddCommGrpCat.free) ⟶ A) ≃ A.obj.obj (op V) :=
  ((sheafificationAdjunction J AddCommGrpCat.{u + 1}).homEquiv _ A).trans
    (((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv (yoneda.obj V) A.obj).trans yonedaEquiv)

private lemma resolutionSectionEquiv_comp
    {C : Type*} [Category.{u + 1} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{u + 1}] (V : C)
    {A B : Sheaf J AddCommGrpCat.{u + 1}}
    (a : (presheafToSheaf J AddCommGrpCat.{u + 1}).obj
      (yoneda.obj V ⋙ AddCommGrpCat.free) ⟶ A) (f : A ⟶ B) :
    resolutionSectionEquiv J V B (a ≫ f) =
      (f.hom.app (op V)).hom (resolutionSectionEquiv J V A a) := by
  rfl

private lemma resolutionSectionEquiv_zero
    {C : Type*} [Category.{u + 1} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{u + 1}] (V : C)
    (A : Sheaf J AddCommGrpCat.{u + 1}) :
    resolutionSectionEquiv J V A 0 = 0 := by
  rfl

/-- The canonical pullback-counit map is represented by any augmented comparison. -/
theorem zariski_etale_resolution_homology_data_exists
    {X : Scheme.{u + 1}}
    (i : X.Opens ⥤ X.Etale)
    (hi : i.IsContinuous (Opens.grothendieckTopology X.carrier)
      X.smallEtaleTopology)
    [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u + 1}]
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [HasExt
      (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u + 1})]
    [HasExt (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
    [(sheafPullback i AddCommGrpCat.{u + 1}
      (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology).Additive]
    [PreservesFiniteLimits (sheafPullback i AddCommGrpCat.{u + 1}
      (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology)]
    (fstar : ∀ (p : ℕ) (V : X.Opens)
      (A : Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u + 1}),
      Sheaf.H' A p V ⟶
        Sheaf.H' ((sheafPullback i AddCommGrpCat.{u + 1}
          (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology).obj A)
          p (i.obj V))
    (hfstar : (∀ (p : ℕ) (V : X.Opens) (A A' : Sheaf (Opens.grothendieckTopology X.carrier)
      AddCommGrpCat.{u + 1}) (φ : A ⟶ A'),
        ((Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X.carrier) p).map φ).app
          (op V) ≫
            fstar p V A' =
          fstar p V A ≫
            ((Sheaf.cohomologyPresheafFunctor X.smallEtaleTopology p).map
              ((sheafPullback i AddCommGrpCat.{u + 1}
                (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology).map φ)).app
                  (op (i.obj V))) ∧
      (∀ (S : ShortComplex (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u + 1}))
        (hS : S.ShortExact)
        (hS' : (S.map (sheafPullback i AddCommGrpCat.{u + 1}
          (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology)).ShortExact)
        (p : ℕ) (V : X.Opens) (x : Sheaf.H' S.X₃ p V),
        (fstar (p + 1) V S.X₁).hom (Abelian.Ext.comp x hS.extClass rfl) =
          Abelian.Ext.comp ((fstar p V S.X₃).hom x) hS'.extClass rfl) ∧
      (∀ (V : X.Opens) (A : Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u + 1})
        (x : Sheaf.H' A 0 V),
        ((Abelian.Ext.addEquiv₀ ((fstar 0 V A).hom x)).hom.app (op (i.obj V))).hom
            (((toSheafify X.smallEtaleTopology
              (yoneda.obj (i.obj V) ⋙ AddCommGrpCat.free)).app (op (i.obj V))).hom
                (FreeAbelianGroup.of (𝟙 (i.obj V)))) =
          (((sheafAdjunctionContinuous i AddCommGrpCat.{u + 1}
            (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology).unit.app A).hom.app
              (op V)).hom
            (((Abelian.Ext.addEquiv₀ x).hom.app (op V)).hom
              (((toSheafify (Opens.grothendieckTopology X.carrier)
                (yoneda.obj V ⋙ AddCommGrpCat.free)).app (op V)).hom
                  (FreeAbelianGroup.of (𝟙 V))))))
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (I : InjectiveResolution F)
    (R : InjectiveResolution ((i.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology).obj F))
    (b : R.cocomplex ⟶
      ((i.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj I.cocomplex)
    (hb : R.ι.f 0 ≫ b.f 0 = (i.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology).map (I.ι.f 0))
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
      ∀ x, e₂ ((fstar q V
          ((i.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
            (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology).obj F) ≫
        ((Sheaf.cohomologyPresheafFunctor X.smallEtaleTopology q).map
          ((sheafAdjunctionContinuous i AddCommGrpCat.{u + 1}
            (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology).counit.app F)).app
              (op (i.obj V))).hom x) =
        (HomologicalComplex.homologyMap
          (((sheafToPresheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u + 1} ⋙
            (evaluation X.Opensᵒᵖ AddCommGrpCat.{u + 1}).obj (op V)).mapHomologicalComplex
               (ComplexShape.up ℕ)).map b) q).hom (e₁ x) := by
  obtain ⟨e₁, e₂, he⟩ :=
    zariski_etale_resolution_cocycle_homology i hi F I R b q V
  refine ⟨e₁, e₂, ?_⟩
  intro x
  obtain ⟨a, ha, rfl⟩ := R.extMk_surjective x (q + 1) rfl
  let J := Opens.grothendieckTopology X.carrier
  let K := X.smallEtaleTopology
  let s := resolutionSectionEquiv J V (R.cocomplex.X q) a
  let c := (resolutionSectionEquiv K (i.obj V) (I.cocomplex.X q)).symm
    ((b.f q).hom.app (op V) s)
  have hsec : (b.f q).hom.app (op V) s =
      resolutionSectionEquiv K (i.obj V) (I.cocomplex.X q) c := by
    exact (Equiv.apply_symm_apply _ _).symm
  have hc : c ≫ I.cocomplex.d q (q + 1) = 0 := by
    apply (resolutionSectionEquiv K (i.obj V) (I.cocomplex.X (q + 1))).injective
    rw [resolutionSectionEquiv_comp, ← hsec, resolutionSectionEquiv_zero]
    have hcomm := congrArg
      (fun f ↦ (f.hom.app (op V)).hom s) (b.comm q (q + 1))
    have hz : (R.cocomplex.d q (q + 1)).hom.app (op V) s = 0 := by
      change resolutionSectionEquiv J V (R.cocomplex.X (q + 1))
        (a ≫ R.cocomplex.d q (q + 1)) = 0
      rw [ha, resolutionSectionEquiv_zero]
    change (I.cocomplex.d q (q + 1)).hom.app (op (i.obj V))
        ((b.f q).hom.app (op V) s) =
      (b.f (q + 1)).hom.app (op V)
        ((R.cocomplex.d q (q + 1)).hom.app (op V) s) at hcomm
    rw [hz, map_zero] at hcomm
    exact hcomm
  have hclass := zariski_etale_resolution_pullback_cocycle
    i hi fstar hfstar F I R b hb q V a ha c hc hsec
  rw [hclass]
  exact he a ha c hc hsec
