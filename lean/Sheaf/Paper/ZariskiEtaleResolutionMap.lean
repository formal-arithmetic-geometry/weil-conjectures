/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S3
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Abelian.RightDerived

/-! # Resolution representation of canonical cohomology comparison

Source: Stacks Project, Tags 072W and 0733(1).
(blueprint: lem-weil-pbc-zariski-etale-resolution-map)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.Functor.sheafPullbackConstruction

/-- Represent the canonical comparison by a map of section complexes.

Source: Stacks Project, Cohomology on Sites, Tags 0730 and 0733(1), and
Cohomology, Tags 01F7, 01F8, 01FB.
(blueprint: lem-weil-pbc-zariski-etale-resolution-map)

Proof: the free abelian sheaf on V represents evaluation at V by the
sheafification adjunction, free-abelian adjunction and Yoneda. Apply that additive
identification termwise to the Hom complex of R, and the corresponding one at
i(V) to I; the latter is the same complex as evaluating i_*I at V.
The injective-resolution computation of Ext gives the two additive equivalences.
A resolution comparison lifting the unit represents cohomology pullback: it is
natural in coefficients, respects the connecting maps, and evaluates the unit
in degree zero. Exactness of inverse image and uniqueness of the universal
cohomological delta-functor identify it with the family characterized by hfstar.
Postcomposition with the counit is represented by the given a: its augmentation
condition is precisely the triangle identity. Comparison maps between resolutions
are unique up to homotopy, so any such a induces the same homology map. Transport
through the termwise evaluation identifications to obtain the displayed equation.
No invertibility of a, and no vanishing hypothesis, is used. -/
theorem zariski_etale_resolution_map
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
    (a : R.cocomplex ⟶
      ((i.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj I.cocomplex)
    (ha : R.ι.f 0 ≫ a.f 0 = (i.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
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
               (ComplexShape.up ℕ)).map a) q).hom (e₁ x) := by sorry
