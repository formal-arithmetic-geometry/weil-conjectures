/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E3
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Abelian.Injective.Ext
import Sheaf.CategoryTheory.RightDerivedUniversalDeltaFunctor
import Sheaf.CategoryTheory.SiteCohomologyPullback
import Sheaf.Paper.ZariskiEtaleResolutionHomologyIndependent


/-! # Cocycle comparisons for object cohomology

Source: Stacks Project, Cohomology, Tags 01F8 and 01FB;
Derived Categories, Tags 013P and 015B (4).
(blueprint: lem-weil-pbc-zariski-etale-resolution-pullback-cocycle)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.Functor.sheafPullbackConstruction

/-- The characterized pullback-counit map sends a resolution cocycle to the
section cocycle obtained by an augmented comparison.

Source: Stacks Project, Cohomology, Tag 01FB; Derived Categories, Tags 013P
and 015B (4); Cohomology on Sites, Section 01FT and Tag 0730.
(blueprint: lem-weil-pbc-zariski-etale-resolution-pullback-cocycle)

Proof: The equality hsec identifies the evaluated cocycle of c with the image
of the evaluated cocycle of a under b. To identify its Ext class, resolve an
arbitrary Zariski sheaf A and its inverse
image. Exactness of inverse image implies preservation of injectives by direct
image. Extend the unit to a comparison of resolutions degree by degree.
Two extensions are homotopic: factor their difference through successive
differentials using exactness of the source and injectivity of the target.
The horseshoe construction shows that the induced maps on cocycle classes
commute with connecting homomorphisms, and lifts of coefficient morphisms
show naturality. In degree zero the map is evaluation of the unit. Efface
positive Ext in the coefficient variable by embedding A into an injective.
The surjective connecting maps then determine the transformation inductively,
so hfstar identifies it with fstar. For A = i_*F, compose with a counit lift
into I. The triangle identity identifies its augmentation with i_* of I.ι.
The difference from b is null-homotopic by the same extension argument.
Consequently their cocycles differ by a coboundary and have the same Ext
class. The counit coefficient map gives exactly the displayed composite.
Degree zero has no incoming boundaries; zero sheaves and empty opens satisfy
the same adjunction calculations. No homology equivalences are assumed. -/
theorem zariski_etale_resolution_pullback_cocycle
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
    (q : ℕ) (V : X.Opens)
    (a : (presheafToSheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u + 1}).obj
        (yoneda.obj V ⋙ AddCommGrpCat.free) ⟶ R.cocomplex.X q)
    (ha : a ≫ R.cocomplex.d q (q + 1) = 0)
    (c : (presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (yoneda.obj (i.obj V) ⋙ AddCommGrpCat.free) ⟶ I.cocomplex.X q)
    (hc : c ≫ I.cocomplex.d q (q + 1) = 0)
    (hsec : (b.f q).hom.app (op V) ((a.hom.app (op V)).hom
          (((toSheafify (Opens.grothendieckTopology X.carrier)
            (yoneda.obj V ⋙ AddCommGrpCat.free)).app (op V)).hom
              (FreeAbelianGroup.of (𝟙 V)))) =
        ((c.hom.app (op (i.obj V))).hom
          (((toSheafify X.smallEtaleTopology
            (yoneda.obj (i.obj V) ⋙ AddCommGrpCat.free)).app (op (i.obj V))).hom
              (FreeAbelianGroup.of (𝟙 (i.obj V)))))) :
      (fstar q V
          ((i.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
            (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology).obj F) ≫
        ((Sheaf.cohomologyPresheafFunctor X.smallEtaleTopology q).map
          ((sheafAdjunctionContinuous i AddCommGrpCat.{u + 1}
            (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology).counit.app F)).app
              (op (i.obj V))).hom (R.extMk a (q + 1) rfl ha) = I.extMk c (q + 1) rfl hc := by sorry
