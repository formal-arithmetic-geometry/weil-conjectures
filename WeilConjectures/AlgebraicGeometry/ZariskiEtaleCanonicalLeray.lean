/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.LocallyInjective
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import WeilConjectures.AlgebraicGeometry.ZariskiEtalePushedResolution
import WeilConjectures.AlgebraicGeometry.ZariskiEtaleResolutionMap
import WeilConjectures.AlgebraicGeometry.ZariskiEtaleResolutionHomologyDataExists
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Preserves

/-! # Canonical Leray comparison for the Zariski-to-étale morphism

## References

* [Stacks Project, Tag 072W](https://stacks.math.columbia.edu/tag/072W)
* [Stacks Project, Tag 0733](https://stacks.math.columbia.edu/tag/0733)
* [Stacks Project, Tag 09AX](https://stacks.math.columbia.edu/tag/09AX)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.Functor.sheafPullbackConstruction

/-- If zero on every positive object-cohomology presheaf is locally injective,
the canonical pullback followed by the counit is an isomorphism on every open.
There is no strict-henselian hypothesis here. -/
theorem zariski_etale_canonical_leray
    {X : Scheme.{u + 1}}
    (i : X.Opens ⥤ X.Etale)
    (hi_inclusion : i ⋙ Scheme.Etale.forget X = X.restrictFunctor)
    (hi : i.IsContinuous (Opens.grothendieckTopology X.carrier)
      X.smallEtaleTopology)
    [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u + 1}]
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [HasExt
      (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u + 1})]
    [HasExt (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
    [(sheafPullback i AddCommGrpCat.{u + 1}
      (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology).Additive]
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
    (hvan : ∀ q : ℕ, 0 < q →
      Presheaf.IsLocallyInjective (Opens.grothendieckTopology X.carrier)
        (0 : i.op ⋙ Sheaf.cohomologyPresheaf F q ⟶
          i.op ⋙ Sheaf.cohomologyPresheaf F q)) :
    ∀ (q : ℕ) (V : X.Opens), IsIso
      (fstar q V
          ((i.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
            (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology).obj F) ≫
        ((Sheaf.cohomologyPresheafFunctor X.smallEtaleTopology q).map
          ((sheafAdjunctionContinuous i AddCommGrpCat.{u + 1}
            (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology).counit.app F)).app
              (op (i.obj V))) := by
  let := hi
  obtain ⟨hlex, hquasi⟩ :=
    zariski_etale_pushed_resolution i hi_inclusion hi F hvan
  let := hlex
  let G := i.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology
  let : G.PreservesInjectiveObjects :=
    (sheafAdjunctionContinuous i AddCommGrpCat.{u + 1}
      (Opens.grothendieckTopology X.carrier)
      X.smallEtaleTopology).preservesInjectiveObjects_of_preservesFiniteLimits
  let I := InjectiveResolution.of F
  let a := (HomologicalComplex.singleMapHomologicalComplex G
      (ComplexShape.up ℕ) 0).inv.app F ≫
    (G.mapHomologicalComplex (ComplexShape.up ℕ)).map I.ι
  let R : InjectiveResolution (G.obj F) :=
    { cocomplex := (G.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
      injective n := G.injective_obj_of_injective (I.injective n)
      ι := a
      quasiIso := hquasi I }
  have he : R.ι.f 0 ≫ HomologicalComplex.Hom.f (𝟙 R.cocomplex) 0 = G.map (I.ι.f 0) := by
    simp [R, a, HomologicalComplex.singleMapHomologicalComplex_inv_app_self]
  intro q V
  obtain ⟨e₁, e₂, hcomp⟩ :=
    zariski_etale_resolution_homology_data_exists i hi fstar hfstar F I R (𝟙 R.cocomplex) he q V
  let E := sheafToPresheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u + 1} ⋙
    (evaluation X.Opensᵒᵖ AddCommGrpCat.{u + 1}).obj (op V)
  let b := HomologicalComplex.homologyMap
    ((E.mapHomologicalComplex (ComplexShape.up ℕ)).map (𝟙 R.cocomplex)) q
  have hb : IsIso b := inferInstance
  have hbij : Function.Bijective b.hom :=
    (ConcreteCategory.isIso_iff_bijective b).mp hb
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  constructor
  · intro x y h
    apply e₁.injective
    apply hbij.1
    rw [← hcomp x, ← hcomp y, h]
  · intro y
    obtain ⟨z, hz⟩ := hbij.2 (e₂ y)
    obtain ⟨x, rfl⟩ := e₁.surjective z
    refine ⟨x, e₂.injective ?_⟩
    rw [hcomp x]
    exact hz
