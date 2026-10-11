/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U1
-/
module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.Pullback
public import Sheaf.CategoryTheory.SitePullbackAbelianExact
public import Sheaf.CategoryTheory.Abelian.HorseshoeDeltaFunctor
public import Sheaf.CategoryTheory.Abelian.RightDerived.FullLongExactSequence
public import Sheaf.CategoryTheory.DeltaFunctor
public import Sheaf.CategoryTheory.RightDerivedUniversalDeltaFunctor
public import Sheaf.CategoryTheory.SiteMorphismComposition

/-!
# Pullback on cohomology over objects of sites

Source: Stacks Project, Cohomology, Tags 01F7, 01F8 and 01FB; Sites, Tag 08J6;
Derived Categories, Tag 015B
(blueprint: lem-weil-pbc-site-cohomology-pullback).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction

namespace CategoryTheory

/--
Source: Stacks Project, Cohomology, Tags 01F7, 01F8 and 01FB; Sites, Tag 08J6;
Derived Categories, Tag 015B (4)
(blueprint: lem-weil-pbc-site-cohomology-pullback).

The sites are precoverages with the conditions of 00VH, the morphism of sites `f` is given
by the continuous functor `U` (00WV conditions `hcover`, `hpullback`, exactness of `U_s` on
sheaves of sets), `f⁻¹ = sheafPullback U`, `f_* = U.sheafPushforwardContinuous` with unit
`sheafAdjunctionContinuous U`, and `H^p(V, A) = Sheaf.H' A p V` (Ext from the free abelian
sheaf on `V`, the cohomology over an object of the project). The `Additive` instances of
the three abelian inverse images are consequences of the hypotheses
(lem-weil-pbc-site-pullback-abelian-exact, lem-weil-pbc-site-morphism-composition); they
only make the images `S.map _` of short complexes typeable.

`H'(V, x)` for `x : H' A 0 V` is evaluated through `Ext.addEquiv₀` at the class of `𝟙 V`
in the free sheaf on `V`, i.e. the identification `H⁰(V, A) = A(V)`. The connecting map of
a short exact sequence `S` is the Yoneda product with `S`'s class `hS.extClass`.

First conjunct: there is exactly one family `f*` of maps `H^p(V, A) → H^p(U(V), f⁻¹A)`
which is natural in `A` (clause (2)), commutes with the connecting maps of every short
exact sequence `S` and its image `f⁻¹S` (clause (3)) and is `η_A(V)` in degree `0`
(clause (1)); the uniqueness is the universality statement of clause (3), and the
choice-free characterisation is clause (1)'s independence of choices.

Second conjunct (clause (4)): for a second morphism of sites given by `W`, the families of
`U`, `W` and `U ⋙ W` so characterised satisfy `(f ∘ g)* = H^p(c) ∘ g* ∘ f*`, where `c` is
`e.inv` for the isomorphism `e` of left adjoints compatible with the units
(lem-weil-pbc-site-morphism-composition). -/
theorem siteCohomology_pullback
    {C D E : Type u} [SmallCategory C] [SmallCategory D] [SmallCategory E]
    (J : Precoverage C) (K : Precoverage D) (L : Precoverage E)
    [J.HasIsos] [J.IsStableUnderComposition] [J.IsStableUnderBaseChange] [J.HasPullbacks]
    [K.HasIsos] [K.IsStableUnderComposition] [K.IsStableUnderBaseChange] [K.HasPullbacks]
    [L.HasIsos] [L.IsStableUnderComposition] [L.IsStableUnderBaseChange] [L.HasPullbacks]
    (U : C ⥤ D) (W : D ⥤ E)
    (hUcover : ∀ (X : C) (R : Presieve X), R ∈ J X → R.map U ∈ K (U.obj X))
    (hUpullback : ∀ (X Y Z : C) (R : Presieve X), R ∈ J X →
      ∀ (f : Y ⟶ X) (g : Z ⟶ X), R f → PreservesLimit (cospan f g) U)
    (hWcover : ∀ (X : D) (R : Presieve X), R ∈ K X → R.map W ∈ L (W.obj X))
    (hWpullback : ∀ (X Y Z : D) (R : Presieve X), R ∈ K X →
      ∀ (f : Y ⟶ X) (g : Z ⟶ X), R f → PreservesLimit (cospan f g) W)
    [U.IsContinuous J.toGrothendieck K.toGrothendieck]
    [W.IsContinuous K.toGrothendieck L.toGrothendieck]
    [(U ⋙ W).IsContinuous J.toGrothendieck L.toGrothendieck]
    [PreservesFiniteLimits (sheafPullback U (Type u) J.toGrothendieck K.toGrothendieck)]
    [PreservesFiniteColimits (sheafPullback U (Type u) J.toGrothendieck K.toGrothendieck)]
    [PreservesFiniteLimits (sheafPullback W (Type u) K.toGrothendieck L.toGrothendieck)]
    [PreservesFiniteColimits (sheafPullback W (Type u) K.toGrothendieck L.toGrothendieck)]
    [(sheafPullback U AddCommGrpCat.{u} J.toGrothendieck K.toGrothendieck).Additive]
    [(sheafPullback W AddCommGrpCat.{u} K.toGrothendieck L.toGrothendieck).Additive]
    [(sheafPullback (U ⋙ W) AddCommGrpCat.{u} J.toGrothendieck L.toGrothendieck).Additive]
    [HasExt.{u} (Sheaf J.toGrothendieck AddCommGrpCat.{u})]
    [HasExt.{u} (Sheaf K.toGrothendieck AddCommGrpCat.{u})]
    [HasExt.{u} (Sheaf L.toGrothendieck AddCommGrpCat.{u})] :
    (∃! fstar : ∀ (p : ℕ) (V : C) (A : Sheaf J.toGrothendieck AddCommGrpCat.{u}),
        Sheaf.H' A p V ⟶
          Sheaf.H' ((sheafPullback U AddCommGrpCat.{u}
            J.toGrothendieck K.toGrothendieck).obj A) p (U.obj V),
      (∀ (p : ℕ) (V : C) (A A' : Sheaf J.toGrothendieck AddCommGrpCat.{u}) (φ : A ⟶ A'),
        ((Sheaf.cohomologyPresheafFunctor J.toGrothendieck p).map φ).app (op V) ≫
            fstar p V A' =
          fstar p V A ≫
            ((Sheaf.cohomologyPresheafFunctor K.toGrothendieck p).map
              ((sheafPullback U AddCommGrpCat.{u}
                J.toGrothendieck K.toGrothendieck).map φ)).app (op (U.obj V))) ∧
      (∀ (S : ShortComplex (Sheaf J.toGrothendieck AddCommGrpCat.{u})) (hS : S.ShortExact)
        (hS' : (S.map (sheafPullback U AddCommGrpCat.{u}
          J.toGrothendieck K.toGrothendieck)).ShortExact)
        (p : ℕ) (V : C) (x : Sheaf.H' S.X₃ p V),
        (fstar (p + 1) V S.X₁).hom (Abelian.Ext.comp x hS.extClass rfl) =
          Abelian.Ext.comp ((fstar p V S.X₃).hom x) hS'.extClass rfl) ∧
      (∀ (V : C) (A : Sheaf J.toGrothendieck AddCommGrpCat.{u}) (x : Sheaf.H' A 0 V),
        ((Abelian.Ext.addEquiv₀ ((fstar 0 V A).hom x)).hom.app (op (U.obj V))).hom
            (((toSheafify K.toGrothendieck
              (yoneda.obj (U.obj V) ⋙ AddCommGrpCat.free)).app (op (U.obj V))).hom
                (FreeAbelianGroup.of (𝟙 (U.obj V)))) =
          (((sheafAdjunctionContinuous U AddCommGrpCat.{u}
            J.toGrothendieck K.toGrothendieck).unit.app A).hom.app (op V)).hom
            (((Abelian.Ext.addEquiv₀ x).hom.app (op V)).hom
              (((toSheafify J.toGrothendieck
                (yoneda.obj V ⋙ AddCommGrpCat.free)).app (op V)).hom
                  (FreeAbelianGroup.of (𝟙 V)))))) ∧
    ∀ (fU : ∀ (p : ℕ) (V : C) (A : Sheaf J.toGrothendieck AddCommGrpCat.{u}),
        Sheaf.H' A p V ⟶
          Sheaf.H' ((sheafPullback U AddCommGrpCat.{u}
            J.toGrothendieck K.toGrothendieck).obj A) p (U.obj V))
      (fW : ∀ (p : ℕ) (V : D) (A : Sheaf K.toGrothendieck AddCommGrpCat.{u}),
        Sheaf.H' A p V ⟶
          Sheaf.H' ((sheafPullback W AddCommGrpCat.{u}
            K.toGrothendieck L.toGrothendieck).obj A) p (W.obj V))
      (fUW : ∀ (p : ℕ) (V : C) (A : Sheaf J.toGrothendieck AddCommGrpCat.{u}),
        Sheaf.H' A p V ⟶
          Sheaf.H' ((sheafPullback (U ⋙ W) AddCommGrpCat.{u}
            J.toGrothendieck L.toGrothendieck).obj A) p ((U ⋙ W).obj V)),
      ((∀ (p : ℕ) (V : C) (A A' : Sheaf J.toGrothendieck AddCommGrpCat.{u}) (φ : A ⟶ A'),
        ((Sheaf.cohomologyPresheafFunctor J.toGrothendieck p).map φ).app (op V) ≫
            fU p V A' =
          fU p V A ≫
            ((Sheaf.cohomologyPresheafFunctor K.toGrothendieck p).map
              ((sheafPullback U AddCommGrpCat.{u}
                J.toGrothendieck K.toGrothendieck).map φ)).app (op (U.obj V))) ∧
      (∀ (S : ShortComplex (Sheaf J.toGrothendieck AddCommGrpCat.{u})) (hS : S.ShortExact)
        (hS' : (S.map (sheafPullback U AddCommGrpCat.{u}
          J.toGrothendieck K.toGrothendieck)).ShortExact)
        (p : ℕ) (V : C) (x : Sheaf.H' S.X₃ p V),
        (fU (p + 1) V S.X₁).hom (Abelian.Ext.comp x hS.extClass rfl) =
          Abelian.Ext.comp ((fU p V S.X₃).hom x) hS'.extClass rfl) ∧
      (∀ (V : C) (A : Sheaf J.toGrothendieck AddCommGrpCat.{u}) (x : Sheaf.H' A 0 V),
        ((Abelian.Ext.addEquiv₀ ((fU 0 V A).hom x)).hom.app (op (U.obj V))).hom
            (((toSheafify K.toGrothendieck
              (yoneda.obj (U.obj V) ⋙ AddCommGrpCat.free)).app (op (U.obj V))).hom
                (FreeAbelianGroup.of (𝟙 (U.obj V)))) =
          (((sheafAdjunctionContinuous U AddCommGrpCat.{u}
            J.toGrothendieck K.toGrothendieck).unit.app A).hom.app (op V)).hom
            (((Abelian.Ext.addEquiv₀ x).hom.app (op V)).hom
              (((toSheafify J.toGrothendieck
                (yoneda.obj V ⋙ AddCommGrpCat.free)).app (op V)).hom
                  (FreeAbelianGroup.of (𝟙 V)))))) →
      ((∀ (p : ℕ) (V : D) (A A' : Sheaf K.toGrothendieck AddCommGrpCat.{u}) (φ : A ⟶ A'),
        ((Sheaf.cohomologyPresheafFunctor K.toGrothendieck p).map φ).app (op V) ≫
            fW p V A' =
          fW p V A ≫
            ((Sheaf.cohomologyPresheafFunctor L.toGrothendieck p).map
              ((sheafPullback W AddCommGrpCat.{u}
                K.toGrothendieck L.toGrothendieck).map φ)).app (op (W.obj V))) ∧
      (∀ (S : ShortComplex (Sheaf K.toGrothendieck AddCommGrpCat.{u})) (hS : S.ShortExact)
        (hS' : (S.map (sheafPullback W AddCommGrpCat.{u}
          K.toGrothendieck L.toGrothendieck)).ShortExact)
        (p : ℕ) (V : D) (x : Sheaf.H' S.X₃ p V),
        (fW (p + 1) V S.X₁).hom (Abelian.Ext.comp x hS.extClass rfl) =
          Abelian.Ext.comp ((fW p V S.X₃).hom x) hS'.extClass rfl) ∧
      (∀ (V : D) (A : Sheaf K.toGrothendieck AddCommGrpCat.{u}) (x : Sheaf.H' A 0 V),
        ((Abelian.Ext.addEquiv₀ ((fW 0 V A).hom x)).hom.app (op (W.obj V))).hom
            (((toSheafify L.toGrothendieck
              (yoneda.obj (W.obj V) ⋙ AddCommGrpCat.free)).app (op (W.obj V))).hom
                (FreeAbelianGroup.of (𝟙 (W.obj V)))) =
          (((sheafAdjunctionContinuous W AddCommGrpCat.{u}
            K.toGrothendieck L.toGrothendieck).unit.app A).hom.app (op V)).hom
            (((Abelian.Ext.addEquiv₀ x).hom.app (op V)).hom
              (((toSheafify K.toGrothendieck
                (yoneda.obj V ⋙ AddCommGrpCat.free)).app (op V)).hom
                  (FreeAbelianGroup.of (𝟙 V)))))) →
      ((∀ (p : ℕ) (V : C) (A A' : Sheaf J.toGrothendieck AddCommGrpCat.{u}) (φ : A ⟶ A'),
        ((Sheaf.cohomologyPresheafFunctor J.toGrothendieck p).map φ).app (op V) ≫
            fUW p V A' =
          fUW p V A ≫
            ((Sheaf.cohomologyPresheafFunctor L.toGrothendieck p).map
              ((sheafPullback (U ⋙ W) AddCommGrpCat.{u}
                J.toGrothendieck L.toGrothendieck).map φ)).app (op ((U ⋙ W).obj V))) ∧
      (∀ (S : ShortComplex (Sheaf J.toGrothendieck AddCommGrpCat.{u})) (hS : S.ShortExact)
        (hS' : (S.map (sheafPullback (U ⋙ W) AddCommGrpCat.{u}
          J.toGrothendieck L.toGrothendieck)).ShortExact)
        (p : ℕ) (V : C) (x : Sheaf.H' S.X₃ p V),
        (fUW (p + 1) V S.X₁).hom (Abelian.Ext.comp x hS.extClass rfl) =
          Abelian.Ext.comp ((fUW p V S.X₃).hom x) hS'.extClass rfl) ∧
      (∀ (V : C) (A : Sheaf J.toGrothendieck AddCommGrpCat.{u}) (x : Sheaf.H' A 0 V),
        ((Abelian.Ext.addEquiv₀ ((fUW 0 V A).hom x)).hom.app (op ((U ⋙ W).obj V))).hom
            (((toSheafify L.toGrothendieck
              (yoneda.obj ((U ⋙ W).obj V) ⋙ AddCommGrpCat.free)).app
                (op ((U ⋙ W).obj V))).hom
                (FreeAbelianGroup.of (𝟙 ((U ⋙ W).obj V)))) =
          (((sheafAdjunctionContinuous (U ⋙ W) AddCommGrpCat.{u}
            J.toGrothendieck L.toGrothendieck).unit.app A).hom.app (op V)).hom
            (((Abelian.Ext.addEquiv₀ x).hom.app (op V)).hom
              (((toSheafify J.toGrothendieck
                (yoneda.obj V ⋙ AddCommGrpCat.free)).app (op V)).hom
                  (FreeAbelianGroup.of (𝟙 V)))))) →
      ∀ (e : sheafPullback (U ⋙ W) AddCommGrpCat.{u} J.toGrothendieck L.toGrothendieck ≅
          sheafPullback U AddCommGrpCat.{u} J.toGrothendieck K.toGrothendieck ⋙
            sheafPullback W AddCommGrpCat.{u} K.toGrothendieck L.toGrothendieck),
        (∀ F : Sheaf J.toGrothendieck AddCommGrpCat.{u},
          (sheafAdjunctionContinuous (U ⋙ W) AddCommGrpCat.{u}
            J.toGrothendieck L.toGrothendieck).unit.app F ≫
            ((U ⋙ W).sheafPushforwardContinuous AddCommGrpCat.{u}
              J.toGrothendieck L.toGrothendieck).map (e.hom.app F) =
          (sheafAdjunctionContinuous U AddCommGrpCat.{u}
            J.toGrothendieck K.toGrothendieck).unit.app F ≫
            (U.sheafPushforwardContinuous AddCommGrpCat.{u} J.toGrothendieck K.toGrothendieck).map
              ((sheafAdjunctionContinuous W AddCommGrpCat.{u}
                K.toGrothendieck L.toGrothendieck).unit.app
                ((sheafPullback U AddCommGrpCat.{u} J.toGrothendieck K.toGrothendieck).obj F))) →
        ∀ (p : ℕ) (V : C) (A : Sheaf J.toGrothendieck AddCommGrpCat.{u}),
          fUW p V A =
            fU p V A ≫ fW p (U.obj V)
                ((sheafPullback U AddCommGrpCat.{u} J.toGrothendieck K.toGrothendieck).obj A) ≫
              ((Sheaf.cohomologyPresheafFunctor L.toGrothendieck p).map (e.inv.app A)).app
                (op (W.obj (U.obj V))) := by
  sorry

end CategoryTheory
