# AlgebraicGeometry.Etale.rawModuleScalar_pullback_formulas

## Reason

Restore the existing Lean attachment from its current quarantine archive. The archived
private import of `WeilConjectures.AlgebraicGeometry.RawModuleScalarPullbackModuleFormula`
loads upstream coefficient-factor declarations already defined by the public Sheaf imports.
The unchanged archive reproduces the duplicate `abelianCoefficientFactor` import error.

Replace that private import and component application with a proved private categorical
factorization lemma, then instantiate it with the actual raw-map data. The abelian half still
uses its existing proved component. `Over.w_assoc` replaces the three equivalent triangle
proofs in the statement and supplies the inverse triangle in the proof. The universes,
binders, class type, functor-map conclusion and all public imports are preserved; changing
proofs of triangle equalities changes no proposition by proof irrelevance.

The associated performance repair is documented separately in
`G3-raw-module-coefficient-factor-endpoints.md`. No adopted upstream declaration is changed.

## Old

The quarantined module, verbatim:

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M2
-/
module

public import Sheaf.AlgebraicGeometry.RawModuleAbelianHomMap
public import Sheaf.AlgebraicGeometry.RawModuleScalarCoefficientSquare
import WeilConjectures.AlgebraicGeometry.RawModuleScalarPullbackModuleFormula
public import Sheaf.AlgebraicGeometry.RawModuleScalarSourceFactors
import Sheaf.AlgebraicGeometry.RawModuleScalarPullbackAbelianFormula


/-! # Concrete formulas for raw scalar comparison
Source: Stacks Project, Tags 03FD, 03Q8 and 03D7.
-/


@[expose] public section

universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency true in
/-- Factorization of the two explicit raw pullbacks.
Source: Stacks Project, Tags 03FD and 03Q8, formula-expansion step of
lem-sbc-raw-module-abelian-hom-map-naturality.
(blueprint: lem-sbc-raw-scalar-pullback-formulas).

Proof: Evaluate higherDirectImageRawOverFunctor.map via
higherDirectImageRawOverPullbackHom_apply and expand higherDirectImageRawOverPullback and
higherDirectImageRawTrianglePullback. The first two factors are moduleSourceFactor and the last
two are moduleCoefficientFactor. Associativity joins the first two, leaving the derived image of
z in the middle. Expand abelianHigherDirectImageRawPullback on the arbitrary abelian class x.
Its first two factors are abelianSourceFactor and its last two are abelianCoefficientFactor, so
the same associativity equation gives the second identity. These are formulas for the two maps
separately; scalar comparison, its coherence and any relationship between z and x are not used.
All zero and identity cases follow from the same expansions. -/
theorem rawModuleScalar_pullback_formulas
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ) (U : S.Etale)
    (A B : Over W) (f : A ⟶ B)
    (z : (higherDirectImageRawOverFunctor Λ k G (q : ℤ) U).obj (op B)) :
    ((higherDirectImageRawOverFunctor Λ k G (q : ℤ) U).map f.op z =
      moduleSourceFactor Λ f.left (B.hom ≫ k) (A.hom ≫ k)
        (by rw [← Category.assoc, Over.w]) ((freeSheaf Λ S).obj U) ≫
      (upperStar (ModuleCat.{u + 1} Λ) f.left).mapDerivedCategoryPlus.map z ≫
        moduleCoefficientFactor Λ G (q : ℤ) A B f) ∧
    (∀ (x : (abelianHigherDirectImageRawPresheaf (B.hom ≫ k) q
      (restrictedOverCoefficient ((RawModuleScalarComparison.forget Λ W).obj G) B)).obj
        (op U)),
      abelianHigherDirectImageRawPullback f.left (B.hom ≫ k) (A.hom ≫ k)
        (by rw [← Category.assoc, Over.w]) q _ _
        ((upperStarComp AddCommGrpCat.{u + 1} f.left B.hom A.hom
          (Over.w f).symm).inv.app ((RawModuleScalarComparison.forget Λ W).obj G)) U x =
      abelianSourceFactor f.left (B.hom ≫ k) (A.hom ≫ k)
        (by rw [← Category.assoc, Over.w]) (RawModuleScalarComparison.freeAbelian S U) ≫
      (upperStar AddCommGrpCat.{u + 1} f.left).mapDerivedCategoryPlus.map x ≫
      abelianCoefficientFactor ((RawModuleScalarComparison.forget Λ W).obj G)
        (q : ℤ) A B f) := by
  constructor
  · exact rawModuleScalar_pullback_module_formula Λ k G q U A B f z
  · exact rawModuleScalar_pullback_abelian_formula Λ k G q U A B f

end AlgebraicGeometry.Etale
```

## New

The restored module:

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M2
-/
module

public import Sheaf.AlgebraicGeometry.RawModuleAbelianHomMap
public import Sheaf.AlgebraicGeometry.RawModuleScalarCoefficientSquare
public import Sheaf.AlgebraicGeometry.RawModuleScalarSourceFactors
import Sheaf.AlgebraicGeometry.RawModuleScalarPullbackAbelianFormula


/-! # Concrete formulas for raw scalar comparison
Source: Stacks Project, Tags 03FD, 03Q8 and 03D7.
-/


@[expose] public section

universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

private theorem rawTriangleMap_factorization
    {C₀ C D E D' E' : Type*}
    [Category C₀] [Category C] [Category D] [Category E] [Category D'] [Category E']
    [Preadditive D'] [Preadditive E']
    (Q : C₀ ⥤ C) (H : C ⥤ D) (H' : C ⥤ E) (P : D ⥤ E)
    (A : D ⥤ D') (B : E ⥤ E') (F : D' ⥤ E')
    (c : H' ⟶ H ⋙ P) (e : P ⋙ B ⟶ A ⋙ F)
    (U : C₀) {K : D'} {K' : E'}
    (z : A.obj (H.obj (Q.obj U)) ⟶ K)
    (s : F.obj K ⟶ K') :
    rawTriangleMap (Q ⋙ H) (Q ⋙ H') P A B F (Functor.whiskerLeft Q c) e U z s =
      rawTriangleSource H H' P A B F c e (Q.obj U) ≫ F.map z ≫ s := by
  exact (Category.assoc (B.map (c.app (Q.obj U)))
    (e.app (H.obj (Q.obj U))) (F.map z ≫ s)).symm

set_option backward.isDefEq.respectTransparency true in
/-- Factorization of the two explicit raw pullbacks.
Source: Stacks Project, Tags 03FD and 03Q8, formula-expansion step of
lem-sbc-raw-module-abelian-hom-map-naturality.
(blueprint: lem-sbc-raw-scalar-pullback-formulas).

Proof: Evaluate higherDirectImageRawOverFunctor.map via
higherDirectImageRawOverPullbackHom_apply and expand higherDirectImageRawOverPullback and
higherDirectImageRawTrianglePullback. The first two factors are moduleSourceFactor and the last
two are moduleCoefficientFactor. Associativity joins the first two, leaving the derived image of
z in the middle. Expand abelianHigherDirectImageRawPullback on the arbitrary abelian class x.
Its first two factors are abelianSourceFactor and its last two are abelianCoefficientFactor, so
the same associativity equation gives the second identity. These are formulas for the two maps
separately; scalar comparison, its coherence and any relationship between z and x are not used.
All zero and identity cases follow from the same expansions. -/
theorem rawModuleScalar_pullback_formulas
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ) (U : S.Etale)
    (A B : Over W) (f : A ⟶ B)
    (z : (higherDirectImageRawOverFunctor Λ k G (q : ℤ) U).obj (op B)) :
    ((higherDirectImageRawOverFunctor Λ k G (q : ℤ) U).map f.op z =
      moduleSourceFactor Λ f.left (B.hom ≫ k) (A.hom ≫ k)
        (Over.w_assoc f k) ((freeSheaf Λ S).obj U) ≫
      (upperStar (ModuleCat.{u + 1} Λ) f.left).mapDerivedCategoryPlus.map z ≫
        moduleCoefficientFactor Λ G (q : ℤ) A B f) ∧
    (∀ (x : (abelianHigherDirectImageRawPresheaf (B.hom ≫ k) q
      (restrictedOverCoefficient ((RawModuleScalarComparison.forget Λ W).obj G) B)).obj
        (op U)),
      abelianHigherDirectImageRawPullback f.left (B.hom ≫ k) (A.hom ≫ k)
        (Over.w_assoc f k) q _ _
        ((upperStarComp AddCommGrpCat.{u + 1} f.left B.hom A.hom
          (Over.w f).symm).inv.app ((RawModuleScalarComparison.forget Λ W).obj G)) U x =
      abelianSourceFactor f.left (B.hom ≫ k) (A.hom ≫ k)
        (Over.w_assoc f k) (RawModuleScalarComparison.freeAbelian S U) ≫
      (upperStar AddCommGrpCat.{u + 1} f.left).mapDerivedCategoryPlus.map x ≫
      abelianCoefficientFactor ((RawModuleScalarComparison.forget Λ W).obj G)
        (q : ℤ) A B f) := by
  constructor
  · exact rawTriangleMap_factorization
      (freeSheaf Λ S)
      (upperStar (ModuleCat.{u + 1} Λ) (B.hom ≫ k))
      (upperStar (ModuleCat.{u + 1} Λ) (A.hom ≫ k))
      (upperStar (ModuleCat.{u + 1} Λ) f.left)
      (DerivedCategory.Plus.singleFunctor _ 0) (DerivedCategory.Plus.singleFunctor _ 0)
      (upperStar (ModuleCat.{u + 1} Λ) f.left).mapDerivedCategoryPlus
      (upperStarComp (ModuleCat.{u + 1} Λ) f.left (B.hom ≫ k) (A.hom ≫ k)
        (Over.w_assoc f k).symm).hom
      ((upperStar (ModuleCat.{u + 1} Λ) f.left).mapDerivedCategoryPlusSingleFunctor 0).inv
      U z (moduleCoefficientFactor Λ G (q : ℤ) A B f)
  · exact rawModuleScalar_pullback_abelian_formula Λ k G q U A B f

end AlgebraicGeometry.Etale
```

## Users

`tools/downstream.py` reports this module as unknown because it is quarantined. Searching
both tracked Lean roots and both quarantine roots finds no consumer of its module or its
declaration outside its own archive. Its existing DAG attachment is retained; absence of
source consumers is not used to infer withdrawal.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.RawModuleScalarPullbackFormulas | G3 | Restore the same statement with a complete local module calculation and the existing abelian calculation. All public imports and data definitions are preserved. |

No consumer adaptation is required. The unit `sk-lem-failure-field` has no realized statement
or step attached to this node, and its route is unchanged.

## Status

landed 20261020T221157-L-4153838 2026-10-20 (merge of deliver/G3/Sheaf.AlgebraicGeometry.RawModuleScalarPullbackFormulas)
