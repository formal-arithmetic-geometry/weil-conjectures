module

public import Sheaf.Paper.CompleteCompactificationLimitSupport
import Sheaf.Paper.CompactificationScalarData
import Sheaf.Paper.CompactificationOpenLimit
import Sheaf.Paper.CompactificationPushLimit

/-!
# Complete compactification images: canonical limit realization
Source: blueprint paragraph (2)
(blueprint: lem-sp-complete-compactification-limit-realization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
namespace AlgebraicGeometry.ProEtale.CompleteCompactificationLimit
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The canonical strict-system scalar comparisons. The ordinary comparisons are
normalized before localization by the actual finite scalar maps. The derived direct-image
comparison is fixed by the two composition units on every cochain complex.
Source: blueprint paragraph (2), scalar comparisons and transition compatibility
(blueprint: lem-sp-complete-compactification-limit-realization). -/
structure ScalarComparison (b : SpTowerShriek.Base l E)
    (o : SpTowerShriek.Operations l E b) (h : ScalarSquares l E)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (DX : SpCoefficientTowersAbelian l E X) (DZ : SpCoefficientTowersAbelian l E c.Z)
    (DY : SpCoefficientTowersAbelian l E Y)
    (rX : SpReductionTower l E X DX) (rZ : SpReductionTower l E c.Z DZ)
    (rY : SpReductionTower l E Y DY)
    (aX : LimitPresentation l E X DX rX) (aZ : LimitPresentation l E c.Z DZ rZ)
    (aY : LimitPresentation l E Y DY rY)
    (vX : Evaluation l E b X DX) (vZ : Evaluation l E b c.Z DZ)
    (vY : Evaluation l E b Y DY) where
  openOrdinary : forgetting l E X DX ⋙ fixedOpenOrd l E c.i ≅
    ordinaryTowerOpen l E b o c.i ⋙ forgetting l E c.Z DZ
  open_normalized : ∀ (N : spCoefficientTowers l E X) (n : ℕ),
    (openOrdinary.hom.app N).app (op n) ≫
        (spCompletedEllRestriction l E c.Z n).map
          ((ordinaryOpenEvaluation l E b o c.i DX DZ vX vZ n).hom.app N) =
      (ordinaryOpenScalar l E b h c.i n).hom.app
        ((spCoefficientEvaluation l E X DX.equivalence n).obj N)
  pushOrdinary : forgetting l E c.Z DZ ⋙ fixedPushOrd l E c.g ≅
    ordinaryTowerPush l E b o c.g ⋙ forgetting l E Y DY
  push_normalized : ∀ (N : spCoefficientTowers l E c.Z) (n : ℕ),
    (pushOrdinary.hom.app N).app (op n) ≫
        (spCompletedEllRestriction l E Y n).map
          ((ordinaryPushEvaluation l E b o c.g DZ DY vZ vY n).hom.app N) =
      (ordinaryPushScalar l E h c.g n).hom.app
        ((spCoefficientEvaluation l E c.Z DZ.equivalence n).obj N)
  pushDerived : forgetDerived l E c.Z DZ rZ aZ ⋙
      (fixedPushOrd l E c.g).rightDerivedFunctor ≅
    towerPush l E b o c.g DZ DY ⋙ forgetDerived l E Y DY rY aY
  derived_normalized : IsPushScalarNormalized l E b o c.g DZ DY rZ rY aZ aY
    pushOrdinary pushDerived

/-- The normalization of direct-image evaluation on actual K-injective strict towers.
Source: blueprint paragraph (2); Stacks 0A07
(blueprint: lem-sp-complete-compactification-limit-realization). -/
def IsFixedPushEvaluation {Z Y : Scheme.{u}} (p : Z ⟶ Y) (n : ℕ)
    (v : (fixedPushOrd l E p).rightDerivedFunctor ⋙
        coefficientConstantTowerEvaluation l E Y n ≅
      coefficientConstantTowerEvaluation l E Z n ⋙ (pushOrd l E p).rightDerivedFunctor) :
    Prop :=
  ∀ (I : CochainComplex (Fixed l E Z) ℤ) [I.IsKInjective],
    (fixedEvaluation l E Y n).mapDerivedCategory.map
        ((fixedPushOrd l E p).rightDerivedFunctorObjQIso I).hom ≫
      (fixedEvaluation l E Y n).mapDerivedCategoryFactors.hom.app
        (((fixedPushOrd l E p).mapHomologicalComplex (.up ℤ)).obj I) =
    v.hom.app (DerivedCategory.Q.obj I) ≫
      (pushOrd l E p).rightDerivedFunctor.map
        ((fixedEvaluation l E Z n).mapDerivedCategoryFactors.hom.app I) ≫
      ((pushOrd l E p).rightDerivedFunctorObjQIso
        (((fixedEvaluation l E Z n).mapHomologicalComplex (.up ℤ)).obj I)).hom

/-- The input subcategory is defined only by the specified completeness unit and D+.
Source: blueprint paragraph (2), hypotheses on M
(blueprint: lem-sp-complete-compactification-limit-realization). -/
def IsInput (T : Scheme.{u}) (D : SpCoefficientTowersAbelian l E T)
    (r : SpReductionTower l E T D) (a : LimitPresentation l E T D r)
    (M : Integral l E T) : Prop := by
  letI := D.hasDerived
  exact IsIso ((completionUnit l E T D r a).app M) ∧
    ∃ k : ℤ, ((reduction l E T D r).obj M).IsGE k

/-- The actual augmentation to positive quotient n+1, before changing finite coordinates.
Its composite with the exact forgetting/evaluation isomorphism is the scalar adjunction
unit by LimitPresentation.unit_projection.
Source: blueprint paragraph (2), actual quotient augmentation
(blueprint: lem-sp-complete-compactification-limit-realization). -/
def quotientAugmentation (T : Scheme.{u}) (D : SpCoefficientTowersAbelian l E T)
    (r : SpReductionTower l E T D) (a : LimitPresentation l E T D r)
    (M : Integral l E T) (n : ℕ) :=
  (completionUnit l E T D r a).app M ≫
    (coefficientConstantTowerProjection l E T n).app
      ((forgetDerived l E T D r a).obj ((reduction l E T D r).obj M))

/-- The finite projection of the canonical strict scalar composite, before the
canonical finite-coordinate identification. The first two factors are the inverse
exact-open and derived-pushforward evaluation comparisons; the last is evaluation
of the strict scalar comparison itself, hence retains all semilinear transitions.
Source: blueprint paragraph (2), b_(n,N)
(blueprint: lem-sp-complete-compactification-limit-realization). -/
def finiteScalarComposite (b : SpTowerShriek.Base l E)
    (o : SpTowerShriek.Operations l E b)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (DX : SpCoefficientTowersAbelian l E X) (DZ : SpCoefficientTowersAbelian l E c.Z)
    (DY : SpCoefficientTowersAbelian l E Y)
    (rX : SpReductionTower l E X DX) (rZ : SpReductionTower l E c.Z DZ)
    (rY : SpReductionTower l E Y DY)
    (aX : LimitPresentation l E X DX rX) (aZ : LimitPresentation l E c.Z DZ rZ)
    (aY : LimitPresentation l E Y DY rY)
    (e₀ : forgetting l E X DX ⋙ fixedOpenOrd l E c.i ≅
      ordinaryTowerOpen l E b o c.i ⋙ forgetting l E c.Z DZ)
    (d : forgetDerived l E c.Z DZ rZ aZ ⋙ (fixedPushOrd l E c.g).rightDerivedFunctor ≅
      towerPush l E b o c.g DZ DY ⋙ forgetDerived l E Y DY rY aY)
    (n : ℕ)
    (v : (fixedPushOrd l E c.g).rightDerivedFunctor ⋙
        coefficientConstantTowerEvaluation l E Y n ≅
      coefficientConstantTowerEvaluation l E c.Z n ⋙ (pushOrd l E c.g).rightDerivedFunctor)
    (N : spDerivedCoefficientTowers l E X DX) :=
  (pushOrd l E c.g).rightDerivedFunctor.map
      ((fixedOpenEvaluation l E c.i n).inv.app ((forgetDerived l E X DX rX aX).obj N)) ≫
    v.inv.app (((fixedOpenOrd l E c.i).mapDerivedCategory).obj
      ((forgetDerived l E X DX rX aX).obj N)) ≫
    (coefficientConstantTowerEvaluation l E Y n).map
      ((scalarComposite l E b o c DX DZ DY rX rZ rY aX aZ aY e₀ d).hom.app N)

attribute [local irreducible] scalarComposite pushLimit openLimit comparison
  finiteScalarComposite quotientAugmentation

/-- Complete compactification images are canonically realized by strict coefficient limits.

Proof. Restrict the full coefficient diagram to completed scalars, using the actual
coefficient projections. Exact evaluation identifies the derived reduction/limit
adjunction unit with each scalar adjunction unit; the tensor-generator and universal
counit conditions fix these identifications. The open scalar comparison is the identity
on each extension summand. It commutes with every semilinear transition, and exactness
localizes it. The diagram-ring direct-image comparison gives the push scalar comparison;
its two composite units fix the derived comparison on arbitrary complexes. Quasi-compact
open extension is exact and preserves products (Stacks 09BP). Exact countable products
on the pro-etale site therefore identify its constant-diagram mate with the product
comparison on the signed Roos fiber. This mate is invertible and preserves projections.
The direct-image/limit mate is invertible by derived adjunction composition (Stacks 0A07,
0D6E); its K-injective evaluation preserves the specified projections. Compose, in order,
the compactification image of the completion unit, the open mate, the push mate and the
limit of the strict scalar comparison. On the stated inputs the first factor is invertible
by completeness; the other factors are the just constructed isomorphisms. This is exactly
`comparison`, a natural transformation already defined on the whole unbounded category.
Its naturality and the two projection identities give the final augmentation equation.
Every scalar factor is a morphism of strict diagrams, so all quotient transitions commute;
no argument detects morphism equality by evaluations and no triangulated cone is chosen.
Source: current blueprint, sec-smooth-purity/sk-prop-sp-integral-adjunction,
sk-prop-sp-integral-adjunction-direct-image.proof.md, paragraph (2)
(blueprint: lem-sp-complete-compactification-limit-realization). -/
theorem complete_compactification_limit_realization
    (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (D : ∀ T : Scheme.{u}, SpCoefficientTowersAbelian l E T)
    (r : ∀ T : Scheme.{u}, SpReductionTower l E T (D T)) :
    ∃ (h : ScalarSquares l E)
      (a : ∀ T : Scheme.{u}, LimitPresentation l E T (D T) (r T))
      (v : ∀ T : Scheme.{u}, Evaluation l E b T (D T)),
    ∀ (X Y : Scheme.{u}) (f : X ⟶ Y) (c : Compactification f)
      (_ : CompactSpace X) (_ : QuasiSeparatedSpace X)
      (_ : CompactSpace c.Z) (_ : QuasiSeparatedSpace c.Z)
      (_ : CompactSpace Y) (_ : QuasiSeparatedSpace Y)
      (_ : ∀ x : X, IsUnit (l : X.residueField x))
      (_ : ∀ x : c.Z, IsUnit (l : c.Z.residueField x))
      (_ : ∀ x : Y, IsUnit (l : Y.residueField x)) (_ : QuasiCompact c.i),
    ∃ s : ScalarComparison l E b o h c (D X) (D c.Z) (D Y)
        (r X) (r c.Z) (r Y) (a X) (a c.Z) (a Y) (v X) (v c.Z) (v Y),
    ∃ w : ∀ n : ℕ, (fixedPushOrd l E c.g).rightDerivedFunctor ⋙
        coefficientConstantTowerEvaluation l E Y n ≅
      coefficientConstantTowerEvaluation l E c.Z n ⋙ (pushOrd l E c.g).rightDerivedFunctor,
    (∀ n : ℕ, IsFixedPushEvaluation l E c.g n (w n)) ∧
    (∀ (K : DerivedCategory (Fixed l E X)) (n : ℕ),
      (openLimit l E c.i).app K ≫
          (coefficientConstantTowerProjection l E c.Z n).app
            (((fixedOpenOrd l E c.i).mapDerivedCategory).obj K) =
        (openOrd l E c.i).mapDerivedCategory.map
          ((coefficientConstantTowerProjection l E X n).app K) ≫
            (fixedOpenEvaluation l E c.i n).inv.app K) ∧
    (∀ (K : DerivedCategory (Fixed l E c.Z)) (n : ℕ),
      (pushLimit l E c.g).hom.app K ≫
          (coefficientConstantTowerProjection l E Y n).app
            (((fixedPushOrd l E c.g).rightDerivedFunctor).obj K) =
        (pushOrd l E c.g).rightDerivedFunctor.map
          ((coefficientConstantTowerProjection l E c.Z n).app K) ≫ (w n).inv.app K) ∧
    ∀ (M : Integral l E X), IsInput l E X (D X) (r X) (a X) M →
      ∃ α : (image l E c).obj M ≅
        (totalLimit l E Y (D Y) (r Y) (a Y)).obj
          ((towerPush l E b o c.g (D c.Z) (D Y)).obj
            ((towerOpen l E b o c.i (D X) (D c.Z)).obj
              ((reduction l E X (D X) (r X)).obj M))),
      α.hom = (comparison l E b o c (D X) (D c.Z) (D Y) (r X) (r c.Z) (r Y)
        (a X) (a c.Z) (a Y) s.openOrdinary s.pushDerived).app M ∧
      ∀ n : ℕ, α.hom ≫
        (coefficientConstantTowerProjection l E Y n).app
          ((forgetDerived l E Y (D Y) (r Y) (a Y)).obj
            ((towerPush l E b o c.g (D c.Z) (D Y)).obj
              ((towerOpen l E b o c.i (D X) (D c.Z)).obj
                ((reduction l E X (D X) (r X)).obj M)))) =
        (image l E c).map (quotientAugmentation l E X (D X) (r X) (a X) M n) ≫
          finiteScalarComposite l E b o c (D X) (D c.Z) (D Y) (r X) (r c.Z) (r Y)
            (a X) (a c.Z) (a Y) s.openOrdinary s.pushDerived n (w n)
              ((reduction l E X (D X) (r X)).obj M) := by
  obtain ⟨h, a, v, hs⟩ := compactificationScalarData l E b o D r
  refine ⟨h, a, v, ?_⟩
  intro X Y f c hX hXs hZ hZs hY hYs hlX hlZ hlY hj
  obtain ⟨e, d₀, d, he, hd, hn⟩ :=
    hs X Y f c hX hXs hZ hZs hY hYs hlX hlZ hlY hj
  let s : ScalarComparison l E b o h c (D X) (D c.Z) (D Y)
      (r X) (r c.Z) (r Y) (a X) (a c.Z) (a Y) (v X) (v c.Z) (v Y) :=
    ⟨e, he, d₀, hd, d, hn⟩
  obtain ⟨w, hw, hp⟩ := compactificationPushLimit l E c.g
  obtain ⟨ho, heval⟩ := compactificationOpenLimit l E c.i
  refine ⟨s, w, hw, heval, hp, ?_⟩
  intro M hM
  have hη : IsIso ((completionUnit l E X (D X) (r X) (a X)).app M) := hM.1
  have : IsIso (openLimit l E c.i) := ho
  let N := (reduction l E X (D X) (r X)).obj M
  let K := (forgetDerived l E X (D X) (r X) (a X)).obj N
  let F := (pushOrd l E c.g).rightDerivedFunctor
  let Q := scalarComposite l E b o c (D X) (D c.Z) (D Y)
    (r X) (r c.Z) (r Y) (a X) (a c.Z) (a Y) e d
  let q := Q.hom.app N
  let m := (comparison l E b o c (D X) (D c.Z) (D Y)
    (r X) (r c.Z) (r Y) (a X) (a c.Z) (a Y) e d).app M
  have hm : m =
      (image l E c).map ((completionUnit l E X (D X) (r X) (a X)).app M) ≫
        F.map ((openLimit l E c.i).app K) ≫
        (pushLimit l E c.g).hom.app (((fixedOpenOrd l E c.i).mapDerivedCategory).obj K) ≫
        (coefficientConstantTowerLimit l E Y).map q := by
    simp only [m, comparison, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
      Category.id_comp, Category.comp_id]
    rfl
  have : IsIso q := by dsimp only [q]; infer_instance
  have : IsIso m := by
    rw [hm]
    infer_instance
  refine ⟨asIso m, rfl, ?_⟩
  intro n
  change m ≫ (coefficientConstantTowerProjection l E Y n).app _ = _
  rw [hm]
  simp only [Category.assoc]
  erw [(coefficientConstantTowerProjection l E Y n).naturality q]
  erw [reassoc_of% (hp _ n)]
  have heF := congrArg F.map (heval K n)
  simp only [Functor.map_comp] at heF
  erw [reassoc_of% heF]
  simp only [quotientAugmentation, finiteScalarComposite, Functor.comp_map,
    Functor.map_comp, Category.assoc]
  dsimp only [F, K, N, q, Q, s]

end AlgebraicGeometry.ProEtale.CompleteCompactificationLimit
