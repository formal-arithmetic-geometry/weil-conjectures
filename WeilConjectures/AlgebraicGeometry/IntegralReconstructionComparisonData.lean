/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralDirectImageTower
public import WeilConjectures.AlgebraicGeometry.SmoothPurityTowerGluing
public import WeilConjectures.AlgebraicGeometry.CompleteCompactificationLimitRealization
public import WeilConjectures.AlgebraicGeometry.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralCoefficientGerm
public import WeilConjectures.AlgebraicGeometry.SmoothPurityTowerGamma

/-! # Integral reconstruction comparison data

Source: latest blueprint, integral-adjunction-bijection proof,
Normalization and Bijections (blueprint: def-sp-integral-reconstruction-comparison-data).

All comparison arrows are in ordinary derived categories of strict coefficient towers.
The compactification comparison retains its actual total-limit and scalar normalization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpIntegralAdjunction
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The specified total derived inverse limit after restriction of finite actions.
Source: Normalization (blueprint: def-sp-integral-reconstruction-comparison-data). -/
def limit (T : Scheme.{u}) (D : SpCoefficientTowersAbelian l E T)
    (R : SpReductionTower l E T D) (N : SpNormalizedEquivalence l E T D R) :=
  letI := N.forgetAdditive
  letI := N.forgetLimits
  letI := N.forgetColimits
  spCompletedTotalLimit l E T D

/-- Simultaneous derived reduction on the full integral constructible category.
Source: Bijections (blueprint: def-sp-integral-reconstruction-comparison-data). -/
def reduction (T : Scheme.{u}) (D : SpCoefficientTowersAbelian l E T)
    (R : SpReductionTower l E T D) :=
  (sfIntegralConstructible l E T).ι ⋙ spCompletedReduction l E T D R

/-- Regard reduction as a constructible tower, retaining its actual object and maps.
The membership proof is supplied in the conclusion, not assumed of the geometry.
Source: Normalization (blueprint: def-sp-integral-reconstruction-comparison-data). -/
def reduce (T : Scheme.{u}) (D : SpCoefficientTowersAbelian l E T)
    (R : SpReductionTower l E T D)
    (h : ∀ K : sfIntegralConstructibleCategory l E T,
      spConstructibleTorTowers l E T D ((reduction l E T D R).obj K)) :=
  ObjectProperty.lift _ (reduction l E T D R) h

/-- Compact support is the separately derived completed-ring compactification composite.
Source: Bijections, first term (blueprint: def-sp-integral-reconstruction-comparison-data). -/
def support {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (h : ∀ M : sfIntegralConstructibleCategory l E X,
      sfIntegralConstructible l E Y ((CompleteCompactificationLimit.image l E c).obj M.obj)) :=
  ObjectProperty.lift _
    ((sfIntegralConstructible l E X).ι ⋙ CompleteCompactificationLimit.image l E c) h

/-- The actual ambient functor H=L_X G_bullet red_Y. Its target is not chosen by existence.
Source: Normalization (blueprint: def-sp-integral-reconstruction-comparison-data). -/
def exceptional {X Y : Scheme.{u}} (b : SpTowerShriek.Base l E)
    (q : SpTowerCalculus.Coordinates l E b)
    (RX : SpReductionTower l E X (q.abelian X))
    (NX : SpNormalizedEquivalence l E X (q.abelian X) RX)
    (RY : SpReductionTower l E Y (q.abelian Y))
    (hY : ∀ K : sfIntegralConstructibleCategory l E Y,
      spConstructibleTorTowers l E Y (q.abelian Y)
        ((reduction l E Y (q.abelian Y) RY).obj K))
    (G : SpTowerCalculus.C l E b q Y ⥤ SpTowerCalculus.C l E b q X) :=
  reduce l E Y (q.abelian Y) RY hY ⋙ G ⋙ SpTowerCalculus.inclusion l E b q X ⋙
    limit l E X (q.abelian X) RX NX

/-- Restrict the very same derived-limit object to the full integral subcategory.
Source: Normalization (blueprint: def-sp-integral-reconstruction-comparison-data). -/
def right {X Y : Scheme.{u}} (b : SpTowerShriek.Base l E)
    (q : SpTowerCalculus.Coordinates l E b)
    (RX : SpReductionTower l E X (q.abelian X))
    (NX : SpNormalizedEquivalence l E X (q.abelian X) RX)
    (RY : SpReductionTower l E Y (q.abelian Y))
    (hY : ∀ K : sfIntegralConstructibleCategory l E Y,
      spConstructibleTorTowers l E Y (q.abelian Y)
        ((reduction l E Y (q.abelian Y) RY).obj K))
    (G : SpTowerCalculus.C l E b q Y ⥤ SpTowerCalculus.C l E b q X)
    (hH : ∀ K : sfIntegralConstructibleCategory l E Y,
      sfIntegralConstructible l E X ((exceptional l E b q RX NX RY hY G).obj K)) :=
  ObjectProperty.lift _ (exceptional l E b q RX NX RY hY G) hH

/-- Canonical conjugation of ordinary strict-system operations by the section equivalence.
Its sole nontrivial factor is that equivalence's counit, so every section is fixed.
Source: Bijections, compactification comparison
(blueprint: def-sp-integral-reconstruction-comparison-data). -/
def ordinaryConjugation (b : SpTowerShriek.Base l E) {V W : Scheme.{u}}
    (F : SpTowerShriek.S l E V ⥤ SpTowerShriek.S l E W) :
    ((b.realization V).functor ⋙ F ⋙ (b.realization W).inverse) ⋙
        (b.realization W).functor ≅ (b.realization V).functor ⋙ F :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft F (b.realization W).counitIso ≪≫ Functor.rightUnitor F)

/-- The canonical whole-tower compactification comparison between the two published
coordinate presentations. Exact localization treats open extension; the normalized
right-derived composition comparisons treat proper image. No evaluations define it.
Source: Bijections, first comparison
(blueprint: def-sp-integral-reconstruction-comparison-data). -/
def towerWord {X Y : Scheme.{u}} {f : X ⟶ Y} (b : SpTowerShriek.Base l E)
    (o : SpTowerShriek.Operations l E b) (q : SpTowerCalculus.Coordinates l E b)
    (c : Compactification f) :
    CompleteCompactificationLimit.towerOpen l E b o c.i (q.abelian X) (q.abelian c.Z) ⋙
        CompleteCompactificationLimit.towerPush l E b o c.g (q.abelian c.Z) (q.abelian Y) ≅
      SpTowerCalculus.F l E b o q c := by
  letI := (q.abelian X).hasDerived
  letI := (q.abelian c.Z).hasDerived
  letI := (q.abelian Y).hasDerived
  letI := (q.abelian c.Z).grothendieck
  letI := b.realizationAdditive X
  letI := b.realizationAdditive c.Z
  letI := b.realizationAdditive Y
  letI := Functor.additive_of_preserves_binary_products (b.realization X).inverse
  letI := Functor.additive_of_preserves_binary_products (b.realization c.Z).inverse
  letI := Functor.additive_of_preserves_binary_products (b.realization Y).inverse
  let pushComparison :
      (CompleteCompactificationLimit.ordinaryTowerPush l E b o c.g).rightDerivedFunctor ⋙
          (b.realization Y).functor.mapDerivedCategory ≅
        (b.realization c.Z).functor.mapDerivedCategory ⋙
          (o.geometry c.g).push.rightDerivedFunctor :=
    (Functor.rightDerivedFunctorCompMapDerivedCategoryIso _ _).symm ≪≫
      Functor.rightDerivedFunctorNatIso
        (ordinaryConjugation l E b (o.geometry c.g).push) ≪≫
      Functor.rightDerivedFunctorCompIso _ _ ≪≫
      Functor.isoWhiskerRight
        (b.realization c.Z).functor.rightDerivedFunctorIsoMapDerivedCategory _
  let openComparison :
      (CompleteCompactificationLimit.ordinaryTowerOpen l E b o c.i).mapDerivedCategory ⋙
          (b.realization c.Z).functor.mapDerivedCategory ≅
        (b.realization X).functor.mapDerivedCategory ⋙
          (o.openOp c.i).extension.mapDerivedCategory :=
    (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
      Functor.mapDerivedCategoryNatIso
        (ordinaryConjugation l E b (o.openOp c.i).extension) ≪≫
      Functor.mapDerivedCategoryCompIso _ _
  exact CategoryTheory.Iso.isoCompInverse
    (H := SpTowerCalculus.realization l E b Y (q.abelian Y))
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ pushComparison ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight openComparison _ ≪≫ Functor.associator _ _ _)

/-- Natural whole-tower comparisons, the inverse normalization equivalences,
and the reconstruction identity, all with their actual units and counits.
Source: latest blueprint, Normalization and Bijections
(blueprint: def-sp-integral-reconstruction-comparison-data). -/
structure Reconstruction {X Z Y : Scheme.{u}}
    (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (q : SpTowerCalculus.Coordinates l E b)
    (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y) [IsProper p]
    [QuasiCompact (j ≫ p)] [HasCompactification (j ≫ p)]
    (RX : SpReductionTower l E X (q.abelian X))
    (NX : SpNormalizedEquivalence l E X (q.abelian X) RX)
    (RY : SpReductionTower l E Y (q.abelian Y))
    (NY : SpNormalizedEquivalence l E Y (q.abelian Y) RY)
    (hF : ∀ M : SpTowerCalculus.C l E b q X,
      spConstructibleTorTowers l E Y (q.abelian Y)
        ((SpTowerCalculus.F l E b o q (SpTowerGamma.factorization j p)).obj M.obj))
    (G : SpTowerCalculus.C l E b q Y ⥤ SpTowerCalculus.C l E b q X)
    (a : SpTowerGluing.support l E b o q (SpTowerGamma.factorization j p) hF ⊣ G) where
  [noetherianX : IsNoetherian X]
  [noetherianY : IsNoetherian Y]
  reductionX : ∀ M : sfIntegralConstructibleCategory l E X,
    spConstructibleTorTowers l E X (q.abelian X)
      ((reduction l E X (q.abelian X) RX).obj M)
  reductionY : ∀ K : sfIntegralConstructibleCategory l E Y,
    spConstructibleTorTowers l E Y (q.abelian Y)
      ((reduction l E Y (q.abelian Y) RY).obj K)
  normalized : ∀ K : sfIntegralConstructibleCategory l E Y,
    IsSpNormalizedTower l E X (q.abelian X)
      (G.obj ((reduce l E Y (q.abelian Y) RY reductionY).obj K)).obj
  closed : ∀ K : sfIntegralConstructibleCategory l E Y,
    sfIntegralConstructible l E X ((exceptional l E b q RX NX RY reductionY G).obj K)
  support_closed : ∀ M : sfIntegralConstructibleCategory l E X,
    sfIntegralConstructible l E Y
      ((CompleteCompactificationLimit.image l E (SpTowerGamma.factorization j p)).obj M.obj)
  fullyFaithfulX : (reduce l E X (q.abelian X) RX reductionX).FullyFaithful
  fullyFaithfulY : (reduce l E Y (q.abelian Y) RY reductionY).FullyFaithful
  reductionZ : SpReductionTower l E Z (q.abelian Z)
  scalarSquares : CompleteCompactificationLimit.ScalarSquares l E
  limitX : CompleteCompactificationLimit.LimitPresentation l E X (q.abelian X) RX
  limitZ : CompleteCompactificationLimit.LimitPresentation l E Z (q.abelian Z) reductionZ
  limitY : CompleteCompactificationLimit.LimitPresentation l E Y (q.abelian Y) RY
  evaluationX : CompleteCompactificationLimit.Evaluation l E b X (q.abelian X)
  evaluationZ : CompleteCompactificationLimit.Evaluation l E b Z (q.abelian Z)
  evaluationY : CompleteCompactificationLimit.Evaluation l E b Y (q.abelian Y)
  scalar : CompleteCompactificationLimit.ScalarComparison l E b o scalarSquares
    (SpTowerGamma.factorization j p) (q.abelian X) (q.abelian Z) (q.abelian Y)
    RX reductionZ RY limitX limitZ limitY evaluationX evaluationZ evaluationY
  imageComparison : ∀ M : sfIntegralConstructibleCategory l E X,
    (CompleteCompactificationLimit.image l E (SpTowerGamma.factorization j p)).obj M.obj ≅
      (limit l E Y (q.abelian Y) RY NY).obj
        ((SpTowerCalculus.F l E b o q (SpTowerGamma.factorization j p)).obj
          ((reduction l E X (q.abelian X) RX).obj M))
  image_normalization : ∀ M : sfIntegralConstructibleCategory l E X,
    (imageComparison M).hom =
      (CompleteCompactificationLimit.comparison l E b o (SpTowerGamma.factorization j p)
        (q.abelian X) (q.abelian Z) (q.abelian Y) RX reductionZ RY
        limitX limitZ limitY scalar.openOrdinary scalar.pushDerived).app M.obj ≫
      (limit l E Y (q.abelian Y) RY NY).map
        ((towerWord l E b o q (SpTowerGamma.factorization j p)).hom.app
          ((reduction l E X (q.abelian X) RX).obj M))
  leftComparison : support l E (SpTowerGamma.factorization j p) support_closed ⋙
      reduce l E Y (q.abelian Y) RY reductionY ≅
    reduce l E X (q.abelian X) RX reductionX ⋙
      SpTowerGluing.support l E b o q (SpTowerGamma.factorization j p) hF
  left_normalization : ∀ M : sfIntegralConstructibleCategory l E X,
    (leftComparison.hom.app M).hom =
      (spCompletedReduction l E Y (q.abelian Y) RY).map (imageComparison M).hom ≫
        NY.adjunction.counit.app
          ((SpTowerCalculus.F l E b o q (SpTowerGamma.factorization j p)).obj
            ((reduction l E X (q.abelian X) RX).obj M))
  rightComparison : right l E b q RX NX RY reductionY G closed ⋙
      reduce l E X (q.abelian X) RX reductionX ≅
    reduce l E Y (q.abelian Y) RY reductionY ⋙ G
  right_normalization : ∀ K : sfIntegralConstructibleCategory l E Y,
    (rightComparison.hom.app K).hom = NX.adjunction.counit.app
      (G.obj ((reduce l E Y (q.abelian Y) RY reductionY).obj K)).obj
  equivalenceX : sfIntegralConstructibleCategory l E X ≌
    spNormalizedConstructibleTorTowerCategory l E X (q.abelian X)
  equivalenceY : sfIntegralConstructibleCategory l E Y ≌
    spNormalizedConstructibleTorTowerCategory l E Y (q.abelian Y)
  equivalenceX_reduction : equivalenceX.functor ⋙
      (spNormalizedConstructibleTorTowers l E X (q.abelian X)).ι =
    reduction l E X (q.abelian X) RX
  equivalenceY_reduction : equivalenceY.functor ⋙
      (spNormalizedConstructibleTorTowers l E Y (q.abelian Y)).ι =
    reduction l E Y (q.abelian Y) RY
  equivalenceX_limit : equivalenceX.inverse ⋙ (sfIntegralConstructible l E X).ι =
    (spNormalizedConstructibleTorTowers l E X (q.abelian X)).ι ⋙
      limit l E X (q.abelian X) RX NX
  equivalenceY_limit : equivalenceY.inverse ⋙ (sfIntegralConstructible l E Y).ι =
    (spNormalizedConstructibleTorTowers l E Y (q.abelian Y)).ι ⋙
      limit l E Y (q.abelian Y) RY NY
  support_normalized : ∀ M : SpTowerCalculus.C l E b q X,
    IsSpNormalizedTower l E X (q.abelian X) M.obj →
      IsSpNormalizedTower l E Y (q.abelian Y)
        ((SpTowerGluing.support l E b o q (SpTowerGamma.factorization j p) hF).obj M).obj
  exceptional_normalized : ∀ K : SpTowerCalculus.C l E b q Y,
    IsSpNormalizedTower l E Y (q.abelian Y) K.obj →
      IsSpNormalizedTower l E X (q.abelian X) (G.obj K).obj
  reconstructionX : ∀ M : sfIntegralConstructibleCategory l E X,
    M.obj ≅ (limit l E X (q.abelian X) RX NX).obj
      ((reduction l E X (q.abelian X) RX).obj M)
  reconstructionY : ∀ K : sfIntegralConstructibleCategory l E Y,
    K.obj ≅ (limit l E Y (q.abelian Y) RY NY).obj
      ((reduction l E Y (q.abelian Y) RY).obj K)
  reconstructionX_normalization : ∀ M : sfIntegralConstructibleCategory l E X,
    (reconstructionX M).hom = NX.adjunction.unit.app M.obj
  reconstructionY_normalization : ∀ K : sfIntegralConstructibleCategory l E Y,
    (reconstructionY K).hom = NY.adjunction.unit.app K.obj
  reconstructX : ∀ (A B : sfIntegralConstructibleCategory l E X) (z : A ⟶ B),
    z.hom = (reconstructionX A).hom ≫
      (limit l E X (q.abelian X) RX NX).map
        ((reduction l E X (q.abelian X) RX).map z) ≫ (reconstructionX B).inv
  reconstructY : ∀ (A B : sfIntegralConstructibleCategory l E Y) (z : A ⟶ B),
    z.hom = (reconstructionY A).hom ≫
      (limit l E Y (q.abelian Y) RY NY).map
        ((reduction l E Y (q.abelian Y) RY).map z) ≫ (reconstructionY B).inv

/-- The reconstruction package with its geometric instances derived from the standing
finite-type setting and the specified compactification, rather than assumed separately.
Source: latest blueprint, integral adjunction
(blueprint: def-sp-integral-reconstruction-comparison-data). -/
def reconstructionResult
    (D : FiniteFieldDatum.{u})
    {X Z Y : Scheme.{u}} [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y) [IsProper p]
    [(j ≫ p).IsOver (Spec (.of D.k))]
    (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (q : SpTowerCalculus.Coordinates l E b)
    (RX : SpReductionTower l E X (q.abelian X))
    (NX : SpNormalizedEquivalence l E X (q.abelian X) RX)
    (RY : SpReductionTower l E Y (q.abelian Y))
    (NY : SpNormalizedEquivalence l E Y (q.abelian Y) RY)
    (hF : ∀ M : SpTowerCalculus.C l E b q X,
      spConstructibleTorTowers l E Y (q.abelian Y)
        ((SpTowerCalculus.F l E b o q (SpTowerGamma.factorization j p)).obj M.obj))
    (G : SpTowerCalculus.C l E b q Y ⥤ SpTowerCalculus.C l E b q X)
    (a : SpTowerGluing.support l E b o q (SpTowerGamma.factorization j p) hF ⊣ G) : Type _ :=
  letI : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of D.k))
  letI : QuasiSeparatedSpace Y :=
    quasiSeparatedSpace_of_quasiSeparated (Y ↘ Spec (.of D.k))
  letI : QuasiCompact (j ≫ p) := inferInstance
  letI : HasCompactification (j ≫ p) := (SpTowerGamma.factorization j p).hasCompactification
  Reconstruction l E b o q j p RX NX RY NY hF G a

end AlgebraicGeometry.ProEtale.SpIntegralAdjunction
