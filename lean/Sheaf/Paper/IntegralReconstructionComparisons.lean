module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.Paper.SmoothPurityCoefficientTowers
public import Sheaf.Paper.SmoothPurityNormalizedTowers
public import Sheaf.Paper.SmoothPurityNormalizedEquivalence
public import Sheaf.Paper.SmoothPurityTowerGluing
public import Sheaf.Paper.CompleteCompactificationLimitSupport
import Sheaf.Paper.CompleteCompactificationLimitRealization
public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Sheaf.Paper.SfIntegralConstructibleTriangulated
import Sheaf.Paper.SfDerivedCompleteLegacyComparison
import Sheaf.Paper.SmoothPurityTowerGamma
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-!
# Natural integral reconstruction comparisons

Source: current blueprint, sec-smooth-purity/sk-prop-sp-integral-adjunction,
Normalization and Bijections in sk-prop-sp-integral-adjunction-bijection.proof.md
(blueprint: lem-sp-integral-reconstruction-comparisons).

The original strict-tower category is retained. Section-model coordinate changes below
are localizations of the given ordinary equivalences and their units and counits.
The comparison b is reduction of the canonical compactification-limit comparison,
followed by the actual reconstruction counit, as a map of entire strict towers.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.IntegralReconstructionComparisons
open CompleteCompactificationLimit

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The exact-open localization of the specified ordinary section-coordinate word.
Source: blueprint, compactification comparison
(blueprint: lem-sp-integral-reconstruction-comparisons). -/
def openCoordinates (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
    (DX : SpCoefficientTowersAbelian l E X) (DZ : SpCoefficientTowersAbelian l E Z) :
    towerOpen l E b o j DX DZ ≅
      (SpTowerCalculus.realization l E b X DX).functor ⋙
        SpTowerShriek.openD l E b (o.openOp j) ⋙
          (SpTowerCalculus.realization l E b Z DZ).inverse := by
  letI := DX.hasDerived
  letI := DZ.hasDerived
  letI := b.realizationAdditive X
  letI := Functor.additive_of_preserves_binary_products (b.realization Z).inverse
  exact Functor.mapDerivedCategoryCompIso (b.realization X).functor
      ((o.openOp j).extension ⋙ (b.realization Z).inverse) ≪≫
    Functor.isoWhiskerLeft _
      (Functor.mapDerivedCategoryCompIso (o.openOp j).extension (b.realization Z).inverse)

/-- The direct-image coordinate word, using uniqueness of right derived functors.
Both outer equivalences are exact; the first preserves K-injectives.
Source: blueprint, compactification comparison
(blueprint: lem-sp-integral-reconstruction-comparisons). -/
def pushCoordinates (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    {Z Y : Scheme.{u}} (p : Z ⟶ Y)
    (DZ : SpCoefficientTowersAbelian l E Z) (DY : SpCoefficientTowersAbelian l E Y) :
    towerPush l E b o p DZ DY ≅
      (SpTowerCalculus.realization l E b Z DZ).functor ⋙
        SpTowerShriek.push l E b (o.geometry p) ⋙
          (SpTowerCalculus.realization l E b Y DY).inverse := by
  letI := DZ.hasDerived
  letI := DY.hasDerived
  letI := DZ.grothendieck
  letI := b.realizationAdditive Z
  letI := Functor.additive_of_preserves_binary_products (b.realization Y).inverse
  exact Functor.mapDerivedCategoryCompRightDerivedFunctorIso (b.realization Z).functor
      ((o.geometry p).push ⋙ (b.realization Y).inverse) ≪≫
    Functor.isoWhiskerLeft _
      (Functor.rightDerivedFunctorCompMapDerivedCategoryIso
        (o.geometry p).push (b.realization Y).inverse)

/-- Cancel the intermediate section equivalence by its actual counit. This compares
entire strict derived-tower functors, without selecting maps from finite evaluations.
Source: blueprint, compactification comparison
(blueprint: lem-sp-integral-reconstruction-comparisons). -/
def supportCoordinates (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (D : ∀ T : Scheme.{u}, SpCoefficientTowersAbelian l E T)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    towerOpen l E b o c.i (D X) (D c.Z) ⋙ towerPush l E b o c.g (D c.Z) (D Y) ≅
      SpTowerCalculus.compactSupport l E b o D c :=
  Functor.isoWhiskerRight (openCoordinates l E b o c.i (D X) (D c.Z)) _ ≪≫
    Functor.isoWhiskerLeft _ (pushCoordinates l E b o c.g (D c.Z) (D Y)) ≪≫
    Functor.isoWhiskerLeft
      ((SpTowerCalculus.realization l E b X (D X)).functor ⋙
        SpTowerShriek.openD l E b (o.openOp c.i))
      (Functor.isoWhiskerRight (SpTowerCalculus.realization l E b c.Z (D c.Z)).counitIso
        (SpTowerShriek.push l E b (o.geometry c.g) ⋙
          (SpTowerCalculus.realization l E b Y (D Y)).inverse))

/-- Reconstruction data on the two full subcategories. The functors are the recorded
reduction and total limit, and all inverses below invert their actual unit/counit.
Source: blueprint, Normalization
(blueprint: lem-sp-integral-reconstruction-comparisons). -/
structure Reconstruction (T : Scheme.{u}) (D : SpCoefficientTowersAbelian l E T)
    (r : SpReductionTower l E T D) where
  presentation : LimitPresentation l E T D r
  reduction_mem : ∀ M : sfIntegralConstructibleCategory l E T,
    spNormalizedConstructibleTorTowers l E T D ((reduction l E T D r).obj M.obj)
  limit_mem : ∀ N : spNormalizedConstructibleTorTowerCategory l E T D,
    sfIntegralConstructible l E T ((totalLimit l E T D r presentation).obj N.obj)
  unit_iso : ∀ M : sfIntegralConstructibleCategory l E T,
    IsIso (presentation.adjunction.unit.app M.obj)
  counit_iso : ∀ N : spNormalizedConstructibleTorTowerCategory l E T D,
    IsIso (presentation.adjunction.counit.app N.obj)

/-- Restriction of the actual reduction, retaining every ambient morphism.
Source: blueprint, r_T (blueprint: lem-sp-integral-reconstruction-comparisons). -/
def red (T : Scheme.{u}) (D : SpCoefficientTowersAbelian l E T)
    (r : SpReductionTower l E T D) (a : Reconstruction l E T D r) :=
  (spNormalizedConstructibleTorTowers l E T D).lift
    ((sfIntegralConstructible l E T).ι ⋙ reduction l E T D r) a.reduction_mem

/-- Restriction of total derived limit after scalar forgetting.
Source: blueprint, L_T (blueprint: lem-sp-integral-reconstruction-comparisons). -/
def lim (T : Scheme.{u}) (D : SpCoefficientTowersAbelian l E T)
    (r : SpReductionTower l E T D) (a : Reconstruction l E T D r) :=
  (sfIntegralConstructible l E T).lift
    ((spNormalizedConstructibleTorTowers l E T D).ι ⋙
      totalLimit l E T D r a.presentation) a.limit_mem

/-- The actual reconstruction unit as an isomorphism in the full integral category.
Source: blueprint, u_A (blueprint: lem-sp-integral-reconstruction-comparisons). -/
def unit (T : Scheme.{u}) (D : SpCoefficientTowersAbelian l E T)
    (r : SpReductionTower l E T D) (a : Reconstruction l E T D r)
    (M : sfIntegralConstructibleCategory l E T) :
    M ≅ (lim l E T D r a).obj ((red l E T D r a).obj M) :=
  ObjectProperty.isoMk _
    (@asIso _ _ _ _ (a.presentation.adjunction.unit.app M.obj) (a.unit_iso M))

/-- The normalized full subcategory inside the ambient uniformly constructible category.
Source: blueprint, restriction of the tower adjunction
(blueprint: lem-sp-integral-reconstruction-comparisons). -/
def normalizedInclusion (T : Scheme.{u}) (D : SpCoefficientTowersAbelian l E T) :
    spNormalizedConstructibleTorTowerCategory l E T D ⥤ spConstructibleTorTowerCategory l E T D :=
  ObjectProperty.ιOfLE (fun _ h ↦ h.1)

/-- Restrict the specified left tower functor using its normalization preservation.
Source: blueprint, F_bullet on N_X (blueprint: lem-sp-integral-reconstruction-comparisons). -/
def towerLeft {X Y : Scheme.{u}} (DX : SpCoefficientTowersAbelian l E X)
    (DY : SpCoefficientTowersAbelian l E Y)
    (F : spConstructibleTorTowerCategory l E X DX ⥤ spConstructibleTorTowerCategory l E Y DY)
    (hF : ∀ N : spNormalizedConstructibleTorTowerCategory l E X DX,
      IsSpNormalizedTower l E Y DY (F.obj ((normalizedInclusion l E X DX).obj N)).obj) :=
  (spNormalizedConstructibleTorTowers l E Y DY).lift
    (normalizedInclusion l E X DX ⋙ F ⋙ (spConstructibleTorTowers l E Y DY).ι)
    (fun N ↦ ⟨(F.obj ((normalizedInclusion l E X DX).obj N)).property, hF N⟩)

/-- Restrict the specified right tower functor using its normalization preservation.
Source: blueprint, G_bullet on N_Y (blueprint: lem-sp-integral-reconstruction-comparisons). -/
def towerRight {X Y : Scheme.{u}} (DX : SpCoefficientTowersAbelian l E X)
    (DY : SpCoefficientTowersAbelian l E Y)
    (G : spConstructibleTorTowerCategory l E Y DY ⥤ spConstructibleTorTowerCategory l E X DX)
    (hG : ∀ N : spNormalizedConstructibleTorTowerCategory l E Y DY,
      IsSpNormalizedTower l E X DX (G.obj ((normalizedInclusion l E Y DY).obj N)).obj) :=
  (spNormalizedConstructibleTorTowers l E X DX).lift
    (normalizedInclusion l E Y DY ⋙ G ⋙ (spConstructibleTorTowers l E X DX).ι)
    (fun N ↦ ⟨(G.obj ((normalizedInclusion l E Y DY).obj N)).property, hG N⟩)

/-- The exceptional integral functor is the specified composite L_X G_bullet r_Y.
Source: blueprint, H(K) (blueprint: lem-sp-integral-reconstruction-comparisons). -/
def exceptional {X Y : Scheme.{u}} (DX : SpCoefficientTowersAbelian l E X)
    (DY : SpCoefficientTowersAbelian l E Y)
    (rX : SpReductionTower l E X DX) (rY : SpReductionTower l E Y DY)
    (aX : Reconstruction l E X DX rX) (aY : Reconstruction l E Y DY rY)
    (G : spNormalizedConstructibleTorTowerCategory l E Y DY ⥤
      spNormalizedConstructibleTorTowerCategory l E X DX) :=
  red l E Y DY rY aY ⋙ G ⋙ lim l E X DX rX aX

/-- Restrict the separately derived proper/open integral functor, without changing maps.
Source: blueprint, F = R bar-f_* j_!
(blueprint: lem-sp-integral-reconstruction-comparisons). -/
def integralLeft {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (hF : ∀ M : sfIntegralConstructibleCategory l E X,
      sfIntegralConstructible l E Y ((image l E c).obj M.obj)) :=
  (sfIntegralConstructible l E Y).lift
    ((sfIntegralConstructible l E X).ι ⋙ image l E c) hF

/-- The canonical compactification-limit word, followed by the fixed coordinate
comparison. All factors are actual natural transformations of strict-tower functors.
Source: blueprint, alpha_M in Bijections
(blueprint: lem-sp-integral-reconstruction-comparisons). -/
def realization (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (D : ∀ T : Scheme.{u}, SpCoefficientTowersAbelian l E T)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (rX : SpReductionTower l E X (D X)) (rZ : SpReductionTower l E c.Z (D c.Z))
    (rY : SpReductionTower l E Y (D Y))
    (aX : LimitPresentation l E X (D X) rX)
    (aZ : LimitPresentation l E c.Z (D c.Z) rZ)
    (aY : LimitPresentation l E Y (D Y) rY)
    (e : forgetting l E X (D X) ⋙ fixedOpenOrd l E c.i ≅
      ordinaryTowerOpen l E b o c.i ⋙ forgetting l E c.Z (D c.Z))
    (d : forgetDerived l E c.Z (D c.Z) rZ aZ ⋙ (fixedPushOrd l E c.g).rightDerivedFunctor ≅
      towerPush l E b o c.g (D c.Z) (D Y) ⋙ forgetDerived l E Y (D Y) rY aY) :
    image l E c ⟶ reduction l E X (D X) rX ⋙
      SpTowerCalculus.compactSupport l E b o D c ⋙ totalLimit l E Y (D Y) rY aY :=
  comparison l E b o c (D X) (D c.Z) (D Y) rX rZ rY aX aZ aY e d ≫
    Functor.whiskerLeft (reduction l E X (D X) rX)
      (Functor.whiskerRight (supportCoordinates l E b o D c).hom
        (totalLimit l E Y (D Y) rY aY))

/-- The conclusions retain the actual ambient arrows: the reconstruction equivalence,
the restricted specified adjunction, and natural b,c with their canonical formulas.
Source: blueprint, Normalization and Bijections
(blueprint: lem-sp-integral-reconstruction-comparisons). -/
structure Comparisons (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (q : SpTowerCalculus.Coordinates l E b)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (rX : SpReductionTower l E X (q.abelian X))
    (rZ : SpReductionTower l E c.Z (q.abelian c.Z))
    (rY : SpReductionTower l E Y (q.abelian Y))
    (aX : Reconstruction l E X (q.abelian X) rX)
    (aY : Reconstruction l E Y (q.abelian Y) rY)
    (aZ : LimitPresentation l E c.Z (q.abelian c.Z) rZ)
    (e : forgetting l E X (q.abelian X) ⋙ fixedOpenOrd l E c.i ≅
      ordinaryTowerOpen l E b o c.i ⋙ forgetting l E c.Z (q.abelian c.Z))
    (d : forgetDerived l E c.Z (q.abelian c.Z) rZ aZ ⋙
        (fixedPushOrd l E c.g).rightDerivedFunctor ≅
      towerPush l E b o c.g (q.abelian c.Z) (q.abelian Y) ⋙
        forgetDerived l E Y (q.abelian Y) rY aY.presentation)
    (hF : ∀ M : SpTowerCalculus.C l E b q X,
      spConstructibleTorTowers l E Y (q.abelian Y)
        ((SpTowerCalculus.F l E b o q c).obj M.obj))
    (G : SpTowerCalculus.C l E b q Y ⥤ SpTowerCalculus.C l E b q X)
    (adj : SpTowerGluing.support l E b o q c hF ⊣ G)
    (hFn : ∀ N : spNormalizedConstructibleTorTowerCategory l E X (q.abelian X),
      IsSpNormalizedTower l E Y (q.abelian Y)
        ((SpTowerGluing.support l E b o q c hF).obj
          ((normalizedInclusion l E X (q.abelian X)).obj N)).obj)
    (hGn : ∀ N : spNormalizedConstructibleTorTowerCategory l E Y (q.abelian Y),
      IsSpNormalizedTower l E X (q.abelian X)
        (G.obj ((normalizedInclusion l E Y (q.abelian Y)).obj N)).obj) where
  equivalenceX : sfIntegralConstructibleCategory l E X ≌
    spNormalizedConstructibleTorTowerCategory l E X (q.abelian X)
  equivalenceX_functor : equivalenceX.functor = red l E X (q.abelian X) rX aX
  equivalenceX_inverse : equivalenceX.inverse = lim l E X (q.abelian X) rX aX
  equivalenceY : sfIntegralConstructibleCategory l E Y ≌
    spNormalizedConstructibleTorTowerCategory l E Y (q.abelian Y)
  equivalenceY_functor : equivalenceY.functor = red l E Y (q.abelian Y) rY aY
  equivalenceY_inverse : equivalenceY.inverse = lim l E Y (q.abelian Y) rY aY
  adjunction : towerLeft l E (q.abelian X) (q.abelian Y)
      (SpTowerGluing.support l E b o q c hF) hFn ⊣
    towerRight l E (q.abelian X) (q.abelian Y) G hGn
  unit_same : ∀ N : spNormalizedConstructibleTorTowerCategory l E X (q.abelian X),
    (adjunction.unit.app N).hom =
      (adj.unit.app ((normalizedInclusion l E X (q.abelian X)).obj N)).hom
  counit_same : ∀ N : spNormalizedConstructibleTorTowerCategory l E Y (q.abelian Y),
    (adjunction.counit.app N).hom =
      (adj.counit.app ((normalizedInclusion l E Y (q.abelian Y)).obj N)).hom
  image_mem : ∀ M : sfIntegralConstructibleCategory l E X,
    sfIntegralConstructible l E Y ((image l E c).obj M.obj)
  direct : integralLeft l E c image_mem ⋙ red l E Y (q.abelian Y) rY aY ≅
    red l E X (q.abelian X) rX aX ⋙
      towerLeft l E (q.abelian X) (q.abelian Y) (SpTowerGluing.support l E b o q c hF) hFn
  direct_hom : ∀ M : sfIntegralConstructibleCategory l E X,
    (direct.hom.app M).hom =
      (reduction l E Y (q.abelian Y) rY).map
        ((realization l E b o q.abelian c rX rZ rY aX.presentation aZ aY.presentation e d).app
          M.obj) ≫
      aY.presentation.adjunction.counit.app
        ((SpTowerCalculus.F l E b o q c).obj
          ((reduction l E X (q.abelian X) rX).obj M.obj))
  exceptionalComparison :
    exceptional l E (q.abelian X) (q.abelian Y) rX rY aX aY
        (towerRight l E (q.abelian X) (q.abelian Y) G hGn) ⋙
      red l E X (q.abelian X) rX aX ≅
    red l E Y (q.abelian Y) rY aY ⋙ towerRight l E (q.abelian X) (q.abelian Y) G hGn
  exceptional_hom : ∀ K : sfIntegralConstructibleCategory l E Y,
    (exceptionalComparison.hom.app K).hom =
      aX.presentation.adjunction.counit.app
        (G.obj ((normalizedInclusion l E Y (q.abelian Y)).obj
          ((red l E Y (q.abelian Y) rY aY).obj K))).obj
  direct_naturality : ∀ (M M' : sfIntegralConstructibleCategory l E X) (a : M ⟶ M'),
    (direct.hom.app M) ≫
        (red l E X (q.abelian X) rX aX ⋙
          towerLeft l E (q.abelian X) (q.abelian Y)
            (SpTowerGluing.support l E b o q c hF) hFn).map a =
      (integralLeft l E c image_mem ⋙ red l E Y (q.abelian Y) rY aY).map a ≫
        direct.hom.app M'
  exceptional_naturality : ∀ (K K' : sfIntegralConstructibleCategory l E Y) (h : K ⟶ K'),
    exceptionalComparison.hom.app K ≫
        (red l E Y (q.abelian Y) rY aY ⋙
          towerRight l E (q.abelian X) (q.abelian Y) G hGn).map h =
      (exceptional l E (q.abelian X) (q.abelian Y) rX rY aX aY
          (towerRight l E (q.abelian X) (q.abelian Y) G hGn) ⋙
        red l E X (q.abelian X) rX aX).map h ≫ exceptionalComparison.hom.app K'
  reconstructX : ∀ (A B : sfIntegralConstructibleCategory l E X) (a : A ⟶ B),
    a = (unit l E X (q.abelian X) rX aX A).hom ≫
      (lim l E X (q.abelian X) rX aX).map ((red l E X (q.abelian X) rX aX).map a) ≫
        (unit l E X (q.abelian X) rX aX B).inv
  reconstructY : ∀ (A B : sfIntegralConstructibleCategory l E Y) (a : A ⟶ B),
    a = (unit l E Y (q.abelian Y) rY aY A).hom ≫
      (lim l E Y (q.abelian Y) rY aY).map ((red l E Y (q.abelian Y) rY aY).map a) ≫
        (unit l E Y (q.abelian Y) rY aY B).inv

private theorem tower_bounded_below (T : Scheme.{u})
    (D : SpCoefficientTowersAbelian l E T)
    (N : spNormalizedConstructibleTorTowerCategory l E T D) :
    letI := D.hasDerived
    ∃ k : ℤ, N.obj.IsGE k := by
  let := D.hasDerived
  let := D.equivalenceAdditive
  obtain ⟨a, b, c, d, hab, hcd, hbound⟩ := N.property.1.2
  refine ⟨a, (DerivedCategory.isGE_iff N.obj a).mpr ?_⟩
  intro i hi
  have hz : IsZero (D.equivalence.functor.obj
      ((DerivedCategory.homologyFunctor _ i).obj N.obj)) := by
    apply (SheafOfModules.strictRingSystem_isZero_iff.{u + 1, u, u + 1}
      (spCoefficientCommRings l E T)
      (D.equivalence.functor.obj ((DerivedCategory.homologyFunctor _ i).obj N.obj))).mpr
    intro n
    let := D.evaluationLimits n
    let := D.evaluationColimits n
    let : (spCoefficientEvaluation l E T D.equivalence n).Additive :=
      CategoryTheory.Functor.additive_of_preserves_binary_products _
    exact ((hbound n).1 i (Or.inl hi)).of_iso
      ((spCoefficientEvaluation l E T D.equivalence n).mapDerivedCategoryHomologyFunctorIso i
        |>.app N.obj)
  apply (IsZero.iff_id_eq_zero _).mpr
  apply D.equivalence.functor.map_injective
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero]
  exact (IsZero.iff_id_eq_zero _).mp hz

private theorem normalized_adjoints
    (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (q : SpTowerCalculus.Coordinates l E b) (D₀ : FiniteFieldDatum.{u})
    [CharP D₀.k D₀.p] (hl : l ≠ D₀.p)
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    [X.Over (Spec (.of D₀.k))] [Y.Over (Spec (.of D₀.k))]
    [IsSeparated (X ↘ Spec (.of D₀.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D₀.k))] [QuasiCompact (X ↘ Spec (.of D₀.k))]
    [IsSeparated (Y ↘ Spec (.of D₀.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D₀.k))] [QuasiCompact (Y ↘ Spec (.of D₀.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D₀.k))] [QuasiCompact f]
    [HasCompactification f] (d : ℕ) [SmoothOfRelativeDimension d f]
    (c : Compactification f) (w : SpChartAdmissibility.Twists l E X)
    (hF : ∀ M : SpTowerCalculus.C l E b q X,
      spConstructibleTorTowers l E Y (q.abelian Y)
        ((SpTowerCalculus.F l E b o q c).obj M.obj))
    (G : SpTowerCalculus.C l E b q Y ⥤ SpTowerCalculus.C l E b q X)
    (adj : SpTowerGluing.support l E b o q c hF ⊣ G)
    (lv : SpTowerGluing.Levels l E b o q c hF G adj) :
    (∀ M : SpTowerCalculus.C l E b q X,
      IsSpNormalizedTower l E X (q.abelian X) M.obj →
      IsSpNormalizedTower l E Y (q.abelian Y)
        ((SpTowerGluing.support l E b o q c hF).obj M).obj) ∧
    (∀ N : SpTowerCalculus.C l E b q Y,
      IsSpNormalizedTower l E Y (q.abelian Y) N.obj →
      IsSpNormalizedTower l E X (q.abelian X) (G.obj N).obj) := by
  rcases c with ⟨Z, p, j, h, hp, hj⟩
  subst f
  let := hp
  let := hj
  obtain ⟨pur⟩ := SpTowerGamma.tower_gamma l E b o q D₀ hl j p d w hF G adj lv
  exact ⟨pur.support_normalized, pur.exceptional_normalized⟩

private theorem reconstruction_exists
    (T : Scheme.{u}) [IsNoetherian T] [∀ x : T, Invertible (l : T.residueField x)]
    (D : SpCoefficientTowersAbelian l E T) (r : SpReductionTower l E T D)
    (a : LimitPresentation l E T D r) :
    ∃ a' : Reconstruction l E T D r, a'.presentation = a := by
  obtain ⟨n⟩ := sp_normalized_equivalence l E T D r
  obtain ⟨e, he, hi⟩ := n.restriction inferInstance
  have hr (M : sfIntegralConstructibleCategory l E T) :
      spNormalizedConstructibleTorTowers l E T D ((reduction l E T D r).obj M.obj) := by
    have h := congrArg (fun F ↦ F.obj M) he
    change (e.functor.obj M).obj = (reduction l E T D r).obj M.obj at h
    rw [← h]
    exact (e.functor.obj M).property
  have hlim (N : spNormalizedConstructibleTorTowerCategory l E T D) :
      sfIntegralConstructible l E T ((totalLimit l E T D r a).obj N.obj) := by
    have h := congrArg (fun F ↦ F.obj N) hi
    change (e.inverse.obj N).obj = (totalLimit l E T D r a).obj N.obj at h
    rw [← h]
    exact (e.inverse.obj N).property
  refine ⟨{ presentation := a
            reduction_mem := hr
            limit_mem := hlim
            unit_iso := ?_
            counit_iso := ?_ }, rfl⟩
  · intro M
    obtain ⟨p, hp, hprime⟩ := Nat.exists_infinite_primes (l + 1)
    let : Fact p.Prime := ⟨hprime⟩
    let K : FiniteFieldDatum.{0} :=
      { p := p
        a := 1
        q := p
        prime := hprime
        exponent_pos := by decide
        cardinality_eq := by simp
        k₀ := ZMod p
        card_base := by simp [Nat.card_eq_fintype_card]
        k := AlgebraicClosure (ZMod p) }
    have hlK : l ≠ K.p := by change l ≠ p; omega
    have hcomplete : IntegralOnSlice.IsComplete l E T none M.obj :=
      ⟨K, hlK, (sfDerivedComplete_iff_legacy l E T K hlK M.obj).mp M.property.1⟩
    have := n.unit_isIso M.obj hcomplete
    rw [← n.adjunction.unit_rightAdjointUniq_hom_app a.adjunction M.obj]
    infer_instance
  · intro N
    have := n.counit_isIso N.obj N.property.2
    rw [← a.adjunction.leftAdjointUniq_hom_app_counit n.adjunction N.obj]
    infer_instance

private def reconstructionAdjunction (T : Scheme.{u})
    (D : SpCoefficientTowersAbelian l E T) (r : SpReductionTower l E T D)
    (a : Reconstruction l E T D r) : red l E T D r a ⊣ lim l E T D r a :=
  a.presentation.adjunction.restrictFullyFaithful
    (sfIntegralConstructible l E T).fullyFaithfulι
    (spNormalizedConstructibleTorTowers l E T D).fullyFaithfulι
    (Iso.refl _) (Iso.refl _)

private theorem reconstruction_unit (T : Scheme.{u})
    (D : SpCoefficientTowersAbelian l E T) (r : SpReductionTower l E T D)
    (a : Reconstruction l E T D r) (M : sfIntegralConstructibleCategory l E T) :
    ((reconstructionAdjunction l E T D r a).unit.app M).hom =
      a.presentation.adjunction.unit.app M.obj := by
  change (sfIntegralConstructible l E T).ι.map
    ((reconstructionAdjunction l E T D r a).unit.app M) = _
  dsimp only [reconstructionAdjunction]
  rw [Adjunction.map_restrictFullyFaithful_unit_app]
  change _ ≫ (totalLimit l E T D r a.presentation).map (𝟙 _) ≫ 𝟙 _ = _
  rw [CategoryTheory.Functor.map_id, Category.comp_id, Category.comp_id]
  rfl

private theorem reconstruction_counit (T : Scheme.{u})
    (D : SpCoefficientTowersAbelian l E T) (r : SpReductionTower l E T D)
    (a : Reconstruction l E T D r)
    (N : spNormalizedConstructibleTorTowerCategory l E T D) :
    ((reconstructionAdjunction l E T D r a).counit.app N).hom =
      a.presentation.adjunction.counit.app N.obj := by
  change (spNormalizedConstructibleTorTowers l E T D).ι.map
    ((reconstructionAdjunction l E T D r a).counit.app N) = _
  dsimp only [reconstructionAdjunction]
  rw [Adjunction.map_restrictFullyFaithful_counit_app]
  change 𝟙 _ ≫ (reduction l E T D r).map (𝟙 _) ≫ _ = _
  rw [CategoryTheory.Functor.map_id, Category.id_comp, Category.id_comp]
  rfl

private def reconstructionEquivalence (T : Scheme.{u})
    (D : SpCoefficientTowersAbelian l E T) (r : SpReductionTower l E T D)
    (a : Reconstruction l E T D r) : sfIntegralConstructibleCategory l E T ≌
      spNormalizedConstructibleTorTowerCategory l E T D := by
  let adj := reconstructionAdjunction l E T D r a
  have hu (M : sfIntegralConstructibleCategory l E T) : IsIso (adj.unit.app M) := by
    have : IsIso ((sfIntegralConstructible l E T).ι.map (adj.unit.app M)) := by
      change IsIso ((adj.unit.app M).hom)
      rw [reconstruction_unit]
      exact a.unit_iso M
    exact isIso_of_reflects_iso _ (sfIntegralConstructible l E T).ι
  have hc (N : spNormalizedConstructibleTorTowerCategory l E T D) :
      IsIso (adj.counit.app N) := by
    have : IsIso ((spNormalizedConstructibleTorTowers l E T D).ι.map
        (adj.counit.app N)) := by
      change IsIso ((adj.counit.app N).hom)
      rw [reconstruction_counit]
      exact a.counit_iso N
    exact isIso_of_reflects_iso _ (spNormalizedConstructibleTorTowers l E T D).ι
  exact adj.toEquivalence

private theorem reconstruct_morphism (T : Scheme.{u})
    (D : SpCoefficientTowersAbelian l E T) (r : SpReductionTower l E T D)
    (a : Reconstruction l E T D r) (A B : sfIntegralConstructibleCategory l E T)
    (f : A ⟶ B) :
    f = (unit l E T D r a A).hom ≫
      (lim l E T D r a).map ((red l E T D r a).map f) ≫
        (unit l E T D r a B).inv := by
  have hn : (unit l E T D r a A).hom ≫
      (lim l E T D r a).map ((red l E T D r a).map f) =
      f ≫ (unit l E T D r a B).hom := by
    apply ObjectProperty.hom_ext
    exact (a.presentation.adjunction.unit.naturality f.hom).symm
  rw [← Category.assoc, hn]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

private theorem assembleComparisons (b : SpTowerShriek.Base l E)
    (o : SpTowerShriek.Operations l E b)
    (q : SpTowerCalculus.Coordinates l E b)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (rX : SpReductionTower l E X (q.abelian X))
    (rZ : SpReductionTower l E c.Z (q.abelian c.Z))
    (rY : SpReductionTower l E Y (q.abelian Y))
    (aX : Reconstruction l E X (q.abelian X) rX)
    (aY : Reconstruction l E Y (q.abelian Y) rY)
    (aZ : LimitPresentation l E c.Z (q.abelian c.Z) rZ)
    (e : forgetting l E X (q.abelian X) ⋙ fixedOpenOrd l E c.i ≅
      ordinaryTowerOpen l E b o c.i ⋙ forgetting l E c.Z (q.abelian c.Z))
    (d : forgetDerived l E c.Z (q.abelian c.Z) rZ aZ ⋙
        (fixedPushOrd l E c.g).rightDerivedFunctor ≅
      towerPush l E b o c.g (q.abelian c.Z) (q.abelian Y) ⋙
        forgetDerived l E Y (q.abelian Y) rY aY.presentation)
    (hF : ∀ M : SpTowerCalculus.C l E b q X,
      spConstructibleTorTowers l E Y (q.abelian Y)
        ((SpTowerCalculus.F l E b o q c).obj M.obj))
    (G : SpTowerCalculus.C l E b q Y ⥤ SpTowerCalculus.C l E b q X)
    (adj : SpTowerGluing.support l E b o q c hF ⊣ G)
    (hFn : ∀ N : spNormalizedConstructibleTorTowerCategory l E X (q.abelian X),
      IsSpNormalizedTower l E Y (q.abelian Y)
        ((SpTowerGluing.support l E b o q c hF).obj
          ((normalizedInclusion l E X (q.abelian X)).obj N)).obj)
    (hGn : ∀ N : spNormalizedConstructibleTorTowerCategory l E Y (q.abelian Y),
      IsSpNormalizedTower l E X (q.abelian X)
        (G.obj ((normalizedInclusion l E Y (q.abelian Y)).obj N)).obj)
    (himage : ∀ M : sfIntegralConstructibleCategory l E X,
      sfIntegralConstructible l E Y ((image l E c).obj M.obj))
    (halpha : ∀ M : sfIntegralConstructibleCategory l E X,
      IsIso ((realization l E b o q.abelian c rX rZ rY aX.presentation aZ
        aY.presentation e d).app M.obj)) :
    Nonempty (Comparisons l E b o q c rX rZ rY aX aY aZ e d hF G adj hFn hGn) := by
  let P := sfIntegralConstructible l E X
  let Q := spNormalizedConstructibleTorTowers l E Y (q.abelian Y)
  let F := SpTowerCalculus.F l E b o q c
  let rx := red l E X (q.abelian X) rX aX
  let ry := red l E Y (q.abelian Y) rY aY
  let fn := towerLeft l E (q.abelian X) (q.abelian Y)
    (SpTowerGluing.support l E b o q c hF) hFn
  let gn := towerRight l E (q.abelian X) (q.abelian Y) G hGn
  let an : fn ⊣ gn := adj.restrictFullyFaithful
    (ObjectProperty.fullyFaithfulιOfLE (fun _ h ↦ h.1))
    (ObjectProperty.fullyFaithfulιOfLE (fun _ h ↦ h.1)) (Iso.refl _) (Iso.refl _)
  have hun N : (an.unit.app N).hom =
      (adj.unit.app ((normalizedInclusion l E X (q.abelian X)).obj N)).hom := by
    have h := Adjunction.map_restrictFullyFaithful_unit_app adj
      (ObjectProperty.fullyFaithfulιOfLE (fun _ h ↦ h.1))
      (ObjectProperty.fullyFaithfulιOfLE (fun _ h ↦ h.1))
      (L := fn) (R := gn) (Iso.refl _) (Iso.refl _) N
    dsimp only [Iso.refl_hom, NatTrans.id_app] at h
    erw [G.map_id, Category.comp_id, Category.comp_id] at h
    exact congrArg (InducedCategory.Hom.hom) h
  have hcn N : (an.counit.app N).hom =
      (adj.counit.app ((normalizedInclusion l E Y (q.abelian Y)).obj N)).hom := by
    have h := Adjunction.map_restrictFullyFaithful_counit_app adj
      (ObjectProperty.fullyFaithfulιOfLE (fun _ h ↦ h.1))
      (ObjectProperty.fullyFaithfulιOfLE (fun _ h ↦ h.1))
      (L := fn) (R := gn) (Iso.refl _) (Iso.refl _) N
    dsimp only [Iso.refl_inv, NatTrans.id_app] at h
    erw [(SpTowerGluing.support l E b o q c hF).map_id,
      Category.id_comp, Category.id_comp] at h
    exact congrArg (InducedCategory.Hom.hom) h
  let alpha := realization l E b o q.abelian c rX rZ rY aX.presentation aZ
    aY.presentation e d
  let beta : (integralLeft l E c himage ⋙ ry) ⋙ Q.ι ⟶ (rx ⋙ fn) ⋙ Q.ι :=
    Functor.whiskerRight (Functor.whiskerLeft P.ι alpha)
        (reduction l E Y (q.abelian Y) rY) ≫
      Functor.whiskerLeft (P.ι ⋙ reduction l E X (q.abelian X) rX ⋙ F)
        aY.presentation.adjunction.counit
  have hb M : IsIso (beta.app M) := by
    have := halpha M
    have := aY.counit_iso (fn.obj (rx.obj M))
    change IsIso ((reduction l E Y (q.abelian Y) rY).map (alpha.app M.obj) ≫
      aY.presentation.adjunction.counit.app (fn.obj (rx.obj M)).obj)
    infer_instance
  have : IsIso beta := NatIso.isIso_of_isIso_app beta
  let direct := Functor.fullyFaithfulCancelRight Q.ι (asIso beta)
  have hcx (N : spNormalizedConstructibleTorTowerCategory l E X (q.abelian X)) :
      IsIso ((reconstructionAdjunction l E X (q.abelian X) rX aX).counit.app N) := by
    have : IsIso ((spNormalizedConstructibleTorTowers l E X (q.abelian X)).ι.map
        ((reconstructionAdjunction l E X (q.abelian X) rX aX).counit.app N)) := by
      change IsIso (((reconstructionAdjunction l E X (q.abelian X) rX aX).counit.app N).hom)
      rw [reconstruction_counit]
      exact aX.counit_iso N
    exact isIso_of_reflects_iso _ (spNormalizedConstructibleTorTowers l E X (q.abelian X)).ι
  have : IsIso (reconstructionAdjunction l E X (q.abelian X) rX aX).counit :=
    NatIso.isIso_of_isIso_app _
  let ex : exceptional l E (q.abelian X) (q.abelian Y) rX rY aX aY gn ⋙ rx ≅
      ry ⋙ gn :=  Functor.isoWhiskerLeft (ry ⋙ gn)
    (asIso (reconstructionAdjunction l E X (q.abelian X) rX aX).counit)
  refine ⟨{
    equivalenceX := reconstructionEquivalence l E X (q.abelian X) rX aX
    equivalenceX_functor := rfl
    equivalenceX_inverse := rfl
    equivalenceY := reconstructionEquivalence l E Y (q.abelian Y) rY aY
    equivalenceY_functor := rfl
    equivalenceY_inverse := rfl
    adjunction := an
    unit_same := hun
    counit_same := hcn
    image_mem := himage
    direct := direct
    direct_hom := ?_
    exceptionalComparison := ex
    exceptional_hom := ?_
    direct_naturality := fun _ _ f ↦ (direct.hom.naturality f).symm
    exceptional_naturality := fun _ _ f ↦ (ex.hom.naturality f).symm
    reconstructX := reconstruct_morphism l E X (q.abelian X) rX aX
    reconstructY := reconstruct_morphism l E Y (q.abelian Y) rY aY }⟩
  · intro M
    change Q.ι.map (Q.ι.preimage (beta.app M)) = beta.app M
    exact Q.ι.map_preimage (beta.app M)
  · intro K
    change ((reconstructionAdjunction l E X (q.abelian X) rX aX).counit.app
      (gn.obj (ry.obj K))).hom = _
    exact reconstruction_counit l E X (q.abelian X) rX aX (gn.obj (ry.obj K))

/-- The natural reconstruction comparisons for the specified smooth tower adjunction.
Source: current blueprint, integral-adjunction Bijections and Normalization
(blueprint: lem-sp-integral-reconstruction-comparisons).

Proof:
1. The finite field and its algebraic closure are Noetherian. Finite-type structure
maps give Noetherian X,Y and the proper compactification middle scheme, by
lem-weil-pbc-finite-type-over-noetherian and def-weil-proper-morphism. They are qcqs by
lem-weil-pbc-locally-noetherian-quasi-separated; the compactification open is quasi-compact
by lemma-nagata-open-immersion-qc-over-separated-target. Ell is invertible on each.
2. Apply det-sp-normalized-equivalence to X,Y. Its actual reduction/limit adjunction
restricts to the full integral and normalized categories. Its unit and counit are
invertible there, and red is fully faithful with inverse lim. Choose the quotient-unit
normalized presentations supplied by lem-sp-complete-compactification-limit-realization;
the tensor-generator normalization identifies their adjunctions with the same ones.
3. det-sp-tower-gamma preserves normalization under both specified adjoints. Restrict
the Hom bijection from det-sp-tower-gluing to the full normalized categories. Its unit
and counit remain exactly the original ambient morphisms.
4. Define H as red_Y followed by the restricted G followed by lim_X. Its reduction
comparison c is the actual reconstruction counit at G(red_Y K), hence invertible and
natural in K.
5. The reduction of a constructible integral M has a common lower cohomological bound.
Levelwise cohomology from det-sp-coefficient-towers-abelian makes it bounded below as a
strict tower. The compactification realization lemma gives the canonical natural alpha
from F(M) to lim_Y(F_bullet(red_X M)), using the completion unit, open/limit mate,
proper/limit mate, and scalar comparison. det-sp-tower-shriek-levels identifies the
proper/open tower word with F_bullet. The exact-coordinate word supportCoordinates
retains this identification. The normalized target reconstructs to an integral
constructible object; alpha therefore also proves that F(M) belongs to that category.
Set b = reduction(alpha) followed by the actual reconstruction counit.
6. Naturality of alpha and the counit gives F_bullet(red_X a) b_M = b_M' red_Y(F a).
Naturality of the same counit gives the displayed equation for c. Both are equalities
of actual entire-tower morphisms, not claims detected by finite evaluations.
7. Naturality of the actual unit says u_A followed by lim(red a) = a followed by u_B.
Cancel the invertible u_B to obtain a = u_A followed by lim(red a) followed by u_B inverse.
This applies to every arrow, including units and counits transported along b,c. -/
theorem integral_reconstruction_comparisons
    (D₀ : FiniteFieldDatum.{u}) (_hl : l ≠ D₀.p)
    (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (q : SpTowerCalculus.Coordinates l E b)
    (r : ∀ T : Scheme.{u}, SpReductionTower l E T (q.abelian T))
    (X Y : Over (Spec (.of D₀.k)))
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (f : X ⟶ Y) (d₀ : ℕ) [SmoothOfRelativeDimension d₀ f.left]
    (c : Compactification f.left)
    (hF : ∀ M : SpTowerCalculus.C l E b q X.left,
      spConstructibleTorTowers l E Y.left (q.abelian Y.left)
        ((SpTowerCalculus.F l E b o q c).obj M.obj))
    (G : SpTowerCalculus.C l E b q Y.left ⥤ SpTowerCalculus.C l E b q X.left)
    (adj : SpTowerGluing.support l E b o q c hF ⊣ G)
    (_charts : SpTowerGluing.Charts l E b o q D₀.k X Y
      ⟨inferInstance, inferInstance, inferInstance⟩ f d₀ c hF G adj)
    (_levels : SpTowerGluing.Levels l E b o q c hF G adj) :
    IsNoetherian X.left ∧ IsNoetherian Y.left ∧
    ∃ (aX : Reconstruction l E X.left (q.abelian X.left) (r X.left))
      (aY : Reconstruction l E Y.left (q.abelian Y.left) (r Y.left))
      (aZ : LimitPresentation l E c.Z (q.abelian c.Z) (r c.Z))
      (h : ScalarSquares l E)
      (vX : Evaluation l E b X.left (q.abelian X.left))
      (vZ : Evaluation l E b c.Z (q.abelian c.Z))
      (vY : Evaluation l E b Y.left (q.abelian Y.left))
      (e : forgetting l E X.left (q.abelian X.left) ⋙ fixedOpenOrd l E c.i ≅
        ordinaryTowerOpen l E b o c.i ⋙ forgetting l E c.Z (q.abelian c.Z))
      (pO : forgetting l E c.Z (q.abelian c.Z) ⋙ fixedPushOrd l E c.g ≅
        ordinaryTowerPush l E b o c.g ⋙ forgetting l E Y.left (q.abelian Y.left))
      (d : forgetDerived l E c.Z (q.abelian c.Z) (r c.Z) aZ ⋙
          (fixedPushOrd l E c.g).rightDerivedFunctor ≅
        towerPush l E b o c.g (q.abelian c.Z) (q.abelian Y.left) ⋙
          forgetDerived l E Y.left (q.abelian Y.left) (r Y.left) aY.presentation)
      (hFn : ∀ N : spNormalizedConstructibleTorTowerCategory l E X.left (q.abelian X.left),
        IsSpNormalizedTower l E Y.left (q.abelian Y.left)
          ((SpTowerGluing.support l E b o q c hF).obj
            ((normalizedInclusion l E X.left (q.abelian X.left)).obj N)).obj)
      (hGn : ∀ N : spNormalizedConstructibleTorTowerCategory l E Y.left (q.abelian Y.left),
        IsSpNormalizedTower l E X.left (q.abelian X.left)
          (G.obj ((normalizedInclusion l E Y.left (q.abelian Y.left)).obj N)).obj),
      (∀ (N : spCoefficientTowers l E X.left) (n : ℕ),
        (e.hom.app N).app (op n) ≫
            (spCompletedEllRestriction l E c.Z n).map
              ((ordinaryOpenEvaluation l E b o c.i (q.abelian X.left) (q.abelian c.Z)
                vX vZ n).hom.app N) =
          (ordinaryOpenScalar l E b h c.i n).hom.app
            ((spCoefficientEvaluation l E X.left (q.abelian X.left).equivalence n).obj N)) ∧
      (∀ (N : spCoefficientTowers l E c.Z) (n : ℕ),
        (pO.hom.app N).app (op n) ≫
            (spCompletedEllRestriction l E Y.left n).map
              ((ordinaryPushEvaluation l E b o c.g (q.abelian c.Z) (q.abelian Y.left)
                vZ vY n).hom.app N) =
          (ordinaryPushScalar l E h c.g n).hom.app
            ((spCoefficientEvaluation l E c.Z (q.abelian c.Z).equivalence n).obj N)) ∧
      IsPushScalarNormalized l E b o c.g (q.abelian c.Z) (q.abelian Y.left)
        (r c.Z) (r Y.left) aZ aY.presentation pO d ∧
      Nonempty (Comparisons l E b o q c (r X.left) (r c.Z) (r Y.left) aX aY aZ
        e d hF G adj hFn hGn) := by
  classical
  have : Fact D₀.p.Prime := ⟨D₀.prime⟩
  let : Fintype D₀.k₀ := Fintype.ofFinite _
  have : CharP D₀.k₀ D₀.p := charP_of_card_eq_prime_pow
    ((Nat.card_eq_fintype_card).symm.trans (D₀.card_base.trans D₀.cardinality_eq))
  have : CharP D₀.k D₀.p := charP_of_injective_algebraMap' D₀.k₀ D₀.p
  have hlk : IsUnit (l : D₀.k) := isUnit_iff_ne_zero.mpr
    (CharP.cast_ne_zero_of_ne_of_prime D₀.k (Fact.out : l.Prime) _hl.symm)
  let iz : c.Z ⟶ Spec (.of D₀.k) := c.g ≫ Y.hom
  have hnoeth (T : Scheme.{u}) (g : T ⟶ Spec (.of D₀.k))
      [LocallyOfFiniteType g] [QuasiCompact g] : IsNoetherian T := by
    have := LocallyOfFiniteType.isLocallyNoetherian g
    have := QuasiCompact.compactSpace_of_compactSpace g
    exact ⟨⟩
  have hX := hnoeth X.left X.hom
  have hY := hnoeth Y.left Y.hom
  have hZ := hnoeth c.Z iz
  have hunit (T : Scheme.{u}) (g : T ⟶ Spec (.of D₀.k)) (x : T) :
      IsUnit (l : T.residueField x) := by
    let φ := ((Scheme.ΓSpecIso (.of D₀.k)).inv ≫ g.appTop ≫ T.Γevaluation x).hom
    exact Eq.mp (congrArg IsUnit (map_natCast φ l)) (hlk.map φ)
  let : ∀ x : X.left, Invertible (l : X.left.residueField x) :=
    fun x ↦ (hunit X.left X.hom x).invertible
  let : ∀ x : Y.left, Invertible (l : Y.left.residueField x) :=
    fun x ↦ (hunit Y.left Y.hom x).invertible
  have hi : QuasiCompact c.i := QuasiCompact.of_comp c.i iz
  obtain ⟨hs, a, v, ha⟩ := complete_compactification_limit_realization l E b o q.abelian r
  obtain ⟨ax, hax⟩ := reconstruction_exists l E X.left
    (q.abelian X.left) (r X.left) (a X.left)
  obtain ⟨ay, hay⟩ := reconstruction_exists l E Y.left
    (q.abelian Y.left) (r Y.left) (a Y.left)
  let aX : Reconstruction l E X.left (q.abelian X.left) (r X.left) :=
    { ax with
      presentation := a X.left
      unit_iso := fun M ↦ by rw [← hax]; exact ax.unit_iso M
      counit_iso := fun N ↦ by rw [← hax]; exact ax.counit_iso N }
  let aY : Reconstruction l E Y.left (q.abelian Y.left) (r Y.left) :=
    { ay with
      presentation := a Y.left
      unit_iso := fun M ↦ by rw [← hay]; exact ay.unit_iso M
      counit_iso := fun N ↦ by rw [← hay]; exact ay.counit_iso N }
  have haX : aX.presentation = a X.left := rfl
  have haY : aY.presentation = a Y.left := rfl
  obtain ⟨sc, w, hw, ho, hp, halpha⟩ := ha X.left Y.left f.left c
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (hunit X.left X.hom) (hunit c.Z iz) (hunit Y.left Y.hom) hi
  let : X.left.Over (Spec (.of D₀.k)) := ⟨X.hom⟩
  let : Y.left.Over (Spec (.of D₀.k)) := ⟨Y.hom⟩
  have : IsSeparated (X.left ↘ Spec (.of D₀.k)) := by
    change IsSeparated X.hom; infer_instance
  have : LocallyOfFiniteType (X.left ↘ Spec (.of D₀.k)) := by
    change LocallyOfFiniteType X.hom; infer_instance
  have : QuasiCompact (X.left ↘ Spec (.of D₀.k)) := by
    change QuasiCompact X.hom; infer_instance
  have : IsSeparated (Y.left ↘ Spec (.of D₀.k)) := by
    change IsSeparated Y.hom; infer_instance
  have : LocallyOfFiniteType (Y.left ↘ Spec (.of D₀.k)) := by
    change LocallyOfFiniteType Y.hom; infer_instance
  have : QuasiCompact (Y.left ↘ Spec (.of D₀.k)) := by
    change QuasiCompact Y.hom; infer_instance
  have : f.left.IsOver (Spec (.of D₀.k)) := ⟨f.w⟩
  have : HasCompactification f.left := ⟨⟨c⟩⟩
  obtain ⟨purF, purG⟩ := normalized_adjoints l E b o q D₀ _hl f.left d₀ c
    (_charts.twists X.left) hF G adj _levels
  have hFn (N : spNormalizedConstructibleTorTowerCategory l E X.left (q.abelian X.left)) :
      IsSpNormalizedTower l E Y.left (q.abelian Y.left)
        ((SpTowerGluing.support l E b o q c hF).obj
          ((normalizedInclusion l E X.left (q.abelian X.left)).obj N)).obj :=
    purF _ N.property.2
  have hGn (N : spNormalizedConstructibleTorTowerCategory l E Y.left (q.abelian Y.left)) :
      IsSpNormalizedTower l E X.left (q.abelian X.left)
        (G.obj ((normalizedInclusion l E Y.left (q.abelian Y.left)).obj N)).obj :=
    purG _ N.property.2
  have hiso (M : sfIntegralConstructibleCategory l E X.left) :
      IsIso ((realization l E b o q.abelian c (r X.left) (r c.Z) (r Y.left)
        aX.presentation (a c.Z) aY.presentation sc.openOrdinary sc.pushDerived).app M.obj) := by
    have hinput : IsInput l E X.left (q.abelian X.left) (r X.left) (a X.left) M.obj := by
      refine ⟨?_, ?_⟩
      · change IsIso ((a X.left).adjunction.unit.app M.obj)
        rw [← haX]
        exact aX.unit_iso M
      · exact tower_bounded_below l E X.left (q.abelian X.left)
          ((red l E X.left (q.abelian X.left) (r X.left) aX).obj M)
    obtain ⟨alpha, hAlpha, _⟩ := halpha M.obj hinput
    have hAlphaIso : IsIso ((comparison l E b o c (q.abelian X.left) (q.abelian c.Z)
        (q.abelian Y.left) (r X.left) (r c.Z) (r Y.left) (a X.left) (a c.Z) (a Y.left)
        sc.openOrdinary sc.pushDerived).app M.obj) := hAlpha ▸ alpha.isIso_hom
    dsimp only [realization, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app]
    rw [haX, haY]
    infer_instance
  have himage (M : sfIntegralConstructibleCategory l E X.left) :
      sfIntegralConstructible l E Y.left ((image l E c).obj M.obj) := by
    have := hiso M
    apply (sfIntegralConstructible l E Y.left).prop_of_iso
      (asIso ((realization l E b o q.abelian c (r X.left) (r c.Z) (r Y.left)
        aX.presentation (a c.Z) aY.presentation sc.openOrdinary sc.pushDerived).app M.obj)).symm
    exact aY.limit_mem
      ((towerLeft l E (q.abelian X.left) (q.abelian Y.left)
        (SpTowerGluing.support l E b o q c hF) hFn).obj
          ((red l E X.left (q.abelian X.left) (r X.left) aX).obj M))
  refine ⟨hX, hY, aX, aY, a c.Z, hs, v X.left, v c.Z, v Y.left,
    sc.openOrdinary, sc.pushOrdinary, sc.pushDerived, hFn, hGn, sc.open_normalized,
    sc.push_normalized, sc.derived_normalized, ?_⟩
  apply assembleComparisons l E b o q c (r X.left) (r c.Z) (r Y.left)
    aX aY (a c.Z) sc.openOrdinary _ hF G adj hFn hGn himage
  exact hiso

end AlgebraicGeometry.ProEtale.IntegralReconstructionComparisons
