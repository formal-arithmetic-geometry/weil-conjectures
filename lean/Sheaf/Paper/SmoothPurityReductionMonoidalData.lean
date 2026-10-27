/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.SmoothPurityReductionTowerNormalized
public import Sheaf.Paper.SemilinearDerivedSections
public import Sheaf.Paper.CompletedCondensedCoefficients
public import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
public import Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import Sheaf.CategoryTheory.SystemRingedSequenceSite

/-! # Derived monoidal reduction of integral coefficient towers

Source: blueprint/latest, integral direct-image proof, paragraph (3); Stacks 03EL,
07A4, 0G7E and 0D6D (blueprint: def-sp-reduction-monoidal-comparison-data).

The coefficient index n denotes the positive exponent n+1. We transport the recorded
reduction through the canonical equivalence with module sheaves on the sequence site.
The comparison records below retain both strict representatives and their localization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [-instance] WeilConjectures.SemilinearSections.abelianSheafify
attribute [-instance] WeilConjectures.SemilinearSections.locallyBijective
attribute [-instance] WeilConjectures.SemilinearSections.hasDerived
attribute [-instance] AlgebraicGeometry.Scheme.ProjectionRestriction.derived
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [instance] AlgebraicGeometry.ProEtale.SpReductionTower.additive
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  DerivedCategory CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.rightDerivedFunctor
open WeilConjectures WeilConjectures.SemilinearSections
namespace AlgebraicGeometry.ProEtale
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})


/-- Smallness in the actual coefficient universe, without an auxiliary universe.
Source: small pro-etale site convention
(blueprint: def-sp-reduction-monoidal-comparison-data). -/
instance (priority := 30000) spMonoidalSiteSmall : EssentiallySmall.{u + 1} T.ProEt :=
  essentiallySmallSelf.{0, u, u + 1} _

/-- Ring sheafification at the fixed coefficient size of the small pro-etale site.
Source: Stacks 03CZ (blueprint: def-sp-reduction-monoidal-comparison-data). -/
instance (priority := 40000) spMonoidalRingSheafify :
    HasSheafify (Scheme.ProEt.topology T) CommRingCat.{u + 1} :=
  @hasSheafifyEssentiallySmallSite.{u, u + 1, u + 1, u + 2, u + 1}
    T.ProEt inferInstance (Scheme.ProEt.topology T) CommRingCat.{u + 1}
    inferInstance (essentiallySmallSelf.{0, u, u + 1} _) inferInstance

/-- The sequence site is small in the actual coefficient universe.
Source: Zheng 4.1 (blueprint: def-sp-reduction-monoidal-comparison-data). -/
instance (priority := 30000) spMonoidalSequenceSmall :
    EssentiallySmall.{u + 1} (ℕ × T.ProEt) :=
  essentiallySmallSelf.{0, u, u + 1} _

/-- Abelian sheafification on the sequence site, with its coefficient size fixed.
Source: Stacks 03DA (blueprint: def-sp-reduction-monoidal-comparison-data). -/
instance (priority := 30000) spMonoidalSequenceSheafify :
    HasSheafify (coefficientSequenceTopology (Scheme.ProEt.topology T))
      AddCommGrpCat.{u + 1} :=
  @SemilinearSections.abelianSheafify.{u + 1, u, u + 1} (ℕ × T.ProEt) inferInstance
    (essentiallySmallSelf.{0, u, u + 1} _) _

/-- The same coefficient-size local-bijection criterion.
Source: Stacks 03DA (blueprint: def-sp-reduction-monoidal-comparison-data). -/
instance (priority := 30000) spMonoidalSequenceLocallyBijective :
    (coefficientSequenceTopology (Scheme.ProEt.topology T)).WEqualsLocallyBijective
      AddCommGrpCat.{u + 1} :=
  @SemilinearSections.locallyBijective.{u + 1, u, u + 1} (ℕ × T.ProEt) inferInstance
    (essentiallySmallSelf.{0, u, u + 1} _) _

/-- The coefficient tower as a ring sheaf on the sequence site.
Source: blueprint paragraph (3) (blueprint: def-sp-reduction-monoidal-comparison-data). -/
abbrev spMonoidalSystemRing :
    Sheaf (coefficientSequenceTopology (Scheme.ProEt.topology T)) CommRingCat.{u + 1} :=
  @SheafOfModules.systemSequenceRing.{u + 1, u, u + 1} T.ProEt inferInstance
    (Scheme.ProEt.topology T) (essentiallySmallSelf.{0, u, u + 1} T.ProEt)
    inferInstance (spFiniteLevelLocallyBijective T) (spFiniteLevelSheafify T)
    (spCoefficientCommRings.{u,u} l E T)

/-- Ordinary modules on the actual sequence ring.
Source: Zheng 4.1 (blueprint: def-sp-reduction-monoidal-comparison-data). -/
abbrev spMonoidalSystems :=
  @SemilinearSections.Mod.{u + 1, u, u + 1} (ℕ × T.ProEt) inferInstance
    (essentiallySmallSelf.{0, u, u + 1} (ℕ × T.ProEt))
    (coefficientSequenceTopology (Scheme.ProEt.topology T))
    (spMonoidalSystemRing l E T)

/-- The ordinary unbounded localization on sequence modules, at the recorded size.
Source: Stacks 05RU (blueprint: def-sp-reduction-monoidal-comparison-data). -/
instance (priority := 20000) spMonoidalSystemsDerived :
    HasDerivedCategory.{u + 2} (spMonoidalSystems l E T) :=
  HasDerivedCategory.standard _

/-- The canonical realization, retaining all horizontal maps.
Source: Zheng 4.1 (blueprint: def-sp-reduction-monoidal-comparison-data). -/
def spMonoidalTowerEquivalence (D : SpCoefficientTowersAbelian l E T) :
    spCoefficientTowers l E T ≌ spMonoidalSystems l E T :=
  D.equivalence.trans
    (@SheafOfModules.strictSystemSequenceEquivalence.{u + 1, u, u + 1} T.ProEt inferInstance
      (Scheme.ProEt.topology T) (essentiallySmallSelf.{0, u, u + 1} T.ProEt)
      inferInstance (spFiniteLevelLocallyBijective T) (spFiniteLevelSheafify T)
      (spCoefficientCommRings.{u,u} l E T))

/-- Source closed tensor is the dependency's ordinary derived tensor.
Source: Stacks 07A4 (blueprint: def-sp-reduction-monoidal-comparison-data). -/
abbrev SpIntegralClosed :=
  @SemilinearSections.Closed.{u + 1, u, u + 1} T.ProEt inferInstance (Scheme.ProEt.topology T)
    (essentiallySmallSelf.{0, u, u + 1} T.ProEt) (spIntegralSectionRing l E T)

/-- Target closed tensor is the dependency's ordinary derived system tensor.
Source: Stacks 07A4 (blueprint: def-sp-reduction-monoidal-comparison-data). -/
abbrev SpSystemClosed :=
  @SemilinearSections.Closed.{u + 1, u, u + 1} (ℕ × T.ProEt) inferInstance
    (coefficientSequenceTopology (Scheme.ProEt.topology T))
    (essentiallySmallSelf.{0, u, u + 1} (ℕ × T.ProEt)) (spMonoidalSystemRing l E T)

/-- Additivity of the canonical sequence realization.
Source: Zheng 4.1 (blueprint: def-sp-reduction-monoidal-comparison-data). -/
instance spMonoidalTowerFunctorAdditive (D : SpCoefficientTowersAbelian l E T) :
    (spMonoidalTowerEquivalence l E T D).functor.Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Additivity of the inverse realization.
Source: Zheng 4.1 (blueprint: def-sp-reduction-monoidal-comparison-data). -/
instance spMonoidalTowerInverseAdditive (D : SpCoefficientTowersAbelian l E T) :
    (spMonoidalTowerEquivalence l E T D).inverse.Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The same canonical equivalence after localization at quasi-isomorphisms.
Source: Zheng 4.1 (blueprint: def-sp-reduction-monoidal-comparison-data). -/
abbrev spMonoidalDerivedEquivalence (D : SpCoefficientTowersAbelian l E T) :=
  letI := D.hasDerived
  (spMonoidalTowerEquivalence l E T D).mapDerivedCategory

/-- The recorded reduction, transported along the canonical equivalence of systems.
Source: blueprint paragraph (3) (blueprint: def-sp-reduction-monoidal-comparison-data). -/
abbrev spMonoidalReduction (D : SpCoefficientTowersAbelian l E T)
    (r : SpReductionTower l E T D) :=
  r.red ⋙ (spMonoidalDerivedEquivalence l E T D).functor



/-- Ordinary simultaneous reduction in the canonical sequence realization.
Source: blueprint (3) (blueprint: def-sp-reduction-monoidal-comparison-data). -/
abbrev spMonoidalOrdinary (D : SpCoefficientTowersAbelian l E T)
    (r : SpReductionTower l E T D) :=
  r.ordinary ⋙ (spMonoidalTowerEquivalence l E T D).functor

/-- Additivity of simultaneous reduction.
Source: blueprint (3) (blueprint: def-sp-reduction-monoidal-comparison-data). -/
instance spMonoidalOrdinaryAdditive (D : SpCoefficientTowersAbelian l E T)
    (r : SpReductionTower l E T D) : (spMonoidalOrdinary l E T D r).Additive :=
  letI := r.additive
  inferInstanceAs (r.ordinary ⋙ (spMonoidalTowerEquivalence l E T D).functor).Additive

/-- The existing reduction computation map, transported by the exact realization.
Source: blueprint (3) (blueprint: def-sp-reduction-monoidal-comparison-data). -/
def spMonoidalCounit (D : SpCoefficientTowersAbelian l E T)
    (r : SpReductionTower l E T D) :
    DerivedCategory.Q ⋙ spMonoidalReduction l E T D r ⟶
      (spMonoidalOrdinary l E T D r).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
  letI := D.hasDerived
  Functor.whiskerRight r.counit (spMonoidalDerivedEquivalence l E T D).functor ≫
    Functor.whiskerLeft (r.ordinary.mapHomologicalComplex (.up ℤ))
      (Functor.mapDerivedCategoryFactors
        (spMonoidalTowerEquivalence l E T D).functor).hom

/-- The actual sheafified local tensor q tensor a, with its quotient level retained.
Source: blueprint (3) (blueprint: def-sp-reduction-monoidal-comparison-data). -/
abbrev spMonoidalGenerator (D : SpCoefficientTowersAbelian l E T)
    (r : SpReductionTower l E T D) (M : spIntegralSectionModules l E T)
    (n : ℕ) (U : T.ProEtᵒᵖ)
    (a : ((spCoefficientCommRings.{u, u} l E T).obj (op n)).obj.obj U) (x : M.val.obj U) :
    ((spMonoidalOrdinary l E T D r).obj M).val.obj (op (n, U.unop)) :=
  spReductionGenerator l E T D r.coefficient r.ordinary r.level M n U a x

/-- The source total tensor, using the existing signed direct-sum totalization.
Source: Stacks 06YN (blueprint: def-sp-reduction-monoidal-comparison-data). -/
abbrev spMonoidalIntegralTotal :=
  SemilinearSections.totalTensor.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
    (spIntegralSectionRing l E T)

/-- The system total tensor before localization, on the actual sequence site.
Source: Stacks 06YN (blueprint: def-sp-reduction-monoidal-comparison-data). -/
abbrev spMonoidalSystemTotal :=
  SemilinearSections.totalTensor.{u + 1, u, u + 1}
    (coefficientSequenceTopology (Scheme.ProEt.topology T)) (spMonoidalSystemRing l E T)

/-- The coherent reduction comparison, including its strict chain-level normalization.
Every chain map is a morphism on the sequence site, hence commutes with all transitions.
The derived square is imposed in the whole system category and fixes the comparison
independently of representatives. The unit and associator equations use CoreMonoidal.
Source: blueprint integral direct-image proof (3); Stacks 03EL, 07A4 and 0D6D
(blueprint: def-sp-reduction-monoidal-comparison-data). -/
structure SpReductionMonoidalData (D : SpCoefficientTowersAbelian l E T)
    (r : SpReductionTower l E T D) where
  /-- The actual source closed derived tensor. -/
  source : SpIntegralClosed l E T
  /-- Its existing K-flat total-complex model. -/
  sourceModel : SemilinearSections.Models.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
    (spIntegralSectionRing l E T) source
  /-- The actual system closed derived tensor. -/
  target : SpSystemClosed l E T
  /-- Its existing K-flat total-complex model. -/
  targetModel : SemilinearSections.Models.{u + 1, u, u + 1}
    (coefficientSequenceTopology (Scheme.ProEt.topology T))
      (spMonoidalSystemRing l E T) target
  /-- The normalized source symmetry. -/
  sourceSymmetry : @SymmetricCategory
    (DerivedCategory (spIntegralSectionModules l E T)) _ source.monoidal
  /-- Source associators and unitors are the usual signed-total ones. -/
  sourceCoherence : RingedDerivedTensorCoherence.{u + 1, u, u + 1, u + 2}
    (Scheme.ProEt.topology T) (spIntegralSectionRing l E T)
    source sourceModel sourceSymmetry
  /-- The normalized system symmetry. -/
  targetSymmetry : @SymmetricCategory
    (DerivedCategory (spMonoidalSystems l E T)) _ target.monoidal
  /-- System associators and unitors are the usual signed-total ones. -/
  targetCoherence : RingedDerivedTensorCoherence.{u + 1, u, u + 1, u + 2}
    (coefficientSequenceTopology (Scheme.ProEt.topology T)) (spMonoidalSystemRing l E T)
    target targetModel targetSymmetry
  /-- The comparison is natural on the entire unbounded derived categories. -/
  μ : source.tensor ⋙ spMonoidalReduction l E T D r ≅
    ((spMonoidalReduction l E T D r).prod (spMonoidalReduction l E T D r)) ⋙ target.tensor
  /-- Tensor units and associators commute with reduction. -/
  monoidal : @Functor.CoreMonoidal
    (DerivedCategory (spIntegralSectionModules l E T)) _ source.monoidal
    (DerivedCategory (spMonoidalSystems l E T)) _ target.monoidal
    (spMonoidalReduction l E T D r)
  /-- Ordinary tensor balancing before any localization. -/
  ordinary : ∀ M N : spIntegralSectionModules l E T,
    (spMonoidalOrdinary l E T D r).obj
      (ordinaryTensor.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
        (spIntegralSectionRing l E T) M N) ≅
    ordinaryTensor.{u + 1, u, u + 1} (coefficientSequenceTopology (Scheme.ProEt.topology T))
      (spMonoidalSystemRing l E T)
      ((spMonoidalOrdinary l E T D r).obj M) ((spMonoidalOrdinary l E T D r).obj N)
  /-- One isomorphism of actual strict-system complexes, natural before evaluation. -/
  chain :
    (((spMonoidalOrdinary l E T D r).mapHomologicalComplex (.up ℤ)).prod
      ((spMonoidalOrdinary l E T D r).mapHomologicalComplex (.up ℤ))) ⋙
        spMonoidalSystemTotal l E T ≅
    spMonoidalIntegralTotal l E T ⋙
      (spMonoidalOrdinary l E T D r).mapHomologicalComplex (.up ℤ)

/-- The strong monoidal tensorator is precisely the inverse of mu.
Source: blueprint paragraph (3)
(blueprint: def-sp-reduction-monoidal-comparison-data). -/
def SpReductionMonoidalTensor (D : SpCoefficientTowersAbelian l E T)
    (r : SpReductionTower l E T D) (W : SpReductionMonoidalData l E T D r) : Prop :=
  ∀ X Y : DerivedCategory (spIntegralSectionModules l E T),
    (@Functor.CoreMonoidal.μIso _ _ W.source.monoidal _ _ W.target.monoidal
      (spMonoidalReduction l E T D r) W.monoidal X Y).hom = W.μ.inv.app (X,Y)

/-- Forward balancing on every sheafified pure tensor.
Source: blueprint paragraph (3)
(blueprint: def-sp-reduction-monoidal-comparison-data). -/
def SpReductionForward (D : SpCoefficientTowersAbelian l E T)
    (r : SpReductionTower l E T D) (W : SpReductionMonoidalData l E T D r) : Prop :=
  ∀ (M N : spIntegralSectionModules l E T) (n : ℕ) (U : T.ProEtᵒᵖ)
    (x : M.val.obj U) (y : N.val.obj U)
    (a : ((spCoefficientCommRings.{u, u} l E T).obj (op n)).obj.obj U),
    ((W.ordinary M N).hom.val.app (op (n, U.unop)))
      (spMonoidalGenerator l E T D r _ n U a
        (tensorSection.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
          (spIntegralSectionRing l E T) M N U x y)) =
    tensorSection.{u + 1, u, u + 1} (coefficientSequenceTopology (Scheme.ProEt.topology T))
      (spMonoidalSystemRing l E T) _ _ (op (n, U.unop))
      (spMonoidalGenerator l E T D r M n U 1 x)
      (spMonoidalGenerator l E T D r N n U a y)

/-- The inverse multiplies the quotient coefficients, without flatness assumptions.
Source: blueprint paragraph (3)
(blueprint: def-sp-reduction-monoidal-comparison-data). -/
def SpReductionInverse (D : SpCoefficientTowersAbelian l E T)
    (r : SpReductionTower l E T D) (W : SpReductionMonoidalData l E T D r) : Prop :=
  ∀ (M N : spIntegralSectionModules l E T) (n : ℕ) (U : T.ProEtᵒᵖ)
    (x : M.val.obj U) (y : N.val.obj U)
    (a b : ((spCoefficientCommRings.{u, u} l E T).obj (op n)).obj.obj U),
    ((W.ordinary M N).inv.val.app (op (n, U.unop)))
      (tensorSection.{u + 1, u, u + 1} (coefficientSequenceTopology (Scheme.ProEt.topology T))
        (spMonoidalSystemRing l E T) _ _ (op (n, U.unop))
        (spMonoidalGenerator l E T D r M n U a x)
        (spMonoidalGenerator l E T D r N n U b y)) =
    spMonoidalGenerator l E T D r _ n U (a * b)
      (tensorSection.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
        (spIntegralSectionRing l E T) M N U x y)

/-- Its restriction to each total summand is exactly ordinary inverse balancing.
Source: blueprint paragraph (3)
(blueprint: def-sp-reduction-monoidal-comparison-data). -/
def SpReductionSummand (D : SpCoefficientTowersAbelian l E T)
    (r : SpReductionTower l E T D) (W : SpReductionMonoidalData l E T D r) : Prop :=
  ∀ (P Q : CochainComplex (spIntegralSectionModules l E T) ℤ)
    (p q k : ℤ) (h : p + q = k),
    tensorSummand.{u + 1, u, u + 1} (coefficientSequenceTopology (Scheme.ProEt.topology T))
      (spMonoidalSystemRing l E T)
      (((spMonoidalOrdinary l E T D r).mapHomologicalComplex (.up ℤ)).obj P)
      (((spMonoidalOrdinary l E T D r).mapHomologicalComplex (.up ℤ)).obj Q) p q k h ≫
        (W.chain.hom.app (P,Q)).f k =
    (W.ordinary (P.X p) (Q.X q)).inv ≫ (spMonoidalOrdinary l E T D r).map
      (tensorSummand.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
        (spIntegralSectionRing l E T) P Q p q k h)

/-- Unbounded source totals are again K-flat with flat terms.
Source: blueprint paragraph (3)
(blueprint: def-sp-reduction-monoidal-comparison-data). -/
def SpReductionTotalKflat (D : SpCoefficientTowersAbelian l E T)
    (r : SpReductionTower l E T D) (_W : SpReductionMonoidalData l E T D r) : Prop :=
  ∀ (P Q : CochainComplex (spIntegralSectionModules l E T) ℤ),
    P.IsKFlatIndependentCoefficients → Q.IsKFlatIndependentCoefficients →
    flatTerms.{u + 1, u, u + 1} (Scheme.ProEt.topology T) (spIntegralSectionRing l E T) P →
    flatTerms.{u + 1, u, u + 1} (Scheme.ProEt.topology T) (spIntegralSectionRing l E T) Q →
    ((spMonoidalIntegralTotal l E T).obj (P,Q)).IsKFlatIndependentCoefficients ∧
      flatTerms.{u + 1, u, u + 1} (Scheme.ProEt.topology T) (spIntegralSectionRing l E T)
        ((spMonoidalIntegralTotal l E T).obj (P,Q))

/-- Simultaneous reduction preserves the representative class on the sequence site.
Source: blueprint paragraph (3)
(blueprint: def-sp-reduction-monoidal-comparison-data). -/
def SpReductionSystemKflat (D : SpCoefficientTowersAbelian l E T)
    (r : SpReductionTower l E T D) (_W : SpReductionMonoidalData l E T D r) : Prop :=
  ∀ (P : CochainComplex (spIntegralSectionModules l E T) ℤ),
    P.IsKFlatIndependentCoefficients →
    flatTerms.{u + 1, u, u + 1} (Scheme.ProEt.topology T) (spIntegralSectionRing l E T) P →
    CochainComplex.IsKFlatIndependentCoefficients
      (((spMonoidalOrdinary l E T D r).mapHomologicalComplex (.up ℤ)).obj P)

/-- Each quotient reduction is K-flat over its actual quotient ring.
Source: blueprint paragraph (3)
(blueprint: def-sp-reduction-monoidal-comparison-data). -/
def SpReductionLevelKflat (D : SpCoefficientTowersAbelian l E T)
    (r : SpReductionTower l E T D) (_W : SpReductionMonoidalData l E T D r) : Prop :=
  ∀ (P : CochainComplex (spIntegralSectionModules l E T) ℤ),
    P.IsKFlatIndependentCoefficients →
    flatTerms.{u + 1, u, u + 1} (Scheme.ProEt.topology T) (spIntegralSectionRing l E T) P →
    ∀ n : ℕ,
      CochainComplex.IsKFlatIndependentCoefficients
        ((Functor.mapHomologicalComplex
          (D.scalar (spIntegralReductionScalar l E T r.coefficient n)).model.E
          (.up ℤ)).obj P)

/-- The whole-system derived comparison is the specified chain isomorphism.
Source: blueprint paragraph (3)
(blueprint: def-sp-reduction-monoidal-comparison-data). -/
def SpReductionDerived (D : SpCoefficientTowersAbelian l E T)
    (r : SpReductionTower l E T D) (W : SpReductionMonoidalData l E T D r)
    (hSystem : SpReductionSystemKflat l E T D r W) : Prop :=
  ∀ (P Q : CochainComplex (spIntegralSectionModules l E T) ℤ)
    (hP : P.IsKFlatIndependentCoefficients) (hQ : Q.IsKFlatIndependentCoefficients)
    (fP : flatTerms.{u + 1, u, u + 1} (Scheme.ProEt.topology T) (spIntegralSectionRing l E T) P)
    (fQ : flatTerms.{u + 1, u, u + 1} (Scheme.ProEt.topology T) (spIntegralSectionRing l E T) Q),
    (spMonoidalReduction l E T D r).map
      (tensorModelIso.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
        (spIntegralSectionRing l E T) W.source W.sourceModel P Q hP hQ).hom ≫
      W.μ.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
      W.target.tensor.map (Prod.mkHom ((spMonoidalCounit l E T D r).app P)
        ((spMonoidalCounit l E T D r).app Q)) =
    (spMonoidalCounit l E T D r).app ((spMonoidalIntegralTotal l E T).obj (P,Q)) ≫
      DerivedCategory.Q.map (W.chain.inv.app (P,Q)) ≫
      (tensorModelIso.{u + 1, u, u + 1} (coefficientSequenceTopology (Scheme.ProEt.topology T))
        (spMonoidalSystemRing l E T) W.target W.targetModel
        (((spMonoidalOrdinary l E T D r).mapHomologicalComplex (.up ℤ)).obj P)
        (((spMonoidalOrdinary l E T D r).mapHomologicalComplex (.up ℤ)).obj Q)
        (hSystem P hP fP) (hSystem Q hQ fQ)).hom

/-- The comparison data together with every normalized representative equation.
Source: blueprint direct-image proof (3)
(blueprint: def-sp-reduction-monoidal-comparison-data). -/
structure SpReductionMonoidalTower (D : SpCoefficientTowersAbelian l E T)
    (r : SpReductionTower l E T D) extends SpReductionMonoidalData l E T D r where
  /-- The strong monoidal tensorator is precisely the inverse of mu. -/
  monoidal_tensor : SpReductionMonoidalTensor l E T D r toSpReductionMonoidalData
  /-- Forward balancing on every sheafified pure tensor. -/
  forward : SpReductionForward l E T D r toSpReductionMonoidalData
  /-- The inverse multiplies the quotient coefficients, without flatness assumptions. -/
  inverse : SpReductionInverse l E T D r toSpReductionMonoidalData
  /-- Its restriction to each total summand is exactly ordinary inverse balancing. -/
  summand : SpReductionSummand l E T D r toSpReductionMonoidalData
  /-- Unbounded source totals are again K-flat with flat terms. -/
  total_kflat : SpReductionTotalKflat l E T D r toSpReductionMonoidalData
  /-- Simultaneous reduction preserves the representative class on the sequence site. -/
  system_kflat : SpReductionSystemKflat l E T D r toSpReductionMonoidalData
  /-- Each quotient reduction is K-flat over its actual quotient ring. -/
  level_kflat : SpReductionLevelKflat l E T D r toSpReductionMonoidalData
  /-- The whole-system derived comparison is the specified chain isomorphism. -/
  derived : SpReductionDerived l E T D r toSpReductionMonoidalData system_kflat


/-- The geometric inverse image on the sequence sites, by Kan extension and sheafification.
Source: Stacks 00VC and Zheng 4.1
(blueprint: def-sp-reduction-monoidal-comparison-data). -/
abbrev spMonoidalSequenceInverseImage {T' : Scheme.{u}} (g : T' ⟶ T) :=
  sheafToPresheaf (coefficientSequenceTopology (Scheme.ProEt.topology T)) (Type (u + 1)) ⋙
    ((𝟭 ℕ).prod (Scheme.proEtaleBaseChange g)).op.lan ⋙
    presheafToSheaf (coefficientSequenceTopology (Scheme.ProEt.topology T')) (Type (u + 1))

/-- A canonical Kan-extension generator of inverse image of a sheaf of sets.
Source: Stacks 00VC (blueprint: def-sp-reduction-monoidal-comparison-data). -/
def spMonoidalInverseSection {C C' : Type (u + 1)} [Category.{u} C] [Category.{u} C']
    (J : GrothendieckTopology C) (J' : GrothendieckTopology C')
    [HasWeakSheafify J' (Type (u + 1))] (G : C ⥤ C')
    (M : Sheaf J (Type (u + 1))) (V : Cᵒᵖ) (x : M.obj.obj V) :
    ((sheafToPresheaf J (Type (u + 1)) ⋙ G.op.lan ⋙
      presheafToSheaf J' (Type (u + 1))).obj M).obj.obj (G.op.obj V) :=
  (toSheafify J' (G.op.lan.obj M.obj)).app (G.op.obj V)
    (((G.op.lanAdjunction (Type (u + 1))).unit.app M.obj).app V x)

/-- A pulled-back integral module section in the actual inverse-image lift.
Source: Stacks 03D2 (blueprint: def-sp-reduction-monoidal-comparison-data). -/
def spMonoidalPullSection {T' : Scheme.{u}} (g : T' ⟶ T)
    {R : Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}}
    {R' : Sheaf (Scheme.ProEt.topology T') CommRingCat.{u + 1}}
    (I : SheafOfModules.AlgebraicInverseImage
      (Scheme.proEtaleSheafInverseImage g (Type (u + 1))) R R')
    (M : SemilinearSections.Mod.{u + 1, u, u + 1} (Scheme.ProEt.topology T) R)
    (V : T.ProEtᵒᵖ) (x : M.val.obj V) :
    (I.modules.obj M).val.obj ((Scheme.proEtaleBaseChange g).op.obj V) :=
  ((I.moduleUnderlying.inv.app M).hom.app ((Scheme.proEtaleBaseChange g).op.obj V))
    (spMonoidalInverseSection (Scheme.ProEt.topology T) (Scheme.ProEt.topology T')
      (Scheme.proEtaleBaseChange g) _ V x)

/-- A pulled-back system section in the actual sequence inverse-image lift.
Source: Stacks 03D2 (blueprint: def-sp-reduction-monoidal-comparison-data). -/
def spMonoidalSystemPullSection {T' : Scheme.{u}} (g : T' ⟶ T)
    (I : SheafOfModules.AlgebraicInverseImage (spMonoidalSequenceInverseImage T g)
      (spMonoidalSystemRing l E T) (spMonoidalSystemRing l E T'))
    (M : spMonoidalSystems l E T) (V : (ℕ × T.ProEt)ᵒᵖ) (x : M.val.obj V) :
    (I.modules.obj M).val.obj (((𝟭 ℕ).prod (Scheme.proEtaleBaseChange g)).op.obj V) :=
  ((I.moduleUnderlying.inv.app M).hom.app
    (((𝟭 ℕ).prod (Scheme.proEtaleBaseChange g)).op.obj V))
    (spMonoidalInverseSection (coefficientSequenceTopology (Scheme.ProEt.topology T))
      (coefficientSequenceTopology (Scheme.ProEt.topology T'))
      ((𝟭 ℕ).prod (Scheme.proEtaleBaseChange g)) _ V x)


/-- Pullback of a coefficient section under an algebraic inverse-image identification.
Source: Stacks 00YV, 03D2 (blueprint: def-sp-reduction-monoidal-comparison-data). -/
def spMonoidalPullCoefficient {T' : Scheme.{u}} (g : T' ⟶ T)
    {R : Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}}
    {R' : Sheaf (Scheme.ProEt.topology T') CommRingCat.{u + 1}}
    (I : SheafOfModules.AlgebraicInverseImage
      (Scheme.proEtaleSheafInverseImage g (Type (u + 1))) R R')
    (V : T.ProEtᵒᵖ) (a : R.obj.obj V) :
    R'.obj.obj ((Scheme.proEtaleBaseChange g).op.obj V) :=
  I.ringUnderlying.hom.hom.app ((Scheme.proEtaleBaseChange g).op.obj V)
    (spMonoidalInverseSection (Scheme.ProEt.topology T) (Scheme.ProEt.topology T')
      (Scheme.proEtaleBaseChange g) _ V a)

/-- Constant quotient sections, in the existing ell-power coefficient sheaf.
Source: blueprint coefficient convention
(blueprint: def-sp-reduction-monoidal-comparison-data). -/
def spMonoidalConstantSection (n : ℕ) (V : T.ProEtᵒᵖ)
    (a : ULift.{u + 1} (Padic.coefficientExtensionIntegers l E ⧸
      spEllIdeal l E ^ (n + 1))) :
    ((constantSheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}).obj
      (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E ⧸
        spEllIdeal l E ^ (n + 1))))).obj.obj V :=
  (@toSheafify.{u, u + 1, u + 1, u + 2} T.ProEt inferInstance
    (Scheme.ProEt.topology T) CommRingCat.{u + 1} inferInstance inferInstance
    ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of.{u + 1}
      (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E ⧸
        spEllIdeal l E ^ (n + 1)))))).app V a

/-- Evaluation on the sequence site, with all scalar maps unchanged.
Source: Zheng 4.1 (blueprint: def-sp-reduction-monoidal-comparison-data). -/
abbrev spMonoidalEvaluation (n : ℕ) :=
  SheafOfModules.systemSequenceEvaluation (spCoefficientCommRings.{u, u} l E T) n

/-- Canonical inverse images and reduction comparison, with generator normalizations.
The coefficient equations specify the canonical constant-quotient identifications and
fix the integral identification by all completion projections. The system ring equation
uses those very identifications. The final square specifies nu before evaluation.
Source: blueprint integral direct-image proof (3); Stacks 03EL and 0D6D
(blueprint: def-sp-reduction-monoidal-comparison-data). -/
structure SpReductionPullbackData (D : SpCoefficientTowersAbelian l E T)
    (r : SpReductionTower l E T D) {T' : Scheme.{u}} (g : T' ⟶ T)
    (D' : SpCoefficientTowersAbelian l E T') (r' : SpReductionTower l E T' D') where
  /-- Algebraic inverse image over the canonical integral coefficient identification. -/
  integral : SheafOfModules.AlgebraicInverseImage
    (Scheme.proEtaleSheafInverseImage g (Type (u + 1)))
    (spIntegralSectionRing l E T) (spIntegralSectionRing l E T')
  /-- Algebraic inverse image over the canonical constant quotient identifications. -/
  level : ∀ n : ℕ, SheafOfModules.AlgebraicInverseImage
    (Scheme.proEtaleSheafInverseImage g (Type (u + 1)))
    ((spCoefficientCommRings.{u, u} l E T).obj (op n))
    ((spCoefficientCommRings.{u, u} l E T').obj (op n))
  /-- Algebraic inverse image on the actual ringed sequence sites. -/
  system : SheafOfModules.AlgebraicInverseImage (spMonoidalSequenceInverseImage T g)
    (spMonoidalSystemRing l E T) (spMonoidalSystemRing l E T')
  /-- Integral module inverse image is additive. -/
  [integralAdditive : integral.modules.Additive]
  /-- Integral inverse image is left exact. -/
  [integralLimits : PreservesFiniteLimits integral.modules]
  /-- Integral inverse image is right exact. -/
  [integralColimits : PreservesFiniteColimits integral.modules]
  /-- System inverse image is additive. -/
  [systemAdditive : system.modules.Additive]
  /-- System inverse image is left exact. -/
  [systemLimits : PreservesFiniteLimits system.modules]
  /-- System inverse image is right exact. -/
  [systemColimits : PreservesFiniteColimits system.modules]
  /-- Ordinary evaluation of system pullback. -/
  evaluation : ∀ n : ℕ,
    system.modules ⋙ spMonoidalEvaluation l E T' n ≅
      spMonoidalEvaluation l E T n ⋙ (level n).modules
  /-- The canonical ordinary inverse-image/scalar comparison of whole systems. -/
  ordinary : integral.modules ⋙ spMonoidalOrdinary l E T' D' r' ≅
    spMonoidalOrdinary l E T D r ⋙ system.modules
  /-- The canonical comparison is a natural isomorphism of whole derived systems. -/
  ν : integral.modules.mapDerivedCategory ⋙ spMonoidalReduction l E T' D' r' ≅
    spMonoidalReduction l E T D r ⋙ system.modules.mapDerivedCategory

attribute [instance] SpReductionPullbackData.integralAdditive
  SpReductionPullbackData.integralLimits SpReductionPullbackData.integralColimits
  SpReductionPullbackData.systemAdditive SpReductionPullbackData.systemLimits
  SpReductionPullbackData.systemColimits

/-- These coefficient identifications carry each constant section to itself.
Source: blueprint paragraph (3)
(blueprint: def-sp-reduction-monoidal-comparison-data). -/
def SpPullbackConstant (D : SpCoefficientTowersAbelian l E T)
    (r : SpReductionTower l E T D) {T' : Scheme.{u}} (g : T' ⟶ T)
    (D' : SpCoefficientTowersAbelian l E T') (r' : SpReductionTower l E T' D')
    (W : SpReductionPullbackData l E T D r g D' r') : Prop :=
  ∀ (n : ℕ) (V : T.ProEtᵒᵖ)
    (a : ULift.{u + 1} (Padic.coefficientExtensionIntegers l E ⧸
      spEllIdeal l E ^ (n + 1))),
    spMonoidalPullCoefficient T g (W.level n) V (spMonoidalConstantSection l E T n V a) =
      spMonoidalConstantSection l E T' n ((Scheme.proEtaleBaseChange g).op.obj V) a

/-- The integral identification commutes with every actual quotient augmentation.
Source: blueprint paragraph (3)
(blueprint: def-sp-reduction-monoidal-comparison-data). -/
def SpPullbackProjection (D : SpCoefficientTowersAbelian l E T)
    (r : SpReductionTower l E T D) {T' : Scheme.{u}} (g : T' ⟶ T)
    (D' : SpCoefficientTowersAbelian l E T') (r' : SpReductionTower l E T' D')
    (W : SpReductionPullbackData l E T D r g D' r') : Prop :=
  ∀ (n : ℕ) (V : T.ProEtᵒᵖ)
    (a : (spIntegralSectionRing l E T).obj.obj V),
    spMonoidalPullCoefficient T g (W.level n) V
      ((spIntegralReductionScalar l E T r.coefficient n).hom.app V a) =
    (spIntegralReductionScalar l E T' r'.coefficient n).hom.app
      ((Scheme.proEtaleBaseChange g).op.obj V)
      (spMonoidalPullCoefficient T g W.integral V a)

/-- Its structural ring identification is exactly the level coefficient identification.
Source: blueprint paragraph (3)
(blueprint: def-sp-reduction-monoidal-comparison-data). -/
def SpPullbackSystemRing (D : SpCoefficientTowersAbelian l E T)
    (r : SpReductionTower l E T D) {T' : Scheme.{u}} (g : T' ⟶ T)
    (D' : SpCoefficientTowersAbelian l E T') (r' : SpReductionTower l E T' D')
    (W : SpReductionPullbackData l E T D r g D' r') : Prop :=
  ∀ (n : ℕ) (V : T.ProEtᵒᵖ)
    (a : ((spCoefficientCommRings.{u, u} l E T).obj (op n)).obj.obj V),
    W.system.ringUnderlying.hom.hom.app (op (n, (Scheme.proEtaleBaseChange g).obj V.unop))
      (spMonoidalInverseSection (coefficientSequenceTopology (Scheme.ProEt.topology T))
        (coefficientSequenceTopology (Scheme.ProEt.topology T'))
        ((𝟭 ℕ).prod (Scheme.proEtaleBaseChange g)) _ (op (n,V.unop)) a) =
    spMonoidalPullCoefficient T g (W.level n) V a

/-- The evaluation identification fixes every inverse-image section generator.
Source: blueprint paragraph (3)
(blueprint: def-sp-reduction-monoidal-comparison-data). -/
def SpPullbackEvaluationSection (D : SpCoefficientTowersAbelian l E T)
    (r : SpReductionTower l E T D) {T' : Scheme.{u}} (g : T' ⟶ T)
    (D' : SpCoefficientTowersAbelian l E T') (r' : SpReductionTower l E T' D')
    (W : SpReductionPullbackData l E T D r g D' r') : Prop :=
  ∀ (n : ℕ) (M : spMonoidalSystems l E T) (V : T.ProEtᵒᵖ)
    (x : M.val.obj (op (n,V.unop))),
    ((W.evaluation n).hom.app M).val.app ((Scheme.proEtaleBaseChange g).op.obj V)
      (spMonoidalSystemPullSection l E T g W.system M (op (n,V.unop)) x) =
    spMonoidalPullSection T g (W.level n) ((spMonoidalEvaluation l E T n).obj M) V x

/-- It carries each pulled-back tensor to the same quotient tensor.
Source: blueprint paragraph (3)
(blueprint: def-sp-reduction-monoidal-comparison-data). -/
def SpPullbackOrdinarySection (D : SpCoefficientTowersAbelian l E T)
    (r : SpReductionTower l E T D) {T' : Scheme.{u}} (g : T' ⟶ T)
    (D' : SpCoefficientTowersAbelian l E T') (r' : SpReductionTower l E T' D')
    (W : SpReductionPullbackData l E T D r g D' r') : Prop :=
  ∀ (M : spIntegralSectionModules l E T) (n : ℕ) (V : T.ProEtᵒᵖ)
    (x : M.val.obj V)
    (a : ((spCoefficientCommRings.{u, u} l E T).obj (op n)).obj.obj V),
    (W.ordinary.inv.app M).val.app (op (n, (Scheme.proEtaleBaseChange g).obj V.unop))
      (spMonoidalSystemPullSection l E T g W.system
        ((spMonoidalOrdinary l E T D r).obj M) (op (n,V.unop))
        (spMonoidalGenerator l E T D r M n V a x)) =
    spMonoidalGenerator l E T' D' r' (W.integral.modules.obj M) n
      ((Scheme.proEtaleBaseChange g).op.obj V)
      (spMonoidalPullCoefficient T g (W.level n) V a)
      (spMonoidalPullSection T g W.integral M V x)

/-- Its value on a flat-term K-flat representative is exactly ordinary pullback/scalar.
Source: blueprint paragraph (3)
(blueprint: def-sp-reduction-monoidal-comparison-data). -/
def SpPullbackDerived (D : SpCoefficientTowersAbelian l E T)
    (r : SpReductionTower l E T D) {T' : Scheme.{u}} (g : T' ⟶ T)
    (D' : SpCoefficientTowersAbelian l E T') (r' : SpReductionTower l E T' D')
    (W : SpReductionPullbackData l E T D r g D' r') : Prop :=
  ∀ (P : CochainComplex (spIntegralSectionModules l E T) ℤ)
    (_hP : P.IsKFlatIndependentCoefficients)
    (_fP : flatTerms.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
      (spIntegralSectionRing l E T) P),
    (spMonoidalReduction l E T' D' r').map
      ((Functor.mapDerivedCategoryFactors W.integral.modules).hom.app P) ≫
      (spMonoidalCounit l E T' D' r').app
        ((W.integral.modules.mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex W.ordinary (.up ℤ)).hom.app P) =
    W.ν.hom.app (DerivedCategory.Q.obj P) ≫
      W.system.modules.mapDerivedCategory.map ((spMonoidalCounit l E T D r).app P) ≫
      (Functor.mapDerivedCategoryFactors W.system.modules).hom.app
        (((spMonoidalOrdinary l E T D r).mapHomologicalComplex (.up ℤ)).obj P)

/-- The geometric comparison with all canonical coefficient and model equations.
Source: blueprint direct-image proof (3)
(blueprint: def-sp-reduction-monoidal-comparison-data). -/
structure SpReductionPullbackTower (D : SpCoefficientTowersAbelian l E T)
    (r : SpReductionTower l E T D) {T' : Scheme.{u}} (g : T' ⟶ T)
    (D' : SpCoefficientTowersAbelian l E T') (r' : SpReductionTower l E T' D') extends
    SpReductionPullbackData l E T D r g D' r' where
  /-- These coefficient identifications carry each constant section to itself. -/
  constant : SpPullbackConstant l E T D r g D' r' toSpReductionPullbackData
  /-- The integral identification commutes with every actual quotient augmentation. -/
  projection : SpPullbackProjection l E T D r g D' r' toSpReductionPullbackData
  /-- Its structural ring identification is exactly the level coefficient identification. -/
  system_ring : SpPullbackSystemRing l E T D r g D' r' toSpReductionPullbackData
  /-- The evaluation identification fixes every inverse-image section generator. -/
  evaluation_section : SpPullbackEvaluationSection l E T D r g D' r' toSpReductionPullbackData
  /-- It carries each pulled-back tensor to the same quotient tensor. -/
  ordinary_section : SpPullbackOrdinarySection l E T D r g D' r' toSpReductionPullbackData
  /-- Its value on a flat-term K-flat representative is exactly ordinary pullback/scalar. -/
  derived : SpPullbackDerived l E T D r g D' r' toSpReductionPullbackData

/-- Monoidal coherence of the geometric comparison, on the existing tensor models.
Both inverse-image tensor comparisons are fixed by their pure-tensor models. The two
last equations are precisely monoidality of nu, including the tensor unit.
Source: Stacks 07A4 and 0D6D; blueprint direct-image proof (3)
(blueprint: def-sp-reduction-monoidal-comparison-data). -/
structure SpReductionPullbackCoherence (D : SpCoefficientTowersAbelian l E T)
    (r : SpReductionTower l E T D) (M : SpReductionMonoidalTower l E T D r)
    {T' : Scheme.{u}} (g : T' ⟶ T) (D' : SpCoefficientTowersAbelian l E T')
    (r' : SpReductionTower l E T' D') (M' : SpReductionMonoidalTower l E T' D' r')
    (p : SpReductionPullbackTower l E T D r g D' r') where
  /-- The integral inverse-image tensor comparison. -/
  integralTensor : M.source.tensor ⋙ p.integral.modules.mapDerivedCategory ≅
    (p.integral.modules.mapDerivedCategory.prod p.integral.modules.mapDerivedCategory) ⋙
      M'.source.tensor
  /-- Its K-flat representative normalization, before evaluation. -/
  integralModel : TensorComparisonModel.{u + 1, u, u + 1}
    (Scheme.ProEt.topology T) (Scheme.ProEt.topology T')
    (spIntegralSectionRing l E T) (spIntegralSectionRing l E T') p.integral.modules
    M.source M'.source M.sourceModel M'.sourceModel integralTensor
  /-- It pulls back actual pure tensors. -/
  integralPure : InverseTensorPure.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
    (Scheme.ProEt.topology T') (Scheme.proEtaleSheafInverseImage g (Type (u + 1)))
    (spIntegralSectionRing l E T) (spIntegralSectionRing l E T')
    p.integral integralModel.ordinary
  /-- Integral inverse image respects associators and units. -/
  integralMonoidal : @Functor.CoreMonoidal
    (DerivedCategory (spIntegralSectionModules l E T)) _ M.source.monoidal
    (DerivedCategory (spIntegralSectionModules l E T')) _ M'.source.monoidal
    p.integral.modules.mapDerivedCategory
  /-- The coherent integral tensorator is the same normalized comparison. -/
  integral_tensor : ∀ X Y : DerivedCategory (spIntegralSectionModules l E T),
    (@Functor.CoreMonoidal.μIso _ _ M.source.monoidal _ _ M'.source.monoidal
      p.integral.modules.mapDerivedCategory integralMonoidal X Y).hom =
      integralTensor.inv.app (X,Y)
  /-- The system inverse-image tensor comparison. -/
  systemTensor : M.target.tensor ⋙ p.system.modules.mapDerivedCategory ≅
    (p.system.modules.mapDerivedCategory.prod p.system.modules.mapDerivedCategory) ⋙
      M'.target.tensor
  /-- Its K-flat representative normalization in the whole system category. -/
  systemModel : TensorComparisonModel.{u + 1, u, u + 1}
    (coefficientSequenceTopology (Scheme.ProEt.topology T))
    (coefficientSequenceTopology (Scheme.ProEt.topology T'))
    (spMonoidalSystemRing l E T) (spMonoidalSystemRing l E T') p.system.modules
    M.target M'.target M.targetModel M'.targetModel systemTensor
  /-- The system comparison pulls back actual pure tensors. -/
  systemPure : InverseTensorPure.{u + 1, u, u + 1}
    (coefficientSequenceTopology (Scheme.ProEt.topology T))
    (coefficientSequenceTopology (Scheme.ProEt.topology T'))
    (spMonoidalSequenceInverseImage T g) (spMonoidalSystemRing l E T)
    (spMonoidalSystemRing l E T') p.system systemModel.ordinary
  /-- System inverse image respects associators and units. -/
  systemMonoidal : @Functor.CoreMonoidal
    (DerivedCategory (spMonoidalSystems l E T)) _ M.target.monoidal
    (DerivedCategory (spMonoidalSystems l E T')) _ M'.target.monoidal
    p.system.modules.mapDerivedCategory
  /-- Its coherent tensorator is the same normalized comparison. -/
  system_tensor : ∀ X Y : DerivedCategory (spMonoidalSystems l E T),
    (@Functor.CoreMonoidal.μIso _ _ M.target.monoidal _ _ M'.target.monoidal
      p.system.modules.mapDerivedCategory systemMonoidal X Y).hom =
      systemTensor.inv.app (X,Y)
  /-- The tensor comparison of reduction commutes with the geometric comparison. -/
  tensor : ∀ X Y : DerivedCategory (spIntegralSectionModules l E T),
    (spMonoidalReduction l E T' D' r').map (integralTensor.hom.app (X,Y)) ≫
      M'.μ.hom.app (p.integral.modules.mapDerivedCategory.obj X,
        p.integral.modules.mapDerivedCategory.obj Y) ≫
      M'.target.tensor.map (Prod.mkHom (p.ν.hom.app X) (p.ν.hom.app Y)) =
    p.ν.hom.app (M.source.tensor.obj (X,Y)) ≫
      p.system.modules.mapDerivedCategory.map (M.μ.hom.app (X,Y)) ≫
      systemTensor.hom.app ((spMonoidalReduction l E T D r).obj X,
        (spMonoidalReduction l E T D r).obj Y)
  /-- The same compatibility for the tensor unit. -/
  unit :
    (@Functor.CoreMonoidal.εIso _ _ M'.source.monoidal _ _ M'.target.monoidal
      (spMonoidalReduction l E T' D' r') M'.monoidal).hom ≫
      (spMonoidalReduction l E T' D' r').map
        (@Functor.CoreMonoidal.εIso _ _ M.source.monoidal _ _ M'.source.monoidal
          p.integral.modules.mapDerivedCategory integralMonoidal).hom ≫
      p.ν.hom.app M.source.monoidal.tensorUnit =
    (@Functor.CoreMonoidal.εIso _ _ M.target.monoidal _ _ M'.target.monoidal
      p.system.modules.mapDerivedCategory systemMonoidal).hom ≫
      p.system.modules.mapDerivedCategory.map
        (@Functor.CoreMonoidal.εIso _ _ M.source.monoidal _ _ M.target.monoidal
          (spMonoidalReduction l E T D r) M.monoidal).hom


end AlgebraicGeometry.ProEtale
