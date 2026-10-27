module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted
public import Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport
public import Sheaf.Paper.ExchangeProjectionSuppliedDomains
public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.AlgebraicGeometry.ComparisonDerivedPullbackFixed
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Sheaf.AlgebraicGeometry.AffineSpaceTopTrace
public import Sheaf.Paper.FiniteTateSiteDescent
public import Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison
public import Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate
public import Sheaf.Paper.FiniteSiteCoordinates
public import Sheaf.Paper.ProEtaleProjectiveLineTrace
public import Sheaf.Paper.ProEtaleAffineLineCounit
public import Sheaf.Paper.FiniteSiteTensorProjection
public import Sheaf.Paper.ProEtaleProjectiveCoefficient
public import Sheaf.Paper.ProEtaleProjectionIntegration
public import Sheaf.Paper.ProEtaleOrderedIntegration
public import Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Sheaf.AlgebraicGeometry.ProjectiveLineTrace
public import Sheaf.AlgebraicGeometry.AffineLinearTraceAction
import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.AlgebraicGeometry.EtaleCompactSupportComparisons
import Sheaf.AlgebraicGeometry.FiniteEtaleTwistLine
public import Sheaf.Paper.CompactSupportSiteCoherence
public import Sheaf.Paper.RefinementComparisonIsomorphism
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import all Sheaf.Paper.CompactSupportSiteCoherence
import all Sheaf.AlgebraicGeometry.AffineSpaceTopTrace
import Sheaf.AlgebraicGeometry.AffineTraceTowerCounitBaseChange
import all Sheaf.Paper.OrderedIntegrationComparison
import all Sheaf.AlgebraicGeometry.AffineTraceRightNormalForm
import Mathlib.Algebra.CharP.CharAndCard
import Mathlib.Algebra.CharP.Algebra
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantModuleValues
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison
import WeilConjectures.SixFunctors.Etale.Derived.CoefficientsShift
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel

/-! # Ordered affine-space integration and change of sites

Source: main-20261015, sec-smooth-purity/sk-prop-an,
lem-amb-affine-space-top-trace.proof.md, paragraphs 2--3; Stacks 099R, 0E48, 0GL1.
(blueprint: lem-pur-affine-tower-integration-site-transport).

All source identifications below contain only canonical comparison maps, never traces.
The pro-etale trace remains the independent ordered composite of supported-Kummer counits.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.VectorIntegrationSite.AffineTowerTransport

attribute [local implicit_reducible] Etale.cartierAbelianPro Etale.cartierAbelianEtale
attribute [local implicit_reducible] affineTraceTower
attribute [local implicit_reducible] Etale.rightDerivedLowerShriekPlus
attribute [local implicit_reducible] coherenceSiteFunctor coherenceBoundedSiteFunctor
  coherenceEtaleFunctor coherenceProEtaleFunctor

variable (A : Type (u + 1)) [CommRing A] [Finite A]


/-- Compare the ordinary ordered left tower with any compactification, using the
published compositor and the compactification-independence isomorphism.
Source: blueprint paragraphs 2--3; Stacks 0F7J
(blueprint: lem-pur-affine-tower-integration-site-transport). -/
@[irreducible]
def etaleCompact (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (c : Compactification (affineTraceProjection S d))
    (J : DerivedCategory.Plus (Sheaf (affineTraceTower S d).smallEtaleTopology
      (ModuleCat.{u + 1} A))) :
    (Etale.affineTraceLeft A S d).obj J.obj ≅
      (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj J.obj :=
  ((Etale.affineTracePlusCompatibility A S d).app J).symm ≪≫
    DerivedCategory.Plus.ι.mapIso
      (((Etale.affineTraceCompactSupportComparison A S d).app J) ≪≫
        (Etale.rightDerivedLowerShriekOfCompactificationPlusIso A
          (HasCompactification.compactification (affineTraceProjection S d)) c).app J) ≪≫
    (Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
      (ModuleCat.{u + 1} A) c).app J



variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E] (n : ℕ)

/-- The ordinary ordered affine-space trace uses the normalized projective-line datum.
This is the published counit, with no site transport in its definition.
Source: blueprint paragraphs 2--3
(blueprint: lem-pur-affine-tower-integration-site-transport). -/
@[irreducible]
def ordinaryTrace (S : Scheme.{u}) [IsNoetherian S]
    (hS : IsUnit (l : Γ(S, ⊤))) (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0) (d : ℕ) :
    (Etale.affineTraceLeft (Scheme.finiteTateCoefficient l E n) S d).obj
      ((Etale.affineTraceRight _ (l ^ (r + 1)) hA S d).obj
        (Etale.ordinaryFiniteUnit _ S)) ⟶ Etale.ordinaryFiniteUnit _ S :=
  Etale.affineTraceCounit _ (l ^ (r + 1)) hA
    (Etale.projectiveLineTraceTransport _ (pow_pos (Fact.out : l.Prime).pos _) _ hA)
    (Etale.projectiveLineTraceDatum _ (pow_pos (Fact.out : l.Prime).pos _) _ hA)
    S (by simpa only [Nat.cast_pow] using hS.pow (r + 1)) d


/-- The constant complex has its canonical degree-zero lower bound.
Source: the single-functor t-structure bound (blueprint:
lem-pur-affine-tower-integration-site-transport). -/
theorem ordinaryUnit_plus (R : Type (u + 1)) [CommRing R] (T : Scheme.{u}) :
    DerivedCategory.TStructure.t.plus (Etale.ordinaryFiniteUnit R T) :=
  ⟨0, inferInstance⟩

/-- The bounded-below ordered Tate input, using the recorded boundedness theorem.
Source: blueprint paragraph 3, shifted rank-one inputs
(blueprint: lem-pur-affine-tower-integration-site-transport). -/
abbrev input (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (l : Γ(S, ⊤))) (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0) (d : ℕ) :
    DerivedCategory.Plus (Sheaf (affineTraceTower S d).smallEtaleTopology
      (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n))) :=
  ⟨_, rightTower_plus l E n S hS r hA d
    ⟨Etale.ordinaryFiniteUnit _ S, ordinaryUnit_plus _ S⟩⟩


/-- The specified independent pro-etale trace in a chosen compactification's coordinates.
Source: blueprint paragraphs 2--3, ordered counit and canonical compactification compositor
(blueprint: lem-pur-affine-tower-integration-site-transport). -/
@[irreducible]
def proTrace (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (l : Γ(S, ⊤))) (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0) (d : ℕ)
    (c : Compactification (affineTraceProjection S d)) :
    (rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)) c).obj
      ((comparison _ _).obj (input l E n S hS r hA d).obj) ⟶
        unit (Scheme.finiteTateCoefficient l E n) S :=
  ((compactSupportSiteComparison (Scheme.finiteTateCoefficient l E n) c).app
    (input l E n S hS r hA d)).hom ≫
    (comparison _ S).map (etaleCompact _ S d c (input l E n S hS r hA d)).inv ≫
    orderedIntegration l E n S hS r hA d

/-- The ordinary trace in the same compactification's coordinates.
Source: blueprint paragraphs 2--3, canonical compactification compositor
(blueprint: lem-pur-affine-tower-integration-site-transport). -/
@[irreducible]
def etaleTrace (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (l : Γ(S, ⊤))) (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0) (d : ℕ)
    (c : Compactification (affineTraceProjection S d)) :
    (Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)) c).obj
      (input l E n S hS r hA d).obj ⟶ Etale.ordinaryFiniteUnit _ S :=
  (etaleCompact _ S d c (input l E n S hS r hA d)).inv ≫
    ordinaryTrace l E n S hS r hA d


/-- The line hypothesis, at the constant input, on precisely the coordinate lines.
The two sides use the actual restricted supported trace and actual ordinary line counit.
Source: blueprint paragraph 2 and the node's explicit line-comparison hypothesis
(blueprint: lem-pur-affine-tower-integration-site-transport). -/
def LineComparison (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (l : Γ(S, ⊤)))
    (r : ℕ) (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0) : Prop :=
  ∀ (d : ℕ),
    letI := affineTraceNoetherian S d
    HEq (orderedIntegration l E n (affineTraceTower S d)
      (affineTraceInvertible l S hS d) r hA 1)
      ((comparison (Scheme.finiteTateCoefficient l E n) (affineTraceTower S d)).map
        (ordinaryTrace l E n (affineTraceTower S d) (affineTraceInvertible l S hS d) r hA 1))

/-- The standard iterated projective-line completion of the coordinate tower.
Source: blueprint paragraphs 2--3, chosen line compactifications
(blueprint: lem-pur-affine-tower-integration-site-transport). -/
def projectiveTower (S : Scheme.{u}) : ℕ → Scheme.{u}
  | 0 => S
  | d + 1 => ProjectiveLine (projectiveTower S d)

/-- Closure under the six tower operations, with the operations as parameters.
The least closed predicate is expressed by its universal elimination property,
avoiding generated recursors over the concrete scheme gluing constructions. Source: node Step 1
(blueprint: lem-pur-affine-tower-integration-site-transport). -/
def ModelFamily {X : Type*} (affine projective tower : ℕ → X)
    (relative : X → ℕ → X) (C : ℕ → Type*) (complete : ∀ d, C d → X)
    (O : X → Type*) (restrict : ∀ T, O T → X) (T : X) : Prop :=
  ∀ P : X → Prop,
    (∀ d, P (affine d)) → (∀ d, P (projective d)) → (∀ d, P (tower d)) →
    (∀ T, P T → ∀ d, P (relative T d)) → (∀ d c, P (complete d c)) →
    (∀ T, P T → ∀ U, P (restrict T U)) → P T

/-- Schemes occurring in the tower, its standard completions, and their open restrictions.
Source: blueprint paragraphs 2--3 and node Step 1
(blueprint: lem-pur-affine-tower-integration-site-transport). -/
abbrev Model (S : Scheme.{u}) : Scheme.{u} → Prop :=
  ModelFamily (affineTraceTower S)
    (fun d ↦ ProjectiveSpace (ULift.{u} (Fin (d + 1))) S) (projectiveTower S)
    (fun T d ↦ ProjectiveSpace (ULift.{u} (Fin (d + 1))) T)
    (fun d ↦ Compactification (affineTraceProjection S d)) (fun _ c ↦ c.Z)
    (fun T ↦ T.Opens) (fun _ U ↦ U.toScheme)

namespace Model

/-- The affine coordinate towers belong to the model family. Source: node Step 1.
(blueprint: lem-pur-affine-tower-integration-site-transport). -/
theorem affine (S : Scheme.{u}) (d : ℕ) : Model S (affineTraceTower S d) :=
  fun _ ha _ _ _ _ _ ↦ ha d

/-- Projective spaces belong to the model family. Source: node Step 1.
(blueprint: lem-pur-affine-tower-integration-site-transport). -/
theorem projective (S : Scheme.{u}) (d : ℕ) :
    Model S (ProjectiveSpace (ULift.{u} (Fin (d + 1))) S) :=
  fun _ _ hp _ _ _ _ ↦ hp d

/-- Projective towers belong to the model family. Source: node Step 1.
(blueprint: lem-pur-affine-tower-integration-site-transport). -/
theorem tower (S : Scheme.{u}) (d : ℕ) : Model S (projectiveTower S d) :=
  fun _ _ _ ht _ _ _ ↦ ht d

/-- Relative projective spaces remain in the family. Source: node Step 1.
(blueprint: lem-pur-affine-tower-integration-site-transport). -/
theorem relativeProjective {S T : Scheme.{u}} (h : Model S T) (d : ℕ) :
    Model S (ProjectiveSpace (ULift.{u} (Fin (d + 1))) T) :=
  fun P ha hp ht hr hc ho ↦ hr _ (h P ha hp ht hr hc ho) d

/-- Every compactification of a tower projection belongs to the family. Source: node Step 1.
(blueprint: lem-pur-affine-tower-integration-site-transport). -/
theorem completion (S : Scheme.{u}) (d : ℕ)
    (c : Compactification (affineTraceProjection S d)) : Model S c.Z :=
  fun _ _ _ _ _ hc _ ↦ hc d c

/-- Open restrictions remain in the family. Source: node Step 1.
(blueprint: lem-pur-affine-tower-integration-site-transport). -/
theorem restriction {S T : Scheme.{u}} (h : Model S T) (U : T.Opens) :
    Model S U.toScheme :=
  fun P ha hp ht hr hc ho ↦ ho _ (h P ha hp ht hr hc ho) U

end Model

/-- Bounded constructibility and finite Tor amplitude of an ordinary input and its
canonical comparison image, using constant-module derived categories on both sites.
Source: node Step 2; finite rank-one Tate lines and Stacks 099R
(blueprint: lem-pur-affine-tower-integration-site-transport). -/
@[irreducible]
def FiniteInput (T : Scheme.{u})
    (K : Etale.DerivedCategoryModule A T) : Prop :=
  Etale.DerivedCategory.isBoundedConstructible A T K ∧
    DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) T
      ((comparison A T).obj K) ∧
    ∃ a b : ℤ, a ≤ b ∧ Etale.DerivedCategory.hasTorAmplitudeIn A T a b K ∧
      DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} A) T a b ((comparison A T).obj K)

/-- The open-restriction square for the actual ordered pro-etale trace. The source
uses the published affine compact-support exchange and normalized right-object pullback;
the other side uses the canonical pro-etale inverse-image comparison and unit map.
Source: blueprint paragraph 3, node Step 10
(blueprint: lem-pur-affine-tower-integration-site-transport). -/
def OpenCompatibility (S : Scheme.{u}) [IsNoetherian S]
    (hS : IsUnit (l : Γ(S, ⊤))) (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0) : Prop :=
  ∀ (S' : Scheme.{u}) [IsNoetherian S'] (g : S' ⟶ S) [IsOpenImmersion g] (d : ℕ),
    (comparison _ S').map
      (Etale.affineTraceExchange (Scheme.finiteTateCoefficient l E n) g d
        (input l E n S hS r hA d).obj ≫
      (Etale.affineTraceLeft _ S' d).map
        ((Etale.affineTraceRightBaseChange _ (l ^ (r + 1)) hA
          (Etale.projectiveLineTraceTransport _ (pow_pos (Fact.out : l.Prime).pos _) _ hA)
          g (by simpa only [Nat.cast_pow] using hS.pow (r + 1)) d
          (Etale.ordinaryFiniteUnit _ S)).hom ≫
        (Etale.affineTraceRight _ (l ^ (r + 1)) hA S' d).map
          (Etale.ordinaryFiniteUnitPullback _ g).hom)) ≫
      orderedIntegration l E n S' (affineTracePullbackInvertible l g hS) r hA d =
    ((pullback (Scheme.finiteTateCoefficient l E n) g).app
      ((Etale.affineTraceLeft _ S d).obj (input l E n S hS r hA d).obj)).hom ≫
      (upperStar (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)) g).leftDerivedFunctor.map
        (orderedIntegration l E n S hS r hA d) ≫
      (pullbackUnit (Scheme.finiteTateCoefficient l E n) g).hom

/-- All clauses of ordered tower transport, in canonical compact-support coordinates.
Source: blueprint paragraphs 2--3; node Steps 1--11
(blueprint: lem-pur-affine-tower-integration-site-transport). -/
def Conclusion (S : Scheme.{u}) [IsNoetherian S]
    (hS : IsUnit (l : Γ(S, ⊤))) (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0) : Prop :=
  (∀ (T : Scheme.{u}), Model S T → IsNoetherian T) ∧
  (∀ (T T' : Scheme.{u}), Model S T → Model S T' →
    ∀ f : T ⟶ T', QuasiCompact f ∧ QuasiSeparated f) ∧
  (∀ (T : Scheme.{u}) (_h : Model S T) [IsNoetherian T]
    (hT : IsUnit (l : Γ(T, ⊤))) (m : ℕ),
    FiniteInput (Scheme.finiteTateCoefficient l E n) (affineTraceTower T m)
      (input l E n T hT r hA m).obj) ∧
  (∀ (T : Scheme.{u}) (_h : Model S T) (d : ℕ),
    FiniteInput (Scheme.finiteTateCoefficient l E n) T
      (((DerivedCategory.singleFunctor _ 0).obj
        (Scheme.finiteEtaleTateSheaf (Scheme.finiteTateCoefficient l E n)
          (l ^ (r + 1)) T hA (d : ℤ)))⟦(2 * (d : ℤ))⟧)) ∧
  (∀ (d : ℕ),
    orderedIntegration l E n S hS r hA d =
      (comparison _ S).map (ordinaryTrace l E n S hS r hA d)) ∧
  (∀ (d : ℕ) (c : Compactification (affineTraceProjection S d)),
    ((compactSupportSiteComparison (Scheme.finiteTateCoefficient l E n) c).app
      (input l E n S hS r hA d)).inv ≫ proTrace l E n S hS r hA d c =
      (comparison _ S).map (etaleTrace l E n S hS r hA d c)) ∧
  (∀ (d : ℕ) (c c' : Compactification (affineTraceProjection S d)),
    (coherenceCompactificationChange (Scheme.finiteTateCoefficient l E n) c c'
      (input l E n S hS r hA d)).hom ≫ proTrace l E n S hS r hA d c' =
        proTrace l E n S hS r hA d c) ∧
  (∀ (d : ℕ) (c c' : Compactification (affineTraceProjection S d))
    (q : c.Refinement c'),
    (properTransportRefinement (Scheme.finiteTateCoefficient l E n) q
      (input l E n S hS r hA d)).hom ≫ proTrace l E n S hS r hA d c' =
        proTrace l E n S hS r hA d c) ∧
  OpenCompatibility l E n S hS r hA ∧
  (∀ (d : ℕ) (c : Compactification (affineTraceProjection S d)),
    IsIso (proTrace l E n S hS r hA d c) ∧ IsIso (etaleTrace l E n S hS r hA d c)) ∧
  HEq (orderedIntegration l E n S hS r hA 0)
    (𝟙 (unit (Scheme.finiteTateCoefficient l E n) S)) ∧
  HEq (towerSiteComparison (Scheme.finiteTateCoefficient l E n) S 0
    (input l E n S hS r hA 0))
    (Iso.refl (unit (Scheme.finiteTateCoefficient l E n) S)) ∧
  HEq (ordinaryTrace l E n S hS r hA 0)
    (𝟙 (Etale.ordinaryFiniteUnit (Scheme.finiteTateCoefficient l E n) S))

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem finiteInput_of_generic (T : Scheme.{u})
    (K : Etale.DerivedCategoryModule A T)
    (hc : Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) T K)
    (a b : ℤ) (hab : a ≤ b)
    (ht : Etale.DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} A) T a b K) :
    FiniteInput A T K := by
  unfold FiniteInput
  have hh := DerivedCategory.homologyConcentratedIn_of_torAmplitudeIn ht
  refine ⟨⟨fun i ↦ ?_, a, b, hab, fun i hi ↦ ?_⟩,
    DerivedCategory.boundedConstructible_comparisonUpperStar_mapDerivedCategory_obj hc,
    a, b, hab, Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.2 ht,
    DerivedCategory.torAmplitudeIn_mapDerivedCategory A ht⟩
  · exact (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).2 (hc.2 i)
  · rcases hi with hi | hi
    · exact (DerivedCategory.isGE_iff K a).1 hh.1 i hi
    · exact (DerivedCategory.isLE_iff K b).1 hh.2 i hi

private theorem finiteInput_shift (T : Scheme.{u})
    (K : Etale.DerivedCategoryModule A T) (h : FiniteInput A T K) (s : ℤ) :
    FiniteInput A T (K⟦s⟧) := by
  unfold FiniteInput at h
  obtain ⟨a, b, hab, ht, _⟩ := h.2.2
  have ht' := Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.1 ht
  have hc : Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) T K := by
    refine ⟨(DerivedCategory.exists_homologyConcentratedIn_iff_bounded K).1
      ⟨a, b, DerivedCategory.homologyConcentratedIn_of_torAmplitudeIn ht'⟩, ?_⟩
    intro i
    exact (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).1 (h.1.1 i)
  exact finiteInput_of_generic A T _
    ((Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) T).le_shift s _ hc)
    (a - s) (b - s) (sub_le_sub_right hab s) (ht'.shift s)

section
variable {C : Type*} [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [MonoidalPreadditive C] [Abelian.HasFunctorialFlatResolution C]

private theorem flatSingleProperty (P : DerivedCategory C → Prop)
    (hP : ∀ K, _root_.DerivedCategory.torAmplitudeIn C 0 0 K → P K)
    (F : C) (hf : ObjectProperty.flat F) :
    P ((DerivedCategory.singleFunctor C 0).obj F) :=
  hP _ (DerivedCategory.torAmplitudeIn_singleFunctor_obj_of_flat hf)
end

private theorem finiteInput_single (T : Scheme.{u})
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
    (hc : Scheme.IsConstructibleSheaf F) (hf : ObjectProperty.flat F) (s : ℤ) :
    FiniteInput A T (((DerivedCategory.singleFunctor _ 0).obj F)⟦s⟧) := by
  let := hc
  apply finiteInput_shift A T _ _ s
  apply flatSingleProperty
    (fun K ↦ Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) T K →
      FiniteInput A T K) (fun K ht hc ↦ finiteInput_of_generic A T K hc 0 0 le_rfl ht)
    F hf
  exact Etale.DerivedCategory.boundedConstructible_singleFunctor_obj F 0

private theorem finiteInput_twist (T : Scheme.{u}) (N : ℕ) (hN : 0 < N)
    (hT : IsUnit (N : Γ(T, ⊤))) (hA : (N : A) = 0) (d : ℕ) (s : ℤ) :
    FiniteInput A T (((DerivedCategory.singleFunctor _ 0).obj
      (Scheme.finiteEtaleTateSheaf A N T hA (d : ℤ)))⟦s⟧) := by
  let F := Scheme.finiteEtaleTateTwist T N A hA d
  have hst : ∀ x : T, IsUnit (N : T.presheaf.stalk x) := by
    intro x
    simpa only [map_natCast] using hT.map (T.presheaf.germ ⊤ x (by trivial)).hom
  obtain ⟨⟨cover, he⟩, hlc, hf, _⟩ :=
    Scheme.finite_etale_torsion_twist_line T N hN hst A hA d
  have hflc : Scheme.IsFiniteLocallyConstantSheaf F := by
    apply (Scheme.finite_locally_constant_module_values_iff F).1.mp
    let dat : Scheme.LocallyConstantDatum F :=
      ⟨cover, fun i ↦ Sheaf.isConstant_of_iso _ (he i).some⟩
    exact ⟨dat, fun i ↦ ⟨ModuleCat.of A A, inferInstance, he i⟩⟩
  have : Scheme.IsConstructibleSheaf F := hflc.isConstructibleSheaf
  exact finiteInput_single A T F inferInstance
    ((ObjectProperty.flat_iff_preservesFiniteLimits F).2 hf) s

private theorem finiteInput_of_iso (T : Scheme.{u})
    {K L : Etale.DerivedCategoryModule A T} (e : K ≅ L) (h : FiniteInput A T L) :
    FiniteInput A T K := by
  unfold FiniteInput at h
  obtain ⟨a, b, hab, ht, _⟩ := h.2.2
  have ht' := Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.1 ht
  have hc : Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) T L := by
    refine ⟨(DerivedCategory.exists_homologyConcentratedIn_iff_bounded L).1
      ⟨a, b, DerivedCategory.homologyConcentratedIn_of_torAmplitudeIn ht'⟩, ?_⟩
    intro i
    exact (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).1 (h.1.1 i)
  exact finiteInput_of_generic A T K
    ((Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) T).prop_of_iso
      e.symm hc) a b hab
    ((Etale.DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} A) T a b).prop_of_iso
      e.symm ht')

section
attribute [local instance] Sheaf.monoidalCategory

@[irreducible]
private def normalFormUnitIso
    (B : Type*) [Category.{u + 1} B] [Abelian B] [IsGrothendieckAbelian.{u + 1} B]
    [MonoidalCategory B] [MonoidalPreadditive B] [SymmetricCategory B] [MonoidalClosed B]
    [Abelian.HasFunctorialFlatResolution B] {T X : Scheme.{u}} (f : X ⟶ T)
    (H : DerivedCategory (Sheaf T.smallEtaleTopology B) ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology B))
    (L : DerivedCategory (Sheaf X.smallEtaleTopology B)) (s : ℤ)
    (e : H ≅ (Etale.upperStar B f).leftDerivedFunctor ⋙
      Etale.derivedTensorRight B X L ⋙ shiftFunctor _ s) :
    H.obj ((DerivedCategory.singleFunctor _ 0).obj
      ((constantSheaf T.smallEtaleTopology B).obj (MonoidalCategoryStruct.tensorUnit B))) ≅ L⟦s⟧ :=
  e.app _ ≪≫ (shiftFunctor _ s).mapIso (Etale.pullbackUnitTensor B f L)

private theorem normalFormUnitProperty
    (B : Type*) [Category.{u + 1} B] [Abelian B] [IsGrothendieckAbelian.{u + 1} B]
    [MonoidalCategory B] [MonoidalPreadditive B] [SymmetricCategory B] [MonoidalClosed B]
    [Abelian.HasFunctorialFlatResolution B] {T X : Scheme.{u}} (f : X ⟶ T)
    (H : DerivedCategory (Sheaf T.smallEtaleTopology B) ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology B))
    (L : DerivedCategory (Sheaf X.smallEtaleTopology B)) (s : ℤ)
    (P : DerivedCategory (Sheaf X.smallEtaleTopology B) → Prop)
    (hP : ∀ {K M}, (K ≅ M) → P M → P K)
    (he : Nonempty (H ≅ (Etale.upperStar B f).leftDerivedFunctor ⋙
      Etale.derivedTensorRight B X L ⋙ shiftFunctor _ s)) (hL : P (L⟦s⟧)) :
    P (H.obj ((DerivedCategory.singleFunctor _ 0).obj
      ((constantSheaf T.smallEtaleTopology B).obj (MonoidalCategoryStruct.tensorUnit B)))) := by
  obtain ⟨e⟩ := he
  exact hP (normalFormUnitIso B f H L s e) hL

private theorem finiteInput_normalForm {T X : Scheme.{u}} (f : X ⟶ T)
    (H : Etale.DerivedCategoryModule A T ⥤ Etale.DerivedCategoryModule A X)
    (L : Etale.DerivedCategoryModule A X) (s : ℤ)
    (he : Nonempty (H ≅ Etale.ordinaryFinitePullback A f ⋙
      Etale.derivedTensorRight (ModuleCat.{u + 1} A) X L ⋙ shiftFunctor _ s))
    (hL : FiniteInput A X (L⟦s⟧)) :
    FiniteInput A X (H.obj (Etale.ordinaryFiniteUnit A T)) := by
  exact normalFormUnitProperty (ModuleCat.{u + 1} A) f H L s (FiniteInput A X)
    (fun e h ↦ finiteInput_of_iso A _ e h) he hL

private theorem finiteInput_right (T : Scheme.{u}) [IsNoetherian T]
    (N : ℕ) (hN : 0 < N) (hT : IsUnit (N : Γ(T, ⊤))) (hA : (N : A) = 0)
    (d : ℕ) :
    FiniteInput A (affineTraceTower T d)
      ((Etale.affineTraceRight A N hA T d).obj (Etale.ordinaryFiniteUnit A T)) := by
  apply finiteInput_normalForm A (affineTraceProjection T d) _ _ _
    (Etale.affineTraceRight_normalForm A N hN hA T hT d).1
  exact finiteInput_twist A _ N hN (affineTraceInvertible N T hT d) hA d _

end


private theorem ordinaryTrace_isIso (S : Scheme.{u}) [IsNoetherian S]
    (hS : IsUnit (l : Γ(S, ⊤))) (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0) (d : ℕ) :
    IsIso (ordinaryTrace l E n S hS r hA d) := by
  unfold ordinaryTrace Etale.affineTraceCounit
  exact Etale.towerCounit_isIso _ _ (pow_pos (Fact.out : l.Prime).pos _) _ _ _ S _ d _

private theorem compact_trace_comparison (S : Scheme.{u}) [IsNoetherian S]
    (hS : IsUnit (l : Γ(S, ⊤))) (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0) (d : ℕ)
    (h : orderedIntegration l E n S hS r hA d =
      (comparison _ S).map (ordinaryTrace l E n S hS r hA d))
    (c : Compactification (affineTraceProjection S d)) :
    ((compactSupportSiteComparison (Scheme.finiteTateCoefficient l E n) c).app
      (input l E n S hS r hA d)).inv ≫ proTrace l E n S hS r hA d c =
      (comparison _ S).map (etaleTrace l E n S hS r hA d c) := by
  unfold proTrace etaleTrace
  rw [Iso.inv_hom_id_assoc, h, Functor.map_comp]

private theorem compactification_coordinate_square (S : Scheme.{u}) [IsNoetherian S]
    (d : ℕ) (c c' : Compactification (affineTraceProjection S d))
    (J : DerivedCategory.Plus (Sheaf (affineTraceTower S d).smallEtaleTopology
      (ModuleCat.{u + 1} A))) :
    (comparison A S).map (etaleCompact A S d c J).hom ≫
        ((compactSupportSiteComparison A c).app J).inv ≫
        (coherenceCompactificationChange A c c' J).hom =
      (comparison A S).map (etaleCompact A S d c' J).hom ≫
        ((compactSupportSiteComparison A c').app J).inv := by
  let := affineTraceNoetherian S d
  let c₀ := HasCompactification.compactification (affineTraceProjection S d)
  let ch := Etale.rightDerivedLowerShriekOfCompactificationPlusIso A
    (f := affineTraceProjection S d)
  let V := comparison A S
  let e := fun c : Compactification (affineTraceProjection S d) ↦
    (Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
      (ModuleCat.{u + 1} A) c).app J
  have h := compactification_change_square A c c' J
  have h' : V.map (DerivedCategory.Plus.ι.map ((ch c c').hom.app J)) ≫
        V.map (e c').hom ≫ ((compactSupportSiteComparison A c').app J).inv =
      V.map (e c).hom ≫ ((compactSupportSiteComparison A c).app J).inv ≫
        (coherenceCompactificationChange A c c' J).hom := by
    dsimp only [coherenceSiteFunctor, coherenceBoundaryIso,
      compactExchangeTransportComparison, coherenceEtaleChangeIso, Iso.trans_hom,
      Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Iso.symm_hom,
      NatTrans.comp_app, Iso.app_inv, Iso.app_hom] at h
    dsimp only [Functor.comp_obj] at h
    repeat' erw [Category.id_comp] at h
    simp only [Category.assoc] at h
    simpa only [V, e, ch, comparison, geoP1Comparison, Iso.app_hom, Iso.app_inv,
      Category.id_comp, Category.comp_id, Category.assoc] using h
  unfold etaleCompact
  simp only [Iso.trans_hom, Iso.app_hom, Functor.map_comp]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_inv,
    Functor.map_comp, Category.assoc]
  dsimp only [V, e, ch] at h'
  simp only [Iso.app_hom, Iso.app_inv] at h'
  with_unfolding_all rw [← h']
  have ht := congrArg (fun z ↦ z.hom.app J)
    (Etale.rightDerivedLowerShriekOfCompactificationPlusIso_trans A c₀ c c')
  simp only [Iso.trans_hom, NatTrans.comp_app] at ht
  simp only [← Functor.map_comp_assoc]
  dsimp only [Iso.app_hom]
  with_unfolding_all rw [ht]

private theorem compact_coordinate_change (S : Scheme.{u}) [IsNoetherian S]
    (d : ℕ) (c c' : Compactification (affineTraceProjection S d))
    (J : DerivedCategory.Plus (Sheaf (affineTraceTower S d).smallEtaleTopology
      (ModuleCat.{u + 1} A))) {Z : DerivedCategory (Sheaf (Scheme.ProEt.topology S)
        (ModuleCat.{u + 1} A))}
    (v : (comparison A S).obj ((Etale.affineTraceLeft A S d).obj J.obj) ⟶ Z) :
    (coherenceCompactificationChange A c c' J).hom ≫
        ((compactSupportSiteComparison A c').app J).hom ≫
        (comparison A S).map (etaleCompact A S d c' J).inv ≫ v =
      ((compactSupportSiteComparison A c).app J).hom ≫
        (comparison A S).map (etaleCompact A S d c J).inv ≫ v := by
  have h := compactification_coordinate_square A S d c c' J
  apply (cancel_epi ((comparison A S).map (etaleCompact A S d c J).hom ≫
    ((compactSupportSiteComparison A c).app J).inv)).1
  simp only [Category.assoc]
  rw [reassoc_of% h]
  simp only [Iso.inv_hom_id_assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id]

private theorem compact_trace_change (S : Scheme.{u}) [IsNoetherian S]
    (hS : IsUnit (l : Γ(S, ⊤))) (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0) (d : ℕ)
    (c c' : Compactification (affineTraceProjection S d)) :
    (coherenceCompactificationChange (Scheme.finiteTateCoefficient l E n) c c'
      (input l E n S hS r hA d)).hom ≫ proTrace l E n S hS r hA d c' =
        proTrace l E n S hS r hA d c := by
  unfold proTrace
  exact compact_coordinate_change _ S d c c' _ _

private theorem refinement_change (S : Scheme.{u}) [IsNoetherian S]
    (d : ℕ) (c c' : Compactification (affineTraceProjection S d)) (q : c.Refinement c')
    (J : DerivedCategory.Plus (Sheaf (affineTraceTower S d).smallEtaleTopology
      (ModuleCat.{u + 1} A))) :
    properTransportRefinement A q J = coherenceCompactificationChange A c c' J := by
  let := affineTraceNoetherian S d
  have hr := refinement_site_square A q J
  rw [Etale.rightDerivedLowerShriekOfCompactificationPlusRefinementIso_eq] at hr
  have hc := compactification_change_square A c c' J
  apply Iso.ext
  apply (cancel_epi ((coherenceBoundaryIso A c).hom.app J)).1
  exact hr.symm.trans hc

private theorem compact_trace_isIso (S : Scheme.{u}) [IsNoetherian S]
    (hS : IsUnit (l : Γ(S, ⊤))) (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0) (d : ℕ)
    (h : orderedIntegration l E n S hS r hA d =
      (comparison _ S).map (ordinaryTrace l E n S hS r hA d))
    (c : Compactification (affineTraceProjection S d)) :
    IsIso (proTrace l E n S hS r hA d c) ∧
      IsIso (etaleTrace l E n S hS r hA d c) := by
  have := ordinaryTrace_isIso l E n S hS r hA d
  have : IsIso (orderedIntegration l E n S hS r hA d) := by rw [h]; infer_instance
  constructor
  · unfold proTrace
    infer_instance
  · unfold etaleTrace
    infer_instance

private theorem trace_zero (S : Scheme.{u}) [IsNoetherian S]
    (hS : IsUnit (l : Γ(S, ⊤))) (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0) :
    HEq (orderedIntegration l E n S hS r hA 0)
      (𝟙 (unit (Scheme.finiteTateCoefficient l E n) S)) := by
  apply heq_of_eq
  rw [orderedIntegration_comparison]
  unfold Etale.affineTraceCounit Etale.affineTraceAdjunction
    Etale.affineTraceAdjunctionTower
  change (comparison (Scheme.finiteTateCoefficient l E n) S).map (𝟙 _) = 𝟙 _
  exact CategoryTheory.Functor.map_id _ _

private theorem unit_site_zero (T : Scheme.{u})
    (J : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (h : J.obj = Etale.ordinaryFiniteUnit A T) :
    HEq (towerSiteComparison A T 0 J) (Iso.refl (unit A T)) := by
  rcases J with ⟨K, hK⟩
  dsimp only at h
  subst K
  exact heq_of_eq (towerSiteComparison_zero A T _)

private theorem ordinary_counit_baseChange (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (t : Etale.OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      Etale.OrdinaryFiniteP1Datum A N hA t T hT)
    (hD : Etale.OrdinaryFiniteP1BaseChange A N hA t D)
    {S S' : Scheme.{u}} [IsNoetherian S] [IsNoetherian S'] (g : S' ⟶ S)
    (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) :
    Etale.affineTraceExchange A g d
        ((Etale.affineTraceRight A N hA S d).obj (Etale.ordinaryFiniteUnit A S)) ≫
      (Etale.affineTraceLeft A S' d).map
        ((Etale.affineTraceRightBaseChange A N hA t g hS d
          (Etale.ordinaryFiniteUnit A S)).hom ≫
        (Etale.affineTraceRight A N hA S' d).map
          (Etale.ordinaryFiniteUnitPullback A g).hom) ≫
      Etale.affineTraceCounit A N hA t D S'
        (affineTracePullbackInvertible N g hS) d =
    (Etale.ordinaryFinitePullback A g).map (Etale.affineTraceCounit A N hA t D S hS d) ≫
      (Etale.ordinaryFiniteUnitPullback A g).hom := by
  have h := Etale.affineTraceTowerCounit_baseChange A N hN hA t D hD g hS d
    (Etale.ordinaryFiniteUnit A S)
  have hn := (Etale.affineTraceAdjunction A N hA t D S'
    (affineTracePullbackInvertible N g hS) d).counit.naturality
      (Etale.ordinaryFiniteUnitPullback A g).hom
  simp only [Functor.comp_map, Functor.id_map] at hn
  unfold Etale.affineTraceCounit
  simp only [Functor.map_comp, Category.assoc]
  rw [hn]
  simpa only [Category.assoc] using
    congrArg (fun f ↦ f ≫ (Etale.ordinaryFiniteUnitPullback A g).hom) h

private theorem projectiveLine_baseChange (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) :
    Etale.OrdinaryFiniteP1BaseChange A N hA
      (Etale.projectiveLineTraceTransport N hN A hA)
      (Etale.projectiveLineTraceDatum N hN A hA) :=
  Classical.choose_spec (Classical.choose_spec
    (Etale.exists_ordinaryFiniteP1Adjunction N hN A hA))

private theorem canonical_counit_baseChange (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {S S' : Scheme.{u}} [IsNoetherian S] [IsNoetherian S'] (g : S' ⟶ S)
    (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) :
    Etale.affineTraceExchange A g d
        ((Etale.affineTraceRight A N hA S d).obj (Etale.ordinaryFiniteUnit A S)) ≫
      (Etale.affineTraceLeft A S' d).map
        ((Etale.affineTraceRightBaseChange A N hA
          (Etale.projectiveLineTraceTransport N hN A hA) g hS d
          (Etale.ordinaryFiniteUnit A S)).hom ≫
        (Etale.affineTraceRight A N hA S' d).map
          (Etale.ordinaryFiniteUnitPullback A g).hom) ≫
      Etale.affineTraceCounit A N hA (Etale.projectiveLineTraceTransport N hN A hA)
        (Etale.projectiveLineTraceDatum N hN A hA) S'
        (affineTracePullbackInvertible N g hS) d =
    (Etale.ordinaryFinitePullback A g).map
      (Etale.affineTraceCounit A N hA (Etale.projectiveLineTraceTransport N hN A hA)
        (Etale.projectiveLineTraceDatum N hN A hA) S hS d) ≫
      (Etale.ordinaryFiniteUnitPullback A g).hom :=
  ordinary_counit_baseChange A N hN hA _ _ (projectiveLine_baseChange A N hN hA) g hS d

private theorem ordinaryTrace_baseChange (S S' : Scheme.{u})
    [IsNoetherian S] [IsNoetherian S'] (g : S' ⟶ S)
    (hS : IsUnit (l : Γ(S, ⊤))) (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0) (d : ℕ) :
    Etale.affineTraceExchange (Scheme.finiteTateCoefficient l E n) g d
        (input l E n S hS r hA d).obj ≫
      (Etale.affineTraceLeft _ S' d).map
        ((Etale.affineTraceRightBaseChange _ (l ^ (r + 1)) hA
          (Etale.projectiveLineTraceTransport _ (pow_pos (Fact.out : l.Prime).pos _) _ hA)
          g (by simpa only [Nat.cast_pow] using hS.pow (r + 1)) d
          (Etale.ordinaryFiniteUnit _ S)).hom ≫
        (Etale.affineTraceRight _ (l ^ (r + 1)) hA S' d).map
          (Etale.ordinaryFiniteUnitPullback _ g).hom) ≫
      ordinaryTrace l E n S' (affineTracePullbackInvertible l g hS) r hA d =
    (Etale.ordinaryFinitePullback _ g).map (ordinaryTrace l E n S hS r hA d) ≫
      (Etale.ordinaryFiniteUnitPullback _ g).hom := by
  unfold ordinaryTrace
  exact canonical_counit_baseChange _ _ (pow_pos (Fact.out : l.Prime).pos _) hA g
    (by simpa only [Nat.cast_pow] using hS.pow (r + 1)) d

private theorem open_compatibility (S : Scheme.{u}) [IsNoetherian S]
    (hS : IsUnit (l : Γ(S, ⊤))) (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (h : ∀ (T : Scheme.{u}) [IsNoetherian T] (g : T ⟶ S) [IsOpenImmersion g] (d : ℕ),
      orderedIntegration l E n T (affineTracePullbackInvertible l g hS) r hA d =
        (comparison _ T).map
          (ordinaryTrace l E n T (affineTracePullbackInvertible l g hS) r hA d)) :
    OpenCompatibility l E n S hS r hA := by
  unfold OpenCompatibility
  intro S' _ g _ d
  have hs : orderedIntegration l E n S hS r hA d =
      (comparison _ S).map (ordinaryTrace l E n S hS r hA d) := by
    simpa only using h S (𝟙 S) d
  have ht := h S' g d
  rw [hs, ht]
  have hn := (pullback (Scheme.finiteTateCoefficient l E n) g).hom.naturality
    (ordinaryTrace l E n S hS r hA d)
  simp only [Functor.comp_map] at hn
  have ho := ordinaryTrace_baseChange l E n S S' g hS r hA d
  rw [← Functor.map_comp]
  trans (comparison (Scheme.finiteTateCoefficient l E n) S').map
    ((Etale.ordinaryFinitePullback _ g).map (ordinaryTrace l E n S hS r hA d) ≫
      (Etale.ordinaryFiniteUnitPullback _ g).hom)
  · exact congrArg ((comparison (Scheme.finiteTateCoefficient l E n) S').map)
      ((Category.assoc _ _ _).trans ho)
  rw [Functor.map_comp]
  unfold pullbackUnit geoP1UnitPullback
  simp only [Iso.trans_hom, Functor.mapIso_hom]
  have hh := congrArg (fun z ↦ z ≫
    (geoP1PullComparison (Scheme.finiteTateCoefficient l E n) g).hom.app
      (Etale.ordinaryFiniteUnit _ S) ≫
    (comparison (Scheme.finiteTateCoefficient l E n) S').map
      (Etale.ordinaryFiniteUnitPullback _ g).hom) hn
  unfold pullback at hh
  simp only [Iso.symm_hom, Category.assoc, Iso.inv_hom_id_app_assoc] at hh
  simpa only [pullback, Iso.app_hom, Iso.symm_hom, comparison] using hh

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem model_map {S T : Scheme.{u}} (h : Model S T) : Nonempty (T ⟶ S) := by
  apply h (fun T ↦ Nonempty (T ⟶ S))
  · intro d
    exact ⟨affineTraceProjection S d⟩
  · intro d
    exact ⟨ProjectiveSpace (ULift.{u} (Fin (d + 1))) S ↘ S⟩
  · intro d
    induction d with
    | zero => exact ⟨𝟙 S⟩
    | succ d ih =>
        obtain ⟨f⟩ := ih
        exact ⟨(ProjectiveLine (projectiveTower S d) ↘ projectiveTower S d) ≫ f⟩
  · intro T hT d
    obtain ⟨f⟩ := hT
    exact ⟨(ProjectiveSpace (ULift.{u} (Fin (d + 1))) T ↘ T) ≫ f⟩
  · intro d c
    exact ⟨c.g⟩
  · intro T hT U
    obtain ⟨f⟩ := hT
    exact ⟨U.ι ≫ f⟩

private theorem model_noetherian {S T : Scheme.{u}} [IsNoetherian S]
    (h : Model S T) : IsNoetherian T := by
  apply h (fun T ↦ IsNoetherian T)
  · intro d
    exact affineTraceNoetherian S d
  · intro d
    let := LocallyOfFiniteType.isLocallyNoetherian
      (ProjectiveSpace (ULift.{u} (Fin (d + 1))) S ↘ S)
    let := QuasiCompact.compactSpace_of_compactSpace
      (ProjectiveSpace (ULift.{u} (Fin (d + 1))) S ↘ S)
    exact ⟨⟩
  · intro d
    induction d with
    | zero => exact inferInstanceAs (IsNoetherian S)
    | succ d ih =>
        let := ih
        let := LocallyOfFiniteType.isLocallyNoetherian
          (ProjectiveLine (projectiveTower S d) ↘ projectiveTower S d)
        let := QuasiCompact.compactSpace_of_compactSpace
          (ProjectiveLine (projectiveTower S d) ↘ projectiveTower S d)
        change IsNoetherian (ProjectiveLine (projectiveTower S d))
        exact ⟨⟩
  · intro T hT d
    let := hT
    let := LocallyOfFiniteType.isLocallyNoetherian
      (ProjectiveSpace (ULift.{u} (Fin (d + 1))) T ↘ T)
    let := QuasiCompact.compactSpace_of_compactSpace
      (ProjectiveSpace (ULift.{u} (Fin (d + 1))) T ↘ T)
    exact ⟨⟩
  · intro d c
    let := LocallyOfFiniteType.isLocallyNoetherian c.g
    let := QuasiCompact.compactSpace_of_compactSpace c.g
    exact ⟨⟩
  · intro T hT U
    let := hT
    let : CompactSpace U := isCompact_iff_compactSpace.mp
      (TopologicalSpace.NoetherianSpace.isCompact _)
    exact ⟨⟩

private theorem prime_isUnit (P : WeilConjectures.PurityFiniteSetting.{u})
    (S : Scheme.{u}) (a : S ⟶ Spec (.of P.field.k)) :
    IsUnit (P.coefficients.l : Γ(S, ⊤)) := by
  let : Fintype P.field.k₀ := Fintype.ofFinite _
  let : Fact P.field.p.Prime := ⟨P.field.prime⟩
  let : CharP P.field.k₀ P.field.p := charP_of_card_eq_prime_pow (by
    rw [← Nat.card_eq_fintype_card, P.field.card_base, P.field.cardinality_eq])
  let : CharP P.field.k P.field.p :=
    charP_of_injective_algebraMap' P.field.k₀ P.field.p
  have hl : IsUnit (P.coefficients.l : P.field.k) :=
    isUnit_iff_ne_zero.mpr (CharP.cast_ne_zero_of_ne_of_prime _
      (Fact.out : P.coefficients.l.Prime) P.coefficients.different.symm)
  let f := (Scheme.ΓSpecIso (CommRingCat.of P.field.k)).inv ≫ a.appTop
  simpa only [map_natCast] using hl.map f.hom

private theorem ordered_comparison (S : Scheme.{u}) [IsNoetherian S]
    (hS : IsUnit (l : Γ(S, ⊤))) (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0) (d : ℕ) :
    orderedIntegration l E n S hS r hA d =
      (comparison _ S).map (ordinaryTrace l E n S hS r hA d) := by
  unfold ordinaryTrace
  exact orderedIntegration_comparison l E n S hS r hA d

private theorem conclusion (S : Scheme.{u}) [IsNoetherian S]
    (hS : IsUnit (l : Γ(S, ⊤))) (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0) :
    Conclusion l E n S hS r hA := by
  unfold Conclusion
  refine ⟨?_, ?_, ?_⟩
  · intro T hT
    exact model_noetherian hT
  · intro T T' hT hT' f
    let := model_noetherian hT
    let := model_noetherian hT'
    exact ⟨inferInstance, inferInstance⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro T hT _ hunit m
      exact finiteInput_right (Scheme.finiteTateCoefficient l E
        n) T (l ^ (r + 1))
        (pow_pos (Fact.out : l.Prime).pos _)
        (by simpa only [Nat.cast_pow] using hunit.pow (r + 1)) hA m
    · intro T hT d
      obtain ⟨f⟩ := @model_map S T hT
      have hu : IsUnit (l : Γ(T, ⊤)) := by
        simpa only [map_natCast] using hS.map f.appTop.hom
      exact finiteInput_twist _ T _ (pow_pos (Fact.out : l.Prime).pos _)
        (by simpa only [Nat.cast_pow] using hu.pow (r + 1)) hA d _
    · have hcompare := ordered_comparison _ _ _ S hS r hA
      refine ⟨hcompare, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact fun d c ↦ compact_trace_comparison _ _ _ _ _ _ _ _ (hcompare d) c
      · exact fun d c c' ↦ compact_trace_change _ _ _ _ _ _ _ _ c c'
      · intro d c c' q
        have hr := refinement_change (Scheme.finiteTateCoefficient l
          E n) S d c c' q
          (input l E n S hS r hA d)
        exact (congrArg (fun e ↦ e.hom ≫
          proTrace l E n S
            hS r hA d c') hr).trans
          (compact_trace_change l E n S
            hS r hA d c c')
      · apply open_compatibility
        intro T _ g _ d
        exact ordered_comparison _ _ _ T _ r hA d
      · intro d c
        exact compact_trace_isIso l E n S
          hS r hA d (hcompare d) c
      · exact trace_zero _ _ _ _ _ _ _
      · exact unit_site_zero _ S
          (input l E n S
            hS r hA 0) rfl
      · unfold ordinaryTrace Etale.affineTraceCounit Etale.affineTraceAdjunction
        exact HEq.rfl

/-- Ordered affine integration agrees across the two sites, for the supported-Kummer
pro-etale trace, every tower prefix, and the canonical compactification comparisons.
The Noetherian and unit witnesses expose consequences of the finite-field hypotheses,
so the statement adds neither separatedness of the base nor a Noetherian hypothesis.
Source: main-20261015, lem-amb-affine-space-top-trace.proof.md paragraphs 2--3;
Stacks 0E48 (projection compatibility), 0GL1 (open tensor), and 099R (comparison)
(blueprint: lem-pur-affine-tower-integration-site-transport).

Proof: (1) Finite type over the field makes S and every affine/projective tower
Noetherian; their opens are Noetherian. Noetherianity gives qcqs morphisms between
these schemes, without absolute separatedness. (2) Every coefficient is a shifted
locally free finite rank-one Tate line. Tensor and pullback preserve this description,
constructibility, and finite Tor amplitude, and finite Tate site descent identifies
its comparison image with the prescribed inverse-limit twist. (3) Apply compact-support
site coherence to the actual proper mate followed by open comparison, including its
composition, refinement and open squares. (4) The finite compact projection theorem
makes the coefficient-first projections invertible. The projection-comparison equation
identifies their inverses. (5) Compose with tensor of the assumed line-trace equation
and the right unitor. The resulting coefficient maps compare. They are the actual
restricted projective counits: use the pro-etale open tensor isomorphism and naturality
of the proper projection to commute the open counit past the inverse projection.
(6) The identical ordinary calculation, with the ordinary open tensor isomorphism
and projective-line adjunction, identifies the ordinary coefficient counit.
(7) Both ordered traces therefore satisfy the same successor composite-counit
recurrence, with identity at zero. (8) Induction, the compact-support composition
square, naturality, and the compared coefficient counit prove equality on every
prefix. (9) The proper-refinement square and a common refinement give invariance
under replacing the completion, in particular the standard projective completion.
(10) Paste the open exchange square with the ordinary trace restriction equation;
cancel the invertible site comparisons. (11) Ordinary affine-space top trace is an
isomorphism; so are the site comparisons, hence the actual pro-etale trace is an
isomorphism. At rank zero all tower maps are identities, also on the empty base.
-/
theorem affineTowerIntegrationSiteTransport (P : WeilConjectures.PurityFiniteSetting.{u})
    (S : Scheme.{u}) (a : S ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType a] [QuasiCompact a] (r : ℕ)
    (hA : ((P.coefficients.l ^ (r + 1) : ℕ) :
      Scheme.finiteTateCoefficient P.coefficients.l P.extension (P.level - 1)) = 0) :
    ∃ (hN : IsNoetherian S) (hS : IsUnit (P.coefficients.l : Γ(S, ⊤))),
      @LineComparison.{u} P.coefficients.l inferInstance P.extension inferInstance
        inferInstance inferInstance (P.level - 1) S hN hS r hA →
      @Conclusion.{u} P.coefficients.l inferInstance P.extension inferInstance
        inferInstance inferInstance (P.level - 1) S hN hS r hA := by
  let := LocallyOfFiniteType.isLocallyNoetherian a
  let := QuasiCompact.compactSpace_of_compactSpace a
  have hN : IsNoetherian S := ⟨⟩
  let := hN
  refine ⟨hN, prime_isUnit P S a, ?_⟩
  intro _hline
  exact conclusion _ _ _ S (prime_isUnit P S a) r hA

end AlgebraicGeometry.ProEtale.VectorIntegrationSite.AffineTowerTransport
