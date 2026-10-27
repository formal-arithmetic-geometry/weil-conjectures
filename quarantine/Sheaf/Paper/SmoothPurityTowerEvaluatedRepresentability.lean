/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NM
-/
module

public import Sheaf.Paper.SmoothPurityTowerCoordinateAdjunctionModels
public import Sheaf.SecSmoothPurity.ReductionExceptional
public import Sheaf.Paper.SmoothPurityTowerBinaryCounitRepresentability
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteTorComparisonNoetherian
public import Sheaf.Paper.ProEtaleFixedModuleConstructible
public import Sheaf.AlgebraicGeometry.ProEtaleTorAmplitudePresentations
import Sheaf.Paper.OpenProEtaleCounitScalar
import Sheaf.AlgebraicGeometry.EtaleOpenCoverShriekNaturalSES
import Sheaf.AlgebraicGeometry.UnboundedOpenCounitSiteTransport
import Sheaf.Paper.CompactSupportDirectImageTriangulated
import Sheaf.Paper.FiniteLocalizingExceptionalPreservation

import Sheaf.Paper.SmoothPurityTowerChartAdmissibility
import Sheaf.Paper.SmoothPurityCoefficientTowersAbelian
import Sheaf.Paper.SmoothPurityTowerShriekLevels
import Sheaf.Paper.CoefficientTowerShriekCalculus
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact

/-! # Evaluated representing pairs on smooth coordinate covers

Source: blueprint latest, sec-smooth-purity/sk-prop-sp-tower-geometric,
`sk-prop-sp-tower-geometric-gluing.proof.md`, Levels, Local pairs and Gluing
(blueprint: lem-sp-tower-evaluated-representability).

Positive level n+1 is indexed by n : ℕ. All tower categories are the recorded
ordinary derived categories; no normalization or lift of a finite test is required.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.SpTowerEvaluated
open SpCoordinateAdjunction

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (k : Type u) [Field k] (b : SpTowerShriek.Base l E)
  (o : SpTowerShriek.Operations l E b) (q : SpTowerCalculus.Coordinates l E b)
  (z : SpTowerCalculus.FiniteCoordinates l E)
  (h : SpTowerCalculus.Preservation l E k b o q)
  (cal : SpTowerCalculus.Calculus l E k b o q z h) (w : TwistFamily l E)

/-- The actual open adjunction transported by the section-preserving equivalences.
Source: Levels, restricted counit equation
(blueprint: lem-sp-tower-evaluated-representability). -/
def openAdjunction {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    SpTowerCalculus.openExtension l E b o q j ⊣ SpTowerCalculus.etalePullback l E b o q j :=
  ((SpTowerCalculus.realization l E b U (q.abelian U)).toAdjunction.comp
    (o.openOp j).derivedAdjunction).comp
      (SpTowerCalculus.realization l E b X (q.abelian X)).symm.toAdjunction

/-- Restrict the global counit using compact-support composition and the open counit.
Source: first display and Levels
(blueprint: lem-sp-tower-evaluated-representability). -/
def restrictedCounit {U X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (j : U ⟶ X) [IsOpenImmersion j]
    (G : spDerivedCoefficientTowers l E X (q.abelian X))
    (K : spDerivedCoefficientTowers l E Y (q.abelian Y))
    (eps : (SpTowerCalculus.F l E b o q c).obj G ⟶ K) :
    (SpTowerCalculus.F l E b o q (c.precomp j)).obj
      ((SpTowerCalculus.etalePullback l E b o q j).obj G) ⟶ K :=
  (SpTowerCalculus.openComposition l E b o q j c).inv.app _ ≫
    (SpTowerCalculus.F l E b o q c).map
      ((openAdjunction l E b o q j).counit.app G) ≫ eps

/-- Evaluate through the fixed compact-support comparison.
Source: Levels, epsilon_n (blueprint: lem-sp-tower-evaluated-representability). -/
def evaluatedCounit {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    {G : spDerivedCoefficientTowers l E X (q.abelian X)}
    {K : spDerivedCoefficientTowers l E Y (q.abelian Y)}
    (eps : (SpTowerCalculus.F l E b o q c).obj G ⟶ K) (n : ℕ) :=
  (supportEvaluation l E b o q c n).inv.app G ≫
    (spDerivedCoefficientEvaluation l E Y (q.abelian Y) n).map eps

/-- Termwise descent of the actual ordinary finite open counit.
Source: Levels, open-extension tests
(blueprint: lem-sp-tower-evaluated-representability). -/
def finiteOpenCounit {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ) :
    proEtaleConstantRingDerivedPullback (SpTowerShriek.R l E n) j ⋙
      sfIntrinsicDerivedOpen (SpTowerShriek.R l E n) j ⟶ 𝟭 _ :=
  (Functor.mapDerivedCategoryCompIso _ _).inv ≫
    sfIntrinsicDeriveMap (SpTowerShriek.R l E n)
      (SpTowerShriek.finiteOpenAdjunction l E b j n).counit ≫
    (Functor.mapDerivedCategoryIdIso _).hom

/-- Termwise descent of the actual ordinary finite open unit.
Source: Levels, open adjunction maps
(blueprint: lem-sp-tower-evaluated-representability). -/
def finiteOpenUnit {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ) :
    𝟭 _ ⟶ sfIntrinsicDerivedOpen (SpTowerShriek.R l E n) j ⋙
      proEtaleConstantRingDerivedPullback (SpTowerShriek.R l E n) j :=
  (Functor.mapDerivedCategoryIdIso _).inv ≫
    sfIntrinsicDeriveMap (SpTowerShriek.R l E n)
      (SpTowerShriek.finiteOpenAdjunction l E b j n).unit ≫
    (Functor.mapDerivedCategoryCompIso _ _).hom

/-- Canonical restriction evaluation, using only section-preserving realizations
and the dependency's fixed pullback evaluation. Source: Levels, restricted pairs
(blueprint: lem-sp-tower-evaluated-representability). -/
def restrictionEvaluation {U X : Scheme.{u}} (j : U ⟶ X) (n : ℕ)
    (G : spDerivedCoefficientTowers l E X (q.abelian X)) :
    (spDerivedCoefficientEvaluation l E U (q.abelian U) n).obj
        ((SpTowerCalculus.etalePullback l E b o q j).obj G) ≅
      (proEtaleConstantRingDerivedPullback (SpTowerShriek.R l E n) j).obj
        ((spDerivedCoefficientEvaluation l E X (q.abelian X) n).obj G) :=
  ((SpTowerCalculus.levelComparison l E b q U n).symm.app _) ≪≫
    (SpTowerShriek.Ev l E U n).mapIso
      ((SpTowerCalculus.realization l E b U (q.abelian U)).counitIso.app
        ((SpTowerShriek.pull l E b (o.geometry j)).obj
          ((SpTowerCalculus.realization l E b X (q.abelian X)).functor.obj G))) ≪≫
    ((o.geometry j).pullEvaluation n).app
      ((SpTowerCalculus.realization l E b X (q.abelian X)).functor.obj G) ≪≫
    (proEtaleConstantRingDerivedPullback (SpTowerShriek.R l E n) j).mapIso
      ((SpTowerCalculus.levelComparison l E b q X n).app G)

/-- Open normalization of finite compact support.
Source: Levels, F_(fj) = F_f j_!
(blueprint: lem-sp-tower-evaluated-representability). -/
def finiteOpenComposition {U X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ) :
    SpTowerShriek.finiteF l E b (c.precomp j) n ≅
      sfIntrinsicDerivedOpen (SpTowerShriek.R l E n) j ⋙ SpTowerShriek.finiteF l E b c n :=
  Functor.isoWhiskerRight
    (sfIntrinsicDerivedOpenComp (SpTowerShriek.R l E n) j c.i) _ ≪≫
      Functor.associator _ _ _

/-- Restrict a finite counit by the actual open counit.
Source: Levels, restricted pair (blueprint: lem-sp-tower-evaluated-representability). -/
def finiteRestrictedCounit {U X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ)
    {G : proEtaleDerivedCategory X (SpTowerShriek.R l E n)}
    {K : proEtaleDerivedCategory Y (SpTowerShriek.R l E n)}
    (eps : (SpTowerShriek.finiteF l E b c n).obj G ⟶ K) :=
  (finiteOpenComposition l E b c j n).hom.app _ ≫
    (SpTowerShriek.finiteF l E b c n).map ((finiteOpenCounit l E b j n).app G) ≫ eps

/-- Representability tests every finite ctf object, with no tower-lifting condition.
Source: Levels, displayed bijection (blueprint: lem-sp-tower-evaluated-representability). -/
def Represents {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) (n : ℕ)
    (G : proEtaleDerivedCategory X (SpTowerShriek.R l E n))
    (K : proEtaleDerivedCategory Y (SpTowerShriek.R l E n))
    (eps : (SpTowerShriek.finiteF l E b c n).obj G ⟶ K) : Prop :=
  ∀ M : spFiniteConstructibleTorCategory X (SpTowerShriek.R l E n),
    Function.Bijective (fun a : M.obj ⟶ G ↦ (SpTowerShriek.finiteF l E b c n).map a ≫ eps)

/-- Finite coordinate cover, actual model isomorphisms and normalized counit equations.
An open immersion represents its open image, including the empty finite cover.
Source: Local pairs and Levels (blueprint: lem-sp-tower-evaluated-representability). -/
structure ChartCover (hc : Models l E k b o q z h cal w)
    (X Y : Bases k) (f : X.val.left ⟶ Y.val.left) (c : Compactification f) (d : ℕ)
    (G : SpTowerCalculus.C l E b q X.val.left)
    (K : SpTowerCalculus.C l E b q Y.val.left)
    (eps : (SpTowerCalculus.F l E b o q c).obj G.obj ⟶ K.obj) where
  count : ℕ
  domains : Fin count → Bases k
  inclusion : ∀ i, (domains i).val.left ⟶ X.val.left
  [openImmersion : ∀ i, IsOpenImmersion (inclusion i)]
  overBase : ∀ i, inclusion i ≫ X.val.hom = (domains i).val.hom
  covers : ∀ x : X.val.left, ∃ i, x ∈ Set.range (inclusion i)
  coordinate : ∀ i, (domains i).val.left ⟶ space Y.val.left d
  [etale : ∀ i, Etale (coordinate i)]
  [separated : ∀ i, IsSeparated (coordinate i)]
  [finiteType : ∀ i, LocallyOfFiniteType (coordinate i)]
  [quasiCompact : ∀ i, QuasiCompact (coordinate i)]
  coordinateOver : ∀ i, coordinate i ≫ proj Y.val.left d ≫ Y.val.hom = (domains i).val.hom
  factors : ∀ i, coordinate i ≫ proj Y.val.left d = inclusion i ≫ f
  model : ∀ i, (SpTowerCalculus.etalePullback l E b o q (inclusion i)).obj G.obj ≅
    (originalChartRight l E b o q (coordinate i) (proj Y.val.left d)
      (w (domains i).val.left) d).obj K.obj
  counit : ∀ i,
    restrictedCounit l E b o q c (inclusion i) G.obj K.obj eps =
      (SpTowerCalculus.F l E b o q (c.precomp (inclusion i))).map (model i).hom ≫
        (hc.chart Y (domains i) d (coordinate i) (coordinateOver i)
          ((c.precomp (inclusion i)).copy (factors i))).counit K

/-- The canonical finite restriction compositor for nested opens.
Source: Gluing and Levels, nested open restriction
(blueprint: lem-sp-tower-evaluated-representability). -/
def finiteRestrictionComp {X : Scheme.{u}} {U V : X.Opens} (i : U ≤ V) (n : ℕ) :
    proEtaleConstantRingDerivedPullback (SpTowerShriek.R l E n) U.ι ≅
      proEtaleConstantRingDerivedPullback (SpTowerShriek.R l E n) V.ι ⋙
        proEtaleConstantRingDerivedPullback (SpTowerShriek.R l E n) (X.homOfLE i) :=
  (proEtaleConstantRingPullbackComposition (X.homOfLE i) V.ι (SpTowerShriek.R l E n) ≪≫
    eqToIso (congrArg (proEtaleConstantRingDerivedPullback (SpTowerShriek.R l E n))
      (X.homOfLE_ι i))).symm

/-- Equality transport of the actual finite open extension; both maps are retained.
Source: Levels, nested inclusions (blueprint: lem-sp-tower-evaluated-representability). -/
def finiteOpenCongr {U X : Scheme.{u}} {j j' : U ⟶ X}
    [IsOpenImmersion j] [IsOpenImmersion j'] (hj : j = j') (n : ℕ) :
    sfIntrinsicDerivedOpen (SpTowerShriek.R l E n) j ≅
      sfIntrinsicDerivedOpen (SpTowerShriek.R l E n) j' := by
  cases hj
  exact Iso.refl _

/-- The open-transpose comparison giving the signed overlap inclusion.
Source: Gluing and Levels (blueprint: lem-sp-tower-evaluated-representability). -/
def finiteCoverComponent {X : Scheme.{u}} {U V : X.Opens} (i : U ≤ V) (n : ℕ)
    (M : proEtaleDerivedCategory X (SpTowerShriek.R l E n)) :
    (sfIntrinsicDerivedOpen (SpTowerShriek.R l E n) U.ι).obj
      ((proEtaleConstantRingDerivedPullback (SpTowerShriek.R l E n) U.ι).obj M) ⟶
    (sfIntrinsicDerivedOpen (SpTowerShriek.R l E n) V.ι).obj
      ((proEtaleConstantRingDerivedPullback (SpTowerShriek.R l E n) V.ι).obj M) :=
  let A := SpTowerShriek.R l E n
  let N := (proEtaleConstantRingDerivedPullback A V.ι).obj M
  (sfIntrinsicDerivedOpen A U.ι).map ((finiteRestrictionComp l E i n).hom.app M) ≫
    (finiteOpenCongr l E b (X.homOfLE_ι i) n).inv.app _ ≫
    (sfIntrinsicDerivedOpenComp A (X.homOfLE i) V.ι).hom.app _ ≫
    (sfIntrinsicDerivedOpen A V.ι).map
      ((finiteOpenCounit l E b (X.homOfLE i) n).app N)

/-- The overlap term in the finite signed open-cover triangle.
Source: Gluing, A (blueprint: lem-sp-tower-evaluated-representability). -/
abbrev finiteA {X : Scheme.{u}} (U V : X.Opens) (n : ℕ)
    (M : proEtaleDerivedCategory X (SpTowerShriek.R l E n)) :=
  (sfIntrinsicDerivedOpen (SpTowerShriek.R l E n) (U ⊓ V).ι).obj
    ((proEtaleConstantRingDerivedPullback (SpTowerShriek.R l E n) (U ⊓ V).ι).obj M)

/-- The two-open term in the finite signed open-cover triangle.
Source: Gluing, B (blueprint: lem-sp-tower-evaluated-representability). -/
abbrev finiteB {X : Scheme.{u}} (U V : X.Opens) (n : ℕ)
    (M : proEtaleDerivedCategory X (SpTowerShriek.R l E n)) :=
  (sfIntrinsicDerivedOpen (SpTowerShriek.R l E n) U.ι).obj
      ((proEtaleConstantRingDerivedPullback (SpTowerShriek.R l E n) U.ι).obj M) ⊞
    (sfIntrinsicDerivedOpen (SpTowerShriek.R l E n) V.ι).obj
      ((proEtaleConstantRingDerivedPullback (SpTowerShriek.R l E n) V.ι).obj M)

/-- Signed overlap inclusions, with the actual restriction compositors.
Source: Gluing, (1,-1) (blueprint: lem-sp-tower-evaluated-representability). -/
def finiteS {X : Scheme.{u}} (U V : X.Opens) (n : ℕ)
    (M : proEtaleDerivedCategory X (SpTowerShriek.R l E n)) :
    finiteA l E b U V n M ⟶ finiteB l E b U V n M :=
  biprod.lift (finiteCoverComponent l E b (inf_le_left : U ⊓ V ≤ U) n M)
    (-finiteCoverComponent l E b (inf_le_right : U ⊓ V ≤ V) n M)

/-- Sum of the two actual open counits.
Source: Gluing, (1,1) (blueprint: lem-sp-tower-evaluated-representability). -/
def finiteT {X : Scheme.{u}} (U V : X.Opens) (n : ℕ)
    (M : proEtaleDerivedCategory X (SpTowerShriek.R l E n)) :
    finiteB l E b U V n M ⟶ M :=
  biprod.desc ((finiteOpenCounit l E b U.ι n).app M)
    ((finiteOpenCounit l E b V.ι n).app M)

/-- Evaluation preserves the triangulated structure and the actual open counits,
including their restricted equations. Every finite ctf test has a separate etale-origin
representative with its specified Tor interval. Source: Levels, steps 1--4
(blueprint: lem-sp-tower-evaluated-representability).

Proof: exact evaluation descends termwise and is triangulated. Descend the ordinary
open evaluation equations in shriek-levels through localization. Apply finite-Tor
comparison and chart admissibility on the Noetherian finite-type schemes and opens.
Functoriality then preserves each restricted counit equation. -/
theorem evaluation_open_compatibility
    (pchar : ℕ) [Fact pchar.Prime] [CharP k pchar] (_hl : l ≠ pchar) :
    (∀ T : Bases k, SpChartAdmissibility.origins l E T.val.left) ∧
    (∀ (T : Scheme.{u}) (n : ℕ), (SpTowerShriek.Ev l E T n).IsTriangulated) ∧
    (∀ {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ)
      (G : SpTowerShriek.D l E X),
      (SpTowerShriek.openEvaluation l E b (o.openOp j) n).inv.app
          ((SpTowerShriek.pull l E b (o.geometry j)).obj G) ≫
        (SpTowerShriek.Ev l E X n).map ((o.openOp j).derivedAdjunction.counit.app G) =
      (sfIntrinsicDerivedOpen (SpTowerShriek.R l E n) j).map
        (((o.geometry j).pullEvaluation n).hom.app G) ≫
          (finiteOpenCounit l E b j n).app ((SpTowerShriek.Ev l E X n).obj G)) ∧
    (∀ {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ)
      (M : SpTowerShriek.D l E U),
      (SpTowerShriek.Ev l E U n).map ((o.openOp j).derivedAdjunction.unit.app M) ≫
          ((o.geometry j).pullEvaluation n).hom.app
            ((SpTowerShriek.openD l E b (o.openOp j)).obj M) ≫
          (proEtaleConstantRingDerivedPullback (SpTowerShriek.R l E n) j).map
            ((SpTowerShriek.openEvaluation l E b (o.openOp j) n).hom.app M) =
        (finiteOpenUnit l E b j n).app ((SpTowerShriek.Ev l E U n).obj M)) ∧
    ∀ {U X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
      (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ)
      (G : spDerivedCoefficientTowers l E X (q.abelian X))
      (K : spDerivedCoefficientTowers l E Y (q.abelian Y))
      (eps : (SpTowerCalculus.F l E b o q c).obj G ⟶ K),
      evaluatedCounit l E b o q (c.precomp j)
          (restrictedCounit l E b o q c j G K eps) n =
        (SpTowerShriek.finiteF l E b (c.precomp j) n).map
          (restrictionEvaluation l E b o q j n G).hom ≫
        finiteRestrictedCounit l E b c j n (evaluatedCounit l E b o q c eps n) := by
  sorry

/-- The finite binary open-cover argument retains the signed triangle, both exact
five-term Hom rows and all four outer bijections. Taking X to be any open of the
original scheme gives the node's assertion for every binary cover inside X.
Source: Gluing repeated in Levels, steps 5--8
(blueprint: lem-sp-tower-evaluated-representability).

Proof: choose a separate etale origin for M preserving its Tor interval. The signed
etale open-cover short exact sequence descends to a distinguished triangle. Exact
site comparison preserves its arrows and actual counits. Apply triangulated compact
support and contravariant Hom exactness, including the rotation, to get the two rows
indexed by B[1], A[1], M, B, A. Open transposition and additivity identify the four
outer maps with the restricted representing bijections. Functoriality commutes with
the boundary too. The five lemma gives the central bijection, for each finite test.
The zero-chart case is the empty scheme, whose derived Hom groups are singletons. -/
theorem finite_binary_representability
    (pchar : ℕ) [Fact pchar.Prime] [CharP k pchar] (_hl : l ≠ pchar)
    (X Y : Bases k) (f : X.val.left ⟶ Y.val.left)
    (_over : f ≫ Y.val.hom = X.val.hom) (c : Compactification f)
    (n : ℕ) (U V : X.val.left.Opens) (_cover : U ⊔ V = ⊤)
    (G : spFiniteConstructibleTorCategory X.val.left (SpTowerShriek.R l E n))
    (K : spFiniteConstructibleTorCategory Y.val.left (SpTowerShriek.R l E n))
    (eps : (SpTowerShriek.finiteF l E b c n).obj G.obj ⟶ K.obj)
    (_local : ∀ D ∈ ({U, V, U ⊓ V} : Set X.val.left.Opens),
      Represents l E b (c.precomp D.ι) n
        ((proEtaleConstantRingDerivedPullback (SpTowerShriek.R l E n) D.ι).obj G.obj)
        K.obj (finiteRestrictedCounit l E b c D.ι n eps)) :
    Represents l E b c n G.obj K.obj eps ∧
    ∀ M : spFiniteConstructibleTorCategory X.val.left (SpTowerShriek.R l E n),
      ∃ δ : M.obj ⟶ (finiteA l E b U V n M.obj)⟦(1 : ℤ)⟧,
        Triangle.mk (finiteS l E b U V n M.obj) (finiteT l E b U V n M.obj) δ ∈
          distTriang _ ∧
        spFiniteConstructibleTor X.val.left (SpTowerShriek.R l E n)
          (finiteA l E b U V n M.obj) ∧
        spFiniteConstructibleTor X.val.left (SpTowerShriek.R l E n)
          (finiteB l E b U V n M.obj) ∧
        spFiniteConstructibleTor X.val.left (SpTowerShriek.R l E n)
          ((finiteA l E b U V n M.obj)⟦(1 : ℤ)⟧) ∧
        spFiniteConstructibleTor X.val.left (SpTowerShriek.R l E n)
          ((finiteB l E b U V n M.obj)⟦(1 : ℤ)⟧) ∧
        SpTowerBinaryCounit.HomFiveExact (finiteS l E b U V n M.obj)
          (finiteT l E b U V n M.obj) δ G.obj ∧
        SpTowerBinaryCounit.ImageHomFiveExact (SpTowerShriek.finiteF l E b c n)
          (finiteS l E b U V n M.obj) (finiteT l E b U V n M.obj) δ K.obj ∧
        SpTowerBinaryCounit.OuterBijective
          (A := finiteA l E b U V n M.obj) (B := finiteB l E b U V n M.obj)
          (SpTowerShriek.finiteF l E b c n) eps := by
  sorry

/-- Chart-normalized pairs represent all finite tests, naturally, and identify uniquely
with the finite adjoint. Source: blueprint latest, Levels; proof steps 1--10
(blueprint: lem-sp-tower-evaluated-representability).

Proof:
1. Chart admissibility makes every open Noetherian and qcqs and each quotient finite
Noetherian. The finite-Tor comparison supplies each finite test its own etale origin,
with its Tor interval; the open counit-scalar theorem preserves the finite ctf domain.
2. Exact evaluation is triangulated. Shriek-levels and coefficient-tower calculus
preserve the actual open maps, composition comparisons and restricted counit equations.
3. Evaluate the chart models using coordinate-adjunction: the finite adjunction on
all finite ctf tests has counit summation followed by ordered integration. Dimension
zero uses the identity projection adjunction.
4. The open adjunction identifies the global Hom map on j_!N with the restricted
counit Hom map on N. Nested open counits compose by the same calculus normalization.
5. The etale natural signed open-cover SES, its complex-SES triangle and unbounded
open site transport give A -> B -> M -> A[1], with arrows (1,-1) and (1,1).
6. Compact-support triangulatedness and Hom-out-of-triangle exactness give the two
five-term rows indexed by B[1], A[1], M, B, A. Functoriality commutes with every arrow,
including the connecting arrow and negative shifted overlap arrow.
7. Restricted representing bijections give all four outer isomorphisms. The five
lemma in abelian groups proves the central bijection.
8. Strong induction on the finite restricted cover works on every open. With no
charts the scheme is empty and both Hom groups are singletons. One chart is step 3;
the successor is step 7. Precomposition gives naturality for arbitrary finite tests.
9. The finite adjunction of reduction-exceptional and shriek-preservation supplies
the other representing pair. Transpose both counits. The two Hom injectivities make
the resulting maps mutually inverse and prove uniqueness of the isomorphism.
10. Evaluate a family's counit equation; finite-adjunction injectivity identifies its
morphisms. The evaluated tower triangle identity identifies its unit with the finite
unit. No faithfulness of derived evaluation is used. -/
theorem tower_evaluated_representability
    (pchar : ℕ) [Fact pchar.Prime] [CharP k pchar] (_hl : l ≠ pchar)
    (hc : Models l E k b o q z h cal w)
    (X Y : Bases k) (f : X.val.left ⟶ Y.val.left)
    (_over : f ≫ Y.val.hom = X.val.hom)
    (c : Compactification f) (d : ℕ) [SmoothOfRelativeDimension d f]
    (G : SpTowerCalculus.C l E b q X.val.left)
    (K : SpTowerCalculus.C l E b q Y.val.left)
    (eps : (SpTowerCalculus.F l E b o q c).obj G.obj ⟶ K.obj)
    (_charts : ChartCover l E k b o q z h cal w hc X Y f c d G K eps) :
    ∀ n : ℕ,
      Represents l E b c n
        ((spDerivedCoefficientEvaluation l E X.val.left (q.abelian X.val.left) n).obj G.obj)
        ((spDerivedCoefficientEvaluation l E Y.val.left (q.abelian Y.val.left) n).obj K.obj)
        (evaluatedCounit l E b o q c eps n) ∧
      (∀ (M M' : spFiniteConstructibleTorCategory X.val.left (SpTowerShriek.R l E n))
        (v : M'.obj ⟶ M.obj)
        (a : M.obj ⟶
          (spDerivedCoefficientEvaluation l E X.val.left (q.abelian X.val.left) n).obj G.obj),
        (SpTowerShriek.finiteF l E b c n).map (v ≫ a) ≫
            evaluatedCounit l E b o q c eps n =
          (SpTowerShriek.finiteF l E b c n).map v ≫
            ((SpTowerShriek.finiteF l E b c n).map a ≫
              evaluatedCounit l E b o q c eps n)) ∧
      ∀ (hF : ∀ M : spFiniteConstructibleTorCategory X.val.left (SpTowerShriek.R l E n),
        spFiniteConstructibleTor Y.val.left (SpTowerShriek.R l E n)
          ((SpTowerShriek.finiteF l E b c n).obj M.obj))
        (H : spFiniteConstructibleTorCategory Y.val.left (SpTowerShriek.R l E n) ⥤
          spFiniteConstructibleTorCategory X.val.left (SpTowerShriek.R l E n))
        (adj : ObjectProperty.lift _
          ((spFiniteConstructibleTor X.val.left (SpTowerShriek.R l E n)).ι ⋙
            SpTowerShriek.finiteF l E b c n) hF ⊣ H),
        ∃! s : (spDerivedCoefficientEvaluation l E X.val.left
              (q.abelian X.val.left) n).obj G.obj ≅
            (H.obj ((evaluation l E b q Y.val.left n).obj K)).obj,
          (SpTowerShriek.finiteF l E b c n).map s.hom ≫
              (adj.counit.app ((evaluation l E b q Y.val.left n).obj K)).hom =
            evaluatedCounit l E b o q c eps n := by
  sorry

private theorem evaluated_equation
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (FT : A ⥤ B) (EX : A ⥤ C) (EY : B ⥤ D) (F : C ⥤ D)
    (e : FT ⋙ EY ≅ EX ⋙ F)
    {G G' : A} {K K' : B} (v : G ⟶ G') (u : K ⟶ K')
    (eps : FT.obj G ⟶ K) (eps' : FT.obj G' ⟶ K')
    (eqn : FT.map v ≫ eps' = eps ≫ u) :
    F.map (EX.map v) ≫ (e.inv.app G' ≫ EY.map eps') =
      (e.inv.app G ≫ EY.map eps) ≫ EY.map u := by
  have hn : F.map (EX.map v) ≫ e.inv.app G' =
      e.inv.app G ≫ EY.map (FT.map v) := e.inv.naturality v
  rw [← Category.assoc, hn, Category.assoc, ← EY.map_comp, eqn,
    EY.map_comp, Category.assoc]

private theorem lifted_transpose_injective
    {A B : Type*} [Category A] [Category B]
    (P : ObjectProperty A) (Q : ObjectProperty B) (F : A ⥤ B)
    (hF : ∀ M : P.FullSubcategory, Q (F.obj M.obj))
    (H : Q.FullSubcategory ⥤ P.FullSubcategory)
    (adj : ObjectProperty.lift Q (P.ι ⋙ F) hF ⊣ H)
    (M : P.FullSubcategory) (K : Q.FullSubcategory) :
    Function.Injective (fun a : M.obj ⟶ (H.obj K).obj ↦
      F.map a ≫ (adj.counit.app K).hom) := by
  intro a b hab
  have hh : (adj.homEquiv M K).symm (ObjectProperty.homMk a) =
      (adj.homEquiv M K).symm (ObjectProperty.homMk b) := by
    apply ObjectProperty.hom_ext
    exact hab
  exact congrArg (fun f ↦ f.hom) ((adj.homEquiv M K).symm.injective hh)

private theorem restricted_transpose_injective
    {A B : Type*} [Category A] [Category B]
    {P : ObjectProperty A} {Q : ObjectProperty B} {F : A ⥤ B} {G : B ⥤ A}
    (a : RestrictedPair P Q F G) (M : P.FullSubcategory) (K : Q.FullSubcategory) :
    Function.Injective (fun f : M.obj ⟶ G.obj K.obj ↦ F.map f ≫ a.counit K) := by
  exact lifted_transpose_injective P Q F a.left_closed
    (ObjectProperty.lift P (Q.ι ⋙ G) a.right_closed) a.adjunction M K

private theorem restricted_left_triangle
    {A B : Type*} [Category A] [Category B]
    {P : ObjectProperty A} {Q : ObjectProperty B} {F : A ⥤ B} {G : B ⥤ A}
    (a : RestrictedPair P Q F G) (M : P.FullSubcategory) :
    F.map (a.unit M) ≫ a.counit ⟨F.obj M.obj, a.left_closed M⟩ = 𝟙 _ :=
  congrArg (fun f ↦ f.hom) (a.adjunction.left_triangle_components M)

private theorem restricted_counit_naturality
    {A B : Type*} [Category A] [Category B]
    {P : ObjectProperty A} {Q : ObjectProperty B} {F : A ⥤ B} {G : B ⥤ A}
    (a : RestrictedPair P Q F G) (K K' : Q.FullSubcategory) (u : K.obj ⟶ K'.obj) :
    F.map (G.map u) ≫ a.counit K' = a.counit K ≫ u :=
  congrArg (fun f ↦ f.hom) (a.adjunction.counit.naturality (ObjectProperty.homMk u))

private theorem evaluated_triangle
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (FT : A ⥤ B) (EX : A ⥤ C) (EY : B ⥤ D) (F : C ⥤ D)
    (e : FT ⋙ EY ≅ EX ⋙ F)
    {M N : A} (eta : M ⟶ N) (eps : FT.obj N ⟶ FT.obj M)
    (eqn : FT.map eta ≫ eps = 𝟙 _) :
    F.map (EX.map eta) ≫ (e.inv.app N ≫ EY.map eps) ≫ e.hom.app M = 𝟙 _ := by
  have hh := evaluated_equation FT EX EY F e eta (𝟙 (FT.obj M)) (𝟙 _) eps
    (by simpa only [Category.id_comp] using eqn)
  have ht := congrArg (fun f ↦ f ≫ e.hom.app M) hh
  have hid : EY.map (𝟙 (FT.obj M)) = 𝟙 _ := EY.map_id _
  dsimp only [Functor.comp_obj] at ht
  rw [hid] at ht
  simp only [Category.comp_id, Category.assoc, Iso.inv_hom_id_app] at ht
  simpa only [Functor.comp_obj, Category.assoc] using ht

/-- The counit-preserving comparisons intertwine every evaluated tower morphism
satisfying the family's counit equation. Source: Levels, functoriality, step 10
(blueprint: lem-sp-tower-evaluated-representability).

Proof: apply exact evaluation to the tower counit equation. Naturality of the fixed
compact-support evaluation comparison gives the finite counit equation. Substitute
the two counit-preserving isomorphisms. The adjunction Hom bijection is injective,
so the resulting conjugate is the finite right-adjoint image of the evaluated map. -/
theorem evaluated_family_morphism
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) (n : ℕ)
    (G G' : SpTowerCalculus.C l E b q X)
    (K K' : SpTowerCalculus.C l E b q Y)
    (eps : (SpTowerCalculus.F l E b o q c).obj G.obj ⟶ K.obj)
    (eps' : (SpTowerCalculus.F l E b o q c).obj G'.obj ⟶ K'.obj)
    (v : G.obj ⟶ G'.obj) (u : K.obj ⟶ K'.obj)
    (_equation : (SpTowerCalculus.F l E b o q c).map v ≫ eps' = eps ≫ u)
    (hF : ∀ M : spFiniteConstructibleTorCategory X (SpTowerShriek.R l E n),
      spFiniteConstructibleTor Y (SpTowerShriek.R l E n)
        ((SpTowerShriek.finiteF l E b c n).obj M.obj))
    (H : spFiniteConstructibleTorCategory Y (SpTowerShriek.R l E n) ⥤
      spFiniteConstructibleTorCategory X (SpTowerShriek.R l E n))
    (adj : ObjectProperty.lift _
      ((spFiniteConstructibleTor X (SpTowerShriek.R l E n)).ι ⋙
        SpTowerShriek.finiteF l E b c n) hF ⊣ H)
    (s : (spDerivedCoefficientEvaluation l E X (q.abelian X) n).obj G.obj ≅
      (H.obj ((evaluation l E b q Y n).obj K)).obj)
    (s' : (spDerivedCoefficientEvaluation l E X (q.abelian X) n).obj G'.obj ≅
      (H.obj ((evaluation l E b q Y n).obj K')).obj)
    (_s : (SpTowerShriek.finiteF l E b c n).map s.hom ≫
      (adj.counit.app ((evaluation l E b q Y n).obj K)).hom =
        evaluatedCounit l E b o q c eps n)
    (_s' : (SpTowerShriek.finiteF l E b c n).map s'.hom ≫
      (adj.counit.app ((evaluation l E b q Y n).obj K')).hom =
        evaluatedCounit l E b o q c eps' n) :
    (spDerivedCoefficientEvaluation l E X (q.abelian X) n).map v ≫ s'.hom =
      s.hom ≫ (H.map (ObjectProperty.homMk
        ((spDerivedCoefficientEvaluation l E Y (q.abelian Y) n).map u))).hom := by
  let EX := spDerivedCoefficientEvaluation l E X (q.abelian X) n
  let EY := spDerivedCoefficientEvaluation l E Y (q.abelian Y) n
  let F := SpTowerShriek.finiteF l E b c n
  let un : (evaluation l E b q Y n).obj K ⟶
      (evaluation l E b q Y n).obj K' := ObjectProperty.homMk (EY.map u)
  have he : F.map (EX.map v) ≫ evaluatedCounit l E b o q c eps' n =
      evaluatedCounit l E b o q c eps n ≫ EY.map u := by
    exact evaluated_equation _ _ _ _ (supportEvaluation l E b o q c n) v u
      eps eps' _equation
  have hc : F.map (H.map un).hom ≫
        (adj.counit.app ((evaluation l E b q Y n).obj K')).hom =
      (adj.counit.app ((evaluation l E b q Y n).obj K)).hom ≫ EY.map u :=
    congrArg (fun t ↦ t.hom) (adj.counit.naturality un)
  apply lifted_transpose_injective
    (spFiniteConstructibleTor X (SpTowerShriek.R l E n))
    (spFiniteConstructibleTor Y (SpTowerShriek.R l E n)) F hF H adj
    ((evaluation l E b q X n).obj G) ((evaluation l E b q Y n).obj K')
  change F.map ((EX.map v) ≫ s'.hom) ≫ _ =
    F.map (s.hom ≫ (H.map un).hom) ≫ _
  rw [F.map_comp, F.map_comp, Category.assoc, _s']
  rw [Category.assoc, hc, ← Category.assoc, _s]
  exact he

/-- For a tower adjunction the evaluated unit is the finite unit under the specified
left evaluation and counit-preserving right comparison. This assertion tests units at
tower objects and requires no lift of an arbitrary finite object.
Source: Levels, units, step 10 (blueprint: lem-sp-tower-evaluated-representability).

Proof: evaluate the tower triangle identity eps_(FM) F(eta_M) = id. The specified
left and counit-preserving right comparisons turn it into the transpose equation
for the identity under the finite adjunction. Uniqueness of that transpose identifies
the evaluated unit with the finite unit. -/
theorem evaluated_adjunction_unit
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (GT : spDerivedCoefficientTowers l E Y (q.abelian Y) ⥤
      spDerivedCoefficientTowers l E X (q.abelian X))
    (a : RestrictedPair (P l E b q X) (P l E b q Y)
      (SpTowerCalculus.F l E b o q c) GT)
    (n : ℕ)
    (GN : proEtaleDerivedCategory Y (SpTowerShriek.R l E n) ⥤
      proEtaleDerivedCategory X (SpTowerShriek.R l E n))
    (an : RestrictedPair (spFiniteConstructibleTor X (SpTowerShriek.R l E n))
      (spFiniteConstructibleTor Y (SpTowerShriek.R l E n))
      (SpTowerShriek.finiteF l E b c n) GN)
    (right : ∀ K : SpTowerCalculus.C l E b q Y,
      (spDerivedCoefficientEvaluation l E X (q.abelian X) n).obj (GT.obj K.obj) ≅
        GN.obj ((spDerivedCoefficientEvaluation l E Y (q.abelian Y) n).obj K.obj))
    (_counit : ∀ K : SpTowerCalculus.C l E b q Y,
      (SpTowerShriek.finiteF l E b c n).map (right K).hom ≫
          an.counit ((evaluation l E b q Y n).obj K) =
        evaluatedCounit l E b o q c (a.counit K) n) :
    ∀ M : SpTowerCalculus.C l E b q X,
      (spDerivedCoefficientEvaluation l E X (q.abelian X) n).map (a.unit M) ≫
        (right ⟨_, a.left_closed M⟩).hom ≫
        GN.map ((supportEvaluation l E b o q c n).hom.app M.obj) =
          an.unit ((evaluation l E b q X n).obj M) := by
  intro M
  let EX := spDerivedCoefficientEvaluation l E X (q.abelian X) n
  let EY := spDerivedCoefficientEvaluation l E Y (q.abelian Y) n
  let F := SpTowerShriek.finiteF l E b c n
  let L : SpTowerCalculus.C l E b q Y := ⟨_, a.left_closed M⟩
  let MN := (evaluation l E b q X n).obj M
  let LN := (evaluation l E b q Y n).obj L
  let FN : spFiniteConstructibleTorCategory Y (SpTowerShriek.R l E n) :=
    ⟨_, an.left_closed MN⟩
  let e := (supportEvaluation l E b o q c n).hom.app M.obj
  have hn : F.map (GN.map e) ≫ an.counit FN = an.counit LN ≫ e :=
    restricted_counit_naturality an LN FN e
  have ht := evaluated_triangle (SpTowerCalculus.F l E b o q c) EX EY F
    (supportEvaluation l E b o q c n) (a.unit M) (a.counit L)
    (restricted_left_triangle a M)
  apply restricted_transpose_injective an MN FN
  change F.map (EX.map (a.unit M) ≫ (right L).hom ≫ GN.map e) ≫ an.counit FN =
    F.map (an.unit MN) ≫ an.counit FN
  rw [F.map_comp, F.map_comp, Category.assoc, Category.assoc, hn,
    ← Category.assoc (F.map (right L).hom), _counit L]
  rw [restricted_left_triangle an MN]
  exact ht

end AlgebraicGeometry.ProEtale.SpTowerEvaluated
