/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q13
-/
module

public import Sheaf.Paper.StrictTowerOperations
public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicFiniteOperations
public import Sheaf.Paper.CompletedBaseChangeMap
public import Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction
public import Sheaf.AlgebraicGeometry.ProEtaleCanonicalPullbackComposition
public import Mathlib.CategoryTheory.Adjunction.Mates

import Sheaf.CategoryTheory.DiagramSiteRealization
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Sites.Limits
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral
import Sheaf.CategoryTheory.SmallModuleDiagramsGrothendieck
import Sheaf.CategoryTheory.KInjectiveTotalDerived
import Sheaf.Paper.RingedExchangeTensorCoherence
import Sheaf.Paper.ProEtaleCanonicalTensorPullback
import Sheaf.Paper.ConstantCompletionEquivalence
import Sheaf.Paper.PerfectProjectionFormula
import Sheaf.Paper.FiniteLevelRectangle
import Sheaf.Algebra.Homology.SiteDerivedTensorDescent
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp

/-! # Strict tower exchange and the canonical mate

Source: literature/blueprint/master/blueprint/sec-proper-base-change/
sk-thm-properbasechange/lemma-weil-pbc-completed-exchange-coherence.md,
proof, first two sentences; Stacks Tag 07A7
(blueprint: lem-weil-pbc-strict-tower-exchange-mate-normalization).

The comparison functors are termwise functors on module towers, localized only
**after** forming the tower category. The strict finite exchange is the
projection-formula realization in `CompletedTowerCompatibility`. Restriction
comparisons retain their normalization on ordinary modules and K-injectives.

## Main definitions

* `exchangeTowerRes`: exact coefficient restriction on strict derived towers.
* `StrictTowerRingedSquare.exchangeTowerMate`: the canonical termwise adjunction mate.
* `exchangeCornerB`, `exchangeCornerD`: the specified natural corner comparisons.
* `strictTowerExchangeMateNormalization`: strict realization and mate equality.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types false
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

variable {X' X Y' Y : Scheme.{t}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {g : Y' ⟶ Y} {sq : ChosenCartesianSquare g' f' f g}

variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)

/-- Constant coefficient identifications agree around the chosen scheme square.
Source: strict normalization, proof steps 5--6; Stacks 07A7
(blueprint: lem-weil-pbc-strict-tower-exchange-mate-normalization).
Proof: the two coefficient maps send every constant a to the constant a on X'.
The sheafification universal property identifies them. Transporting along the
commutativity of the scheme square gives the displayed heterogeneous equality. -/
theorem exchangeConstant_coherent (sq : ChosenCartesianSquare g' f' f g) :
    HEq (proEtaleRingCompositeCoefficients g' f
      (exchangeConstantRing Y A) (exchangeConstantRing X A) (exchangeConstantRing X' A)
      (exchangeConstantIso f A) (exchangeConstantIso g' A))
      (proEtaleRingCompositeCoefficients f' g
        (exchangeConstantRing Y A) (exchangeConstantRing Y' A) (exchangeConstantRing X' A)
        (exchangeConstantIso g A) (exchangeConstantIso f' A)) := by
  sorry

/-- The constant-coefficient ringed square uses the specific constant-section identifications.
Source: strict normalization, paragraph 2; Stacks 07A7
(blueprint: lem-weil-pbc-strict-tower-exchange-mate-normalization). -/
def exchangeConstantSquare (sq : ChosenCartesianSquare g' f' f g) :
    StrictTowerRingedSquare sq where
  RY := exchangeConstantRing Y A
  RX := exchangeConstantRing X A
  RY' := exchangeConstantRing Y' A
  RX' := exchangeConstantRing X' A
  cf := exchangeConstantIso f A
  cg := exchangeConstantIso g A
  cg' := exchangeConstantIso g' A
  cf' := exchangeConstantIso f' A
  coherent := exchangeConstant_coherent sq

/-- The coefficient map sends a constant to its compatible residues in the finite tower.
Source: strict normalization, proof step 5; Stacks 099M
(blueprint: lem-weil-pbc-strict-tower-exchange-mate-normalization). -/
abbrev exchangeScalar (T : Scheme.{t}) : exchangeConstantRing T A ⟶ d.completedRing T :=
  adicDatumScalar T
    { toCompleteCoefficientDatum := d.toCompleteCoefficientDatum,
      quotientFinite := d.quotientFinite } ≫ (pbcCompletedComparison T d).hom

/-- The scalar maps commute with the canonical coefficient inverse images.
Source: strict normalization, proof step 5; Stacks 099M
(blueprint: lem-weil-pbc-strict-tower-exchange-mate-normalization).
Proof: compose the two maps with each finite projection. The profinite comparison
projection formula and naturality of the constant-section map identify both maps
with the constant quotient section a mod I^(n+1). Projections of the completed ring
are jointly monic, so the two scalar maps agree. -/
theorem exchangeScalar_comm {U V : Scheme.{t}} (f : U ⟶ V) :
    (exchangeConstantIso f A).hom ≫ exchangeScalar d U =
      (proEtaleSheafInverseImage f CommRingCat.{t + 1}).map (exchangeScalar d V) ≫
        (d.integralRingIso f).hom := by
  sorry

/-- Termwise restriction changes the scalar action but retains the whole strict diagram.
Source: strict normalization, paragraph 2; Stacks 03D3
(blueprint: lem-weil-pbc-strict-tower-exchange-mate-normalization). -/
abbrev exchangeTowerModuleRes (T : Scheme.{t}) :
    exchangeTowers T (d.completedRing T) ⥤ exchangeTowers T (exchangeConstantRing T A) :=
  (Functor.whiskeringRight _ _ _).obj (proEtaleRingRestrictScalars (exchangeScalar d T))

/-- Exactness of restriction on strict diagrams, with all transition maps retained.
Source: strict normalization, proof step 5; Stacks 03D3
(blueprint: lem-weil-pbc-strict-tower-exchange-mate-normalization).
Proof: ordinary restriction changes only the ring action and preserves kernels
and cokernels. These are computed pointwise in the strict functor category, giving
both finite-limit and finite-colimit preservation for the termwise functor. -/
theorem exchangeTowerModuleRes_exact (T : Scheme.{t}) :
    PreservesFiniteLimits (exchangeTowerModuleRes d T) ∧
      PreservesFiniteColimits (exchangeTowerModuleRes d T) := by
  sorry

/-- Left exact restriction. Source: strict normalization, proof step 5
(blueprint: lem-weil-pbc-strict-tower-exchange-mate-normalization). -/
instance exchangeTowerModuleRes_finiteLimits (T : Scheme.{t}) :
    PreservesFiniteLimits (exchangeTowerModuleRes d T) := (exchangeTowerModuleRes_exact d T).1

/-- Right exact restriction. Source: strict normalization, proof step 5
(blueprint: lem-weil-pbc-strict-tower-exchange-mate-normalization). -/
instance exchangeTowerModuleRes_finiteColimits (T : Scheme.{t}) :
    PreservesFiniteColimits (exchangeTowerModuleRes d T) := (exchangeTowerModuleRes_exact d T).2

/-- Exact restriction on derived strict towers.
Source: strict normalization, paragraph 2; Stacks 03D3
(blueprint: lem-weil-pbc-strict-tower-exchange-mate-normalization). -/
abbrev exchangeTowerRes (T : Scheme.{t}) :
    DerivedCategory (exchangeTowers T (d.completedRing T)) ⥤
      DerivedCategory (exchangeTowers T (exchangeConstantRing T A)) :=
  (exchangeTowerModuleRes d T).mapDerivedCategory

/-- Constant-coefficient inverse image on derived strict towers.
Source: strict normalization, paragraph 2; Stacks 07A7
(blueprint: lem-weil-pbc-strict-tower-exchange-mate-normalization). -/
abbrev exchangeConstantPull {U V : Scheme.{t}} (f : U ⟶ V) :=
  exchangeTowerPull f (exchangeConstantRing V A) (exchangeConstantRing U A)
    (exchangeConstantIso f A)

/-- Total right derived constant-coefficient direct image on strict towers.
Source: strict normalization, paragraph 2; Stacks 07A7
(blueprint: lem-weil-pbc-strict-tower-exchange-mate-normalization). -/
abbrev exchangeConstantPush {U V : Scheme.{t}} (f : U ⟶ V) :=
  exchangeTowerPush f (exchangeConstantRing V A) (exchangeConstantRing U A)
    (exchangeConstantIso f A)

/-- The ordinary restriction/pullback comparison is the termwise normalized module mate.
Source: strict normalization, proof step 5; Stacks 0D6D
(blueprint: lem-weil-pbc-strict-tower-exchange-mate-normalization). -/
def exchangeModuleResPull {U V : Scheme.{t}} (f : U ⟶ V) :
    d.towerModulePull f ⋙ exchangeTowerModuleRes d U ≅
      exchangeTowerModuleRes d V ⋙ exchangeTowerModulePull f
        (exchangeConstantRing V A) (exchangeConstantRing U A) (exchangeConstantIso f A) :=
  ((Functor.whiskeringRight ℕᵒᵖ _ _).mapIso
    (@asIso _ _ _ _ (proEtaleRingRestrictionPullbackInv f
      (exchangeConstantRing V A) (d.completedRing V)
      (exchangeConstantRing U A) (d.completedRing U)
      (exchangeScalar d V) (exchangeScalar d U)
      (exchangeConstantIso f A) (d.integralRingIso f) (exchangeScalar_comm d f))
      (proEtaleRingRestrictionPullbackInv_isIso f
        (exchangeConstantRing V A) (d.completedRing V)
        (exchangeConstantRing U A) (d.completedRing U)
        (exchangeScalar d V) (exchangeScalar d U)
        (exchangeConstantIso f A) (d.integralRingIso f) (exchangeScalar_comm d f)))).symm

/-- The derived comparison is exact descent of the ordinary identity on inverse-image sheaves.
Source: strict normalization, proof step 5; Stacks 0D6D
(blueprint: lem-weil-pbc-strict-tower-exchange-mate-normalization). -/
def exchangeResPull {U V : Scheme.{t}} (f : U ⟶ V) :
    d.towerPull f ⋙ exchangeTowerRes d U ≅
      exchangeTowerRes d V ⋙ exchangeConstantPull (A := A) f :=
  (Functor.mapDerivedCategoryCompIso (d.towerModulePull f)
    (exchangeTowerModuleRes d U)).symm ≪≫
  Functor.mapDerivedCategoryNatIso (exchangeModuleResPull d f) ≪≫
  Functor.mapDerivedCategoryCompIso (exchangeTowerModuleRes d V)
    (exchangeTowerModulePull f (exchangeConstantRing V A) (exchangeConstantRing U A)
      (exchangeConstantIso f A))

/-- The canonical right-derived unit on strict tower complexes, using complex localization.
Source: strict normalization, proof step 5; Stacks 07A5
(blueprint: lem-weil-pbc-strict-tower-exchange-mate-normalization). -/
def exchangeTowerDerivedUnit {U V : Scheme.{t}} (f : U ⟶ V)
    (R : Sheaf (ProEt.topology V) CommRingCat.{t + 1})
    (S : Sheaf (ProEt.topology U) CommRingCat.{t + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{t + 1}).obj R ≅ S)
    (C : CochainComplex (exchangeTowers U S) ℤ) :
    DerivedCategory.Q.obj
        (((exchangeTowerModulePush f R S c).mapHomologicalComplex (.up ℤ)).obj C) ⟶
      (exchangeTowerPush f R S c).obj (DerivedCategory.Q.obj C) :=
  (DerivedCategory.quotientCompQhIso _).inv.app _ ≫
    (exchangeTowerModulePush f R S c).rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient _ _).obj C) ≫
    (exchangeTowerPush f R S c).map ((DerivedCategory.quotientCompQhIso _).hom.app C)

/-- Ordinary direct image commutes with restriction by identity on every section and index.
Source: strict normalization, proof step 5; Stacks 0D6E
(blueprint: lem-weil-pbc-strict-tower-exchange-mate-normalization). -/
def exchangeModuleResPush {U V : Scheme.{t}} (f : U ⟶ V) :
    d.towerModulePush f ⋙ exchangeTowerModuleRes d V ≅
      exchangeTowerModuleRes d U ⋙ exchangeTowerModulePush f
        (exchangeConstantRing V A) (exchangeConstantRing U A) (exchangeConstantIso f A) :=
  (Functor.whiskeringRight ℕᵒᵖ _ _).mapIso
    (proEtaleRingRestrictionDirectImage f
      (exchangeConstantRing V A) (d.completedRing V)
      (exchangeConstantRing U A) (d.completedRing U)
      (exchangeScalar d V) (exchangeScalar d U)
      (exchangeConstantIso f A) (d.integralRingIso f) (exchangeScalar_comm d f))

/-- Normalization of the direct-image comparison by the universal right-derived units.
It records the identity on the full diagram before deriving, rather than evaluations alone.
Source: strict normalization, proof step 5; Stacks 0D6E
(blueprint: lem-weil-pbc-strict-tower-exchange-mate-normalization). -/
def ExchangeResPushNormalized {U V : Scheme.{t}} (f : U ⟶ V)
    (e : d.towerPush f ⋙ exchangeTowerRes d V ≅
      exchangeTowerRes d U ⋙ exchangeConstantPush (A := A) f) : Prop :=
  ∀ C : CochainComplex (exchangeTowers U (d.completedRing U)) ℤ,
    (exchangeTowerRes d V).map
        (exchangeTowerDerivedUnit f (d.completedRing V) (d.completedRing U)
          (d.integralRingIso f) C) ≫
      e.hom.app (DerivedCategory.Q.obj C) ≫
      (exchangeConstantPush (A := A) f).map
        ((exchangeTowerModuleRes d U).mapDerivedCategoryFactors.hom.app C) =
    (exchangeTowerModuleRes d V).mapDerivedCategoryFactors.hom.app
        (((d.towerModulePush f).mapHomologicalComplex (.up ℤ)).obj C) ≫
      DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex (exchangeModuleResPush d f) (.up ℤ)).hom.app C) ≫
      exchangeTowerDerivedUnit f (exchangeConstantRing V A) (exchangeConstantRing U A)
        (exchangeConstantIso f A)
        (((exchangeTowerModuleRes d U).mapHomologicalComplex (.up ℤ)).obj C)

/-- Restriction/direct-image comparison is uniquely determined by the universal units.
Source: strict normalization, proof step 5; Stacks 0D6E and 099M
(blueprint: lem-weil-pbc-strict-tower-exchange-mate-normalization).
Proof: scalar extension from constant to completed coefficients is flat by
constant-completion-equivalence. This remains true on the diagram site, since
its rings and tensor are fiberwise. Restriction, its right adjoint, preserves
K-injectives. On one K-injective tower representative the ordinary comparison
is identity on every section and transition, and both derived units are invertible.
This defines the comparison uniquely there. K-injective resolutions and the
universal property of the right-derived functor give its natural extension and
the displayed unit equation on every complex. -/
theorem exchangeResPush_existsUnique {U V : Scheme.{t}} (f : U ⟶ V) :
    ∃! e : d.towerPush f ⋙ exchangeTowerRes d V ≅
        exchangeTowerRes d U ⋙ exchangeConstantPush (A := A) f,
      ExchangeResPushNormalized d f e := by
  sorry

/-- The specified strict-tower direct-image comparison, with the unit normalization retained.
Source: strict normalization, proof step 5; Stacks 0D6E
(blueprint: lem-weil-pbc-strict-tower-exchange-mate-normalization). -/
def exchangeResPush {U V : Scheme.{t}} (f : U ⟶ V) :
    d.towerPush f ⋙ exchangeTowerRes d V ≅
      exchangeTowerRes d U ⋙ exchangeConstantPush (A := A) f :=
  (exchangeResPush_existsUnique d f).choose

/-- The left strict corner comparison, natural in the complete input tower.
Source: strict normalization, final paragraph; Stacks 0D6D--0D6E
(blueprint: lem-weil-pbc-strict-tower-exchange-mate-normalization). -/
def exchangeCornerB {X Y' Y : Scheme.{t}} (f : X ⟶ Y) (g : Y' ⟶ Y) :
    (d.towerPush f ⋙ d.towerPull g) ⋙ exchangeTowerRes d Y' ≅
      exchangeTowerRes d X ⋙
        (exchangeConstantPush (A := A) f ⋙ exchangeConstantPull (A := A) g) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (exchangeResPull d g) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (exchangeResPush d f) _ ≪≫ Functor.associator _ _ _

/-- The right strict corner comparison, natural in the complete input tower.
Source: strict normalization, final paragraph; Stacks 0D6D--0D6E
(blueprint: lem-weil-pbc-strict-tower-exchange-mate-normalization). -/
def exchangeCornerD {X' X Y' : Scheme.{t}} (g' : X' ⟶ X) (f' : X' ⟶ Y') :
    (d.towerPull g' ⋙ d.towerPush f') ⋙ exchangeTowerRes d Y' ≅
      exchangeTowerRes d X ⋙
        (exchangeConstantPull (A := A) g' ⋙ exchangeConstantPush (A := A) f') :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (exchangeResPush d f') ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (exchangeResPull d g') _ ≪≫ Functor.associator _ _ _

/-- The explicit strict H: inverse pullback/reduction identification followed by h.
Its source is R(M), its target is B, and its projection factor is the adjunct
of the ambient counit tensored with the whole quotient diagram. The preceding
inverse chi identifies R(M) with L_g R_Y(Rf_*K), so h is H after chi.
Source: strict normalization, paragraph 3; Stacks 0B56
(blueprint: lem-weil-pbc-strict-tower-exchange-mate-normalization). -/
def exchangeRealizationH (K : d.derived X) :
    (completedReductionTower Y' d).obj ((d.pull g).obj ((d.push f).obj K)) ≅
      (d.towerPull g).obj ((d.towerPush f).obj ((completedReductionTower X d).obj K)) :=
  ((d.reductionTowerPullbackIso g).symm.app ((d.push f).obj K)) ≪≫
    (d.towerPull g).mapIso (asIso (d.towerProjection f K))

/-- The explicit strict H prime, from R(N) to D: the diagram projection formula
for E followed by direct image of the inverse reduction/pullback identification.
Both H and H prime are isomorphisms before any evaluation is taken.
Source: strict normalization, paragraph 3; Stacks 0B56
(blueprint: lem-weil-pbc-strict-tower-exchange-mate-normalization). -/
def exchangeRealizationHPrime (K : d.derived X) :
    (completedReductionTower Y' d).obj ((d.push f').obj ((d.pull g').obj K)) ≅
      (d.towerPush f').obj ((d.towerPull g').obj ((completedReductionTower X d).obj K)) :=
  asIso (d.towerProjection f' ((d.pull g').obj K)) ≪≫
    (d.towerPush f').mapIso ((d.reductionTowerPullbackIso g').symm.app K)

/-- The specified strict lift commutes with every morphism of the input object.
Source: strict normalization, final paragraph; Stacks 0E48
(blueprint: lem-weil-pbc-strict-tower-exchange-mate-normalization).
Proof: reduction and the ambient exchange are natural. The projection arrow is
its adjunction mate and hence natural in K. Pullback and direct image preserve
these naturality equations. Compose them for h inverse, v and h prime to obtain
the displayed equation for the specified strict composite towerV'. -/
theorem exchangeStrict_naturality (sq : ChosenCartesianSquare g' f' f g)
    {K L : d.derived X} (a : K ⟶ L) :
    (d.towerPull g).map ((d.towerPush f).map ((completedReductionTower X d).map a)) ≫
        d.towerV' sq L =
      d.towerV' sq K ≫
        (d.towerPush f').map ((d.towerPull g').map ((completedReductionTower X d).map a)) := by
  sorry

/-- The specified finite exchange is a natural transformation on strict derived towers.
Its naturality is inherited from the already specified projection-formula tower maps.
Source: strict normalization, final paragraph
(blueprint: lem-weil-pbc-strict-tower-exchange-mate-normalization). -/
def exchangeStrictNatTrans (sq : ChosenCartesianSquare g' f' f g) :
    (completedReductionTower X d ⋙ d.towerPush f) ⋙ d.towerPull g ⟶
      (completedReductionTower X d ⋙ d.towerPull g') ⋙ d.towerPush f' where
  app K := d.towerV' sq K
  naturality _K _L a := exchangeStrict_naturality d sq a

/-- Strict tower exchange, normalized by projection formulas, agrees with the
canonical constant-coefficient mate under the specified corner comparisons.
The first conjunct explicitly fixes v prime as H inverse, R(e), H prime, with
B and D the displayed targets of H and H prime. The second conjunct identifies
its evaluations, including the finite witness transport and both projection maps.
The last conjunct is the equation in D(T_Y prime), with the specified b and d.

Source: blueprint completed-exchange-coherence, first two proof sentences;
Stacks 07A7 (blueprint: lem-weil-pbc-strict-tower-exchange-mate-normalization).

Proof, following the six DAG steps:
1. Realize strict module towers on the ringed diagram site. Termwise pullback and
   direct image are adjoint; derive that precise termwise adjunction, using the
   fraction normalization of preDerivedAdjunctionGeneral. Tensor and pullback are
   evaluated using K-flat flat-term resolutions on the one diagram site.
2. The diagonal preserves K-injectives because its exact left adjoint is evaluation
   at the terminal positive index 1. Thus direct image of diagonal K is diagonal
   Rf_*K. Diagonal K-flat resolutions compute strict reduction with its quotient
   transitions. The unit, counit, and composition on diagonal objects are the
   diagonals of the ordinary ones, so their mate is diagonal ambient exchange.
3. Form H and H prime by the counit-tensor adjunct formula. Their evaluations are
   precisely h_n and h'_n, with the finite scalar action retained. Perfect finite
   coefficients make each component invertible. Levelwise tower cohomology makes
   H and H prime invertible. The finite rectangle identifies the displayed strict
   conjugate with the specified witness-transported finite exchange at every level.
4. Ringed tensor/exchange coherence on the diagram site gives W H = H' R(e).
   Compose with H inverse. This proves equality of strict tower maps themselves,
   without inferring equality from their evaluations.
5. Restrict along the compatible-residue scalar maps. Exact restriction commutes
   with pullback, and the K-injective/unit-normalized direct-image comparison gives
   the natural isomorphisms b and d. Their normalization is the constant-to-completed
   finite-reduction comparison together with the direct-image evaluation comparison.
6. These comparisons preserve units, counits, and pullback composition. Transposing
   the restricted W yields theta followed by the counit for the constant-coefficient
   tower adjunction. The mate bijection identifies it with the canonical tower mate.
   Substitute the strict projection-formula realization from step 4. Every operation
   is natural in K, so the corner identifications and the equality are natural too.
   Properness and the individually chosen etale witnesses interpret finite exchange;
   no common lower bound or cross-level compatibility of these witnesses is used. -/
theorem strictTowerExchangeMateNormalization
    (sq : ChosenCartesianSquare g' f' f g) [IsProper f]
    (K : d.derived X) (hK : d.TowerComplete X K)
    (W : ∀ n : ℕ, FiniteEtaleOriginWitness X (A ⧸ d.ideal ^ (n + 1))
      ((d.reduction X n).obj K)) :
    d.towerV' sq K =
      (exchangeRealizationH (f := f) (g := g) d K).inv ≫
        (completedReductionTower Y' d).map ((d.integralExchange sq).app K) ≫
        (exchangeRealizationHPrime (f' := f') (g' := g') d K).hom ∧
    (∀ n : ℕ, ∃ α : ∀ i : Fin 4,
        (reductionTowerDerivedEvaluation Y'
            (reductionModuleRing Y' (d.completedRing Y')) n).obj
          (d.fourTowerCorners (f := f) (f' := f') (g := g) (g' := g') K i) ≅
        (reductionDerivedRestrict Y' (d.projection Y' n)).obj
          (d.fourCorners (f := f) (f' := f') (g := g) (g' := g') K n i),
      (reductionTowerDerivedEvaluation Y'
          (reductionModuleRing Y' (d.completedRing Y')) n).map
          (d.towerH (f := f) (f' := f') (g := g) (g' := g') K).hom ≫ (α 1).hom =
        (α 0).hom ≫ (reductionDerivedRestrict Y' (d.projection Y' n)).map
          (d.fourArrows sq K hK W n).h.hom ∧
      (reductionTowerDerivedEvaluation Y'
          (reductionModuleRing Y' (d.completedRing Y')) n).map
          (d.towerH' (f := f) (f' := f') (g := g) (g' := g') K).hom ≫ (α 3).hom =
        (α 2).hom ≫ (reductionDerivedRestrict Y' (d.projection Y' n)).map
          (d.fourArrows sq K hK W n).h'.hom ∧
      (reductionTowerDerivedEvaluation Y'
          (reductionModuleRing Y' (d.completedRing Y')) n).map
          (d.towerV sq K) ≫ (α 2).hom =
        (α 0).hom ≫ (reductionDerivedRestrict Y' (d.projection Y' n)).map
          (d.fourArrows sq K hK W n).v ∧
      (reductionTowerDerivedEvaluation Y'
          (reductionModuleRing Y' (d.completedRing Y')) n).map
          (d.towerV' sq K) ≫ (α 3).hom =
        (α 1).hom ≫ (reductionDerivedRestrict Y' (d.projection Y' n)).map
          (d.fourArrows sq K hK W n).v'.hom) ∧
    (exchangeTowerRes d Y').map (d.towerV' sq K) ≫
        (exchangeCornerD d g' f').hom.app ((completedReductionTower X d).obj K) =
      (exchangeCornerB d f g).hom.app ((completedReductionTower X d).obj K) ≫
        (exchangeConstantSquare (A := A) sq).exchangeTowerMate.app
          ((exchangeTowerRes d X).obj ((completedReductionTower X d).obj K)) := by
  sorry

end AlgebraicGeometry.Scheme
