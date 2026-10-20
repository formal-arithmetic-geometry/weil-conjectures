/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q03
-/
module

public import Sheaf.SixFunctors.IntegralCompactificationBridgeWords
public import Sheaf.SixFunctors.ConstantSemilinearGeneratorComparison
public import Sheaf.Paper.QcqsCompactSupportRealization
public import Sheaf.Paper.SfCbcCompactSupportCompositionLimit
public import Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus
public import WeilConjectures.Compactification.Triangle
import Sheaf.CategoryTheory.RingedTowerPushforwardLimitComparison
import Sheaf.SixFunctors.AmbientProperOpenPasting

/-! # Integral compactification comparison bridge

Source: blueprint main-20261015, fix-lem-exchanges, proof Step 5; the additional
constant/semilinear comparison obligation
(blueprint: lem-sf-integral-compactification-comparison-bridge).

The helpers fix the small-site coordinate transports by sections and adjunction mates.
The two composition maps are constructed independently, before any finite evaluation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralCompactificationBridge
open IntegralSystemRealization GeneratorReduction

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

section Integral
variable (k : Type u) [Field k] (hl : IsUnit (l : k))
  {X Y : Scheme.{u}}
  [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
  {f : X ⟶ Y} [f.IsOver (Spec (.of k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]

/-- Direct identification for one compactification, from the universal proper/limit
comparison, the actual open reduction mate and inverse reconstruction unit, then the
published strict-quotient realization. No expression-realization family is selected.
Source: blueprint fix-lem-exchanges Step 5; Bhatt--Scholze Definition 6.7.6
(blueprint: lem-sf-integral-compactification-comparison-bridge). -/
def directIdentification {D : FiniteFieldDatum.{u}}
    (o : IntegralSystemRealization.Operations l E) (r : Realizations l E D o)
    (c : Compactification f) (K : sfIntegralConstructibleCategory l E X) :
    (coefficientSequenceLimit l E Y).obj ((systemWord l E o c).obj
      ((calculus l E X).reduction.obj K.obj)) ⟶
        ((sfCompactSupportFiniteIntegralFunctor l k hl c E).obj K).obj :=
  (r.realizationModel.push l E c.g).hom.app
    ((IntegralSystemRealization.Operations.shriek l E o c.i).obj
      ((calculus l E X).reduction.obj K.obj)) ≫
  (ringedPush l E c.g).map
    ((coefficientSequenceLimit l E c.Z).map
      ((r.realizationModel.openReduction l E c.i).app K.obj) ≫
      inverseOrZero ((calculus l E c.Z).adjunction.unit.app
        ((ringedOpen l E c.i).obj K.obj))) ≫
  (sfQcqsCompactSupportRealization l E k hl c).hom.app K

/-- The canonical passage from the actual compact-support output to its completed word.
The proper comparison is normalized by the universal derived unit; the open factor
uses the actual completion unit. The adjunction is a presentation of those fixed functors.
Source: blueprint fix-lem-exchanges Step 5
(blueprint: lem-sf-integral-compactification-comparison-bridge). -/
def wordCoordinates (c : Compactification f)
    (a : sfCbcModelExtension c.i (constantRing l E) ⊣
      (sfCbcMorphism c.i).modulePull (ULift.{u + 1} (constantRing l E)))
    (K : sfIntegralConstructibleCategory l E X) :
    (H l E Y).obj (((sfCompactSupportFiniteIntegralFunctor l k hl c E).obj K).obj) ⟶
      ((word c).complete (constantDatum l E)).obj ((H l E X).obj K.obj) :=
  (H l E Y).map ((sfQcqsCompactSupportRealization l E k hl c).inv.app K) ≫
  (integralDirectScalarIso l E c.g).hom.app ((ringedOpen l E c.i).obj K.obj) ≫
  ((sfCbcMorphism c.g).push (ULift.{u + 1} (constantRing l E))).map
    (openSigmaHom l E c.i a K.obj)

/-- Exactly L(q_W) eta following the fixed single-compactification coordinates.
Source: blueprint fix-lem-exchanges Step 5
(blueprint: lem-sf-integral-compactification-comparison-bridge). -/
def wordComparison (c : Compactification f)
    (a : sfCbcModelExtension c.i (constantRing l E) ⊣
      (sfCbcMorphism c.i).modulePull (ULift.{u + 1} (constantRing l E)))
    (K : sfIntegralConstructibleCategory l E X) :=
  wordCoordinates l E k hl c a K ≫
    ((word c).a (constantDatum l E) (constantReducedUnits l E)).app ((H l E X).obj K.obj)

/-- The common-window condition for the actual intermediate strict systems of one word.
The origin witnesses and normalization are those of the published generator domain.
Source: Stacks 0941; the domain paragraph of this node
(blueprint: lem-sf-integral-compactification-comparison-bridge). -/
def systemWordDomain (o : IntegralSystemRealization.Operations l E)
    (c : Compactification f) (M : System l E X) (lo hi torLo torHi : ℤ) : Prop :=
  SystemAdmissible l E X M lo hi torLo torHi ∧
    SystemAdmissible l E c.Z
      ((IntegralSystemRealization.Operations.shriek l E o c.i).obj M)
        lo hi torLo torHi ∧
    SystemAdmissible l E Y ((systemWord l E o c).obj M) lo hi torLo torHi

/-- The integral input, its open output, and its actual strict quotient word have
compatible origins, normalized reductions and one fixed cohomological and Tor window.
Source: Stacks 0941; the domain paragraph of this node
(blueprint: lem-sf-integral-compactification-comparison-bridge). -/
def singleDomain (o : IntegralSystemRealization.Operations l E)
    (c : Compactification f) (K : sfIntegralConstructibleCategory l E X)
    (lo hi torLo torHi : ℤ) : Prop :=
  Admissible l E (calculus l E X) K.obj lo hi torLo torHi ∧
    Admissible l E (calculus l E c.Z) ((ringedOpen l E c.i).obj K.obj)
      lo hi torLo torHi ∧
    systemWordDomain l E o c ((calculus l E X).reduction.obj K.obj) lo hi torLo torHi

end Integral
section Integral
variable (k : Type u) [Field k] (hl : IsUnit (l : k))
  {X Y Z : Scheme.{u}}
  [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))] [Z.Over (Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
  [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
  {f : X ⟶ Y} {g : Y ⟶ Z}
  [f.IsOver (Spec (.of k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  [g.IsOver (Spec (.of k))] [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]

/-- The concatenated comparison uses exactly the recursive q of the concatenated word.
Source: blueprint fix-lem-exchanges Step 5
(blueprint: lem-sf-integral-compactification-comparison-bridge). -/
def compositeWordComparison (cf : Compactification f) (cg : Compactification g)
    (af : sfCbcModelExtension cf.i (constantRing l E) ⊣
      (sfCbcMorphism cf.i).modulePull (ULift.{u + 1} (constantRing l E)))
    (ag : sfCbcModelExtension cg.i (constantRing l E) ⊣
      (sfCbcMorphism cg.i).modulePull (ULift.{u + 1} (constantRing l E)))
    (K : sfIntegralConstructibleCategory l E X) :=
  wordCoordinates l E k hl cg ag ((sfCompactSupportFiniteIntegralFunctor l k hl cf E).obj K) ≫
  ((word cg).complete (constantDatum l E)).map (wordCoordinates l E k hl cf af K) ≫
  ((word cf).appendCompleteIso (constantDatum l E) (word cg)).inv.app ((H l E X).obj K.obj) ≫
  (((word cf).append (word cg)).a (constantDatum l E) (constantReducedUnits l E)).app
    ((H l E X).obj K.obj) ≫
  (constantLimit l E Z).map
    (((word cf).appendStrictIso (word cg)).hom.app
      ((constantReduction l E X).obj ((H l E X).obj K.obj)))

/-- The specified constant-tower composition formula, prior to finite evaluation.
Source: blueprint fix-lem-exchanges (2),(4), proof Step 5
(blueprint: lem-sf-integral-compactification-comparison-bridge). -/
def constantComparison (t : Compactification.Triangle f g)
    [QuasiCompact t.q] [QuasiCompact t.cg.i]
    (af : sfCbcModelExtension t.cf.i (constantRing l E) ⊣
      (sfCbcMorphism t.cf.i).modulePull (ULift.{u + 1} (constantRing l E)))
    (ag : sfCbcModelExtension t.cg.i (constantRing l E) ⊣
      (sfCbcMorphism t.cg.i).modulePull (ULift.{u + 1} (constantRing l E)))
    (ah : sfCbcModelExtension t.cfg.i (constantRing l E) ⊣
      (sfCbcMorphism t.cfg.i).modulePull (ULift.{u + 1} (constantRing l E)))
    (K : sfIntegralConstructibleCategory l E X) :=
  compositeWordComparison l E k hl t.cf t.cg af ag K ≫
    (constantLimit l E Z).map (constantBeta l E t af ag ah
      ((constantReduction l E X).obj ((H l E X).obj K.obj))) ≫
    inverseOrZero (wordComparison l E k hl t.cfg ah K)

/-- Full faithfulness on complete coefficient objects uniquely lifts the specified
constant-word coordinate formula to an actual integral morphism.
Source: Stacks 099M; blueprint fix-lem-exchanges (2),(4), proof Step 5
(blueprint: lem-sf-integral-compactification-comparison-bridge).
Proof: the source and target are outputs of the published integral compact-support
functors, hence complete. The constant-completion equivalence is fully faithful on
these objects. Its Hom bijection gives existence and uniqueness for the prescribed
coordinate morphism; it selects no arbitrary expression-realization isomorphism. -/
theorem completedComparison_existsUnique (t : Compactification.Triangle f g)
    [QuasiCompact t.q] [QuasiCompact t.cg.i]
    (af : sfCbcModelExtension t.cf.i (constantRing l E) ⊣
      (sfCbcMorphism t.cf.i).modulePull (ULift.{u + 1} (constantRing l E)))
    (ag : sfCbcModelExtension t.cg.i (constantRing l E) ⊣
      (sfCbcMorphism t.cg.i).modulePull (ULift.{u + 1} (constantRing l E)))
    (ah : sfCbcModelExtension t.cfg.i (constantRing l E) ⊣
      (sfCbcMorphism t.cfg.i).modulePull (ULift.{u + 1} (constantRing l E)))
    (K : sfIntegralConstructibleCategory l E X) :
    ∃! a : ((sfCompactSupportFiniteIntegralFunctor l k hl t.cg E).obj
          ((sfCompactSupportFiniteIntegralFunctor l k hl t.cf E).obj K)).obj ⟶
        ((sfCompactSupportFiniteIntegralFunctor l k hl t.cfg E).obj K).obj,
      (H l E Z).map a = constantComparison l E k hl t af ag ah K := by
  sorry

/-- The specified completed composition, determined uniquely by its constant-word image.
Source: blueprint fix-lem-exchanges (2),(4), proof Step 5
(blueprint: lem-sf-integral-compactification-comparison-bridge). -/
def completedComparison (t : Compactification.Triangle f g)
    [QuasiCompact t.q] [QuasiCompact t.cg.i]
    (af : sfCbcModelExtension t.cf.i (constantRing l E) ⊣
      (sfCbcMorphism t.cf.i).modulePull (ULift.{u + 1} (constantRing l E)))
    (ag : sfCbcModelExtension t.cg.i (constantRing l E) ⊣
      (sfCbcMorphism t.cg.i).modulePull (ULift.{u + 1} (constantRing l E)))
    (ah : sfCbcModelExtension t.cfg.i (constantRing l E) ⊣
      (sfCbcMorphism t.cfg.i).modulePull (ULift.{u + 1} (constantRing l E)))
    (K : sfIntegralConstructibleCategory l E X) :=
  (completedComparison_existsUnique l E k hl t af ag ah K).exists.choose

/-- The exact integral counit composite in the node's displayed conclusion.
The inverseOrZero convention is used only to type this ambient expression; the
bridge theorem asserts invertibility on the stated domain, so these are the unique inverses.
Source: blueprint fix-lem-exchanges Step 5
(blueprint: lem-sf-integral-compactification-comparison-bridge). -/
def semilinearComparison {D : FiniteFieldDatum.{u}}
    (o : IntegralSystemRealization.Operations l E) (r : Realizations l E D o)
    (t : Compactification.Triangle f g) [QuasiCompact t.q] [QuasiCompact t.cg.i]
    (K : sfIntegralConstructibleCategory l E X) :=
  inverseOrZero (directIdentification l E k hl o r t.cg
    ((sfCompactSupportFiniteIntegralFunctor l k hl t.cf E).obj K)) ≫
  (coefficientSequenceLimit l E Z).map ((systemWord l E o t.cg).map
    ((calculus l E Y).reduction.map
      (inverseOrZero (directIdentification l E k hl o r t.cf K)))) ≫
  (coefficientSequenceLimit l E Z).map ((systemWord l E o t.cg).map
    ((calculus l E Y).adjunction.counit.app
      ((systemWord l E o t.cf).obj ((calculus l E X).reduction.obj K.obj)))) ≫
  (coefficientSequenceLimit l E Z).map
    (systemBeta l E o r t ((calculus l E X).reduction.obj K.obj)) ≫
  directIdentification l E k hl o r t.cfg K

/-- All words and the additional proper/open and counit intermediate systems share
these finite windows and retain the published compatible etale-origin witnesses.
Source: the explicit domain paragraph of this node
(blueprint: lem-sf-integral-compactification-comparison-bridge). -/
def bridgeDomain (o : IntegralSystemRealization.Operations l E)
    (t : Compactification.Triangle f g) (K : sfIntegralConstructibleCategory l E X)
    (lo hi torLo torHi : ℤ) : Prop :=
  singleDomain l E o t.cf K lo hi torLo torHi ∧
  singleDomain l E o t.cg ((sfCompactSupportFiniteIntegralFunctor l k hl t.cf E).obj K)
    lo hi torLo torHi ∧
  singleDomain l E o t.cfg K lo hi torLo torHi ∧
  systemWordDomain l E o t.cg
    ((systemWord l E o t.cf).obj ((calculus l E X).reduction.obj K.obj))
      lo hi torLo torHi ∧
  systemWordDomain l E o t.cg
    ((calculus l E Y).reduction.obj ((coefficientSequenceLimit l E Y).obj
      ((systemWord l E o t.cf).obj ((calculus l E X).reduction.obj K.obj))))
      lo hi torLo torHi ∧
  SystemAdmissible l E t.cfg.Z
    ((IntegralSystemRealization.Operations.shriek l E o t.q).obj
      ((IntegralSystemRealization.Operations.shriek l E o t.cf.i).obj
        ((calculus l E X).reduction.obj K.obj))) lo hi torLo torHi ∧
  SystemAdmissible l E t.cg.Z
    ((IntegralSystemRealization.Operations.push l E o t.p).obj
      ((IntegralSystemRealization.Operations.shriek l E o t.cfg.i).obj
        ((calculus l E X).reduction.obj K.obj))) lo hi torLo torHi

/-- The canonical d and normalized word comparisons are invertible on the supplied domain.
Source: Stacks 0941; blueprint fix-lem-exchanges Step 5
(blueprint: lem-sf-integral-compactification-comparison-bridge).
Proof: the normalized quotient systems reconstruct their total limits, including the
open output. The universal proper/limit comparison is invertible. The projection-normalized
realization identifies this composite with the actual compact-support model. The word
reconstruction theorem applies to the same common windows and compatible etale origins,
so its comparisons, after the canonical coefficient identifications, are invertible. -/
theorem comparisons_isIso {D : FiniteFieldDatum.{u}}
    (o : IntegralSystemRealization.Operations l E) (r : Realizations l E D o)
    (t : Compactification.Triangle f g) [QuasiCompact t.q] [QuasiCompact t.cg.i]
    (af : sfCbcModelExtension t.cf.i (constantRing l E) ⊣
      (sfCbcMorphism t.cf.i).modulePull (ULift.{u + 1} (constantRing l E)))
    (ag : sfCbcModelExtension t.cg.i (constantRing l E) ⊣
      (sfCbcMorphism t.cg.i).modulePull (ULift.{u + 1} (constantRing l E)))
    (ah : sfCbcModelExtension t.cfg.i (constantRing l E) ⊣
      (sfCbcMorphism t.cfg.i).modulePull (ULift.{u + 1} (constantRing l E)))
    (K : sfIntegralConstructibleCategory l E X) (lo hi torLo torHi : ℤ)
    (_hK : bridgeDomain l E k hl o t K lo hi torLo torHi) :
    IsIso (directIdentification l E k hl o r t.cf K) ∧
    IsIso (directIdentification l E k hl o r t.cg
      ((sfCompactSupportFiniteIntegralFunctor l k hl t.cf E).obj K)) ∧
    IsIso (directIdentification l E k hl o r t.cfg K) ∧
    IsIso (wordComparison l E k hl t.cfg ah K) ∧
    IsIso (compositeWordComparison l E k hl t.cf t.cg af ag K) := by
  sorry

end Integral

/-- The coefficient prime is a unit in the fixed algebraic closure of the finite field.
Source: the coefficient paragraph of this node; blueprint fix-lem-exchanges
(blueprint: lem-sf-integral-compactification-comparison-bridge).
Proof: the specified cardinality of the finite base field gives characteristic D.p.
The algebraic closure has the same characteristic. A distinct prime has nonzero cast
and hence is a unit in this field. -/
theorem coefficientPrimeUnit (D : FiniteFieldDatum.{u}) (_hl : l ≠ D.p) :
    IsUnit (l : D.k) := by
  sorry

section FiniteField
variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Y Z : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))] [Z.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [IsSeparated (Y ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Z ↘ Spec (.of D.k))] [QuasiCompact (Z ↘ Spec (.of D.k))]
  [IsSeparated (Z ↘ Spec (.of D.k))]
  {f : X ⟶ Y} {g : Y ⟶ Z}
  [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  [g.IsOver (Spec (.of D.k))] [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]

/-- The integral compactification comparison bridge, as equality of actual integral
morphisms, with its naturality on the supplied domain. The definition `completedComparison` uses
exactly the source's coordinate formula,
with the actual recursive strict-word comparison. Full faithfulness on complete
objects uniquely determines its components, independently of the semilinear composite.

Source: blueprint main-20261015, fix-lem-exchanges (2),(4), proof Step 5; the additional
normalization obligation (blueprint: lem-sf-integral-compactification-comparison-bridge).

Proof, Step 1: scalar restriction gives U R = R^T H and H L = L^T U with their actual
units. Step 2: for d : L A -> F, the adjunct of d inverse is e_A R(d inverse);
applying L and composing with the unit gives d inverse by naturality and the triangle.
Step 3: the direct identification for a compactification is the universal proper/limit
comparison followed by the open reduction mate and inverse completion unit, then the
projection-normalized strict-quotient realization. Its adjunct is therefore exactly
r_v = e R(d_v inverse). Step 4: the generator comparison identifies its scalar restriction
with the recursively normalized q for the two-letter word; it uses the same coefficients,
quotient transitions, and completion unit. Step 5: the word adjunct is a_v = H(d_v inverse).
Step 6: recursion for the concatenated word gives H of d_g inverse, followed by L B_g
R(d_f inverse), followed by L B_g(e). Step 7: the proper/open scalar mate and its unit
and counit identify beta with the normalized constant-tower beta, including the unital
compositors. Step 8: substitute these identities in the defining coordinate equation and use
faithfulness of H on
the complete integral source and target. Naturality follows from the naturality of every canonical
factor and uniqueness of the lift under the complete-coefficient equivalence. Step 9: for identity
compactifications the triangles identify
F_id with L R and d_id with its identity; an empty open or zero input gives zero objects
and the unique map between them. No finite evaluation or arbitrary realization is used. -/
theorem integralCompactificationComparisonBridge
    (o : IntegralSystemRealization.Operations l E) (r : Realizations l E D o)
    (t : Compactification.Triangle f g)
    [QuasiCompact t.cf.i] [QuasiCompact t.cg.i] [QuasiCompact t.cfg.i] [QuasiCompact t.q]
    (af : sfCbcModelExtension t.cf.i (constantRing l E) ⊣
      (sfCbcMorphism t.cf.i).modulePull (ULift.{u + 1} (constantRing l E)))
    (ag : sfCbcModelExtension t.cg.i (constantRing l E) ⊣
      (sfCbcMorphism t.cg.i).modulePull (ULift.{u + 1} (constantRing l E)))
    (ah : sfCbcModelExtension t.cfg.i (constantRing l E) ⊣
      (sfCbcMorphism t.cfg.i).modulePull (ULift.{u + 1} (constantRing l E)))
    :
    (∀ (K : sfIntegralConstructibleCategory l E X) (lo hi torLo torHi : ℤ),
      bridgeDomain l E D.k (coefficientPrimeUnit l D hl) o t K lo hi torLo torHi →
      completedComparison l E D.k (coefficientPrimeUnit l D hl) t af ag ah K =
        semilinearComparison l E D.k (coefficientPrimeUnit l D hl) o r t K) ∧
    (∀ (K K' : sfIntegralConstructibleCategory l E X) (m : K ⟶ K')
      (lo hi torLo torHi : ℤ),
      bridgeDomain l E D.k (coefficientPrimeUnit l D hl) o t K lo hi torLo torHi →
      bridgeDomain l E D.k (coefficientPrimeUnit l D hl) o t K' lo hi torLo torHi →
      (sfIntegralConstructible l E Z).ι.map
          ((sfCompactSupportFiniteIntegralFunctor l D.k (coefficientPrimeUnit l D hl)
            t.cf E ⋙ sfCompactSupportFiniteIntegralFunctor l D.k (coefficientPrimeUnit l D hl)
              t.cg E).map m) ≫
        semilinearComparison l E D.k (coefficientPrimeUnit l D hl) o r t K' =
      semilinearComparison l E D.k (coefficientPrimeUnit l D hl) o r t K ≫
        (sfIntegralConstructible l E Z).ι.map
          ((sfCompactSupportFiniteIntegralFunctor l D.k (coefficientPrimeUnit l D hl)
            t.cfg E).map m)) := by
  sorry

end FiniteField
end WeilConjectures.IntegralCompactificationBridge
