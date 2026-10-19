/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q70
-/
module

public import Sheaf.Paper.CompleteCoefficientDatum
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Sheaf.CategoryTheory.DiagramSiteRealization
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Sites.Limits
public import Sheaf.Algebra.Homology.KFlat
public import Sheaf.Paper.CompletedPullbackAdjunction
public import Sheaf.Paper.ConstantCompletionEquivalence
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import Sheaf.Paper.ProEtaleConstantReductionTower
import Sheaf.Paper.RingedTopoiTensorComparisonData
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import Sheaf.Paper.RingedTopoiTensorComparisonConstruction
import Sheaf.Paper.KFlatRingedToposPullback
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitOfUniverses
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Sheaf.Paper.AdicCompletionReduction

import Sheaf.Paper.CompletionMap
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
/-! # The completion unit and completed pullback on strict quotient towers

Source: smooth-purity blueprint, fix-lem-exchanges, Proof Steps 2 and 5;
Stacks Tags 099M and 099N (blueprint: lem-sf-cbc-completed-pullback-unit-tower).

The canonical small model of the original pro-etale site only enlarges its Hom
universe. Its topology and base-change functor are the published transports of
those on the original site. All coefficient rings are constant sheaves, with no
finiteness assumption on their underlying sets. Level n means exponent n+1.
The existing quotient presentation fixes every strict transition and its K-flat
computation; the existing reduction/pullback comparison fixes tensor reassociation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.AdicSites
namespace AlgebraicGeometry.Scheme.CompletedPullbackUnitTower

/-- The published small model, with precisely the original pro-etale topology.
Source: Stacks 09A5 (blueprint: lem-sf-cbc-completed-pullback-unit-tower). -/
def site (T : Scheme.{t}) : Site.{t + 1} where
  objects := proEtaleSiteModel T
  topology := proEtaleModelTopology T

/-- The canonical geometric inverse image on the published small models.
Source: Stacks 00VC and 099N (blueprint: lem-sf-cbc-completed-pullback-unit-tower). -/
def inverse {T' T : Scheme.{t}} (g : T' ⟶ T) :
    Sheaf (proEtaleModelTopology T) (Type (t + 1)) ⥤
      Sheaf (proEtaleModelTopology T') (Type (t + 1)) :=
  letI := proEtaleModelBaseChange_isContinuous g
  (proEtaleModelBaseChange g).sheafPullback (Type (t + 1))
    (proEtaleModelTopology T) (proEtaleModelTopology T')

/-- The corresponding sectionwise direct image on these same models.
Source: Stacks 00VC (blueprint: lem-sf-cbc-completed-pullback-unit-tower). -/
def direct {T' T : Scheme.{t}} (g : T' ⟶ T) :
    Sheaf (proEtaleModelTopology T') (Type (t + 1)) ⥤
      Sheaf (proEtaleModelTopology T) (Type (t + 1)) :=
  letI := proEtaleModelBaseChange_isContinuous g
  (proEtaleModelBaseChange g).sheafPushforwardContinuous (Type (t + 1))
    (proEtaleModelTopology T) (proEtaleModelTopology T')

/-- The defining geometric adjunction, rather than an arbitrary functor adjunction.
Source: Stacks 00VC (blueprint: lem-sf-cbc-completed-pullback-unit-tower). -/
def adjunction {T' T : Scheme.{t}} (g : T' ⟶ T) : inverse g ⊣ direct g :=
  letI := proEtaleModelBaseChange_isContinuous g
  (proEtaleModelBaseChange g).sheafAdjunctionContinuous (Type (t + 1))
    (proEtaleModelTopology T) (proEtaleModelTopology T')

/-- The geometric inverse image is left exact on the equivalent small model.
Source: Stacks 00VC (blueprint: lem-sf-cbc-completed-pullback-unit-tower).
Proof: scheme base change preserves finite limits on the pro-etale sites. The
AsSmall equivalences preserve those limits. The sheaf inverse image is left Kan
extension followed by left exact sheafification, so preserves finite limits. -/
@[instance]
theorem inverse_finiteLimits {T' T : Scheme.{t}} (g : T' ⟶ T) :
    PreservesFiniteLimits (inverse g) := by
  sorry

/-- The ring-valued inverse image on the transported small pro-etale sites.  This is
the same left-Kan-extension/sheafification construction as `inverse`, with the
commutative-ring value category; it is the transported version of
`proEtaleSheafInverseImage` from `def-weil-proetale-inverse-image`.
Source: Stacks 00YV and 03D2 (blueprint: lem-sf-cbc-completed-pullback-unit-tower). -/
noncomputable def transportedRingInverseImage {T' T : Scheme.{t}} (g : T' ⟶ T) :
    Sheaf (proEtaleModelTopology T) CommRingCat.{t + 1} ⥤
      Sheaf (proEtaleModelTopology T') CommRingCat.{t + 1} :=
  letI := proEtaleModelBaseChange_isContinuous g
  (proEtaleModelBaseChange g).sheafPullback (CommRingCat.{t + 1})
    (proEtaleModelTopology T) (proEtaleModelTopology T')

/-- The actual ring direct image on the small models.
Source: Stacks 00YV (blueprint: lem-sf-cbc-completed-pullback-unit-tower). -/
def transportedRingDirectImage {T' T : Scheme.{t}} (g : T' ⟶ T) :
    Sheaf (proEtaleModelTopology T') CommRingCat.{t + 1} ⥤
      Sheaf (proEtaleModelTopology T) CommRingCat.{t + 1} :=
  letI := proEtaleModelBaseChange_isContinuous g
  (proEtaleModelBaseChange g).sheafPushforwardContinuous CommRingCat.{t + 1}
    (proEtaleModelTopology T) (proEtaleModelTopology T')

/-- The ring adjunction unit, forgetting commutativity on the small models.
Source: Stacks 00YV and 03D2 (blueprint: lem-sf-cbc-completed-pullback-unit-tower). -/
def transportedRingUnit {T' T : Scheme.{t}} (g : T' ⟶ T)
    (O : Sheaf (proEtaleModelTopology T) CommRingCat.{t + 1}) :
    siteModuleRings O ⟶
      siteModuleRings ((transportedRingDirectImage g).obj
        ((transportedRingInverseImage g).obj O)) :=
  letI := proEtaleModelBaseChange_isContinuous g
  (sheafCompose (proEtaleModelTopology T) (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map
    (((proEtaleModelBaseChange g).sheafAdjunctionContinuous CommRingCat.{t + 1}
      (proEtaleModelTopology T) (proEtaleModelTopology T')).unit.app O)

/-- Module inverse image along the actual transported ring unit, as in
`proEtaleModuleInverseImage`, already in the small-model coordinates.
Source: Stacks 03D2 (blueprint: lem-sf-cbc-completed-pullback-unit-tower). -/
def transportedModuleInverseImage {T' T : Scheme.{t}} (g : T' ⟶ T)
    (O : Sheaf (proEtaleModelTopology T) CommRingCat.{t + 1}) :
    ConstantCompletion.Mod O ⥤
      ConstantCompletion.Mod ((transportedRingInverseImage g).obj O) :=
  letI := proEtaleModelBaseChange_isContinuous g
  SheafOfModules.pullback.{t + 1} (F := proEtaleModelBaseChange g)
    (J := proEtaleModelTopology T) (K := proEtaleModelTopology T')
    (transportedRingUnit g O)

/-- Underlying ring comparison: the set-adjoint of the ring adjunction unit.
Source: Stacks 00YV (blueprint: lem-sf-cbc-completed-pullback-unit-tower). -/
def ringUnderlyingMap {T' T : Scheme.{t}} (g : T' ⟶ T)
    (O : Sheaf (proEtaleModelTopology T) CommRingCat.{t + 1}) :
    (inverse g).obj ((sheafCompose (proEtaleModelTopology T)
      (CategoryTheory.forget CommRingCat)).obj O) ⟶
      (sheafCompose (proEtaleModelTopology T') (CategoryTheory.forget CommRingCat)).obj
        ((transportedRingInverseImage g).obj O) :=
  letI := proEtaleModelBaseChange_isContinuous g
  ((adjunction g).homEquiv _ _).symm
    ((sheafCompose (proEtaleModelTopology T) (CategoryTheory.forget CommRingCat)).map
      (((proEtaleModelBaseChange g).sheafAdjunctionContinuous CommRingCat.{t + 1}
        (proEtaleModelTopology T) (proEtaleModelTopology T')).unit.app O))

/-- The canonical constant map, adjoint to sheafification of constant sections.
This is `proEtaleConstantInverseImageMap` on the small models, with unrestricted
coefficient universe, rather than a choice of an isomorphism of constant sheaves.
Source: Stacks 0H7J (blueprint: lem-sf-cbc-completed-pullback-unit-tower). -/
def constantInverseImageMap {T' T : Scheme.{t}} (g : T' ⟶ T)
    (B : CommRingCat.{t + 1}) :
    (transportedRingInverseImage g).obj
        ((constantSheaf (proEtaleModelTopology T) CommRingCat.{t + 1}).obj B) ⟶
      (constantSheaf (proEtaleModelTopology T') CommRingCat.{t + 1}).obj B :=
  letI := proEtaleModelBaseChange_isContinuous g
  (((proEtaleModelBaseChange g).sheafAdjunctionContinuous CommRingCat.{t + 1}
    (proEtaleModelTopology T) (proEtaleModelTopology T')).homEquiv _ _).symm
      (((sheafificationAdjunction (proEtaleModelTopology T) CommRingCat.{t + 1}).homEquiv
        _ _).symm
          (Functor.whiskerLeft (proEtaleModelBaseChange g).op
            (toSheafify (proEtaleModelTopology T')
              ((Functor.const (proEtaleSiteModel T')ᵒᵖ).obj B))))

/-- The unique algebraic lift with all data fields fixed by the actual ring and
module inverse images and their adjunction units. `HEq` only handles the dependent
codomains until the preceding equality of ring functors is substituted.
Source: Stacks 00YV, 03D2 and 0H7J
(blueprint: lem-sf-cbc-completed-pullback-unit-tower).
Proof: the set-adjoint of the ring unit is the canonical underlying-set comparison.
Finite-product preservation makes it invertible and preserves all ring-operation
graphs. Pullback along that unit is the module inverse image; the set-adjoint of
its unit is invertible and preserves addition, zero and the scalar-action graph.
These statements follow first on the Kan-extension generators, then after
sheafification. The canonical constant-section map is invertible and natural.
They assemble to InverseImageData with exactly the displayed data. Conversely the
predicate fixes the ring functor, the module functors, both underlying comparisons,
and the constant comparison componentwise. All remaining fields are propositions,
so extensionality and proof irrelevance give uniqueness. -/
theorem canonicalInverseImageData_existsUnique {T' T : Scheme.{t}} (g : T' ⟶ T) :
    letI := proEtaleModelBaseChange_isContinuous g
    ∃! F : ConstantCompletion.InverseImageData (inverse g),
      F.rings = transportedRingInverseImage g ∧
      (∀ O : Sheaf (proEtaleModelTopology T) CommRingCat.{t + 1},
        HEq (F.algebra O).ringUnderlying.hom (ringUnderlyingMap g O) ∧
        HEq (F.algebra O).modules (transportedModuleInverseImage g O) ∧
        ∀ M : ConstantCompletion.Mod O,
          HEq ((adjunction g).homEquiv _ _ ((F.algebra O).moduleUnderlying.inv.app M))
            ((ConstantCompletion.underlying O).map
              ((SheafOfModules.pullbackPushforwardAdjunction.{t + 1}
                (F := proEtaleModelBaseChange g) (J := proEtaleModelTopology T)
                (K := proEtaleModelTopology T')
                (R := siteModuleRings ((transportedRingInverseImage g).obj O))
                (transportedRingUnit g O)).unit.app M))) ∧
      ∀ B : CommRingCat.{t + 1},
        HEq (F.constants.hom.app B) (constantInverseImageMap g B) := by
  sorry

/-- The canonical algebraic inverse image, chosen from a predicate determining all
its data fields by actual pullbacks and unit-normalized comparisons.
Source: Stacks 00YV, 03D2 and 0H7J
(blueprint: lem-sf-cbc-completed-pullback-unit-tower). -/
def canonicalInverseImageData {T' T : Scheme.{t}} (g : T' ⟶ T) :
    ConstantCompletion.InverseImageData (inverse g) :=
  (canonicalInverseImageData_existsUnique g).exists.choose

/-- The geometric morphism with its canonical algebraic lift, using the published
finite-product construction of ring and module inverse images.
Source: Stacks 00YV and 03D2 (blueprint: lem-sf-cbc-completed-pullback-unit-tower). -/
def morphism {T' T : Scheme.{t}} (g : T' ⟶ T) : Morphism (site T) (site T') where
  inverse := inverse g
  direct := direct g
  adjunction := adjunction g
  finiteLimits := inverse_finiteLimits g
  algebra := canonicalInverseImageData g

/-- Ordinary constant towers evaluated at any level are the identity functor.
Source: Stacks 0941 (blueprint: lem-sf-cbc-completed-pullback-unit-tower). -/
def diagonalEvaluation (S : Site.{u}) (A : Type u) [CommRing A] (n : ℕ) :
    S.delta A ⋙ S.evaluate A n ≅ 𝟭 (S.derived A) :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ by rfl)) ≪≫
    Functor.mapDerivedCategoryIdIso (S.modules A)

/-- The projection of the actual derived strict limit, obtained by evaluating the
constant/limit adjunction counit. On a K-injective tower it is the limit projection.
Source: Stacks 0941 (blueprint: lem-sf-cbc-completed-pullback-unit-tower). -/
def projection (S : Site.{u}) (A : Type u) [CommRing A]
    (M : S.towerDerived A) (n : ℕ) :
    (S.rlim A).obj M ⟶ (S.evaluate A n).obj M :=
  (diagonalEvaluation S A n).inv.app ((S.rlim A).obj M) ≫
    (S.evaluate A n).map ((S.deltaAdjunction A).counit.app M)

/-- The projection to the finite reduction, with its quotient action retained.
Source: Stacks 099M (blueprint: lem-sf-cbc-completed-pullback-unit-tower). -/
def finiteProjection (S : Site.{u}) (A : Type u) [CommRing A] (I : Ideal A)
    (N : S.derived A) (n : ℕ) :
    (S.completion A I).obj N ⟶
      (S.finiteRestriction A I n).obj ((S.finiteReduction A I n).obj N) :=
  projection S A ((S.reduction A I).obj N) n ≫
    (S.finiteEvaluationIso A I n).hom.app N

/-- The inverse reduced unit prescribed by clause (i): the scalar-extension adjunct
of the specified limit projection, before forgetting its finite coefficient action.
Source: Stacks 099M (blueprint: lem-sf-cbc-completed-pullback-unit-tower). -/
def finiteInverse (S : Site.{u}) (A : Type u) [CommRing A] (I : Ideal A)
    (N : S.derived A) (n : ℕ) :
    (S.finiteReduction A I n).obj ((S.completion A I).obj N) ⟶
      (S.finiteReduction A I n).obj N :=
  ((S.finiteAdjunction A I n).homEquiv _ _).symm (finiteProjection S A I N n)

/-- The finite coefficient target of the pulled-back strict quotient tower.
Source: Stacks 099N(5) (blueprint: lem-sf-cbc-completed-pullback-unit-tower). -/
def targetEvaluation {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] (I : Ideal A) (K : V.derived A) (n : ℕ) :
    (U.evaluate A n).obj ((f.towerPull A).obj ((V.reduction A I).obj K)) ≅
      (U.finiteRestriction A I n).obj
        ((f.pull (quotientRing A I n)).obj ((V.finiteReduction A I n).obj K)) :=
  (f.evaluatePullIso A n).app ((V.reduction A I).obj K) ≪≫
    (f.pull A).mapIso ((V.finiteEvaluationIso A I n).app K) ≪≫
      (f.finiteRestrictionPullIso A I n).app ((V.finiteReduction A I n).obj K)

/-- The constant-coefficient projection-induced alpha of corrected clause (iii).
It is the scalar-extension adjunct of the limit projection after R lim of tau,
exactly the constant-coefficient presentation in Stacks 099N(5).
Source: Stacks 099N(5) (blueprint: lem-sf-cbc-completed-pullback-unit-tower). -/
def finitePullbackProjection {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] (I : Ideal A) (K : V.derived A) (n : ℕ) :
    (U.finiteReduction A I n).obj ((U.completion A I).obj ((f.pull A).obj K)) ⟶
      (f.pull (quotientRing A I n)).obj ((V.finiteReduction A I n).obj K) :=
  ((U.finiteAdjunction A I n).homEquiv _ _).symm
    ((U.rlim A).map ((f.reductionPullIso A I).inv.app K) ≫
      projection U A ((f.towerPull A).obj ((V.reduction A I).obj K)) n ≫
        (targetEvaluation f A I K n).hom)

/-- Completion-unit reduction, strict tensor/pullback comparison, and the normalized
completed-pullback reduction, with no completeness assumption in (i) or (ii).

Source: smooth-purity blueprint, fix-lem-exchanges Proof Steps 2 and 5; Stacks
099M, 099N, 03EL, 06YS and 0G7E
(blueprint: lem-sf-cbc-completed-pullback-unit-tower).

Proof, following the node:
1. Represent N by one flat-term K-flat complex Q. On the diagram site the
   diagonal of Q is K-flat: tensor and acyclicity are levelwise. Thus the universal
   derived quotient presentation is represented by the strict tower Q tensor P_n.
2. Use the K-injective strict-limit model for C and its unit. The projection p_n
   satisfies p_n eta = u_n. Arbitrary-input adic-completion reduction makes its
   scalar-extension adjunct b_n invertible. Naturality of the scalar adjunction
   gives b_n F_n(eta)=1; hence b_n is the inverse of F_n(eta).
3. The cone of R(eta) evaluates to zero at every level. Kernels, cokernels and
   cohomology of strict towers are levelwise, so its representative is acyclic.
   Localization makes its cone zero, hence R(eta) invertible. Naturality of eta
   gives the natural strict inverse b, with evaluated inverse exactly b_n.
4. On Q the canonical tensor/pullback comparison commutes with each quotient
   transition, naturally in chain maps and chain homotopies. Pullback preserves
   flat-term K-flat representatives and quasi-isomorphisms. Localization of this
   resolving class descends the comparison, independently of Q. It is precisely
   the existing, representative-normalized reductionPullIso in inverse direction.
5. Compose this tau with b at Lg*K. This gives q as a natural isomorphism in the
   derived category of strict towers, so all its evaluated maps respect transitions.
6. For complete K, Stacks 099N(2),(5) and completedPullbackAdjunction express
   completed inverse image in constant-coefficient categories as C(Lg*K), with
   its R lim(tau) presentation. Naturality of the limit counit identifies its
   projection with tau_n p_n. Naturality of scalar extension makes tau_n b_n
   its adjunct, exactly finitePullbackProjection of corrected clause (iii).
   Its restriction of scalars is the component of the isomorphism q up to the
   finite comparison isomorphisms. Restriction of scalars detects
   quasi-isomorphisms, hence is conservative, so this finite-coefficient map is
   invertible, the last conjunct. No completed-ring coefficient arrow is
   identified here. -/
theorem completedPullbackUnitTower {T' T : Scheme.{t}} (g : T' ⟶ T)
    (A : Type (t + 1)) [CommRing A] (d : CompleteCoefficientDatum A) :
    ∃ b : (site T').completion A d.ideal ⋙ (site T').reduction A d.ideal ≅
        (site T').reduction A d.ideal,
      (∀ N : (site T').derived A,
        b.inv.app N = ((site T').reduction A d.ideal).map
          (((site T').unit A d.ideal).app N)) ∧
      (∀ (N : (site T').derived A) (n : ℕ),
        ((site T').evaluate A n).map (b.hom.app N) ≫
            ((site T').finiteEvaluationIso A d.ideal n).hom.app N =
          ((site T').finiteEvaluationIso A d.ideal n).hom.app
              (((site T').completion A d.ideal).obj N) ≫
            ((site T').finiteRestriction A d.ideal n).map
              (finiteInverse (site T') A d.ideal N n)) ∧
      ∃ q : (morphism g).pull A ⋙ (site T').completion A d.ideal ⋙
            (site T').reduction A d.ideal ≅
          (site T).reduction A d.ideal ⋙ (morphism g).towerPull A,
        (∀ K : (site T).derived A,
          q.hom.app K = b.hom.app (((morphism g).pull A).obj K) ≫
            ((morphism g).reductionPullIso A d.ideal).inv.app K) ∧
        ∀ K : (site T).derived A, (site T).IsComplete A d.ideal K → ∀ n : ℕ,
          ((site T').evaluate A n).map (q.hom.app K) ≫
              (targetEvaluation (morphism g) A d.ideal K n).hom =
            ((site T').finiteEvaluationIso A d.ideal n).hom.app
                (((site T').completion A d.ideal).obj (((morphism g).pull A).obj K)) ≫
              ((site T').finiteRestriction A d.ideal n).map
                (finitePullbackProjection (morphism g) A d.ideal K n) ∧
          IsIso (finitePullbackProjection (morphism g) A d.ideal K n) := by
  sorry

end AlgebraicGeometry.Scheme.CompletedPullbackUnitTower
