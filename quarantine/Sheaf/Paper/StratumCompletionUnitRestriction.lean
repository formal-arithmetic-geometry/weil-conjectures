/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Sheaf.Paper.CompletedPullback
public import Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.Paper.ConstantCompletionEquivalence
import Sheaf.Paper.ExactProductFunctorStrictLimit
import Sheaf.Algebra.Homology.RingedSiteRestrictionKFlat
import Sheaf.AlgebraicGeometry.NoetherianStratumDetection
import Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation
import Sheaf.AlgebraicGeometry.ProEtaleInverseImageLimitsZariskiLocal
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap

/-!
# Restriction of the quotient completion unit and finite-stratum detection

Source: Bhatt--Scholze, The pro-etale topology for schemes, Lemma 6.5.8(1),(2)
and Proposition 6.6.11, reverse implication; Stacks Tags 03EL, 0941, 099M, 0A0E
(blueprint: lem-weil-pbc-stratum-completion-unit-restriction).

The coefficient rings, reduction functors, quotient normalizations and completion
unit are the published constructions. Positive level n means exponent n+1.
The ordinary tower comparison is fixed by the quotient augmentation. Its derived
comparison is fixed on K-flat representatives by the universal reduction counits.
The inverse-limit map is the mate of the constant-tower comparison. Thus the
completion comparison includes its specified map from the restricted object.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

/-- The restrictions in the statement: a locally closed immersion, a site-object
restriction, or either order of their composite. A weakly etale morphism is exactly
an object of the small pro-etale site over its target.
Source: Bhatt--Scholze, Lemma 6.5.8 and Proposition 6.6.11
(blueprint: lem-weil-pbc-stratum-completion-unit-restriction). -/
def IsAdicStratumRestriction {X Y : Scheme.{u}} (f : Y ⟶ X) : Prop :=
  IsImmersion f ∨ WeaklyEtale f ∨
    (∃ (Z : Scheme.{u}) (i : Z ⟶ X) (j : Y ⟶ Z),
      IsImmersion i ∧ WeaklyEtale j ∧ j ≫ i = f) ∨
    (∃ (Z : Scheme.{u}) (j : Z ⟶ X) (i : Y ⟶ Z),
      WeaklyEtale j ∧ IsImmersion i ∧ i ≫ j = f)

variable {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
variable {X Y : Scheme.{u}} (f : Y ⟶ X)

/-- The actual module inverse image with the canonical completed coefficient transport.
Source: Bhatt--Scholze, Lemma 6.5.8(1)
(blueprint: lem-weil-pbc-stratum-completion-unit-restriction). -/
abbrev stratumModulePull :=
  proEtaleRingModulePullback f (d.completedRing X) (d.completedRing Y) (d.integralRingIso f)

/-- The ordinary strict reduction comparison is uniquely fixed by its quotient unit.
Source: Stacks Tag 03EL; Bhatt--Scholze, Lemma 6.5.8(1)
(blueprint: lem-weil-pbc-stratum-completion-unit-restriction).
Proof: finite constant coefficients pull back canonically, and the completed map
commutes with every quotient projection (proetale-constant-ring-map and four-corners).
The scalar-extension/pullback balancing map at level n sends a pulled-back tensor
x tensor q to the tensor of its pullbacks. These maps commute with quotient maps,
so they form an isomorphism of strict towers, natural in the input module. Their
composite with x maps to x tensor 1 is the target quotient unit. Conversely each
quotient unit is an epimorphism, because the completed projection is the quotient
by I^(n+1) (constant-completion-equivalence). Pullback is exact, so equality after
these epimorphisms determines every component, hence the natural isomorphism. -/
theorem stratumModuleReductionIso_exists :
    ∃! e : completedReductionModuleTowerFunctor X d ⋙ d.towerModulePull f ≅
        stratumModulePull d f ⋙ completedReductionModuleTowerFunctor Y d,
      ∀ M : reductionModules X (d.completedRing X),
        (d.towerModulePull f).map ((completedReductionModuleUnit d X).app M) ≫
            e.hom.app M =
          (d.constantPullbackIso f).hom.app M ≫
            (completedReductionModuleUnit d Y).app ((stratumModulePull d f).obj M) := by
  sorry

/-- The ordinary comparison selected by its unique augmentation normalization.
Source: Stacks Tag 03EL (blueprint: lem-weil-pbc-stratum-completion-unit-restriction). -/
def stratumModuleReductionIso := (stratumModuleReductionIso_exists d f).exists.choose

/-- The representative equation for the comparison of entire derived strict towers.
It uses actual universal counits and the ordinary strict comparison, so evaluations
alone do not specify a morphism in the derived category of towers.
Source: Stacks Tags 06YY, 03EL
(blueprint: lem-weil-pbc-stratum-completion-unit-restriction). -/
def StratumReductionFormula
    (e : completedReductionTower X d ⋙ d.towerPull f ≅
      d.pull f ⋙ completedReductionTower Y d) : Prop :=
  ∀ P : CochainComplex (reductionModules X (d.completedRing X)) ℤ,
    CochainComplex.IsKFlatIndependentCoefficients (R := d.completedRing X) P →
    e.hom.app (DerivedCategory.Q.obj P) ≫
        (completedReductionTower Y d).map
          ((stratumModulePull d f).mapDerivedCategoryFactors.hom.app P) ≫
        completedReductionTowerComplexCounit Y d
          (((stratumModulePull d f).mapHomologicalComplex (.up ℤ)).obj P) =
      (d.towerPull f).map (completedReductionTowerComplexCounit X d P) ≫
        (d.towerModulePull f).mapDerivedCategoryFactors.hom.app
          ((completedReductionComplexTowerFunctor X d).obj P) ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex (stratumModuleReductionIso d f).hom
            (.up ℤ)).app P)

/-- The normalized strict tower comparison exists uniquely.
Source: Stacks Tags 06YS, 06YY, 03EL
(blueprint: lem-weil-pbc-stratum-completion-unit-restriction).
Proof: use a K-flat resolution with flat terms (reduction-pullback-derived-tower).
Exact inverse image and identified-coefficient pullback carry it to a K-flat
representative. Apply the ordinary strict comparison, conjugated by the reduction
counits and exact-pullback localization factors, as in StratumReductionFormula.
Naturality and compatibility with quasi-isomorphisms descend this construction.
The inverse ordinary comparison descends to its inverse. Every derived object
has a K-flat representative, so the equation determines the comparison uniquely. -/
theorem stratumReductionIso_exists :
    ∃! e : completedReductionTower X d ⋙ d.towerPull f ≅
        d.pull f ⋙ completedReductionTower Y d,
      StratumReductionFormula d f e := by
  sorry

/-- Canonical comparison of the actual strict quotient reduction towers.
Source: Stacks Tag 06YY (blueprint: lem-weil-pbc-stratum-completion-unit-restriction). -/
def stratumReductionIso := (stratumReductionIso_exists d f).exists.choose

/-- The inverse-limit comparison is the mate of the canonical constant-tower
comparison under the two derived constant/limit adjunctions.
Source: Stacks Tag 0941 (blueprint: lem-weil-pbc-stratum-completion-unit-restriction). -/
def stratumRlimComparison (T : DerivedCategory (d.towers X)) :
    (d.pull f).obj ((completedRlim X (d.completedRing X)).obj T) ⟶
      (completedRlim Y (d.completedRing Y)).obj ((d.towerPull f).obj T) :=
  (d.constantRlimAdjunction Y).unit.app
      ((d.pull f).obj ((completedRlim X (d.completedRing X)).obj T)) ≫
    (completedRlim Y (d.completedRing Y)).map
      ((d.derivedConstantPullbackIso f).inv.app ((completedRlim X (d.completedRing X)).obj T) ≫
        (d.towerPull f).map ((d.constantRlimAdjunction X).counit.app T))

/-- The canonical map between quotient completions, retaining its strict-tower map.
Source: Stacks Tags 0941 and 099M
(blueprint: lem-weil-pbc-stratum-completion-unit-restriction). -/
def stratumCompletionComparison (K : d.derived X) :
    (d.pull f).obj ((completedRlim X (d.completedRing X)).obj
      ((completedReductionTower X d).obj K)) ⟶
    (completedRlim Y (d.completedRing Y)).obj
      ((completedReductionTower Y d).obj ((d.pull f).obj K)) :=
  stratumRlimComparison d f ((completedReductionTower X d).obj K) ≫
    (completedRlim Y (d.completedRing Y)).map ((stratumReductionIso d f).hom.app K)

/-- Finite coefficient pullback respects every quotient map, including equal levels.
Source: Stacks Tag 03EL and the finite constant-ring comparison
(blueprint: lem-weil-pbc-stratum-completion-unit-restriction).
Proof: the constant-ring comparison is natural in the homomorphism A/I^(b+1)
to A/I^(a+1). Transport this naturality square through the constant-preserving
function-coefficient comparisons (proetale-constant-ring-map). -/
theorem stratumFiniteCoefficient_naturality (b a : ℕ) (h : a ≤ b) :
    (d.finiteRingIso f b).hom ≫ reductionCoefficientMap Y d b a h =
      (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map
        (reductionCoefficientMap X d b a h) ≫ (d.finiteRingIso f a).hom := by
  sorry

/-- The published normalized tensor/pullback comparison for two finite quotients.
Source: Stacks Tag 03EL (blueprint: lem-weil-pbc-stratum-completion-unit-restriction). -/
def stratumQuotientChi (b a : ℕ) (h : a ≤ b) :
    reductionDerivedChange X (reductionCoefficientMap X d b a h) ⋙ d.finitePull f a ≅
      d.finitePull f b ⋙ reductionDerivedChange Y (reductionCoefficientMap Y d b a h) :=
  proEtaleReductionPullbackIso f (d.finiteRing X b) (d.finiteRing X a)
    (d.finiteRing Y b) (d.finiteRing Y a)
    (reductionCoefficientMap X d b a h) (reductionCoefficientMap Y d b a h)
    (d.finiteRingIso f b) (d.finiteRingIso f a) (stratumFiniteCoefficient_naturality d f b a h)

/-- The finite-reduction comparisons commute with the specified normalizations.
Source: Stacks Tags 03EL and 06YY
(blueprint: lem-weil-pbc-stratum-completion-unit-restriction).
Proof: on a flat-term K-flat representative both paths take (x tensor q) tensor t
to the pullback of x tensor q_(b,a)(q)t. The coefficient square above respects
multiplication and quotient maps. Thus the balanced section maps, sheaf maps and
complex maps agree. Conjugating by the universal counits gives this equality in
the quotient-coefficient derived category (adic-coefficient-datum and
reduction-pullback-derived-tower). This includes b=a and all quotient cocycles. -/
theorem stratumReduction_normalization (b a : ℕ) (h : a ≤ b) (K : d.derived X) :
    (d.finitePull f a).map ((completedReductionDerivedNormalization X d b a h).app K) ≫
        (d.chi f a).hom.app K =
      (stratumQuotientChi d f b a h).hom.app ((d.reduction X b).obj K) ≫
        (reductionDerivedChange Y (reductionCoefficientMap Y d b a h)).map
          ((d.chi f b).hom.app K) ≫
        (completedReductionDerivedNormalization Y d b a h).app ((d.pull f).obj K) := by
  sorry

/-- Termwise exact tower pullback commutes with evaluation by identity components.
Source: Stacks Tag 015F (blueprint: lem-weil-pbc-stratum-completion-unit-restriction). -/
def stratumTowerEvaluationIso (n : ℕ) :
    d.towerPull f ⋙ reductionTowerDerivedEvaluation Y
        (reductionModuleRing Y (d.completedRing Y)) n ≅
      reductionTowerDerivedEvaluation X (reductionModuleRing X (d.completedRing X)) n ⋙
        d.pull f :=
  (Functor.mapDerivedCategoryCompIso (d.towerModulePull f)
    (reductionTowerEvaluation Y (reductionModuleRing Y (d.completedRing Y)) n)).symm ≪≫
    Functor.mapDerivedCategoryNatIso (Iso.refl _) ≪≫
    Functor.mapDerivedCategoryCompIso
      (reductionTowerEvaluation X (reductionModuleRing X (d.completedRing X)) n)
      (stratumModulePull d f)

/-- Evaluations of the strict comparison are the actual finite-coefficient comparisons.
Source: Stacks Tags 03EL, 06YY and 015F
(blueprint: lem-weil-pbc-stratum-completion-unit-restriction).
Proof: use the representative formula of stratumReductionIso. Evaluation of the
ordinary strict comparison is the inverse scalar-extension mate of the canonical
restriction/pullback comparison: both maps agree after the quotient epimorphism.
The universal evaluation counits identify its derived map with chi. The exact
restriction/pullback isomorphism retains the quotient action. Localizing this
identity on K-flat representatives proves the displayed equation. -/
theorem stratumReduction_evaluation (n : ℕ) (K : d.derived X) :
    (reductionTowerDerivedEvaluation Y (reductionModuleRing Y (d.completedRing Y)) n).map
        ((stratumReductionIso d f).hom.app K) ≫
        (completedReductionEvaluation Y d n).app ((d.pull f).obj K) =
      (stratumTowerEvaluationIso d f n).hom.app ((completedReductionTower X d).obj K) ≫
        (d.pull f).map ((completedReductionEvaluation X d n).app K) ≫
        (proEtaleRingRestrictionDerivedPullback f
          (d.completedRing X) (d.finiteRing X n) (d.completedRing Y) (d.finiteRing Y n)
          (d.projection X n) (d.projection Y n) (d.integralRingIso f) (d.finiteRingIso f n)
          (d.projection_comm f n)).inv.app ((d.reduction X n).obj K) ≫
        (reductionDerivedRestrict Y (d.projection Y n)).map ((d.chi f n).hom.app K) := by
  sorry

/-- The strict comparison preserves the actual augmentation from the constant tower.
Source: Stacks Tags 03EL, 06YY
(blueprint: lem-weil-pbc-stratum-completion-unit-restriction).
Proof: on a K-flat representative the ordinary comparison carries the tensor unit
x tensor 1 to its pullback tensor 1, by its defining augmentation equation.
The reduction counits and the exact constant-pullback factors give the same
identity in the derived tower category. This proves the equation for every K by
resolving-class localization, including its fixed source Delta(FK). -/
theorem stratumReduction_augmentation (K : d.derived X) :
    (d.towerPull f).map ((completedReductionAugmentation d X).app K) ≫
        (stratumReductionIso d f).hom.app K =
      (d.derivedConstantPullbackIso f).hom.app K ≫
        (completedReductionAugmentation d Y).app ((d.pull f).obj K) := by
  sorry

/-- These module inverse images are exact and preserve small limits; coefficient
identification is by the canonical completed map with its fixed finite projections.
Source: Bhatt--Scholze, Lemma 6.5.8(1); Stacks Tags 09AA, 03DB, 0E8K
(blueprint: lem-weil-pbc-stratum-completion-unit-restriction).
Proof: for an immersion use proetale-immersion-limit-preservation. For a weakly
etale restriction use weakly-etale-localization: evaluation on the slice computes
limits sectionwise (module-sheaves-limits-sectionwise), and ringed-site restriction
is exact. Transport along the canonical ring isomorphism preserves these properties.
For either composite, compose the inverse images and their canonical coefficient
identifications; quotient projection identities identify the resulting coefficient
map with d.integralRingIso. This proves all four cases without assuming Y Noetherian. -/
theorem stratumRestriction_limits (hf : IsAdicStratumRestriction f) :
    (stratumModulePull d f).Additive ∧
      PreservesFiniteLimits (stratumModulePull d f) ∧
      PreservesFiniteColimits (stratumModulePull d f) ∧
      PreservesLimitsOfSize.{u + 1, u + 1} (stratumModulePull d f) ∧
      (∀ n : ℕ, (d.integralRingIso f).hom ≫ d.projection Y n =
        (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map (d.projection X n) ≫
          (d.finiteRingIso f n).hom) := by
  sorry

/-- The canonical mate commutes with total derived strict inverse limit for the
specified restrictions, including schemes Y which are not Noetherian.
Source: Stacks Tag 0941; Bhatt--Scholze, Lemma 6.5.8
(blueprint: lem-weil-pbc-stratum-completion-unit-restriction).
Proof: stratumRestriction_limits gives exactness and preservation of countable
products. Countable products are exact in both pro-etale module categories by
proetale-countable-products-exact. Apply exact-product-functor-strict-limit to the
specified total right-derived limit. Its normalized Roos comparison uses the
canonical product map on both signed fiber coordinates. Its ordinary limit
projection equation, hence its derived constant/limit adjunction equation,
identifies it with stratumRlimComparison. Thus this particular mate is invertible. -/
theorem stratumRlimComparison_isIso (hf : IsAdicStratumRestriction f)
    (T : DerivedCategory (d.towers X)) : IsIso (stratumRlimComparison d f T) := by
  sorry

/-- Restriction identifies the quotient completion and its unit, including the map
from the restricted input. The isomorphism is the prescribed strict-limit mate
followed by the normalized reduction-tower comparison.
Source: Bhatt--Scholze, Lemma 6.5.8(1),(2); Stacks Tags 0941, 099M
(blueprint: lem-weil-pbc-stratum-completion-unit-restriction).
Proof: stratumRlimComparison_isIso and the strict tower isomorphism make their
composite invertible. Its unit equation follows from stratumReduction_augmentation
and the triangle identities for the two constant/derived-limit adjunctions.
Equivalently the normalized Roos comparison sends ((x tensor 1)_n,0) to
((F(x) tensor 1)_n,0), by exact-product-functor-strict-limit. Thus the equation
involves the specified quotient units and their actual source, not just endpoints. -/
theorem stratumCompletionComparison_unit [IsLocallyNoetherian X] [CompactSpace X]
    (hf : IsAdicStratumRestriction f) (K : d.derived X) :
    IsIso (stratumCompletionComparison d f K) ∧
      (d.pull f).map (d.completionUnit X K) ≫ stratumCompletionComparison d f K =
        d.completionUnit Y ((d.pull f).obj K) := by
  sorry

/-- Intrinsic completeness is preserved, with arbitrary representative realizations.
Source: Bhatt--Scholze, Lemma 6.5.8; Stacks Tags 099M, 0A0E
(blueprint: lem-weil-pbc-stratum-completion-unit-restriction).
Proof: the constant-completion equivalence, via the published unit-normalized
Koszul/quotient comparison, identifies invertibility of each intrinsic unit with
invertibility of its quotient completion unit. stratumCompletionComparison_unit
identifies the restricted quotient unit with the target unit. A functor preserves
invertibility, so an invertible source intrinsic unit gives an invertible target
intrinsic unit. The comparison applies to every supplied representative on Y. -/
theorem stratumIntrinsicComplete_preserved [IsLocallyNoetherian X] [CompactSpace X]
    (hf : IsAdicStratumRestriction f)
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)
    (K : d.derived X)
    (C : CochainComplex (reductionModules X (d.completedRing X)) ℤ)
    (eC : DerivedCategory.Q.obj C ≅ K)
    (D : CochainComplex (reductionModules Y (d.completedRing Y)) ℤ)
    (eD : DerivedCategory.Q.obj D ≅ (d.pull f).obj K) :
    IsDerivedCompleteIntrinsic X d r a ha K C eC →
      IsDerivedCompleteIntrinsic Y d r a ha ((d.pull f).obj K) D eD := by
  sorry

/-- Intrinsic completeness is detected by every chosen pro-etale cover of every
stratum of a finite locally closed stratification.
Source: Bhatt--Scholze, Proposition 6.6.11, reverse implication; Stacks Tags 09AH, 09AB
(blueprint: lem-weil-pbc-stratum-completion-unit-restriction).
Proof: preservation proves the forward direction for every stratum/cover composite.
Conversely the unit-normalized Koszul/quotient comparison makes every local quotient
unit invertible. stratumCompletionComparison_unit identifies these maps with the
restrictions of the single global quotient unit. Noetherian-stratum-detection,
applied to the completed ring, reflects its invertibility. On a Noetherian scheme
locally closed strata are constructible, so the recorded finite locally closed
stratification supplies exactly that detection theorem's stratification. Finally
compare the global quotient unit with the supplied intrinsic unit. This uses no
boundedness and no Noetherian hypothesis on the covering members. -/
theorem stratum_completion_unit_restriction (X : Scheme.{u})
    [IsLocallyNoetherian X] [CompactSpace X]
    (S : FiniteLocallyClosedStratification X)
    (V : ∀ i : Fin S.n, Scheme.Cover.{w} proetalePrecoverage (S.domain i))
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)
    (K : d.derived X)
    (C : CochainComplex (reductionModules X (d.completedRing X)) ℤ)
    (eC : DerivedCategory.Q.obj C ≅ K) :
    IsDerivedCompleteIntrinsic X d r a ha K C eC ↔
      ∀ (i : Fin S.n) (j : (V i).I₀),
        ∀ (D : CochainComplex
          (reductionModules ((V i).X j) (d.completedRing ((V i).X j))) ℤ)
          (eD : DerivedCategory.Q.obj D ≅ (d.pull ((V i).f j ≫ S.immersion i)).obj K),
          IsDerivedCompleteIntrinsic ((V i).X j) d r a ha
            ((d.pull ((V i).f j ≫ S.immersion i)).obj K) D eD := by
  sorry

end AlgebraicGeometry.Scheme
