/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q63
-/
module

public import Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction
public import Sheaf.Paper.IntegralReductionTowerUnrestricted
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Sheaf.Algebra.Homology.QuasiIsoSaturatedTriangulated

/-! # Canonical resolution comparisons without an auxiliary finite-field datum

Source: Stacks Project, sites-cohomology.tex, Tags 06YS/06YT/06YY; derived.tex,
Tags 05RT/06XN; Bhatt--Scholze, p. 24, Definition 3.5.2
(blueprint: lem-weil-integral-reduction-tower-well-defined).

This is the unrestricted interface to the same augmented reduction tower.
It uses the published completed sheaf and scalarReductionExtension, its universal
derived counit, and the canonical localization factorization. Index n means
exponent n+1. The site and coefficient universes remain independent.

## Main definitions and statements

- `unrestrictedTowerResolutionIso`: computation through the universal derived counit.
- `unrestrictedTowerFiniteComparison`: canonical comparison of two resolutions.
- `unrestrictedTowerUnit`: the uniquely normalized unit chain map.
- `unrestrictedTowerTransition`: the published canonical transition at P.
- `unrestrictedReductionTowerWellDefined`: invariance of the augmented derived tower.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe t u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (Y : AlgebraicGeometry.Scheme.{t})

/-- Restriction changes the scalar action and keeps the underlying additive map.
Source: Stacks Tag 03DA (blueprint: lem-weil-integral-reduction-tower-well-defined). -/
noncomputable instance unrestrictedTowerRestrictionAdditive (n : ℕ) :
    (scalarReductionRestriction l E Y n).Additive :=
  inferInstance

/-- Exactness supplies the limits instance for the recorded restriction functor.
Source: Stacks Tag 03DA (blueprint: lem-weil-integral-reduction-tower-well-defined). -/
noncomputable instance unrestrictedTowerRestrictionLimits (n : ℕ) :
    PreservesFiniteLimits (scalarReductionRestriction l E Y n) :=
  scalarReductionRestrictionLimits l E Y n

/-- Exactness supplies the colimits instance for the recorded restriction functor.
Source: Stacks Tag 03DA (blueprint: lem-weil-integral-reduction-tower-well-defined). -/
noncomputable instance unrestrictedTowerRestrictionColimits (n : ℕ) :
    PreservesFiniteColimits (scalarReductionRestriction l E Y n) :=
  scalarReductionRestrictionColimits l E Y n

/-- Additivity of the recorded extension, at the explicit coefficient sizes.
Source: Stacks Tag 06YY (blueprint: lem-weil-integral-reduction-tower-well-defined). -/
noncomputable instance unrestrictedTowerExtensionAdditive (n : ℕ) :
    (scalarReductionExtension l E Y n).Additive :=
  scalarReductionExtensionAdditive.{t, u} l E Y n

/-- The termwise finite reduction, using the recorded change-of-rings functor.
Source: Stacks Tag 06YY (blueprint: lem-weil-integral-reduction-tower-well-defined). -/
noncomputable abbrev unrestrictedTowerFiniteComplex (n : ℕ)
    (P : CochainComplex (scalarReductionSource l E Y) ℤ) :=
  ((scalarReductionExtension l E Y n).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj P

/-- The same reduction regarded as a complex over the completed coefficient sheaf.
Source: Stacks Tag 03EK (blueprint: lem-weil-integral-reduction-tower-well-defined). -/
noncomputable abbrev unrestrictedTowerComplex (n : ℕ)
    (P : CochainComplex (scalarReductionSource l E Y) ℤ) :=
  ((scalarReductionRestriction l E Y n).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj (unrestrictedTowerFiniteComplex l E Y n P)

/-- A pure tensor, followed by sheafification, in the recorded finite reduction.
Transport uses the object equality in the defining change-of-rings witness.
Source: Stacks Tag 03EK (blueprint: lem-weil-integral-reduction-tower-well-defined). -/
noncomputable def unrestrictedTowerTensorSection (n : ℕ)
    (M : scalarReductionSource l E Y)
    (U : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ)
    (s : (integralCoefficientCommRingSheaf l E Y n).obj.obj U) (x : M.val.obj U) :
    ((scalarReductionExtension l E Y n).obj M).val.obj U :=
  unrestrictedIntegralTensorSection l E Y n M U s x

/-- The universal derived counit computes scalar reduction on K-flat complexes.
Source: Stacks Tag 06YY (blueprint: lem-weil-integral-reduction-tower-well-defined).
Proof: specialize the K-flat computation conjunct of the universal
change-of-rings witness defining scalarReductionDerivedExistence to P and hP.
The selected functor and counit are precisely its projections. -/
theorem unrestrictedTowerCounit_isIso (n : ℕ)
    (P : CochainComplex (scalarReductionSource l E Y) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (J := AlgebraicGeometry.Scheme.ProEt.topology Y)
      (R := completedIntegralCommRingSheafUnrestricted l E Y) P) :
    IsIso ((scalarReductionCounit l E Y n).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) := by
  sorry

/-- The canonical computation by a resolution, expressed using complexes rather than
homotopy representatives. Both transports are the standard quotient comparison.
Source: Stacks Tag 06YY (blueprint: lem-weil-integral-reduction-tower-well-defined). -/
noncomputable def unrestrictedTowerResolutionIso (n : ℕ)
    {P K : CochainComplex (scalarReductionSource l E Y) ℤ}
    (q : P ⟶ K)
    (hq : CochainComplex.IsKFlatResolutionIndependentCoefficients
      (J := AlgebraicGeometry.Scheme.ProEt.topology Y)
      (R := completedIntegralCommRingSheafUnrestricted l E Y) q) :
    (scalarReductionDerivedExtension l E Y n).obj (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj (unrestrictedTowerFiniteComplex l E Y n P) :=
  letI : QuasiIso q := hq.1
  (scalarReductionDerivedExtension l E Y n).mapIso (asIso (DerivedCategory.Q.map q)).symm ≪≫
    (scalarReductionDerivedExtension l E Y n).mapIso
      ((DerivedCategory.quotientCompQhIso _).app P).symm ≪≫
    @asIso _ _ _ _ ((scalarReductionCounit l E Y n).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P))
      (unrestrictedTowerCounit_isIso l E Y n P hq.2) ≪≫
    DerivedCategory.Qh.mapIso
      (((scalarReductionExtension l E Y n).mapHomotopyCategoryFactors (.up ℤ)).app P) ≪≫
    (DerivedCategory.quotientCompQhIso (scalarReductionTarget l E Y n)).app
      (unrestrictedTowerFiniteComplex l E Y n P)

/-- The finite comparison is defined through the common derived reduction of K.
Source: Stacks Tag 06YY (blueprint: lem-weil-integral-reduction-tower-well-defined). -/
noncomputable def unrestrictedTowerFiniteComparison (n : ℕ)
    {P P' K : CochainComplex (scalarReductionSource l E Y) ℤ}
    (q : P ⟶ K) (q' : P' ⟶ K)
    (hq : CochainComplex.IsKFlatResolutionIndependentCoefficients
      (J := AlgebraicGeometry.Scheme.ProEt.topology Y)
      (R := completedIntegralCommRingSheafUnrestricted l E Y) q)
    (hq' : CochainComplex.IsKFlatResolutionIndependentCoefficients
      (J := AlgebraicGeometry.Scheme.ProEt.topology Y)
      (R := completedIntegralCommRingSheafUnrestricted l E Y) q') :
    DerivedCategory.Q.obj (unrestrictedTowerFiniteComplex l E Y n P) ≅
      DerivedCategory.Q.obj (unrestrictedTowerFiniteComplex l E Y n P') :=
  (unrestrictedTowerResolutionIso l E Y n q hq).symm ≪≫
    unrestrictedTowerResolutionIso l E Y n q' hq'

/-- Restrict the canonical finite comparison, using the canonical localization
factorization to express its endpoints by the restricted complexes.
Source: Stacks Tags 03DA/06YY
(blueprint: lem-weil-integral-reduction-tower-well-defined). -/
noncomputable def unrestrictedTowerComparison (n : ℕ)
    {P P' K : CochainComplex (scalarReductionSource l E Y) ℤ}
    (q : P ⟶ K) (q' : P' ⟶ K)
    (hq : CochainComplex.IsKFlatResolutionIndependentCoefficients
      (J := AlgebraicGeometry.Scheme.ProEt.topology Y)
      (R := completedIntegralCommRingSheafUnrestricted l E Y) q)
    (hq' : CochainComplex.IsKFlatResolutionIndependentCoefficients
      (J := AlgebraicGeometry.Scheme.ProEt.topology Y)
      (R := completedIntegralCommRingSheafUnrestricted l E Y) q') :
    DerivedCategory.Q.obj (unrestrictedTowerComplex l E Y n P) ≅
      DerivedCategory.Q.obj (unrestrictedTowerComplex l E Y n P') :=
  ((scalarReductionRestriction l E Y n).mapDerivedCategoryFactors.app _).symm ≪≫
    (scalarReductionRestriction l E Y n).mapDerivedCategory.mapIso
      (unrestrictedTowerFiniteComparison l E Y n q q' hq hq') ≪≫
    (scalarReductionRestriction l E Y n).mapDerivedCategoryFactors.app _

/-- The unit maps are specified on local sections by x ↦ 1 ⊗ x and sheafification.
Source: Stacks Tag 03EK (blueprint: lem-weil-integral-reduction-tower-well-defined). -/
def unrestrictedTowerUnitCondition
    (P : CochainComplex (scalarReductionSource l E Y) ℤ)
    (γ : ∀ n : ℕ, P ⟶ unrestrictedTowerComplex l E Y n P) : Prop :=
  ∀ (n : ℕ) (i : ℤ) (U : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ) (x : (P.X i).val.obj U),
    ((γ n).f i).val.app U x = unrestrictedTowerTensorSection l E Y n (P.X i) U 1 x

/-- There is a unique family of chain-level unit maps, one for each level, with the
stated sectionwise formula.
Source: Stacks Tag 03EK (blueprint: lem-weil-integral-reduction-tower-well-defined).
Proof: in each degree and site object send x to the sheafification of 1⊗x. Tensor
balancing, naturality of the coefficient projection and of the sheafification unit
make this a map of presheaves of modules, hence of sheaves, linear over the completed
ring after restriction along the projection. It commutes with restrictions and with
the differential by its sectionwise formula, so it defines a chain map. Uniqueness
follows on every section from the formula; degreewise equality is equality of chain
maps, and function extensionality gives uniqueness at every level. -/
theorem unrestrictedTowerMaps_existUnique
    (P : CochainComplex (scalarReductionSource l E Y) ℤ) :
    ∃! γ : ∀ n : ℕ, P ⟶ unrestrictedTowerComplex l E Y n P,
      unrestrictedTowerUnitCondition l E Y P γ := by
  sorry

/-- The chain-level unit x ↦ x⊗1, determined uniquely by its sectionwise formula.
Source: Stacks Tag 03EK (blueprint: lem-weil-integral-reduction-tower-well-defined). -/
noncomputable def unrestrictedTowerUnit
    (P : CochainComplex (scalarReductionSource l E Y) ℤ) (n : ℕ) :
    P ⟶ unrestrictedTowerComplex l E Y n P :=
  (unrestrictedTowerMaps_existUnique l E Y P).exists.choose n

/-- The chain-level reduction id⊗ρ: the published canonical transition of
def-weil-integral-reduction-tower, uniquely determined on sheafified pure tensors
(`unrestrictedIntegralTransition_existsUnique`), evaluated at P.
Source: Stacks Tag 03EK (blueprint: lem-weil-integral-reduction-tower-well-defined). -/
noncomputable def unrestrictedTowerTransition
    (P : CochainComplex (scalarReductionSource l E Y) ℤ) (n : ℕ) :
    unrestrictedTowerComplex l E Y (n + 1) P ⟶ unrestrictedTowerComplex l E Y n P :=
  (unrestrictedIntegralTransition l E Y n).app P

/-- The image of the resolution augmentation is invertible in the derived category.
Source: Stacks Tag 06YS (blueprint: lem-weil-integral-reduction-tower-well-defined). -/
noncomputable def unrestrictedTowerAugmentationIso
    {P K : CochainComplex (scalarReductionSource l E Y) ℤ}
    (q : P ⟶ K)
    (hq : CochainComplex.IsKFlatResolutionIndependentCoefficients
      (J := AlgebraicGeometry.Scheme.ProEt.topology Y)
      (R := completedIntegralCommRingSheafUnrestricted l E Y) q) :
    DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj K :=
  letI : QuasiIso q := hq.1
  asIso (DerivedCategory.Q.map q)

/-- The finite canonical comparisons give an isomorphism of the two augmented towers.
The unit and transition maps are the unique maps with the specified pure-tensor formulas.
The comparison is the recorded derived counit comparison.
Source: Stacks Tags 06YS/06YT/06YY and derived.tex Tags 05RT/06XN;
Bhatt--Scholze, p. 24, Definition 3.5.2
(blueprint: lem-weil-integral-reduction-tower-well-defined).

Proof:
1. Apply the common-roof property for quasi-isomorphisms in the homotopy category
(lem-pur-quasi-isos-saturated-triangulated) to q and q'. Resolve its source V by
lem-pc-kflat-resolution, obtaining K-flat T and quasi-isomorphisms a:T→P, b:T→P'
with qa=q'b in the homotopy category. No direct chain map P→P' is assumed.
2. Termwise tensoring preserves these quasi-isomorphisms by clause (1) of
lem-pur-derived-change-of-rings. Naturality of its universal counit, invertible on
T,P,P', identifies the canonical comparison with [a_n]⁻¹ ≫ [b_n]. This is also the
comparison defined through integralDerivedReductionResolutionIso; the quotient and
restriction factorization isomorphisms merely express the same objects by complexes.
3. On local sections, a_n γ_T = γ_P a and b_n γ_T = γ_P' b, since both sides
send x to 1⊗a(x), respectively 1⊗b(x). Sheafification and localization preserve
these identities. Cancel [a_n], [b_n] and use qa=q'b to obtain clause (1).
4. Similarly a_n τ_T = τ_P a_(n+1) and b_n τ_T = τ_P' b_(n+1), since both
sides send s⊗x to ρ_n(s)⊗a(x), respectively ρ_n(s)⊗b(x). The projection
identity makes these maps linear over the completed sheaf. Sheafify, localize and
cancel to obtain clause (2). The components are isomorphisms by construction;
rearranging clause (2) gives compatibility of their inverses, hence the asserted
isomorphism of inverse systems, and clause (1) respects the augmentations. -/
theorem unrestrictedReductionTowerWellDefined
    {P P' K : CochainComplex (scalarReductionSource l E Y) ℤ}
    (q : P ⟶ K) (q' : P' ⟶ K)
    (hq : CochainComplex.IsKFlatResolutionIndependentCoefficients
      (J := AlgebraicGeometry.Scheme.ProEt.topology Y)
      (R := completedIntegralCommRingSheafUnrestricted l E Y) q)
    (hq' : CochainComplex.IsKFlatResolutionIndependentCoefficients
      (J := AlgebraicGeometry.Scheme.ProEt.topology Y)
      (R := completedIntegralCommRingSheafUnrestricted l E Y) q')
    :
    (∀ n : ℕ,
      (unrestrictedTowerAugmentationIso l E Y q hq).inv ≫
        DerivedCategory.Q.map (unrestrictedTowerUnit l E Y P n) ≫
        (unrestrictedTowerComparison l E Y n q q' hq hq').hom =
      (unrestrictedTowerAugmentationIso l E Y q' hq').inv ≫
        DerivedCategory.Q.map (unrestrictedTowerUnit l E Y P' n)) ∧
    (∀ n : ℕ,
      DerivedCategory.Q.map (unrestrictedTowerTransition l E Y P n) ≫
        (unrestrictedTowerComparison l E Y n q q' hq hq').hom =
      (unrestrictedTowerComparison l E Y (n + 1) q q' hq hq').hom ≫
        DerivedCategory.Q.map (unrestrictedTowerTransition l E Y P' n)) := by
  sorry

end WeilConjectures
