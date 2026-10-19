/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups NC and W5
-/
module

public import Sheaf.Paper.IntegralDerivedReduction
public import Sheaf.Paper.RestrictionOfScalarsExact
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Sheaf.Paper.IntegralReductionTowerWellDefinedUnrestricted

/-!
# Independence of the augmented integral reduction tower

Source: Stacks Project, sites-cohomology.tex, Tags 06YS/06YT/06YY; derived.tex,
Tags 05RT/06XN; Bhatt--Scholze, p. 24, Definition 3.5.2
(blueprint: lem-weil-integral-reduction-tower-well-defined).

The index n denotes exponent n+1. Pure tensors characterize the chain maps before
localization; the finite comparison is the composite of the recorded canonical
K-flat computation isomorphisms. No arbitrary comparison or transition is chosen.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe d t u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

namespace WeilConjectures

-- Avoid unfolding the inverse limit and the constructed maps when identifying interfaces.
attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  scalarReductionExistence scalarReductionDerivedExistence
  unrestrictedIntegralReductionExistence integralReductionExistence
  integralReductionDerivedExistence
  unrestrictedTowerUnit unrestrictedTowerTransition unrestrictedTowerResolutionIso
  unrestrictedTowerFiniteComparison unrestrictedTowerComparison

attribute [local instance] integralReductionChangeOfRingsAdditive

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (Y : AlgebraicGeometry.Scheme.{t})
  (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)

/-- Restriction changes the scalar action and keeps the underlying additive map.
Source: Stacks Tag 03DA (blueprint: lem-weil-integral-reduction-tower-well-defined). -/
noncomputable instance integralTowerRestrictionAdditive (n : ℕ) :
    (completedIntegralRestrictScalars l E Y D hl n).Additive :=
  inferInstanceAs (SheafOfModules.restrictScalars
    (completedIntegralCoefficientProjection l E Y D hl n)).Additive

/-- Exactness supplies the limits instance for the recorded restriction functor.
Source: Stacks Tag 03DA (blueprint: lem-weil-integral-reduction-tower-well-defined). -/
theorem integralTowerRestrictionLimits (n : ℕ) :
    PreservesFiniteLimits (completedIntegralRestrictScalars l E Y D hl n) :=
  (completedIntegralRestrictScalars_exact l E Y D hl n).1

attribute [local instance] integralTowerRestrictionLimits

/-- Exactness supplies the colimits instance for the recorded restriction functor.
Source: Stacks Tag 03DA (blueprint: lem-weil-integral-reduction-tower-well-defined). -/
theorem integralTowerRestrictionColimits (n : ℕ) :
    PreservesFiniteColimits (completedIntegralRestrictScalars l E Y D hl n) :=
  (completedIntegralRestrictScalars_exact l E Y D hl n).2

attribute [local instance] integralTowerRestrictionColimits

/-- The termwise finite reduction, using the recorded change-of-rings functor.
Source: Stacks Tag 06YY (blueprint: lem-weil-integral-reduction-tower-well-defined). -/
noncomputable abbrev integralTowerFiniteComplex (n : ℕ)
    (P : CochainComplex (completedIntegralModuleSheaves l E Y D hl) ℤ) :=
  unrestrictedTowerFiniteComplex l E Y n P

/-- The same reduction regarded as a complex over the completed coefficient sheaf.
Source: Stacks Tag 03EK (blueprint: lem-weil-integral-reduction-tower-well-defined). -/
noncomputable abbrev integralTowerComplex (n : ℕ)
    (P : CochainComplex (completedIntegralModuleSheaves l E Y D hl) ℤ) :=
  unrestrictedTowerComplex l E Y n P

/-- A pure tensor, followed by sheafification, in the recorded finite reduction.
Transport uses the object equality in the defining change-of-rings witness.
Source: Stacks Tag 03EK (blueprint: lem-weil-integral-reduction-tower-well-defined). -/
noncomputable def integralTowerTensorSection (n : ℕ)
    (M : completedIntegralModuleSheaves l E Y D hl)
    (U : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ)
    (s : (integralCoefficientCommRingSheaf l E Y n).obj.obj U) (x : M.val.obj U) :
    ((integralReductionChangeOfRings l E Y D hl n).obj M).val.obj U :=
  (eqToHom ((integralReductionExistence l E Y D hl n).choose_spec.choose M).symm).val.app U
    ((CategoryTheory.toSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y)
      (SheafOfModules.changeOfRingsPresheaf
        (completedIntegralCommRingProjection l E Y D hl n) M).presheaf).app U
          (s ⊗ₜ[(completedIntegralCommRingSheaf l E Y D hl).obj.obj U,
            ((completedIntegralCommRingProjection l E Y D hl n).hom.app U).hom] x))

/-- The canonical computation by a resolution, expressed using complexes rather than
homotopy representatives. Both transports are the standard quotient comparison.
Source: Stacks Tag 06YY (blueprint: lem-weil-integral-reduction-tower-well-defined). -/
noncomputable def integralTowerResolutionIso (n : ℕ)
    {P K : CochainComplex (completedIntegralModuleSheaves l E Y D hl) ℤ}
    (q : P ⟶ K)
    (hq : CochainComplex.IsKFlatResolutionIndependentCoefficients
      (J := AlgebraicGeometry.Scheme.ProEt.topology Y)
      (R := completedIntegralCommRingSheaf l E Y D hl) q) :
    (integralDerivedReduction l E Y D hl n).obj (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj (integralTowerFiniteComplex l E Y D hl n P) :=
  unrestrictedTowerResolutionIso l E Y n q hq

/-- The finite comparison is defined through the common derived reduction of K.
Source: Stacks Tag 06YY (blueprint: lem-weil-integral-reduction-tower-well-defined). -/
noncomputable def integralTowerFiniteComparison (n : ℕ)
    {P P' K : CochainComplex (completedIntegralModuleSheaves l E Y D hl) ℤ}
    (q : P ⟶ K) (q' : P' ⟶ K)
    (hq : CochainComplex.IsKFlatResolutionIndependentCoefficients
      (J := AlgebraicGeometry.Scheme.ProEt.topology Y)
      (R := completedIntegralCommRingSheaf l E Y D hl) q)
    (hq' : CochainComplex.IsKFlatResolutionIndependentCoefficients
      (J := AlgebraicGeometry.Scheme.ProEt.topology Y)
      (R := completedIntegralCommRingSheaf l E Y D hl) q') :
    DerivedCategory.Q.obj (integralTowerFiniteComplex l E Y D hl n P) ≅
      DerivedCategory.Q.obj (integralTowerFiniteComplex l E Y D hl n P') :=
  (integralTowerResolutionIso l E Y D hl n q hq).symm ≪≫
    integralTowerResolutionIso l E Y D hl n q' hq'

/-- Restrict the canonical finite comparison, using the canonical localization
factorization to express its endpoints by the restricted complexes.
Source: Stacks Tags 03DA/06YY
(blueprint: lem-weil-integral-reduction-tower-well-defined). -/
noncomputable def integralTowerComparison (n : ℕ)
    {P P' K : CochainComplex (completedIntegralModuleSheaves l E Y D hl) ℤ}
    (q : P ⟶ K) (q' : P' ⟶ K)
    (hq : CochainComplex.IsKFlatResolutionIndependentCoefficients
      (J := AlgebraicGeometry.Scheme.ProEt.topology Y)
      (R := completedIntegralCommRingSheaf l E Y D hl) q)
    (hq' : CochainComplex.IsKFlatResolutionIndependentCoefficients
      (J := AlgebraicGeometry.Scheme.ProEt.topology Y)
      (R := completedIntegralCommRingSheaf l E Y D hl) q') :
    DerivedCategory.Q.obj (integralTowerComplex l E Y D hl n P) ≅
      DerivedCategory.Q.obj (integralTowerComplex l E Y D hl n P') :=
  ((completedIntegralRestrictScalars l E Y D hl n).mapDerivedCategoryFactors.app _).symm ≪≫
    (completedIntegralRestrictScalars l E Y D hl n).mapDerivedCategory.mapIso
      (integralTowerFiniteComparison l E Y D hl n q q' hq hq') ≪≫
    (completedIntegralRestrictScalars l E Y D hl n).mapDerivedCategoryFactors.app _

/-- The unit maps are specified on local sections by x ↦ 1 ⊗ x and sheafification.
Source: Stacks Tag 03EK (blueprint: lem-weil-integral-reduction-tower-well-defined). -/
def integralTowerUnitCondition
    (P : CochainComplex (completedIntegralModuleSheaves l E Y D hl) ℤ)
    (γ : ∀ n : ℕ, P ⟶ integralTowerComplex l E Y D hl n P) : Prop :=
  ∀ (n : ℕ) (i : ℤ) (U : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ) (x : (P.X i).val.obj U),
    ((γ n).f i).val.app U x = integralTowerTensorSection l E Y D hl n (P.X i) U 1 x

/-- The transition maps are specified on sheafified pure tensors by s ⊗ x ↦ ρ(s) ⊗ x.
Source: Stacks Tag 03EK (blueprint: lem-weil-integral-reduction-tower-well-defined). -/
def integralTowerTransitionCondition
    (P : CochainComplex (completedIntegralModuleSheaves l E Y D hl) ℤ)
    (τ : ∀ n : ℕ, integralTowerComplex l E Y D hl (n + 1) P ⟶
      integralTowerComplex l E Y D hl n P) : Prop :=
  ∀ (n : ℕ) (i : ℤ) (U : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ)
    (s : (integralCoefficientCommRingSheaf l E Y (n + 1)).obj.obj U)
    (x : (P.X i).val.obj U),
    ((τ n).f i).val.app U (integralTowerTensorSection l E Y D hl (n + 1) (P.X i) U s x) =
      integralTowerTensorSection l E Y D hl n (P.X i) U
        ((integralCoefficientSheafTransition l E Y n).hom.app U s) x

private theorem integralTowerTensorSection_ext (n : ℕ)
    (M N : completedIntegralModuleSheaves l E Y D hl)
    (f g : (completedIntegralRestrictScalars l E Y D hl n).obj
      ((integralReductionChangeOfRings l E Y D hl n).obj M) ⟶ N)
    (h : ∀ U s x,
      f.val.app U (integralTowerTensorSection l E Y D hl n M U s x) =
        g.val.app U (integralTowerTensorSection l E Y D hl n M U s x)) : f = g := by
  let e := (integralReductionExistence l E Y D hl n).choose_spec.choose M
  let a := (completedIntegralRestrictScalars l E Y D hl n).map (eqToHom e.symm)
  apply (cancel_epi a).1
  apply (SheafOfModules.toSheaf _).map_injective
  apply Sheaf.hom_ext
  apply CategoryTheory.sheafify_hom_ext _ _ _ N.isSheaf
  ext U z
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul s x => exact h U s x
  | add z w hz hw => simpa only [map_add] using congrArg₂ (· + ·) hz hw

private theorem integralTowerUnrestricted_condition
    (P : CochainComplex (completedIntegralModuleSheaves l E Y D hl) ℤ) :
    integralTowerUnitCondition l E Y D hl P (unrestrictedTowerUnit l E Y P) ∧
      integralTowerTransitionCondition l E Y D hl P
        (unrestrictedTowerTransition l E Y P) := by
  constructor
  · change unrestrictedTowerUnitCondition l E Y P (unrestrictedTowerUnit l E Y P)
    exact unrestrictedTowerUnit_condition l E Y P
  · intro n i U s x
    have h :=
      (unrestrictedIntegralTransition_existsUnique l E Y n).exists.choose_spec P i U s x
    unfold unrestrictedIntegralTensorSection at h
    unfold unrestrictedTowerTransition unrestrictedIntegralTransition integralTowerTensorSection
    exact h

/-- There is a unique pair of chain-level unit and reduction maps with the stated
pure-tensor formulas. These formulas specify maps on the sheafifications, not just on
constant sections.
Source: Stacks Tag 03EK (blueprint: lem-weil-integral-reduction-tower-well-defined).
Proof: in each degree and site object send x to the sheafification of 1⊗x. Tensor
balancing, naturality of the coefficient projection and of the sheafification unit
make this a map of presheaves of modules, hence of sheaves. For the transition send
s⊗x to ρ(s)⊗x before sheafification. The identity π_n = ρ_n π_(n+1) makes this
balanced and linear over the completed ring. Both maps commute with restrictions
and with the differential by their sectionwise formulas, so define chain maps.
Uniqueness of the unit follows on every section from its formula. For the transition,
pure tensors generate the presheaf tensor product, and the universal property of
sheafification extends equality to the sheaves. Degreewise equality is equality of
chain maps; function extensionality gives uniqueness of the pair at every level. -/
theorem integralTowerMaps_existUnique
    (P : CochainComplex (completedIntegralModuleSheaves l E Y D hl) ℤ) :
    ∃! a : (∀ n : ℕ, P ⟶ integralTowerComplex l E Y D hl n P) ×
      (∀ n : ℕ, integralTowerComplex l E Y D hl (n + 1) P ⟶
        integralTowerComplex l E Y D hl n P),
      integralTowerUnitCondition l E Y D hl P a.1 ∧
        integralTowerTransitionCondition l E Y D hl P a.2 := by
  classical
  let γ : ∀ n : ℕ, P ⟶ integralTowerComplex l E Y D hl n P :=
    unrestrictedTowerUnit l E Y P
  let τ : ∀ n : ℕ, integralTowerComplex l E Y D hl (n + 1) P ⟶
      integralTowerComplex l E Y D hl n P := unrestrictedTowerTransition l E Y P
  have hγ : integralTowerUnitCondition l E Y D hl P γ :=
    (integralTowerUnrestricted_condition l E Y D hl P).1
  have hτ : integralTowerTransitionCondition l E Y D hl P τ :=
    (integralTowerUnrestricted_condition l E Y D hl P).2
  refine ⟨(γ, τ), ⟨hγ, hτ⟩, ?_⟩
  intro a ha
  apply Prod.ext
  · funext n
    ext i U x
    exact (ha.1 n i U x).trans (hγ n i U x).symm
  · funext n
    ext i : 1
    apply integralTowerTensorSection_ext l E Y D hl (n + 1) (P.X i)
    intro U s x
    exact (ha.2 n i U s x).trans (hτ n i U s x).symm

/-- The chain-level unit x ↦ x⊗1, determined uniquely by its sectionwise formula.
Source: Stacks Tag 03EK (blueprint: lem-weil-integral-reduction-tower-well-defined). -/
noncomputable def integralTowerUnit
    (P : CochainComplex (completedIntegralModuleSheaves l E Y D hl) ℤ) (n : ℕ) :
    P ⟶ integralTowerComplex l E Y D hl n P :=
  (integralTowerMaps_existUnique l E Y D hl P).exists.choose.1 n

/-- The chain-level reduction id⊗ρ, determined uniquely on sheafified pure tensors.
Source: Stacks Tag 03EK (blueprint: lem-weil-integral-reduction-tower-well-defined). -/
noncomputable def integralTowerTransition
    (P : CochainComplex (completedIntegralModuleSheaves l E Y D hl) ℤ) (n : ℕ) :
    integralTowerComplex l E Y D hl (n + 1) P ⟶ integralTowerComplex l E Y D hl n P :=
  (integralTowerMaps_existUnique l E Y D hl P).exists.choose.2 n

private theorem integralTowerMaps_eq
    (P : CochainComplex (completedIntegralModuleSheaves l E Y D hl) ℤ) :
    (integralTowerMaps_existUnique l E Y D hl P).exists.choose =
      (unrestrictedTowerUnit l E Y P, unrestrictedTowerTransition l E Y P) := by
  exact (integralTowerMaps_existUnique l E Y D hl P).unique
    (integralTowerMaps_existUnique l E Y D hl P).exists.choose_spec
    (integralTowerUnrestricted_condition l E Y D hl P)

private theorem integralTowerUnit_eq
    (P : CochainComplex (completedIntegralModuleSheaves l E Y D hl) ℤ) (n : ℕ) :
    integralTowerUnit l E Y D hl P n = unrestrictedTowerUnit l E Y P n :=
  congrArg (fun a ↦ a.1 n) (integralTowerMaps_eq l E Y D hl P)

private theorem integralTowerTransition_eq
    (P : CochainComplex (completedIntegralModuleSheaves l E Y D hl) ℤ) (n : ℕ) :
    integralTowerTransition l E Y D hl P n = unrestrictedTowerTransition l E Y P n :=
  congrArg (fun a ↦ a.2 n) (integralTowerMaps_eq l E Y D hl P)

/-- The image of the resolution augmentation is invertible in the derived category.
Source: Stacks Tag 06YS (blueprint: lem-weil-integral-reduction-tower-well-defined). -/
noncomputable def integralTowerAugmentationIso
    {P K : CochainComplex (completedIntegralModuleSheaves l E Y D hl) ℤ}
    (q : P ⟶ K)
    (hq : CochainComplex.IsKFlatResolutionIndependentCoefficients
      (J := AlgebraicGeometry.Scheme.ProEt.topology Y)
      (R := completedIntegralCommRingSheaf l E Y D hl) q) :
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
theorem integralReductionTowerWellDefined
    {P P' K : CochainComplex (completedIntegralModuleSheaves l E Y D hl) ℤ}
    (q : P ⟶ K) (q' : P' ⟶ K)
    (hq : CochainComplex.IsKFlatResolutionIndependentCoefficients
      (J := AlgebraicGeometry.Scheme.ProEt.topology Y)
      (R := completedIntegralCommRingSheaf l E Y D hl) q)
    (hq' : CochainComplex.IsKFlatResolutionIndependentCoefficients
      (J := AlgebraicGeometry.Scheme.ProEt.topology Y)
      (R := completedIntegralCommRingSheaf l E Y D hl) q')
    :
    (∀ n : ℕ,
      (integralTowerAugmentationIso l E Y D hl q hq).inv ≫
        DerivedCategory.Q.map (integralTowerUnit l E Y D hl P n) ≫
        (integralTowerComparison l E Y D hl n q q' hq hq').hom =
      (integralTowerAugmentationIso l E Y D hl q' hq').inv ≫
        DerivedCategory.Q.map (integralTowerUnit l E Y D hl P' n)) ∧
    (∀ n : ℕ,
      DerivedCategory.Q.map (integralTowerTransition l E Y D hl P n) ≫
        (integralTowerComparison l E Y D hl n q q' hq hq').hom =
      (integralTowerComparison l E Y D hl (n + 1) q q' hq hq').hom ≫
        DerivedCategory.Q.map (integralTowerTransition l E Y D hl P' n)) := by
  have hc (n : ℕ) : integralTowerComparison l E Y D hl n q q' hq hq' =
      unrestrictedTowerComparison l E Y n q q' hq hq' := by
    simp only [integralTowerComparison, integralTowerFiniteComparison,
      integralTowerResolutionIso, unrestrictedTowerComparison,
      unrestrictedTowerFiniteComparison]
    rfl
  obtain ⟨hu, ht⟩ := unrestrictedReductionTowerWellDefined l E Y q q' hq hq'
  constructor
  · intro n
    rw [integralTowerUnit_eq, integralTowerUnit_eq, hc]
    simpa only [integralTowerAugmentationIso, unrestrictedTowerAugmentationIso] using hu n
  · intro n
    rw [integralTowerTransition_eq, integralTowerTransition_eq, hc, hc]
    exact ht n

end WeilConjectures
