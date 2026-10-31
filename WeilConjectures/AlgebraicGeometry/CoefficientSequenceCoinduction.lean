/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoefficientRingedSequenceSiteSupplement
public import WeilConjectures.CategoryTheory.SystemCoinducedAdjunction
public import WeilConjectures.CategoryTheory.ExactDerivedAdjunctionSupplement
public import WeilConjectures.CategoryTheory.SystemEvaluationTopos

/-! # Exact coinduction at a finite coefficient level

Source: Stacks 0941 and 015F.
(blueprint: lem-coef-sequence-exact-coinduction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures.CoefficientCoinduction
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{u})

/-- The pro-etale site fits in the fixed coefficient universe.
Source: Stacks 03DA and 0941 (blueprint: lem-coef-sequence-exact-coinduction). -/
instance coefficientSiteSmall :
    EssentiallySmall.{u + 1} W.ProEt := essentiallySmallSelf.{u + 1} _

/-- Abelian sheafification on the finite-level site in the fixed coefficient universe.
Source: Stacks 03DA and 0941 (blueprint: lem-coef-sequence-exact-coinduction). -/
instance coefficientSiteAbSheafify :
    HasSheafify (Scheme.ProEt.topology W) AddCommGrpCat.{u + 1} :=
  integralCoefficientAbSheafify.{u, u} W

/-- Local bijectivity detects abelian sheafification in the fixed coefficient universe.
Source: Stacks 03DA and 0941 (blueprint: lem-coef-sequence-exact-coinduction). -/
instance coefficientSiteAbLocallyBijective :
    (Scheme.ProEt.topology W).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  integralCoefficientAbLocallyBijective.{u, u} W

/-- The sequence site fits in the fixed coefficient universe.
Source: Stacks 03DA and 0941 (blueprint: lem-coef-sequence-exact-coinduction). -/
instance sequenceSmall :
    EssentiallySmall.{u + 1} (ℕ × W.ProEt) := essentiallySmallSelf.{u + 1} _

/-- Abelian sheafification on the sequence site in the fixed coefficient universe.
Source: Stacks 03DA and 0941 (blueprint: lem-coef-sequence-exact-coinduction). -/
instance sequenceAbSheafify :
    HasSheafify (coefficientSequenceTopology (Scheme.ProEt.topology W))
      AddCommGrpCat.{u + 1} :=
  hasSheafifyEssentiallySmallSite.{u, u + 1, u + 1, u + 2, u + 1} _ _

/-- Local bijectivity detects sequence-site abelian sheafification.
Source: Stacks 03DA and 0941 (blueprint: lem-coef-sequence-exact-coinduction). -/
instance sequenceAbLocallyBijective :
    (coefficientSequenceTopology (Scheme.ProEt.topology W)).WEqualsLocallyBijective
      AddCommGrpCat.{u + 1} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u, u + 1, u + 1,
    u + 2, u + 1, u + 1, u + 1} _

/-- The actual commutative quotient coefficient system.
Source: Stacks 0941 and 015F (blueprint: lem-coef-sequence-exact-coinduction). -/
abbrev rings : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology W) CommRingCat.{u + 1} :=
  coefficientSequenceCommRingSystem l E W

/-- The explicit equivalence between strict semilinear systems and the sequence site.
Source: Stacks 0941 and 015F (blueprint: lem-coef-sequence-exact-coinduction). -/
abbrev equivalence := SheafOfModules.strictSystemSequenceEquivalence.{u + 1, u, u + 1} (rings l E W)

/-- Slice evaluation under the strict-system equivalence is the recorded evaluation.
Source: Stacks 0941 (blueprint: lem-coef-sequence-exact-coinduction).
Proof: the vertical structural ring maps both have identity components. Their equality
identifies the two continuous module pushforwards. -/
theorem evaluation_eq (n : ℕ) :
    (equivalence l E W).inverse ⋙
      SheafOfModules.systemEvaluation.{u + 1, u, u + 1} (rings l E W) n =
      coefficientSequenceEvaluation l E W n := by
  have hφ : SheafOfModules.systemSequenceVerticalRingMap.{u + 1, u, u + 1} (rings l E W) n =
      eqToHom (coefficientSequenceEvaluationRing_eq l E W n).symm := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext V
    rw [ObjectProperty.eqToHom_hom, eqToHom_app]
    rfl
  change SheafOfModules.pushforward
    (SheafOfModules.systemSequenceVerticalRingMap.{u + 1, u, u + 1} (rings l E W) n) = _
  rw [hφ]
  rfl

/-- Coinduction consists of scalar restriction above n and zero below n,
transported to the actual sequence site. Source: Stacks 0941
(blueprint: lem-coef-sequence-exact-coinduction). -/
def right (n : ℕ) : normalizedDVRModules l E W n ⥤ coefficientSequenceModules l E W :=
  SheafOfModules.SequenceCoinduced.rightExtension.{u + 1, u, u + 1} (rings l E W) n ⋙
    (equivalence l E W).functor

/-- The transported coinduction functor is additive.
Source: Stacks 0941 and 015F (blueprint: lem-coef-sequence-exact-coinduction). -/
instance right_additive (n : ℕ) : (right l E W n).Additive := by
  change (SheafOfModules.SequenceCoinduced.rightExtension (rings l E W) n ⋙
    SheafOfModules.strictSystemToSequenceFunctor (rings l E W)).Additive
  infer_instance

/-- The transported coinduction preserves finite limits.
Source: Stacks 0941 and 015F (blueprint: lem-coef-sequence-exact-coinduction). -/
instance right_limits (n : ℕ) : PreservesFiniteLimits (right l E W n) := by
  have := (SheafOfModules.SequenceCoinduced.rightExtension_exact.{u + 1, u, u + 1}
    (rings l E W) n).1
  unfold right
  infer_instance

/-- The transported coinduction preserves finite colimits.
Source: Stacks 0941 and 015F (blueprint: lem-coef-sequence-exact-coinduction). -/
instance right_colimits (n : ℕ) : PreservesFiniteColimits (right l E W n) := by
  have := (SheafOfModules.SequenceCoinduced.rightExtension_exact.{u + 1, u, u + 1}
    (rings l E W) n).2
  unfold right
  infer_instance

/-- The actual evaluation/coinduction adjunction, including its specified unit.
Source: Stacks 0941 (blueprint: lem-coef-sequence-exact-coinduction).
Proof: compose the inverse-equivalence adjunction with the explicit strict-system
coinduction adjunction, then identify their left functor by evaluation_eq. -/
def adjunction (n : ℕ) : coefficientSequenceEvaluation l E W n ⊣ right l E W n :=
  ((equivalence l E W).symm.toAdjunction.comp
    (SheafOfModules.SequenceCoinduced.adjunction.{u + 1, u, u + 1} (rings l E W) n)).ofNatIsoLeft
      (eqToIso (evaluation_eq l E W n))

/-- Exact coinduction on the derived categories, with the localized actual adjunction.
Source: Stacks 015F (blueprint: lem-coef-sequence-exact-coinduction). -/
def derivedRight (n : ℕ) :
    normalizedDVRDerived l E W n ⥤ coefficientSequenceDerived l E W :=
  letI := HasDerivedCategory.standard (coefficientSequenceModules l E W)
  letI := HasDerivedCategory.standard (normalizedDVRModules l E W n)
  (right l E W n).mapDerivedCategory

/-- The derived adjunction is obtained by localizing the termwise adjunction.
Source: Stacks 015F (blueprint: lem-coef-sequence-exact-coinduction). -/
def derivedAdjunction (n : ℕ) :
    coefficientSequenceDerivedEvaluation l E W n ⊣ derivedRight l E W n :=
  letI := HasDerivedCategory.standard (coefficientSequenceModules l E W)
  letI := HasDerivedCategory.standard (normalizedDVRModules l E W n)
  (adjunction l E W n).mapExactDerivedCategory

end WeilConjectures.CoefficientCoinduction
