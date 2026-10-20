/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q06
-/
module

public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.KrullDimension
public import Sheaf.Paper.BoundedConstructibleTower
public import Sheaf.Paper.IntrinsicCompletionCompleted
public import Sheaf.Paper.WitnessCompatibility

/-!
# Bounded constructible derived-complete objects

Source: blueprint, proper base change, order 1300
(blueprint: def-weil-pbc-bounded-constructible-complete).
The coefficient ring is the actual inverse limit. The three defining conditions
are properties; no origin, local model, or completion representative is retained.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 512
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
open ProEtale
variable (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
variable (d : AdicCoefficientDatum A)

/-- The actual completed-coefficient ambient category. Source: blueprint order 1300
(blueprint: def-weil-pbc-bounded-constructible-complete). -/
abbrev PbcCompletedDerived := DerivedCategory (pbcModules T (pbcAdicCompletion T d))

/-- Derived extension along the actual limit projection. Source: blueprint order 1300
(blueprint: def-weil-pbc-bounded-constructible-complete). -/
abbrev pbcCompletedReduction (n : ℕ) := pbcDerivedExtend (pbcAdicProjection T d n)

/-- Constants mapped to the continuous-function coefficient presentation.
Source: blueprint order 1300 (blueprint: def-weil-pbc-bounded-constructible-complete). -/
def pbcFunctionScalars (n : ℕ) :
    (Functor.const T.ProEtᵒᵖ).obj (RingCat.of (PbcQuotient d n)) ⟶
      ((adicLisseForget T).obj ((pbcAdicRings T d).obj (op n))).obj :=
  finiteCoefficientScalarMap T (PbcQuotient d n) ≫
    (AdicCoefficients.finiteRingComparison T (PbcQuotient d n)).inv.hom

/-- The coefficient-presentation transport preserves local bijectivity of constants.
Source: blueprint order 1300 (blueprint: def-weil-pbc-bounded-constructible-complete).
Proof: finiteCoefficientScalarMap is locally bijective. The second factor is a ring
sheaf isomorphism, so composing it preserves local injectivity and local surjectivity. -/
theorem pbcFunctionScalars_locallyBijective (n : ℕ) :
    Presheaf.IsLocallyInjective (ProEt.topology T) (pbcFunctionScalars T d n) ∧
      Presheaf.IsLocallySurjective (ProEt.topology T) (pbcFunctionScalars T d n) := by
  sorry

/-- Local injectivity of the specified coefficient presentation. Source: blueprint
order 1300 (blueprint: def-weil-pbc-bounded-constructible-complete). -/
instance pbcFunctionScalars_injective (n : ℕ) :
    Presheaf.IsLocallyInjective (ProEt.topology T) (pbcFunctionScalars T d n) :=
  (pbcFunctionScalars_locallyBijective T d n).1

/-- Local surjectivity of the specified coefficient presentation. Source: blueprint
order 1300 (blueprint: def-weil-pbc-bounded-constructible-complete). -/
instance pbcFunctionScalars_surjective (n : ℕ) :
    Presheaf.IsLocallySurjective (ProEt.topology T) (pbcFunctionScalars T d n) :=
  (pbcFunctionScalars_locallyBijective T d n).2

/-- Associated modules for any locally bijective coefficient presentation.
Keeping the presentation abstract avoids expanding the quotient limit during
normalization. Source: blueprint order 1300
(blueprint: def-weil-pbc-bounded-constructible-complete). -/
def pbcAssociatedModule (P : Type (u + 1)) [CommRing P]
    (R : Sheaf (ProEt.topology T) RingCat.{u + 1})
    (α : (Functor.const T.ProEtᵒᵖ).obj (RingCat.of P) ⟶ R.obj)
    [Presheaf.IsLocallyInjective (ProEt.topology T) α]
    [Presheaf.IsLocallySurjective (ProEt.topology T) α] :
    Sheaf (ProEt.topology T) (ModuleCat.{u + 1} P) ⥤ ringedSiteModules.{u + 1} R :=
  sheafToPresheaf _ _ ⋙ finiteCoefficientModulePresheaf T.ProEt P ⋙
    PresheafOfModules.sheafification α

/-- The underlying additive sheafification of a fixed-coefficient module sheaf.
Source: blueprint order 1300 (blueprint: def-weil-pbc-bounded-constructible-complete). -/
def pbcAssociatedAdditive (P : Type (u + 1)) [CommRing P] :=
  sheafToPresheaf (ProEt.topology T) (ModuleCat.{u + 1} P) ⋙
    finiteCoefficientModulePresheaf T.ProEt P ⋙
    PresheafOfModules.toPresheaf ((Functor.const T.ProEtᵒᵖ).obj (RingCat.of P)) ⋙
    presheafToSheaf (ProEt.topology T) AddCommGrpCat.{u + 1}

/-- The source restriction comparison forgets to exactly the ordinary additive
sheafification. Source: blueprint order 1300
(blueprint: def-weil-pbc-bounded-constructible-complete). -/
def pbcAssociatedRestrictionSource (P Q : Type (u + 1)) [CommRing P] [CommRing Q]
    (R : Sheaf (ProEt.topology T) RingCat.{u + 1})
    (α : (Functor.const T.ProEtᵒᵖ).obj (RingCat.of P) ⟶ R.obj)
    [Presheaf.IsLocallyInjective (ProEt.topology T) α]
    [Presheaf.IsLocallySurjective (ProEt.topology T) α] (q : P →+* Q) :
    (Sheaf.restrictScalars (ProEt.topology T) q ⋙ pbcAssociatedModule T P R α) ⋙
        SheafOfModules.toSheaf R ≅ pbcAssociatedAdditive T Q :=
  Iso.refl _

/-- The target restriction comparison forgets to the same additive sheafification.
Source: blueprint order 1300 (blueprint: def-weil-pbc-bounded-constructible-complete). -/
def pbcAssociatedRestrictionTarget (Q : Type (u + 1)) [CommRing Q]
    (R S : Sheaf (ProEt.topology T) RingCat.{u + 1})
    (β : (Functor.const T.ProEtᵒᵖ).obj (RingCat.of Q) ⟶ S.obj)
    [Presheaf.IsLocallyInjective (ProEt.topology T) β]
    [Presheaf.IsLocallySurjective (ProEt.topology T) β] (r : R ⟶ S) :
    (pbcAssociatedModule T Q S β ⋙ SheafOfModules.restrictScalars r) ⋙
        SheafOfModules.toSheaf R ≅ pbcAssociatedAdditive T Q :=
  Iso.refl _

/-- Identity on the underlying additive sheafification uniquely normalizes the
restriction comparison for compatible scalar presentations.
Source: blueprint order 1300 (blueprint: def-weil-pbc-bounded-constructible-complete).
Proof: the scalar-square equality identifies the two restricted actions locally on
coefficient generators and hence everywhere. Identity on the underlying additive
sheafification is therefore linear and natural. Its inverse is the same identity;
faithfulness of the additive forgetful functor gives uniqueness. -/
theorem pbcAssociatedRestriction_exists
    (P Q : Type (u + 1)) [CommRing P] [CommRing Q]
    (R S : Sheaf (ProEt.topology T) RingCat.{u + 1})
    (α : (Functor.const T.ProEtᵒᵖ).obj (RingCat.of P) ⟶ R.obj)
    (β : (Functor.const T.ProEtᵒᵖ).obj (RingCat.of Q) ⟶ S.obj)
    [Presheaf.IsLocallyInjective (ProEt.topology T) α]
    [Presheaf.IsLocallySurjective (ProEt.topology T) α]
    [Presheaf.IsLocallyInjective (ProEt.topology T) β]
    [Presheaf.IsLocallySurjective (ProEt.topology T) β]
    (q : P →+* Q) (r : R ⟶ S)
    (_h : α ≫ r.hom = (Functor.const T.ProEtᵒᵖ).map (RingCat.ofHom q) ≫ β) :
    ∃! e : Sheaf.restrictScalars (ProEt.topology T) q ⋙ pbcAssociatedModule T P R α ≅
        pbcAssociatedModule T Q S β ⋙ SheafOfModules.restrictScalars r,
      Functor.whiskerRight e.hom (SheafOfModules.toSheaf R) =
        (pbcAssociatedRestrictionSource T P Q R α q).hom ≫
          (pbcAssociatedRestrictionTarget T Q R S β r).inv := by
  sorry

/-- Canonical associated-module-sheaf realization, with the coefficient presentation
changed along the recorded isomorphism. Source: blueprint order 1300
(blueprint: def-weil-pbc-bounded-constructible-complete). -/
abbrev pbcFunctionRealization (n : ℕ) :
    Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (PbcQuotient d n)) ⥤
      pbcModules T ((pbcAdicRings T d).obj (op n)) :=
  pbcAssociatedModule T (PbcQuotient d n)
    ((adicLisseForget T).obj ((pbcAdicRings T d).obj (op n)))
    (pbcFunctionScalars T d n)

/-- Realization is the canonical exact additive equivalence, including for zero rings.
Source: blueprint order 1300 (blueprint: def-weil-pbc-bounded-constructible-complete).
Proof: finiteRingComparison is fixed by the coefficient sheafification units.
Its composite with the constants map is locally bijective. Associated module
sheafification therefore has invertible unit and counit on module sheaves.
They identify the underlying sheaves and scalar actions. The equivalence is additive
sectionwise and hence preserves finite limits and colimits. -/
theorem pbcFunctionRealization_exact (n : ℕ) :
    (pbcFunctionRealization T d n).IsEquivalence ∧
      (pbcFunctionRealization T d n).Additive ∧
      PreservesFiniteLimits (pbcFunctionRealization T d n) ∧
      PreservesFiniteColimits (pbcFunctionRealization T d n) := by
  sorry

/-- The canonical realization equivalence. Source: blueprint order 1300
(blueprint: def-weil-pbc-bounded-constructible-complete). -/
instance pbcFunctionRealization_equivalence (n : ℕ) :
    (pbcFunctionRealization T d n).IsEquivalence :=
  (pbcFunctionRealization_exact T d n).1

/-- Exact realization, additive part. Source: blueprint order 1300
(blueprint: def-weil-pbc-bounded-constructible-complete). -/
instance pbcFunctionRealization_additive (n : ℕ) :
    (pbcFunctionRealization T d n).Additive :=
  (pbcFunctionRealization_exact T d n).2.1

/-- Exact realization, left exact part. Source: blueprint order 1300
(blueprint: def-weil-pbc-bounded-constructible-complete). -/
instance pbcFunctionRealization_limits (n : ℕ) :
    PreservesFiniteLimits (pbcFunctionRealization T d n) :=
  (pbcFunctionRealization_exact T d n).2.2.1

/-- Exact realization, right exact part. Source: blueprint order 1300
(blueprint: def-weil-pbc-bounded-constructible-complete). -/
instance pbcFunctionRealization_colimits (n : ℕ) :
    PreservesFiniteColimits (pbcFunctionRealization T d n) :=
  (pbcFunctionRealization_exact T d n).2.2.2

/-- Realization on derived categories. Source: blueprint order 1300
(blueprint: def-weil-pbc-bounded-constructible-complete). -/
abbrev pbcDerivedFunctionRealization (n : ℕ) :=
  (pbcFunctionRealization T d n).mapDerivedCategory

/-- The exact coefficient-presentation equivalence descends to an equivalence.
Source: blueprint order 1300 (blueprint: def-weil-pbc-bounded-constructible-complete).
Proof: apply the ordinary inverse equivalence termwise to cochain complexes.
Exactness preserves quasi-isomorphisms on both sides. Localize both functors and
the unit and counit, which remain isomorphisms and satisfy the triangle identities. -/
@[instance] theorem pbcDerivedFunctionRealization_equivalence (n : ℕ) :
    (pbcDerivedFunctionRealization T d n).IsEquivalence := by
  sorry

/-- The scalar-presentation square is the canonical quotient square.
Source: blueprint order 1300 (blueprint: def-weil-pbc-bounded-constructible-complete).
Proof: all four maps send a constant residue class to its lower residue class.
The finiteRingComparison maps are fixed by the sheafification units, so equality on
these generators proves equality of their sheafified maps. -/
theorem pbcFunctionScalars_comp (n : ℕ) :
    pbcFunctionScalars T d (n + 1) ≫
        ((adicLisseForget T).map
          (pbcAdicQuotient T d (n + 1) n (Nat.le_succ n))).hom =
      (Functor.const T.ProEtᵒᵖ).map
        (RingCat.ofHom (pbcWitnessQuotientMap d (n + 1) n (Nat.le_succ n))) ≫
          pbcFunctionScalars T d n := by
  sorry

/-- The normalized ordinary scalar-restriction comparison. Source: blueprint order 1300
(blueprint: def-weil-pbc-bounded-constructible-complete). -/
def pbcFunctionRestriction (n : ℕ) :
    Sheaf.restrictScalars (ProEt.topology T)
        (pbcWitnessQuotientMap d (n + 1) n (Nat.le_succ n)) ⋙
        pbcFunctionRealization T d (n + 1) ≅
      pbcFunctionRealization T d n ⋙
        pbcRestrict (pbcAdicQuotient T d (n + 1) n (Nat.le_succ n)) :=
  (pbcAssociatedRestriction_exists T (PbcQuotient d (n + 1)) (PbcQuotient d n)
    ((adicLisseForget T).obj ((pbcAdicRings T d).obj (op (n + 1))))
    ((adicLisseForget T).obj ((pbcAdicRings T d).obj (op n)))
    (pbcFunctionScalars T d (n + 1)) (pbcFunctionScalars T d n)
    (pbcWitnessQuotientMap d (n + 1) n (Nat.le_succ n))
    ((adicLisseForget T).map (pbcAdicQuotient T d (n + 1) n (Nat.le_succ n)))
    (pbcFunctionScalars_comp T d n)).exists.choose

/-- Its exact derived descent. Source: blueprint order 1300
(blueprint: def-weil-pbc-bounded-constructible-complete). -/
def pbcDerivedFunctionRestriction (n : ℕ) :
    Sheaf.derivedRestrictScalars (ProEt.topology T)
        (pbcWitnessQuotientMap d (n + 1) n (Nat.le_succ n)) ⋙
      pbcDerivedFunctionRealization T d (n + 1) ≅
    pbcDerivedFunctionRealization T d n ⋙
      pbcDerivedRestrict (pbcAdicQuotient T d (n + 1) n (Nat.le_succ n)) :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (pbcFunctionRestriction T d n) ≪≫
      Functor.mapDerivedCategoryCompIso _ _

/-- The tensor comparison is the mate of the section-normalized restriction comparison.
Source: blueprint order 1300 (blueprint: def-weil-pbc-bounded-constructible-complete). -/
def pbcFunctionReductionMap (n : ℕ) :
    pbcDerivedFunctionRealization T d (n + 1) ⋙
        pbcDerivedExtend (pbcAdicQuotient T d (n + 1) n (Nat.le_succ n)) ⟶
      pbcWitnessReduction T d n ⋙ pbcDerivedFunctionRealization T d n :=
  ((mateEquiv (Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars (ProEt.topology T)
        (pbcWitnessQuotientMap d (n + 1) n (Nat.le_succ n))))
    (pbcDerivedScalarAdjunction
      (pbcAdicQuotient T d (n + 1) n (Nat.le_succ n)))).symm
    (TwoSquare.mk _ _ _ _ (pbcDerivedFunctionRestriction T d n).hom)).natTrans

/-- The canonical tensor mate is invertible. Source: blueprint order 1300
(blueprint: def-weil-pbc-bounded-constructible-complete).
Proof: use flat-term K-flat representatives. Realization is an exact coefficient
presentation equivalence and preserves K-flatness. The mate is ordinary balancing on
these representatives, because the restriction comparison is the identity on local
generators. Its inverse is the reverse balancing map. Localization proves the claim. -/
theorem pbcFunctionReductionMap_isIso (n : ℕ) : IsIso (pbcFunctionReductionMap T d n) := by
  sorry

/-- Canonical coefficient-reduction comparison. Source: blueprint order 1300
(blueprint: def-weil-pbc-bounded-constructible-complete). -/
def pbcFunctionReduction (n : ℕ) :
    pbcDerivedFunctionRealization T d (n + 1) ⋙
        pbcDerivedExtend (pbcAdicQuotient T d (n + 1) n (Nat.le_succ n)) ≅
      pbcWitnessReduction T d n ⋙ pbcDerivedFunctionRealization T d n :=
  letI := pbcFunctionReductionMap_isIso T d n
  asIso (pbcFunctionReductionMap T d n)

/-- Intrinsic completeness transported along the normalized completed-ring comparison.
The generator tuple and complex representative are existential proof witnesses only.
Source: blueprint order 1300 (blueprint: def-weil-pbc-bounded-constructible-complete). -/
def PbcIsIntrinsicallyComplete (K : PbcCompletedDerived T d) : Prop :=
  ∃ (r : ℕ) (f : Fin r → A) (hf : Ideal.span (Set.range f) = d.ideal)
    (C : CochainComplex (adicDatumModules T
      { toCompleteCoefficientDatum := d.toCompleteCoefficientDatum,
        quotientFinite := d.quotientFinite }) ℤ)
    (e : (completedConstantQ _).obj C ≅
      (pbcDerivedExtend (pbcCompletedComparison T d).inv).obj K),
    IsCompletedIntrinsicallyDerivedComplete T
      { toCompleteCoefficientDatum := d.toCompleteCoefficientDatum,
        quotientFinite := d.quotientFinite } r f hf C e

/-- The canonical reduction tower has the recorded common local bounded models.
The equations identify its transitions, not merely its individual levels.
Source: blueprint order 1300 (blueprint: def-weil-pbc-bounded-constructible-complete). -/
def PbcHasUniformConstructibleReductions (K : PbcCompletedDerived T d) : Prop :=
  ∃ (M : AdicTower T d)
    (e : ∀ n : ℕ, M.level n ≅ (pbcCompletedReduction T d n).obj K),
    IsUniformlyBoundedConstructibleAdicTower d M ∧
    ∀ (b a : ℕ) (hab : a ≤ b),
      adicTowerSemilinearTransition T d M.level M.normalization b a hab ≫
          (pbcDerivedRestrict (pbcAdicQuotient T d b a hab)).map (e a).hom =
        (e b).hom ≫ pbcReductionTransition (pbcAdicProjection T d b)
          (pbcAdicQuotient T d b a hab) (pbcAdicProjection T d a)
          (pbcAdicProjection_comp T d b a hab) K

/-- Existence of compatible bounded-below étale origins, with precisely the canonical
normalization. Adjacent equations give all quotient cocycles, including identities,
by the iterated-composite convention of PbcWitnessedTower.
Source: blueprint order 1300 (blueprint: def-weil-pbc-bounded-constructible-complete). -/
def PbcHasCompatibleEtaleOrigins (K : PbcCompletedDerived T d) : Prop :=
  ∃ (P : PbcWitnessedTower T d)
    (e : ∀ n : ℕ, (pbcDerivedFunctionRealization T d n).obj (P.K n) ≅
      (pbcCompletedReduction T d n).obj K),
    ∀ n : ℕ,
      (pbcDerivedFunctionRealization T d n).map (P.theta n).hom ≫ (e n).hom =
        (pbcFunctionReduction T d n).inv.app (P.K (n + 1)) ≫
          (pbcDerivedExtend (pbcAdicQuotient T d (n + 1) n (Nat.le_succ n))).map
            (e (n + 1)).hom ≫
          (pbcReductionNormalization (pbcAdicProjection T d (n + 1))
            (pbcAdicQuotient T d (n + 1) n (Nat.le_succ n)) (pbcAdicProjection T d n)
            (pbcAdicProjection_comp T d (n + 1) n (Nat.le_succ n)) K).hom

/-- The three conditions defining the integral constructible category.
Source: blueprint order 1300 (blueprint: def-weil-pbc-bounded-constructible-complete). -/
def PbcIsBoundedConstructibleComplete (K : PbcCompletedDerived T d) : Prop :=
  PbcIsIntrinsicallyComplete T d K ∧ PbcHasUniformConstructibleReductions T d K ∧
    PbcHasCompatibleEtaleOrigins T d K

/-- The full subcategory; the defining witnesses are not part of its objects' data.
Source: blueprint order 1300 (blueprint: def-weil-pbc-bounded-constructible-complete). -/
abbrev PbcBoundedConstructibleComplete :=
  ObjectProperty.FullSubcategory (PbcIsBoundedConstructibleComplete T d)

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
variable [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The valuation ring in the small site's coefficient universe. ULift changes size
only. Source: blueprint order 1300 (blueprint: def-weil-pbc-bounded-constructible-complete). -/
abbrev PbcIntegralRing := ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)

/-- The recorded uniformizer, with the same harmless size lift.
Source: blueprint order 1300 (blueprint: def-weil-pbc-bounded-constructible-complete). -/
def pbcUniformizer : PbcIntegralRing l E := ULift.up (Padic.coefficientExtensionUniformizer l E)

/-- The finite-extension integer ring satisfies the recorded coefficient hypotheses.
This is proof data only; the ideal and quotient rings are the actual constructions.
Source: blueprint order 1300, coefficient convention; Serre, Local Fields II.2
(blueprint: def-weil-pbc-bounded-constructible-complete).
Proof: the recorded integer ring is a DVR and its uniformizer generates its maximal
ideal. It is Noetherian and that principal ideal is finitely generated. Its finite
residue field has positive characteristic, hence every residue element has finite
additive order. Multiplication by each positive uniformizer power is injective; its
two-term finite-free resolution proves perfectness of the quotient. Positive quotients
are finite by finite_coefficientExtensionRing. Transport through the ULift ring
equivalence gives exactly the lifted ring, ideal powers and quotients displayed here. -/
theorem pbcCoefficientDatumProperties :
    IsNoetherianRing (PbcIntegralRing l E) ∧
      (Ideal.span ({pbcUniformizer l E} : Set (PbcIntegralRing l E))).FG ∧
      (∀ x : PbcIntegralRing l E ⧸ Ideal.span {pbcUniformizer l E},
        ∃ m : ℕ, 0 < m ∧ m • x = 0) ∧
      (∀ n : ℕ, 1 ≤ n → adicQuotientPerfect (PbcIntegralRing l E)
        (Ideal.span {pbcUniformizer l E}) n) ∧
      ∀ n : ℕ, Finite (PbcIntegralRing l E ⧸
        (Ideal.span {pbcUniformizer l E}) ^ (n + 1)) := by
  sorry

/-- The actual uniformizer-adic coefficient datum. All choices here are proofs of
properties of the already specified ring and ideal.
Source: blueprint order 1300 (blueprint: def-weil-pbc-bounded-constructible-complete). -/
def pbcIntegralDatum : AdicCoefficientDatum (PbcIntegralRing l E) where
  ideal := Ideal.span {pbcUniformizer l E}
  noetherian := (pbcCoefficientDatumProperties l E).1
  finitelyGenerated := (pbcCoefficientDatumProperties l E).2.1
  quotientTorsion := (pbcCoefficientDatumProperties l E).2.2.1
  quotientPerfect := (pbcCoefficientDatumProperties l E).2.2.2.1
  quotientFinite := (pbcCoefficientDatumProperties l E).2.2.2.2

/-- The integral full subcategory for the finite-extension coefficients and the base
hypotheses in the source. Source: blueprint order 1300
(blueprint: def-weil-pbc-bounded-constructible-complete). -/
abbrev PbcIntegralCategory (T : Scheme.{u}) [IsNoetherian T]
    (_hdim : ∃ m : ℕ, topologicalKrullDim T ≤ m)
    (_hl : ∀ t : T, IsUnit (l : T.presheaf.stalk t)) :=
  PbcBoundedConstructibleComplete T (pbcIntegralDatum l E)

end AlgebraicGeometry.Scheme
