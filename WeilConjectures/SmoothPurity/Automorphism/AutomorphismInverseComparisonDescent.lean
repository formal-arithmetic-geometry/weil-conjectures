/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.SmoothPurity.Integral.Comparison.IntegralComparisonSystemData
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import WeilConjectures.DeligneLaumon.IsomorphismFieldTransport
import WeilConjectures.SmoothPurity.Integral.IntegralAutomorphismCancellationNormalization

/-! # Normalized inverse comparisons at integral and field coefficient stages

This is the independently compiled inverse-comparison argument from the automorphism
stage-equivalence node, retaining its actual integral, rational and pair components.
(blueprint: lem-sf-automorphism-inverse-comparison-descent).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace WeilConjectures

set_option allowUnsafeReducibility true in
attribute [local reducible] CategoryTheory.Aut constructibleIntegralPullback
attribute [local irreducible] HasDerivedCategory.standard integralDerivedPullback
  integralComparisonComposition integralComparisonUnit AlgebraicGeometry.Scheme.residueField
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

/-- The inverse comparisons at all three infinite coefficient stages have their specified values.
Applying this to the inverse automorphism gives the other inverse-composition comparison.
Source: Weil-structures paragraph, canonical inverse comparisons and their descent
(blueprint: lem-sf-automorphism-inverse-comparison-descent).
Proof: specialize the existing isomorphism transport theorem. The integral
normalization lemma identifies its epsilon with the prescribed compositor
inverse followed by the identity unit. Its rational epsilon already has the
specified localization formula. Equality of integral components identifies the
epsilon natural transformations for independently chosen finite-stage witnesses.
Their rational formulas then identify their rational components. Mapping that
equality through the common-stage inclusion gives the required last formula. -/
theorem automorphismInverseComparisonDescent
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] [Fact (l ≠ D.p)]
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (C : IntegralComparisonSystem.{u} l)
    (T : Over (Spec (.of D.k))) [IsSeparated T.hom] [LocallyOfFiniteType T.hom]
    [QuasiCompact T.hom]
    [∀ x : T.left, Invertible (l : T.left.residueField x)] (e : Aut T.left) :
    ∃ a : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E],
        constructibleIntegralPullback l E e.hom ⋙ constructibleIntegralPullback l E e.inv ≅ 𝟭 _,
      (∀ (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
        (K : sfIntegralConstructibleCategory l E T.left),
        ((a E).hom.app K).hom =
          ((integralComparisonComposition l E C e.inv e.hom K).symm ≪≫
            eqToIso (congrArg (fun g ↦ (integralDerivedPullback l E g).obj K.obj)
              e.inv_hom_id) ≪≫ integralComparisonUnit l E C T.left K).hom) ∧
      ∃ b : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E],
          rationalDerivedPullback l E e.hom ⋙ rationalDerivedPullback l E e.inv ≅ 𝟭 _,
        (∀ (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
          (K : sfRationalConstructibleCategory l E T.left),
          HEq ((b E).hom.app K)
            ((sfRationalConstructibleLocalization l E T.left).map ((a E).hom.app K.obj))) ∧
        ∃ c : commonStageDerivedPullback l Ω e.hom ⋙
            commonStageDerivedPullback l Ω e.inv ≅ 𝟭 _,
          ∀ K : generalAlgebraicallyClosedConstructibleCategory l Ω T.left,
            HEq (c.hom.app K)
              ((GeneralAlgebraicallyClosedCoefficients.inclusion
                (l := l) (Ω := Ω) (Y := T.left) K.stage).map
                ((b (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω K.stage)).hom.app
                  K.obj)) := by
  classical
  obtain ⟨g, hg, he⟩ : ∃ (g : T.left ⟶ T.left) (hg : IsIso g),
      e = (letI : IsIso g := hg; asIso g) := by
    refine ⟨e.hom, inferInstance, ?_⟩
    apply Iso.ext
    rfl
  let : IsIso g := hg
  cases he
  let e : Aut T.left := asIso g
  let i : ∀ x : T.left, Invertible (l : T.left.residueField x) := inferInstance
  have hft : LocallyOfFiniteType T.hom := inferInstance
  have hqc : QuasiCompact T.hom := inferInstance
  let : T.left.Over (Spec (.of D.k)) := ⟨T.hom⟩
  let : LocallyOfFiniteType (T.left ↘ Spec (.of D.k)) := by
    set_option backward.isDefEq.respectTransparency true in
      exact hft
  let : QuasiCompact (T.left ↘ Spec (.of D.k)) := by
    set_option backward.isDefEq.respectTransparency true in
      exact hqc
  let : IsIso e.hom := ⟨⟨e.inv, e.hom_inv_id, e.inv_hom_id⟩⟩
  obtain ⟨iX, iY, h⟩ := isomorphismFieldTransport D l (Fact.out : l ≠ D.p) Ω e.hom
  have hiX : iX = i := Subsingleton.elim _ _
  have hiY : iY = i := Subsingleton.elim _ _
  cases hiX
  cases hiY
  let : IsIso e.hom := ⟨⟨e.inv, e.hom_inv_id, e.inv_hom_id⟩⟩
  obtain ⟨hX, hY, hS, _, S, _, _, ⟨A⟩, _⟩ := h
  have stage (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
      IsomorphismFieldTransportStage l E e.hom hX hY :=
    Classical.choice (hS E).1
  let cancel (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
      (K : sfIntegralConstructibleCategory l E T.left) :
      ((constructibleIntegralPullback l E e.hom ⋙
        constructibleIntegralPullback l E (inv e.hom)).obj K).obj ⟶ K.obj :=
    (((integralComparisonComposition l E C (inv e.hom) e.hom K).symm ≪≫
      eqToIso (congrArg (fun f ↦ (integralDerivedPullback l E f).obj K.obj)
        (IsIso.inv_hom_id e.hom)) ≪≫ integralComparisonUnit l E C T.left K :
      ((constructibleIntegralPullback l E e.hom ⋙
        constructibleIntegralPullback l E (inv e.hom)).obj K).obj ≅ K.obj).hom)
  have hn (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
      (B : IsomorphismFieldTransportStage l E e.hom hX hY)
      (K : sfIntegralConstructibleCategory l E T.left) :
      HEq (B.epsilon.hom.app K).hom (cancel E K) := by
    exact (B.epsilon_formula K).trans
      (integralAutomorphismCancellation_normalization l E C e.hom K)
  let a (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :=
    (stage E).epsilon
  let b (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :=
    (stage E).rationalEpsilon
  have hb (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
      (K : sfRationalConstructibleCategory l E T.left) :
      HEq ((b E).hom.app K)
        ((sfRationalConstructibleLocalization l E T.left).map ((a E).hom.app K.obj)) :=
    (stage E).rational_epsilon_formula K
  refine ⟨a, ?_, b, hb, A.epsilon, ?_⟩
  · intro E _ _ _ K
    apply eq_of_heq
    simpa only [a, cancel, e, asIso_hom, asIso_inv, Functor.id_obj] using hn E (stage E) K
  · intro K
    have he : (S K.stage).epsilon =
        (stage (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω K.stage)).epsilon := by
      apply Iso.ext
      apply NatTrans.ext
      funext J
      apply ObjectProperty.hom_ext
      exact eq_of_heq ((hn _ (S K.stage) J).trans (hn _ (stage _) J).symm)
    have hr := (S K.stage).rational_epsilon_formula K.obj
    rw [he] at hr
    have hrat : (S K.stage).rationalEpsilon.hom.app K.obj =
        (b (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω K.stage)).hom.app K.obj :=
      eq_of_heq (hr.trans (hb _ K.obj).symm)
    exact (A.epsilon_formula K).trans (heq_of_eq (congrArg
      ((GeneralAlgebraicallyClosedCoefficients.inclusion
        (l := l) (Ω := Ω) (Y := T.left) K.stage).map) hrat))

end WeilConjectures
