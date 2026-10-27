/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups Q52 and K9
-/
module

public import Sheaf.Paper.TraceStalkCompositorTowerData

/-! # Descent of strict stalk towers to Roos realizations

Source: Stacks Tags 0F4F and 05V1 and the strict-diagram part of blueprint
Local powers (b) (blueprint: lem-trf-stalk-tower-descent).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Normalized derived descent of a fixed strict germ diagram. The integral
compositor, iteration and point-unit equations are consequences, proved in the parent module.
Source: Stacks 0941, 0F4F (blueprint: lem-trf-stalk-tower-descent). -/
structure TrfStalkTowerDescentLaws (D : FiniteFieldDatum.{u})
    (I : IntegralComparisonSystem.{u} l) (S : TrfStalkCompositorTowerData l E D I) : Prop where
  /-- Realized finite comparison is the localization of the strict cone map. -/
  comparisonFactors : ∀ {X Y : Scheme.{u}} (f : Y ⟶ X) (v : Spec (.of D.k) ⟶ Y)
    (C : CochainComplex (coefficientSequenceModules l E X) ℤ),
    (S.comparison f v).hom.app (DerivedCategory.Q.obj C) ≫
        (S.factors (v ≫ f)).hom.app C =
      (S.realization v).map
          ((integralComparisonSequencePullback l E f).mapDerivedCategoryFactors.hom.app C) ≫
        (S.factors v).hom.app
          (((integralComparisonSequencePullback l E f).mapHomologicalComplex (.up ℤ)).obj C) ≫
        (trfIntegralModuleQ l E).map (integralOperationsRoosMap ((S.c f v).hom.app C))
  /-- Sections-to-stalk realization uses both canonical product coordinates. -/
  sectionsFactors : ∀ {X : Scheme.{u}} (v : Spec (.of D.k) ⟶ X)
    (C : CochainComplex (coefficientSequenceModules l E X) ℤ),
    (S.sections v).hom.app (DerivedCategory.Q.obj C) ≫ (S.factors v).hom.app C =
      (pointFibreIntegralAmbient D l E).map
          ((coefficientSequenceLimit l E _).map
            ((integralComparisonSequencePullback l E v).mapDerivedCategoryFactors.hom.app C)) ≫
        trfSystemSectionsRoosArrow l E D I
          (((integralComparisonSequencePullback l E v).mapHomologicalComplex (.up ℤ)).obj C) ≫
        (trfIntegralModuleQ l E).map (integralOperationsRoosMap ((S.e v).hom.app C))
  /-- The integral comparison is fixed by the defining pullback and the section comparison. -/
  integralNormalized : ∀ {X : Scheme.{u}}
    [_hX : ∀ x : X, Invertible (l : X.residueField x)] (v : Spec (.of D.k) ⟶ X)
    (K : sfIntegralConstructibleCategory l E X),
    (S.integral v).hom.app K =
      (pointFibreIntegralAmbient D l E).map
          (((I.coefficient E).pullback v).realization.hom.app K.obj) ≫
        (S.sections v).hom.app (((I.coefficient E).system X).reduction.obj K.obj)
  /-- Reparametrization after localization is exactly its strict diagonal cone map. -/
  reparamFactors : ∀ {X : Scheme.{u}} (v : Spec (.of D.k) ⟶ X) (α : D.k ≃+* D.k)
    (C : CochainComplex (coefficientSequenceModules l E X) ℤ),
    (S.derivedR v α).hom.app (DerivedCategory.Q.obj C) ≫
        (S.factors (Spec.map (CommRingCat.ofHom α.toRingHom) ≫ v)).hom.app C =
      (S.factors v).hom.app C ≫
        (trfIntegralModuleQ l E).map (integralOperationsRoosMap ((S.r v α).hom.app C))
  /-- The realized square is carried from the strict square, before evaluation. -/
  realizedReparam : ∀ {X Y : Scheme.{u}} (f : Y ⟶ X) (v : Spec (.of D.k) ⟶ Y)
    (α : D.k ≃+* D.k) (C : coefficientSequenceDerived l E X),
    HEq ((S.comparison f v).hom.app C ≫ (S.derivedR (v ≫ f) α).hom.app C)
      ((S.derivedR v α).hom.app ((integralComparisonDerivedSequencePullback l E f).obj C) ≫
        (S.comparison f (Spec.map (CommRingCat.ofHom α.toRingHom) ≫ v)).hom.app C)
  /-- Identity comparison agrees with the finite unit on the whole derived system. -/
  realizedIdentity : ∀ (X : Scheme.{u}) (v : Spec (.of D.k) ⟶ X)
    (C : coefficientSequenceDerived l E X),
    HEq ((S.comparison (𝟙 X) v).hom.app C)
      ((S.realization v).map ((integralComparisonSystemUnit l E X).hom.app C))
  /-- Sections respect the specified entire-system inverse-image compositor. -/
  sectionsComposition : ∀ {X Y : Scheme.{u}} (f : Y ⟶ X)
    (v : Spec (.of D.k) ⟶ Y) (C : coefficientSequenceDerived l E X),
    (pointFibreIntegralAmbient D l E).map
        ((coefficientSequenceLimit l E _).map
          ((integralComparisonSystemComposition l E v f).inv.app C)) ≫
        (S.sections (v ≫ f)).hom.app C =
      (S.sections v).hom.app ((integralComparisonDerivedSequencePullback l E f).obj C) ≫
        (S.comparison f v).hom.app C

/-- The Roos realization of a fixed strict germ diagram descends with the specified
factorizations and agrees with every normalized K-flat quotient presentation.
Source: Stacks 0941, 0F4F, 05V1; parent proof Steps 1, 4, 5, 7, 9 and 10
(blueprint: lem-trf-stalk-tower-descent).

Proof: take products of each strict tower map in both cone coordinates. Naturality
of transitions commutes with 1-shift; the chain equation commutes with the signed
cone differential. Exact products of modules preserve quasi-isomorphisms, as do
finite stalks and coefficient restriction. Thus the stalk Roos functor inverts
quasi-isomorphisms of system complexes. Localize it and its strict c and r maps;
the localization comparison gives factors, comparisonFactors and reparamFactors.
The strict reparametrization square and identity descend by uniqueness, giving
realizedReparam and realizedIdentity. The normalized Roos model and exact point
sections identify sections of the total limit with the section-tower cone.
The diagonal scalarRoosMap and e give sectionsFactors; localization of the strict
finiteSections equation gives sectionsComposition. Compose sections with the
specified pullback realization to define integral and integralNormalized.
The integral iteration equation is then proved in the parent using counit
naturality; it is not required here. For any simultaneous K-flat presentation,
the quotient comparison kappa induces z on stalk towers. Its section formula
identifies z with the finite stalk of kappa, including transitions. Apply the
normalization of the integral pullback model to that presentation. Point sections,
scalarRoosMap and z turn this equation into precisely the quotient-compatibility
equation. The bounded-quotient theorem makes these maps invertible on constructible
inputs through its common good-truncation zigzag, with no bound on K-flat terms.
Naturality for chain maps, inversion for quasi-isomorphisms and composition for
roofs prove all identities for arbitrary derived arrows and every representative.
Zero complexes, identity maps and the first quotient obey the same equations. -/
theorem trfStalkTowerDescent (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (I : IntegralComparisonSystem.{u} l)
    (hI : IntegralComparisonRealizationCoherence l E E (AlgHom.id ℚ_[l] E) I)
    (T : TrfStrictStalkTowerData l E D) (hT : TrfStrictStalkTowerCoherent l E D T) :
    ∃ S : TrfStalkCompositorTowerData l E D I,
      S.toStrict l E = T ∧ TrfStalkTowerDescentLaws l E D I S ∧
        TrfStalkCompositorQuotientCompatible l E D I S := by
  sorry

end WeilConjectures
