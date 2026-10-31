/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Compact.CompactSupportCoefficientAction
public import WeilConjectures.SmoothPurity.Qcqs.QcqsCompactSupportRealization
public import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtensionUniverses
public import WeilConjectures.SixFunctors.FrobeniusExchange.SystemOperationExchangeRealization

import WeilConjectures.SmoothPurity.Compact.CompactSupportCoefficientExchangeInvertible
import WeilConjectures.SmoothPurity.Compact.CompactSupportFiniteScalarMateNormalization
import WeilConjectures.SmoothPurity.Compact.CompactSupportRationalScalarIso

/-! # Normalized compact-support comparisons for individual coefficient inclusions

Source: main-20261015, lem-weil-compact-support-finite-field-independence, first sentence;
lem-fix-operation-reduction, compact-support and final paragraphs
(blueprint: lem-weil-compact-support-normalized-scalar-isomorphisms).

## Main definitions and statements

- `sfCompactSupportScalarSystemMap`: the actual whole-system mate followed by its limit.
- `sfCompactSupportNormalizedScalarIsomorphisms`: integral and raw rational comparisons,
  with the mixed-unit mate and whole-system normalization for one inclusion.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
open GeneralAlgebraicallyClosedCoefficients
open AlgebraicallyClosedCoefficients (Coefficient coefficientInclusion)

variable (l : ℕ) [Fact l.Prime]
  (K₀ : Type u) [Field K₀] (hl : IsUnit (l : K₀))
  {X Y : Scheme.{u}} {f : X ⟶ Y}
  [X.Over (Spec (.of K₀))] [Y.Over (Spec (.of K₀))]
  [LocallyOfFiniteType (X ↘ Spec (.of K₀))] [QuasiCompact (X ↘ Spec (.of K₀))]
  [LocallyOfFiniteType (Y ↘ Spec (.of K₀))] [QuasiCompact (Y ↘ Spec (.of K₀))]
  [f.IsOver (Spec (.of K₀))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (c : Compactification f)

/-- Transport the given base-field unit through global sections to each residue field.
This is data obtained from the given unit, not an additional invertibility hypothesis.
Source: lem-weil-compact-support-finite-field-independence, coefficient convention
(blueprint: lem-weil-compact-support-normalized-scalar-isomorphisms). -/
@[instance_reducible] def sfCompactSupportScalarResidueUnit
    (W : Scheme.{u}) [W.Over (Spec (.of K₀))] (x : W) :
    Invertible (l : W.residueField x) :=
  let φ := ((Scheme.ΓSpecIso (.of K₀)).inv ≫
    (W ↘ Spec (.of K₀)).appTop ≫ W.Γevaluation x).hom
  (Eq.mp (congrArg IsUnit (map_natCast φ l)) (hl.map φ)).invertible

/-- Realize the specified proper/open scalar mate on whole strict systems, conjugated
by the projection-normalized identifications with the fixed integral functors.
The scalar realization uses the reduction counits and the normalized Roos limit;
no maps are chosen from degreewise comparisons.
Source: lem-fix-operation-reduction, compact-support and final paragraphs
(blueprint: lem-weil-compact-support-normalized-scalar-isomorphisms). -/
def sfCompactSupportScalarSystemMap
    (E L : Type u) [Field E] [Field L]
    [Algebra (Padic l) E] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (K : sfIntegralConstructibleCategory l E X) :
    (integralScalarExtension l E L ι Y).obj
        ((sfCompactSupportFiniteIntegralFunctor l K₀ hl c E).obj K).obj ⟶
      ((sfCompactSupportFiniteIntegralFunctor l K₀ hl c L).obj
        ((sfConstructibleIntegralScalarExtension 0 l
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι X).obj K)).obj :=
  letI : ∀ x : X, Invertible (l : X.residueField x) :=
    sfCompactSupportScalarResidueUnit l K₀ hl X
  letI : ∀ y : Y, Invertible (l : Y.residueField y) :=
    sfCompactSupportScalarResidueUnit l K₀ hl Y
  (integralScalarExtension l E L ι Y).map
      ((FrobeniusExchange.compactRealization l E K₀ hl f c).hom.app K) ≫
    (FrobeniusExchange.coefficientExchange l E L ι
      (FrobeniusExchange.systemDerivedOpen l E c.i ⋙ FrobeniusExchange.systemDirect l E c.g)
      (FrobeniusExchange.systemDerivedOpen l L c.i ⋙ FrobeniusExchange.systemDirect l L c.g)
      (FrobeniusExchange.systemCompactScalar l E L ι c)).app K ≫
    (FrobeniusExchange.compactRealization l L K₀ hl f c).inv.app
      ((sfConstructibleIntegralScalarExtension 0 l
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι X).obj K)

/-- Every individual finite-subextension inclusion has the normalized integral
compact-support scalar isomorphism, whose raw localization is a rational natural
isomorphism. The finite mate predicate asserts the Hom bijection for every derived
coefficient object, without boundedness, and identifies the reduction with its unique
mixed-unit lift. The middle conjunct retains the actual whole-system realization.
No associator coherence or common-stage independence is asserted here.
Source: main-20261015, lem-weil-compact-support-finite-field-independence, first sentence;
lem-fix-operation-reduction, compact-support and final paragraphs
(blueprint: lem-weil-compact-support-normalized-scalar-isomorphisms).

Proof (the six steps of the DAG):
1. Use lem-pur-coefficient-extension-reduction-model and the representative-normalized
adjunction lem-pur-sheaf-ring-derived-coefficient-adjunction. The mixed unit of
 def-weil-mixed-reduction-unit becomes the scalar unit. The diagonal Roos leg retains
its augmentation by lem-weil-strict-roos-comparison; its counit is the adjunct of the
projection by lem-coef-normalized-dvr-effectivity. Precompose with the inverse fixed
compact-support reduction. Adjunction gives the Hom bijection for every target Z.
2. Scalar extension preserves integral constructibility by
lem-weil-integral-scalar-extension-constructible. Choose an etale antecedent using
lem-weil-pbc-finite-ring-constructible-derived-origin; tensor/pullback compatibility
and det-pe-classical-sheaves-modules show its scalar extension is bounded. The schemes
of c are Noetherian by lem-weil-pbc-finite-type-over-noetherian. Apply
lem-finite-compact-support-scalar-transport. Its transpose is compact support of the
unit followed by lem-sf-compact-support-restriction-of-scalars. No quotient flatness
or injectivity is assumed.
3. Construct that proper/open mate in the derived category of strict ringed systems,
using lem-coef-semilinear-derived-sections and the fixed tower of
lem-weil-compact-support-reduction-tower-functor. Its evaluations are the preceding
finite mates. Joint conservativity proves invertibility of this actual system arrow.
4. Apply exact completed restriction and total derived limit to the system arrow.
The counits of def-weil-system-operation-exchange-realization identify both ends with
the fixed integral functors. Effectivity and lem-sf-integral-compact-support-constructible
give the required integral isomorphism. The strict Roos comparison and
lem-weil-proetale-countable-products-exact retain both cone coordinates and projections.
5. Naturality of the whole-system counit gives exactly the fixed reduction equation
of def-weil-compact-support-finite-action. Its transpose is the mixed-unit equation;
the Hom bijection proves uniqueness. These are equations of actual system maps.
6. Raw localization preserves inverse, composition and identity. Integral naturality
extends to every pure Hom tensor by scalar multiplication, then to all Hom tensors
by additivity, giving the rational natural isomorphism with the stated components. -/
theorem sfCompactSupportNormalizedScalarIsomorphisms
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (E L : Padic.FiniteCoefficientFields l Ω) (h : E ≤ L) :
    ∃ b : sfCompactSupportFiniteIntegralFunctor l K₀ hl c (Coefficient.{u} l Ω E) ⋙
        integralTransition l Ω Y E L h ≅
      integralTransition l Ω X E L h ⋙
        sfCompactSupportFiniteIntegralFunctor l K₀ hl c (Coefficient.{u} l Ω L),
      SfCompactSupportIntegralBetaSpec l K₀ hl c
        (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
        (coefficientInclusion l Ω E L h) b ∧
      (∀ K : sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) X,
        (b.hom.app K).hom = sfCompactSupportScalarSystemMap l K₀ hl c
          (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
          (coefficientInclusion l Ω E L h) K) ∧
      ∃ β : sfCompactSupportFiniteFunctor l K₀ hl c (Coefficient.{u} l Ω E) ⋙
          transition l Ω Y E L h ≅
        transition l Ω X E L h ⋙
          sfCompactSupportFiniteFunctor l K₀ hl c (Coefficient.{u} l Ω L),
        ∀ K : Stage l Ω X E, HEq (β.hom.app K)
          ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω L) Y).map
            (b.hom.app K.obj)) := by
  let : ∀ x : X, Invertible (l : X.residueField x) :=
    sfCompactSupportScalarResidueUnit l K₀ hl X
  let : ∀ y : Y, Invertible (l : Y.residueField y) :=
    sfCompactSupportScalarResidueUnit l K₀ hl Y
  let A := Coefficient.{u} l Ω E
  let B := Coefficient.{u} l Ω L
  let ι := coefficientInclusion l Ω E L h
  let F := sfCompactSupportFiniteIntegralFunctor l K₀ hl c A ⋙ integralTransition l Ω Y E L h
  let G := integralTransition l Ω X E L h ⋙ sfCompactSupportFiniteIntegralFunctor l K₀ hl c B
  let t : F ⋙ (sfIntegralConstructible l B Y).ι ⟶
      G ⋙ (sfIntegralConstructible l B Y).ι :=
    Functor.whiskerRight (FrobeniusExchange.compactRealization l A K₀ hl f c).hom
        (integralScalarExtension l A B ι Y) ≫
      FrobeniusExchange.coefficientExchange l A B ι
        (FrobeniusExchange.systemDerivedOpen l A c.i ⋙ FrobeniusExchange.systemDirect l A c.g)
        (FrobeniusExchange.systemDerivedOpen l B c.i ⋙ FrobeniusExchange.systemDirect l B c.g)
        (FrobeniusExchange.systemCompactScalar l A B ι c) ≫
      Functor.whiskerLeft (integralTransition l Ω X E L h)
        (FrobeniusExchange.compactRealization l B K₀ hl f c).inv
  let τ : F ⟶ G :=
    { app K := ObjectProperty.homMk (t.app K)
      naturality K M a := by
        apply ObjectProperty.hom_ext
        exact t.naturality a }
  have hi (K : sfIntegralConstructibleCategory l A X) : IsIso (t.app K) := by
    let := sfCompactSupportCoefficientExchange_isIso l K₀ hl c A B ι K
    dsimp only [t, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
    infer_instance
  let (K : sfIntegralConstructibleCategory l A X) : IsIso (τ.app K) :=
    (ObjectProperty.isIso_hom_iff (τ.app K)).mp (hi K)
  let : IsIso τ := NatIso.isIso_of_isIso_app τ
  let b : F ≅ G := asIso τ
  have hb (K : sfIntegralConstructibleCategory l A X) :
      (b.hom.app K).hom = sfCompactSupportScalarSystemMap l K₀ hl c A B ι K := by
    rfl
  refine ⟨b, ?_, hb, ?_⟩
  · apply sfCompactSupportFiniteScalarMateNormalization l K₀ hl c A B ι b
    exact hb
  · exact sfCompactSupportRationalScalarIso l K₀ hl c Ω E L h b

end WeilConjectures
