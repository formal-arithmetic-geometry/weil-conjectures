/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CondensedRefinementReductionSquare
public import WeilConjectures.SixFunctors.ProjectionRefinementDescent

/-! # Native condensed projection transport across compactifications

Source: literature/blueprint/latest/blueprint/sec-six-functors/sk-rem-sf-pf-done/
fix-prop-projection-formula.proof.md, finite geometric-fiber, refinement and reduction
paragraphs (blueprint: lem-sf-finite-projection-compactification-transport).

The index `n` denotes the positive exponent `n + 1`, so zero includes A_1.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option linter.style.setOption false

universe u

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.ProEtale.CondensedRing.CompactificationReindexing
open AlgebraicGeometry.ProEtale.CondensedRing.CondensedOpenProper

namespace WeilConjectures

/-- Type of the native comparison family at one positive finite coefficient level.
This only abbreviates the endpoints of the comparison, using the recorded functors.
Source: fix-prop-projection-formula.proof.md, common-refinement paragraph
(blueprint: lem-sf-finite-projection-compactification-transport). -/
abbrev FiniteProjectionTransportFamily (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (n : ℕ) {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  ∀ c d : Compactification f,
    (constantModelBoundedConstructible (IntegralQuotient.finite l E n) X).ι ⋙
        F (IntegralQuotient.finite l E n) c ≅
      (constantModelBoundedConstructible (IntegralQuotient.finite l E n) X).ι ⋙
        F (IntegralQuotient.finite l E n) d

/-- The specified quotient coefficient map, using the recorded finite ring homomorphism.
Source: fix-prop-projection-formula.proof.md, finite-reduction paragraph
(blueprint: lem-sf-finite-projection-compactification-transport). -/
abbrev finiteProjectionReductionMap (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (n m : ℕ) (hmn : m ≤ n) :=
  CommMon.homMk
    (A := CommMon.mk (IntegralQuotient.finite l E n))
    (B := CommMon.mk (IntegralQuotient.finite l E m))
    (Mon.Hom.mk (IntegralQuotient.finiteMap l E n m hmn))

/-- The scalar comparison at a fixed compactification, used as `sigma` in reduction.
Source: fix-prop-projection-formula.proof.md, finite-reduction paragraph
(blueprint: lem-sf-finite-projection-compactification-transport). -/
abbrev finiteProjectionSigma (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (n m : ℕ) (hmn : m ≤ n) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) :=
  scalarCompactSupportMap (finiteProjectionReductionMap l E n m hmn) c.i c.g

/-- Normalization, identity, cocycle and projection equation for a single comparison
family. Normalization is imposed for every common refinement, so it specifies the
inverse-second-leg times first-leg comparison without choosing an arbitrary map.
Source: fix-prop-projection-formula.proof.md, refinement paragraph
(blueprint: lem-sf-finite-projection-compactification-transport). -/
def FiniteProjectionTransportLaws (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (n : ℕ) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (rho : FiniteProjectionTransportFamily l E n f) : Prop :=
  (∀ (c d b : Compactification f) (r : b.Refinement c) (s : b.Refinement d)
    (K : ConstantModelBoundedConstructible (IntegralQuotient.finite l E n) X),
    (rho c d).hom.app K ≫ (refinement (IntegralQuotient.finite l E n) s).app K.obj =
      (refinement (IntegralQuotient.finite l E n) r).app K.obj) ∧
  (∀ c : Compactification f, rho c c = Iso.refl _) ∧
  (∀ c d b : Compactification f, rho c d ≪≫ rho d b = rho c b) ∧
  (∀ (P : Pasting (IntegralQuotient.finite l E n))
      (c d : Compactification f) (r : c.Refinement d),
    normalizedGammaRefinement (IntegralQuotient.finite l E n) r P =
      refinement (IntegralQuotient.finite l E n) r) ∧
  ∀ (K : ConstantModelBoundedConstructible (IntegralQuotient.finite l E n) X)
    (L : ConstantModelConstructibleFiniteTor (IntegralQuotient.finite l E n) Y),
    ∃ hT : constantModelBoundedConstructible (IntegralQuotient.finite l E n) X
        (K.obj ⊗ (CompactificationReindexing.P (IntegralQuotient.finite l E n) f).obj L.obj),
      ∀ c d : Compactification f,
        pf (IntegralQuotient.finite l E n) c K.obj L.obj ≫
            (rho c d).hom.app
              ⟨K.obj ⊗ (CompactificationReindexing.P
                (IntegralQuotient.finite l E n) f).obj L.obj, hT⟩ =
          ((rho c d).hom.app K ⊗ₘ 𝟙 L.obj) ≫
            pf (IntegralQuotient.finite l E n) d K.obj L.obj

/-- Native finite coefficient projection transport, including reduction of comparisons
and the projection equation at the reduced level. Both positive exponents are indexed
by predecessor naturals; in particular n = 0 and m = 0 are included.

Source: literature/blueprint/latest/blueprint/sec-six-functors/sk-rem-sf-pf-done/
fix-prop-projection-formula.proof.md, finite geometric-fiber and reduction paragraphs
(blueprint: lem-sf-finite-projection-compactification-transport).

Proof steps:
1. At A_(n+1), use the ordinary uncompleted operations and the finite geometric-fiber
projection theorem. Etale-origin descent and finite-Tor comparison give exactly the
bounded-constructible K and finite-Tor L domain, including tensor closure.
2. Choose a common refinement. The condensed refinement-counit identification equates
the clopen/native refinement map with the normalized proper/open map whose inverse is
theta in finite_descent. Thus finite_descent gives invertibility and the common-refinement
normalization, identity and cocycle laws for the native family. Apply the two refinement
projection equations and cancel only the invertible compactification maps to obtain the
projection equation. No projection map is inverted.
3. Scalar reduction preserves the finite-Tor constructible domain. Apply the focused
scalar/refinement square to both common-refinement legs, identifying their maps by
condensed_refinement_counit_identification. Cancel the second refinement isomorphism to
get sigma_d red(rho_N) = rho_M sigma_c. This cancels no sigma. Apply finite descent
directly at A_(m+1) to the reduced K and L to obtain the final projection equation. For
equal levels use scalar unit identifications; identity refinements and empty schemes are
covered by the same normalization. Reduction of arbitrary bounded constructible K is
never asserted bounded. -/
theorem finite_projection_compactification_transport
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra ℚ_[C.l] E] [FiniteDimensional ℚ_[C.l] E]
    (n : ℕ)
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    ∃ rhoN : FiniteProjectionTransportFamily C.l E n f,
      FiniteProjectionTransportLaws C.l E n f rhoN ∧
      ∀ (m : ℕ) (hmn : m ≤ n),
        ∃ rhoM : FiniteProjectionTransportFamily C.l E m f,
          FiniteProjectionTransportLaws C.l E m f rhoM ∧
          (∀ T : ConstantModelConstructibleFiniteTor (IntegralQuotient.finite C.l E n) X,
            ∃ hT : constantModelBoundedConstructible (IntegralQuotient.finite C.l E m) X
                ((scalarSixChange (finiteProjectionReductionMap C.l E n m hmn) X).obj T.obj) ∧
                DerivedCategory.finiteTorAmplitude _
                  ((scalarSixChange (finiteProjectionReductionMap C.l E n m hmn) X).obj T.obj),
              ∀ c d : Compactification f,
                (scalarSixChange (finiteProjectionReductionMap C.l E n m hmn) Y).map
                    ((rhoN c d).hom.app ⟨T.obj, T.property.1⟩) ≫
                  (finiteProjectionSigma C.l E n m hmn d).app T.obj =
                (finiteProjectionSigma C.l E n m hmn c).app T.obj ≫
                  (rhoM c d).hom.app
                    ⟨(scalarSixChange (finiteProjectionReductionMap C.l E n m hmn) X).obj
                      T.obj, hT.1⟩) ∧
          (∀ (K : ConstantModelConstructibleFiniteTor (IntegralQuotient.finite C.l E n) X)
            (L : ConstantModelConstructibleFiniteTor (IntegralQuotient.finite C.l E n) Y),
            ∃ (hK : constantModelBoundedConstructible (IntegralQuotient.finite C.l E m) X
                ((scalarSixChange (finiteProjectionReductionMap C.l E n m hmn) X).obj K.obj) ∧
                DerivedCategory.finiteTorAmplitude _
                  ((scalarSixChange (finiteProjectionReductionMap C.l E n m hmn) X).obj K.obj))
              (hL : constantModelBoundedConstructible (IntegralQuotient.finite C.l E m) Y
                ((scalarSixChange (finiteProjectionReductionMap C.l E n m hmn) Y).obj L.obj) ∧
                DerivedCategory.finiteTorAmplitude _
                  ((scalarSixChange (finiteProjectionReductionMap C.l E n m hmn) Y).obj L.obj))
              (hT : constantModelBoundedConstructible (IntegralQuotient.finite C.l E m) X
                ((scalarSixChange (finiteProjectionReductionMap C.l E n m hmn) X).obj K.obj ⊗
                  (CompactificationReindexing.P (IntegralQuotient.finite C.l E m) f).obj
                    ((scalarSixChange (finiteProjectionReductionMap C.l E n m hmn) Y).obj
                      L.obj))),
              ∀ c d : Compactification f,
                pf (IntegralQuotient.finite C.l E m) c
                    ((scalarSixChange (finiteProjectionReductionMap C.l E n m hmn) X).obj
                      K.obj)
                    ((scalarSixChange (finiteProjectionReductionMap C.l E n m hmn) Y).obj
                      L.obj) ≫
                  (rhoM c d).hom.app
                    ⟨(scalarSixChange (finiteProjectionReductionMap C.l E n m hmn) X).obj
                        K.obj ⊗ (CompactificationReindexing.P
                          (IntegralQuotient.finite C.l E m) f).obj
                          ((scalarSixChange (finiteProjectionReductionMap C.l E n m hmn) Y).obj
                            L.obj), hT⟩ =
                ((rhoM c d).hom.app
                    ⟨(scalarSixChange (finiteProjectionReductionMap C.l E n m hmn) X).obj
                      K.obj, hK.1⟩ ⊗ₘ
                    𝟙 ((scalarSixChange (finiteProjectionReductionMap C.l E n m hmn) Y).obj
                      L.obj)) ≫
                  pf (IntegralQuotient.finite C.l E m) d
                    ((scalarSixChange (finiteProjectionReductionMap C.l E n m hmn) X).obj
                      K.obj)
                    ((scalarSixChange (finiteProjectionReductionMap C.l E n m hmn) Y).obj
                      L.obj)) := by
  sorry

end WeilConjectures
