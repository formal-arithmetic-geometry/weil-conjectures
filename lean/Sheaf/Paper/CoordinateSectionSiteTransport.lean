/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A9
-/
module

public import Sheaf.Paper.TwistedCoordinateSectionCartier

/-! Site transport of the coordinate normalization. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CoordinateSectionNormalization
open AffineLinePurity VectorIntegrationSite

/-- The supported Cartier realization is independent of the annihilating
exponent, and the normalized ordinary equations transport to the specified
pro-etale comparison and exceptional composition.

Source: current blueprint, sec-smooth-purity/sk-prop-an,
cor-pur-affine-space-zero-section-purity.proof.md, finite etale-origin transport;
lem-pur-twisted-coordinate-section-normalization, Steps 5--6 and 10.
(blueprint: lem-pur-coordinate-section-site-transport).

Proof: Apply cartier_kummer_map to the affine zero divisor. Uniqueness of the
ordinary relative boundary identifies its ordinary family with ordinaryClass.
The supported-constant quotient unit is epic, so its normalization makes all
source comparisons equal. The root projection condition fixes the target as
twistDerived. Applying Ext.hom with the exact-image/single and comparison/single
isomorphisms gives exactly cartierSource and the CartierRealization equation,
simultaneously for every annihilating exponent. Common larger exponents compare
all root maps with this same published Cartier arrow.
For each Tate input, finite twist pullback gives constructibility and finite Tor
amplitude, and its compared complex is bounded. The finite-origin comparison
unit is invertible on these ordinary objects and their exceptional values.
Transport the ordinary supported arrow and orientation using boundedSiteRho.
The vector-integration site comparison identifies the actual integration,
projection and transpose with gammaCoordinates. The closed counit transport
fixes the closed adjunction; closed-section compact origin fixes the section
source. Compact-support site coherence, conjugated under the adjunctions,
identifies exceptionalComposition with proComposition, including its inverse
middleUnit and final comparison counit. Apply comparison to the ordinary
exceptional identity and cancel these units and counits. This proves the literal
pro-etale identity and preserves the two isomorphy assertions. The unit input
is retained separately, while each Tate input uses its own bounded witness.
No divisibility by the ramification index or coefficient flatness is needed. -/
theorem coordinateSectionSiteTransport
    (P : WeilConjectures.PurityFiniteSetting.{u}) (T : Scheme.{u})
    (aT : T ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aT] [QuasiCompact aT] [IsSeparated aT] [IsNoetherian T]
    (hI : (sectionMap T).ker.IsInvertible) :
    CartierRealization T P aT hI ∧
    ∀ (b : ℕ) (hA : ((P.coefficients.l ^ (b + 1) : ℕ) : Ring P) = 0)
      (hT : IsUnit ((P.coefficients.l ^ (b + 1) : ℕ) : Γ(T, ⊤))),
      OrdinaryNormalization (Ring P) T (P.coefficients.l ^ (b + 1))
        (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) hA hT hI →
      CoprojectionNormalization (Ring P) T (P.coefficients.l ^ (b + 1))
        (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) hA hT hI →
      ProNormalization T P b hA aT hT hI := by sorry

end AlgebraicGeometry.ProEtale.CoordinateSectionNormalization
