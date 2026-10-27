/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q14
-/
module

public import Sheaf.SixFunctors.FrobeniusPointTransport
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.Paper.SfDerivedComplete
public import Sheaf.Paper.AdicCoefficientDatum
public import Sheaf.Paper.IntegralPointTransportTowerData
public import Sheaf.Paper.PointTransportTowerRealizationSpec
import all Sheaf.Paper.PointTransportTowerRealizationAssembly

/-!
# Integral point transport as the realization of the finite transports

Source: Weil blueprint, main-20261015, sec-trace-formula/sk-d-weil,
prop-trf-rational-frobenius-integral-model.proof.md, clause (3)
(blueprint: lem-trf-integral-point-transport-tower-realization).

All towers below are strict towers of complexes over the single integral coefficient
ring. The index n denotes exponent n+1. The existential comparisons are normalized
on both cone components, so the assertion fixes the specified derived morphism.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option synthInstance.maxSize 2048

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale

namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The finite transports form a strict tower morphism; its specified cone realization
is the actual integral point transport, naturally in the derived object.

Source: blueprint main-20261015, prop-trf-rational-frobenius-integral-model.proof.md,
clause (3) (blueprint: lem-trf-integral-point-transport-tower-realization).

Proof:
1. The all-complex strict quotient laws assemble the existing finite maps into a
   natural strict tower map, with exactly the required section formula.
2. The source augmentation is the existing zero-homotopy lift of the actual quotient
   units. Unit naturality and joint cone-coordinate extensionality prove naturality.
   Its first coordinate is 1 tensor x and its entire shifted coordinate is zero.
3. Exact sections preserve the products and biproduct defining the Roos cone. Whisker
   the normalized sectionwise comparison by the actual pullback tower to obtain beta;
   its two projection equations give the asserted normalization.
4. The actual-quotient augmentation completeness lemma makes alpha invertible on
   integral constructible good representatives. No new resolution is chosen here.
5. The strict augmentation square on a good representative supplies the hypothesis
   of the existing normalized identity for the specified integral transport. Expanding
   its target comparison gives the displayed derived realization equality, including
   both cone coordinates. The existing derived natural transformation gives naturality.
6. The complete seven-property statement is stored in the named specification.
   Its equivalence to the original expanded formula is proved in the specification
   module. This theorem applies the fully proved private assembly directly.
   No hypothesis or coordinate condition is changed. -/
theorem integralPointTransportTowerRealization (hl : l ≠ D.p) :
    pointTransportTowerRealizationSpec D l E hl := by
  exact canonicalPointTransportTowerRealization D l E hl

end WeilConjectures
