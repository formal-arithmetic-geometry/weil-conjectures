module

public import Sheaf.Paper.PurIntegralRepresentingPairData
import Sheaf.Paper.PurIntegralReductionUniformTor
import Sheaf.Paper.PurNormalizedReconstructionAdjunctionCalculus
import Sheaf.CategoryTheory.ExactDerivedCohomologyCoherence
import Sheaf.Paper.RoosIntrinsicCompletenessEquivalence

/-! # Coordinate representing families

Source: blueprint integral adjunction, coordinate Hom chain and actual counits.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry SheafOfModules
open WeilConjectures AlgebraicGeometry.Scheme
attribute [local instance 5000] AlgebraicGeometry.strictEtaleLevelDerived
  AlgebraicGeometry.strictEtaleSystemDerived
namespace WeilConjectures.PurIntegralRepresentingPair
open PurIntegralSupportComparison

variable (l : ℕ) [Fact l.Prime] (E : Type u) [NormedField E]
  [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
variable {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
  (S : StrictEtaleCompactSupport (integralExceptionalIntegers l E)
    (integralExceptionalUniformizer l E) c)
  (G : EtaleTowerBrownAdjunction S) (H : BrownTowerComparison.FiniteEvaluation S G)
  (D : BrownTowerComparison.TransportData S G H)

/-- The representing Hom chain in quotient coordinates, including normalized theta,
its finite counit equation and naturality on actual supplied system maps.
Source: current blueprint sk-prop-sp-integral-adjunction, Hom display and final
unit/counit paragraph (blueprint: lem-pur-coordinate-representing-family).

Proof: apply uniform integral reduction to the input and test objects to obtain the
finite Tor bounds and etale-origin witnesses. Transfer the supplied finite interval
through phi to bound the exceptional outputs. Apply Brown transport to these inputs.
In recognition mode (a) retain theta. In mode (b), exact conservative evaluations
detect concentration of both systems; the transition squares on H^r give an actual
strict-system isomorphism. Conjugate it by the H^r-normalized good truncations to
obtain theta and use full faithfulness of the shifted heart for common-degree squares.
Intrinsic completeness and normalized reconstruction invert the actual units and
counits. The support object is integral because supportPresentation identifies it
with rawSupport, which the integral model preserves. Compose reduction/limit Hom,
theta, Brown Hom, and the inverse reduction Hom map. These maps are linear and natural
and their composite is precisely transpose. Apply this formula to the identity and
use the adjunction triangles to obtain trace_reduction. Evaluate that equality and
paste the Brown finite counit normalization to obtain trace_evaluation. Naturality
of all four Hom maps gives the two family naturality equations. -/
theorem coordinateRepresentingFamily
    (p : ℕ) [Fact p.Prime] (_hpl : p ≠ l)
    (k : Type u) [Field k] [CharP k p]
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [f.IsOver (Spec (.of k))]
    (R : ∀ W : Scheme.{u}, CoefficientDerivedSystemCalculus l E W)
    (M : CompactSupportCondensedRealization.IntegralModel l E c R)
    (hD : BrownTowerComparison.Transport S G H D (finite := D.finite)) :
    Nonempty (Family l E (R X) (R Y) S G H D hD) := by
  sorry


end WeilConjectures.PurIntegralRepresentingPair
