/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SixFunctorOperationDatum
public import WeilConjectures.AlgebraicGeometry.ExceptionalAdjointAdmissibility
public import WeilConjectures.SixFunctors.TensorHomTranspositionData
public import WeilConjectures.Algebra.Homology.RingedInternalHomShiftOfUniversesSupplement
public import WeilConjectures.AlgebraicGeometry.DerivedAutomorphismHomEvaluation
public import WeilConjectures.SixFunctors.TensorExchangePresentation
import WeilConjectures.SixFunctors.TensorExchangeNormalizedModels
import WeilConjectures.SixFunctors.TensorExchangeCoherentConclusions

/-! # Tensor-adjunction exchange

Source: latest blueprint, sec-six-functors/sk-thm-sf-package,
fix-lem-tensor-adjunction.proof.md (blueprint: fix-lem-tensor-adjunction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
namespace TensorAdjunctionExchange
open ConstructibleExceptionalCoefficients

/-- The tensor-adjunction exchange, natural in both variables, with finite reduction,
scalar extension and the signed first/second shift squares. The chosen normalized
System presents the operations of the six-functor datum on the actual finite-Tor
categories. Admissibility is retained at each stage, not silently discharged.

Source: blueprint main-20261015, sec-six-functors/sk-thm-sf-package,
fix-lem-tensor-adjunction (blueprint: fix-lem-tensor-adjunction).

Proof, following the nine DAG steps:
1. On each small ringed site apply lem-pur-rhom-global-sections and
   lem-weil-pbc-ringed-internal-hom-exact-restriction to get the tensor-Hom
   adjunction with evaluation as counit, naturally in all three inputs.
2. At integral coefficients use the actual completed tensor. Its quotient tower
   is the quotient tower of ordinary tensor by the K-flat balancing map
   (p tensor a) tensor (m tensor b) to (p tensor m) tensor ab. Use
   lem-weil-pbc-constant-completion-equivalence to identify its limit with Koszul
   completion and lem-weil-pbc-ringed-koszul-completion-reflector to map into the
   complete target. Compose this bijection with step 1.
3. Before Yoneda, check both representing objects at finite coefficients.
   fix-prop-adjunctions preserves the finite-Tor inputs. Choose finite dimension
   bounds by lem-kun-dimension-finite-type. Cover each scheme by finitely many
   affine opens, apply cor-weil-finite-constructible-hom on these separated charts,
   and glue finite constructible stratifications by disjoint refinement. The Tor
   interval is uniform on the cover. cor-sf-direct-image-ctf-proetale gives the
   finite-Tor direct image. Empty schemes give zero objects.
4. Use cor-coef-integral-internal-hom and the same finite bounds integrally.
   prop-weil-pbc-direct-image-limits preserves completeness and computes every
   reduction; the finite direct-image bounds are uniform. Then
   lem-coef-integral-residue-tor puts both objects in the integral finite-Tor category.
5. For every finite-Tor test object L form the five bijections: tensor-Hom,
   inverse projection, exceptional adjunction, tensor-Hom, ordinary adjunction.
   The intermediate pullback and tensor inputs lie in their proved domains by
   lem-sf-pullback-tor-amplitude, lem-sf-tensor-ctf and
   lem-pur-integral-operations-preserve-constructible. Use completed tensor in
   every integral occurrence. The projection realization is the actual proper
   counit/open projection paste, not a freely selected isomorphism.
6. Apply fully faithful Yoneda to the full finite-Tor category. The inverse
   component is h_B(1), explicitly inverseComponent above; the forward component
   is the inverse chain applied to 1_A. Naturality gives the two identity composites
   and naturality in the contravariant M and covariant N variables.
7. Transpose the two coefficient routes through the five bijections. Tensor and
   evaluation compatibility, the canonical q/b unit and counit equations, and
   projection compatibility identify the resulting maps. Use thm-coef-finite-hom
   and lem-coef-finite-direct-image for finite reductions, the arbitrary-first-input
   lem-coef-integral-hom-reduction for integral reduction, and
   lem-pur-integral-operations-scalar-extension for integral scalar extension.
   This proves Compatible for these actual morphisms, not just their endpoints.
8. Transpose the shift square by the same chain. Source shifting in Hom gives
   the negative shift and target shifting gives the positive shift, with the
   signed Hom-complex differential. The projection is a composite of tensor,
   open comparison, pullback composition and proper counit, so its shifted map
   is the same specified map. Completion is exact and its unit is natural;
   lem-weil-pbc-ringed-strict-tower-homotopy-limit gives the limit comparison.
   Uniqueness in step 6 proves both exchange shift squares.
9. Rationalization localizes the Hom groups and sends the inverse pair to an
   inverse pair. Over the algebraic closure choose a common finite coefficient
   field for the finitely many objects and morphisms; step 7 makes the result
   independent of a larger field. Composition, naturality and shift equations
   descend through the common-stage Hom colimit. These are the operations of
   def-weil-rationalization-karoubi and def-weil-algebraically-closed-coefficients.
No Verdier-exchange, biduality or downstream preservation theorem is used. -/
theorem tensor_adjunction
    (D : FiniteFieldDatum.{u}) (A : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic A.l) E]
    [FiniteDimensional (Padic A.l) E] (n : ℕ) (hn : 1 ≤ n)
    (six : SixFunctorOperationDatum D A E n hn)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    (S : System A.l A.Qbar D A.different (f := f.hom.left))
    (c : Compactification f.hom.left) :
    Package D A E n hn six f S c := by
  classical
  obtain ⟨p, hp⟩ := normalized_models D A E n hn six f S c
  obtain ⟨conclusion, ringShifts, naturality, ⟨coefficients⟩⟩ :=
    coherent_conclusions D A E n hn six f S c p hp
  let core : CorePackage A.l A.Qbar D A.different f.hom.left S c :=
    { stage := p.stage
      ring := p.ring
      projection := p.projection
      conclusion := conclusion
      ringShifts := fun L m h ↦ Classical.choice (ringShifts L m h)
      integralX := p.integralX
      integralY := p.integralY
      rationalX := p.rationalX
      rationalY := p.rationalY
      closedX := p.closedX
      closedY := p.closedY
      coefficientNaturality := naturality
      coefficients := coefficients }
  exact ⟨core, hp⟩

end TensorAdjunctionExchange
end WeilConjectures
