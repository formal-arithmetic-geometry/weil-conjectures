/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q107
-/
module

public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.NumberTheory.Padics.IntegersProfiniteTower
public import Sheaf.Topology.ProfiniteCondensedRing
public import Sheaf.Topology.ProfiniteSectionsFiniteQuotient
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Topology.Algebra.Ring.Basic
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Mathlib.LinearAlgebra.FreeModule.PID

/-!
# Finite integral coefficients have a condensed finite free resolution

Source: blueprint main-20261015, scalar-six direct-image proof, paragraph
"Finite free and finitely presented coefficient extensions", second bullet
(blueprint: lem-sfb-finite-integral-condensed-resolution).

The conclusion is packaged transparently so that the arithmetic theorem can install the
recorded valuation topology and the discrete topology explicitly. The two free condensed
modules are the continuous-section modules of the coordinate modules O^r. The component
formulas specify their arrows by postcomposition, rather than by arbitrary exact arrows.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace Padic

/-- The conclusion of the finite integral condensed resolution assertion, with specified
coefficient topologies and scalar homomorphism. The free module is presented in coordinates:
its sections over S are C(S,O^r), naturally the finite direct sum of r copies of C(S,O).
The pointwise scalar action is the recorded restriction of the regular module.

Source: blueprint scalar-six direct-image proof, finite coefficients bullet
(blueprint: lem-sfb-finite-integral-condensed-resolution). -/
def FiniteIntegralCondensedResolution
    (O A : Type u) [CommRing O] [CommRing A]
    [TopologicalSpace O] [TopologicalSpace A] [IsTopologicalRing O] [IsTopologicalRing A]
    (a : O →+* A) (ha : Continuous a) : Prop :=
  letI := a.toAlgebra
  letI := continuousSMul_of_algebraMap O A ha
  letI : HasFiniteBiproducts
      (Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
        (Profinite.continuousCoefficientRingObj O)) := .of_hasFiniteProducts
  ∃ (r : ℕ) (q : (Fin r → O) →L[O] A) (φ : (Fin r → O) →L[O] (Fin r → O)),
    Function.Surjective q ∧ Function.Injective φ ∧
    Function.Exact φ q ∧
    (∃ M : Matrix (Fin r) (Fin r) O, ∀ x : Fin r → O, φ x = M.mulVec x) ∧
    (∃ e : (Fin r → O) ≃ₜ LinearMap.ker q.toLinearMap,
      ∀ x : Fin r → O, (e x).val = φ x) ∧
    (∀ S : Profinite.{u},
      Function.Injective (ContinuousLinearMap.compLeftContinuous O S φ) ∧
      Function.Exact (ContinuousLinearMap.compLeftContinuous O S φ)
        (ContinuousLinearMap.compLeftContinuous O S q) ∧
      Function.Surjective (ContinuousLinearMap.compLeftContinuous O S q)) ∧
    Nonempty (Profinite.continuousSectionsModule O (Fin r → O) ≅
      biproduct (fun _i : Fin r ↦ Mod.regular (Profinite.continuousCoefficientRingObj O))) ∧
    (∃ (F : Profinite.continuousSectionsModule O (Fin r → O) ⟶
          Profinite.continuousSectionsModule O (Fin r → O))
       (G : Profinite.continuousSectionsModule O (Fin r → O) ⟶
          Profinite.continuousSectionsModule O A)
       (h : F ≫ G = 0),
      (∀ (S : Profinite.{u}) (f : ULift.{u + 1} C(S, Fin r → O)) (s : S),
        ((F.hom.hom.app (op S)) f).down s = φ (f.down s)) ∧
      (∀ (S : Profinite.{u}) (f : ULift.{u + 1} C(S, Fin r → O)) (s : S),
        ((G.hom.hom.app (op S)) f).down s = q (f.down s)) ∧
      (ShortComplex.mk F G h).ShortExact)

/-- The recorded integer-ring topology is a topological ring structure. This is only the
existing subring topological-ring instance for the spectral norm, with its topology exposed.

Source: blueprint scalar-six direct-image proof, valuation topology on O_E
(blueprint: lem-sfb-finite-integral-condensed-resolution). -/
noncomputable abbrev finiteIntegralIntegersTopologicalRing
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] :
    @IsTopologicalRing (coefficientExtensionIntegers l E)
      (coefficientExtensionIntegersTopology l E) inferInstance := by
  let := spectralNorm.normedField (Padic l) E
  exact inferInstanceAs (IsTopologicalRing (coefficientExtensionIntegers l E))

/-- Finite discrete integral coefficient algebras have a two-term finite free resolution
that is exact on continuous functions from every profinite set and as condensed modules.

Source: blueprint main-20261015, scalar-six direct-image proof, paragraph
"Finite free and finitely presented coefficient extensions", second bullet
(blueprint: lem-sfb-finite-integral-condensed-resolution).

Proof plan:
1. If A is the zero ring, take r=0 and the unique maps. This also works for empty S.
2. Otherwise enumerate A and define q(x)=sum_i a(x_i)b_i. The coordinate vectors show
   surjectivity. Finite sums of continuous maps show continuity. Give K=ker q its
   subspace topology.
3. N! annihilates every element of the additive group of A, where N=|A|. Its image c
   in O is nonzero because O lies in the characteristic-zero field E. Hence c O^r ≤ K.
4. By lem-weil-l-adic-extension-integers-dvr, O is a domain and PID. Apply
   lem-sc-dvr-saturation-line-smith-normal-form to K ≤ O^r to obtain ambient basis u_i
   and kernel basis v_i=d_i u_i with distinct ambient indices and nonzero d_i.
5. There are r kernel basis vectors: otherwise c times an unused ambient basis vector
   belongs to K, contradicting its nonzero coordinate. Let φ have columns v_i.
   It is injective with image K, is a matrix over O, and is continuous.
6. The ambient basis change and its inverse are continuous matrices. On K the inverse
   of φ has coordinates (P⁻¹ y)_i/d_i in E, with values in O. Division by each fixed
   nonzero d_i is continuous. The subspace and product topologies make this inverse
   continuous, giving the required homeomorphism onto K.
7. On C(S,-), injectivity is pointwise. A section killed by q factors continuously
   through K; compose with the inverse in step 6 to obtain its unique preimage.
8. Choose a preimage in O^r for each element of A. A continuous S→A has finite clopen
   fibres; taking the chosen constant preimage on each fibre gives a continuous lift.
9. Coordinate projections and assembly identify C(S,O^r) with C(S,O)^r, naturally in S
   and linearly over C(S,O). The coordinate inclusions and projections make these the
   finite direct sums of the regular condensed O-module. The target is the recorded
   continuous A-valued coefficient sheaf with the action through a.
10. Postcomposition commutes with restrictions and scalar actions, giving F and G.
    Step 7 gives the kernel universal property sectionwise. For a map killing F,
    factor through G by choosing lifts as in step 8; differences are in the image of F,
    so the factor is well defined, linear and natural. Sectionwise surjectivity gives
    uniqueness. Thus the condensed sequence is short exact.
-/
theorem finite_integral_condensed_resolution
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (A : Type u) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A]
    (a : coefficientExtensionIntegers l E →+* A)
    (ha : @Continuous _ _ (coefficientExtensionIntegersTopology l E) inferInstance a) :
    @FiniteIntegralCondensedResolution (coefficientExtensionIntegers l E) A
      inferInstance inferInstance (coefficientExtensionIntegersTopology l E) inferInstance
      (finiteIntegralIntegersTopologicalRing l E) inferInstance a ha := by
  sorry

end Padic
