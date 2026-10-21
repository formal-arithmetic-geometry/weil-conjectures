/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NM
-/
module

public import Sheaf.Topology.ContinuousMapCondensedRing
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
import Sheaf.Topology.FiniteQuotientFiberProduct
import Sheaf.NumberTheory.Padics.IntegersProfiniteTower

/-!
# Continuous Cech exactness with finite p-adic field coefficients

Source: Bhatt–Scholze, The pro-etale topology for schemes, Lemma 4.3.9(2)–(4), p. 33,
with trivial group, expanded by the DAG into an explicit continuous-function assertion
(blueprint: lem-sfb-normed-scalar-profinite-cech-exact).

The equations below are the pointwise alternating differentials on continuous cochains.
The coefficient topology is the spectral norm topology, with no local constancy condition.
-/

@[expose] public section

universe u v

namespace Profinite

/-- Equal-image tuples in the Cech nerve, with the subtype topology of the finite product.
Source: Bhatt–Scholze, Lemma 4.3.9(2)–(4), explicit Cech expansion in the DAG
(blueprint: lem-sfb-normed-scalar-profinite-cech-exact). -/
abbrev scalarCechTuples {S T : Profinite.{v}} (q : C(T, S)) (r : ℕ) :=
  {t : Fin r → T // ∀ i j : Fin r, q (t i) = q (t j)}

/-- Delete coordinate `j`, retaining the equal-image condition.
Source: Bhatt–Scholze, Lemma 4.3.9(2)–(4), explicit Cech expansion in the DAG
(blueprint: lem-sfb-normed-scalar-profinite-cech-exact). -/
def scalarCechDelete {S T : Profinite.{v}} (q : C(T, S)) (r : ℕ) (j : Fin (r + 1))
    (x : scalarCechTuples q (r + 1)) : scalarCechTuples q r :=
  ⟨fun i ↦ x.val (j.succAbove i), fun i k ↦ x.property (j.succAbove i) (j.succAbove k)⟩

/-- Every positive-degree continuous Cech cocycle with finite p-adic field coefficients
is a continuous coboundary. The degree is `n + 1`, so `n = 0` includes degree one.

Source: Bhatt–Scholze, Lemma 4.3.9(2)–(4), p. 33, and its explicit Cech expansion
(blueprint: lem-sfb-normed-scalar-profinite-cech-exact).

Proof: (1) Iterate lem-sfb-finite-quotient-fiber-product to obtain profiniteness of all
finite fibre powers. Coordinate deletions are continuous and the two orders of deleting
coordinates cancel with opposite signs, giving d squared zero. If both spaces are empty,
all cochains vanish. (2) By lem-sfb-finite-valued-cech-cocycle-descent, a finite discrete
coefficient cocycle descends, including its cocycle equation, to a finite surjection.
Choose a section of that finite surjection and insert it as the first coordinate.
The cocycle equation on the resulting tuple says this gives a primitive; pull it back.
(3) Use def-weil-l-adic-coefficient-extension, lem-weil-l-adic-extension-integers-dvr,
lem-weil-valued-dvr-finite-quotients and lem-sfb-integers-profinite-tower: the integers
are the topological inverse limit of their finite uniformizer-power quotients, whose
transition maps are surjective. (4) For an integral cocycle, first solve modulo the
uniformizer. (5) Lift a primitive at one level by a set section of the next finite
quotient map; the difference between its boundary and the next cocycle lies in the
finite kernel and is a cocycle. (6) Apply the finite-coefficient result to this kernel
cocycle and subtract its primitive. This corrects the lift while preserving its
reduction. Induction gives compatible primitives, also in degree one.
(7) Reconstruct the integral primitive by the inverse-limit homeomorphism. Its boundary
is the given cocycle because they agree in every finite quotient. (8) Compactness bounds
the image of an E-valued cocycle, so multiplication by a single uniformizer power makes
it integral. Solve there and divide the primitive by that same scalar. All constructed
cochains are continuous; none is required to be locally constant. -/
theorem normedScalarProfiniteCech_exact (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (S T : Profinite.{v}) (q : C(T, S)) (hq : Function.Surjective q) (n : ℕ)
    (f : @ContinuousMap (scalarCechTuples q (n + 2)) E inferInstance
      (spectralNorm.normedField (Padic l) E).toUniformSpace.toTopologicalSpace)
    (hf : ∀ x : scalarCechTuples q (n + 3),
      ∑ j : Fin (n + 3), (-1 : E) ^ j.val * f (scalarCechDelete q (n + 2) j x) = 0) :
    ∃ g : @ContinuousMap (scalarCechTuples q (n + 1)) E inferInstance
        (spectralNorm.normedField (Padic l) E).toUniformSpace.toTopologicalSpace,
      ∀ x : scalarCechTuples q (n + 2),
        ∑ j : Fin (n + 2), (-1 : E) ^ j.val * g (scalarCechDelete q (n + 1) j x) = f x := by
  sorry

end Profinite
