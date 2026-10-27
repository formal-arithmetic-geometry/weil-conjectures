/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K7
-/
module

public import Sheaf.AlgebraicGeometry.NodalLocalTangentGrading
public import Sheaf.RingTheory.QuadraticSeriesIntegralClosure
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.KrullDimension.Basic

/-!
# Intrinsic tangent comparison from a nondegenerate quadratic completion

Source: Stacks Project, curves.tex, Tag 0CBT, constructions (2) and (3),
using the explicit quadratic calculation in Tag 0C4A.
(blueprint: lem-sfb-nodal-quadratic-tangent-comparison).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.NodalLocal

/-- The local algebra comparison, independent of scheme normalization or geometric lifts.

Source: Stacks Project, curves.tex, Tags 0C4A and 0CBT, constructions (2) and (3).
(blueprint: lem-sfb-nodal-quadratic-tangent-comparison).

Proof:
Choose coordinates with nonzero X² coefficient: one of q(1,0), q(0,1), q(1,1)
works, also in characteristic two. Normalization/completion for the reduced algebraic
curve and the quadratic-series integral-closure calculation identify the completed
normalization with L[[t]], where L = F[Z]/(aZ²+bZ+c), X = zt, Y = t, and the completed
local ring is F+tL[[t]]. The nth positive power of its maximal ideal is t^n L[[t]].
Completion modulo powers preserves the original quotients, hence the associated graded
ring is F in degree zero and L t^n in each positive degree. Lift t in degree one to f
in the original maximal ideal. Its completed image is t(1+th). Every homogeneous prime
containing t contains the irrelevant ideal, since products of two positive homogeneous
elements belong to (t). Thus the whole Proj is D_+(in(f)), with chart ring L.
Faithful flatness of completion, applied to B and B/fB, descends regularity of f and
mB=fB from the completed normalization. For every allowed denominator g define the
chart map in_n(a)/in(g)^n ↦ a/g^n modulo mB. Regularity gives uniqueness of the division;
changing a by m^(n+1) or changing a representative of a homogeneous fraction does not
change the residue. Common denominators prove the ring identities. Tensor reduction
identifies B/mB with L, and the map is the identity in the displayed chart, so it is
an isomorphism over F. Two allowed denominators differ by a unit of B, so the chart
formulas agree; they also prove uniqueness and compatibility with pointed local-ring
isomorphisms, including the formulas on graded classes and on integral closures.
The separable quadratic L has basis 1,z. A root gives two distinct roots and interpolation
identifies L with F×F; with no root the quadratic is irreducible and L is a separable
field of degree two. This proves the final alternative without assuming a split node.
-/
theorem quadratic_tangent_comparison
    (k A : Type u) [Field k] [CommRing A] [Algebra k A]
    [IsLocalRing A] [_root_.IsReduced A] [IsNoetherianRing A] [Algebra.EssFiniteType k A]
    (hdim : ringKrullDim A = (1 : WithBot ℕ∞))
    (hquad : ∃ a b c : IsLocalRing.ResidueField A, b ^ 2 - 4 * a * c ≠ 0 ∧
      Nonempty (AdicCompletion (IsLocalRing.maximalIdeal A) A ≃+*
        QuadraticSeries.CurveRing a b c)) :
    letI := canonicalGrading A
    ∃ i : Proj (tangentGrading A) ≅ Spec (.of (ResidueAlgebra A)),
      IsNormalized A i ∧
      (∃ (f : A) (hf : f ∈ IsLocalRing.maximalIdeal A),
        initialForm A 1 ⟨f, by simpa using hf⟩ ∈ tangentGrading A 1 ∧
        algebraMap A (Normalization A) f ∈ nonZeroDivisors (Normalization A) ∧
        normalizationIdeal A = Ideal.span {algebraMap A (Normalization A) f} ∧
        Proj.basicOpen (tangentGrading A)
          (initialForm A 1 ⟨f, by simpa using hf⟩) = ⊤) ∧
      (Nonempty (ResidueAlgebra A ≃ₐ[IsLocalRing.ResidueField A]
          (IsLocalRing.ResidueField A × IsLocalRing.ResidueField A)) ∨
        (IsField (ResidueAlgebra A) ∧
          Algebra.IsSeparable (IsLocalRing.ResidueField A) (ResidueAlgebra A) ∧
          Module.finrank (IsLocalRing.ResidueField A) (ResidueAlgebra A) = 2)) ∧
      IsNaturalIso A i := by sorry

end AlgebraicGeometry.NodalLocal
