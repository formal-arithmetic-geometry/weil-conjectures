/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NS
-/
module

public import Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback
public import Sheaf.AlgebraicGeometry.RegularImmersionClassCalculus
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Topology.Separation.Basic
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.Topology.Sober
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.AlgebraicGeometry.Curve.SeparablyClosedAlgebraicClosure
import Sheaf.AlgebraicGeometry.RegularNormalDecomposition
import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
import WeilConjectures.AlgebraicGeometry.ReductionUniversalHomeomorphism
import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
import Sheaf.AlgebraicGeometry.UniversalHomeomorphismInvariance
import Sheaf.AlgebraicGeometry.SecondKummerDivisors
import Sheaf.AlgebraicGeometry.Curve.DegreeNormalizedTrace
import WeilConjectures.FieldTheory.PurelyInseparablePthRootTower
import Sheaf.AlgebraicGeometry.ReducedAlgebraicNormalizationFieldChange

/-!
# Trace on a regular proper curve over a separably closed field

Source: ILO, Exposé XVII, proof of Proposition 3.4.1.3, printed pp.271--272
(blueprint: lem-per-sepclosed-regular-proper-curve-trace).

Ordinary cohomology is written as Ext from the constant coefficient sheaf.
Enlarging support is precomposition with the actual constant-sheaf unit.
The coefficient universe lift is the one already used by the regular Gysin classes.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Abelian

namespace AlgebraicGeometry.Etale

/-- Closedness gives the canonical closed immersion of the residue-field spectrum.
Source: ILO XVII 3.4.1.3, p.272
(blueprint: lem-per-sepclosed-regular-proper-curve-trace). -/
abbrev sepclosedCurvePointImmersion (D : Scheme.{u}) (z : closedPoints D) :
    IsClosedImmersion (D.fromSpecResidueField z.val) :=
  isClosed_singleton_iff_isClosedImmersion.mp z.property

/-- Codimension-one regularity of the canonical residue-field immersion, with its
closed-immersion evidence supplied by closedness, rather than assumed independently.
Source: ILO XVII 3.4.1.3, p.272
(blueprint: lem-per-sepclosed-regular-proper-curve-trace). -/
abbrev SepclosedCurvePointRegular (D : Scheme.{u}) (z : closedPoints D) : Prop :=
  @IsStalkRegularClosedImmersion _ _ (D.fromSpecResidueField z.val)
    (sepclosedCurvePointImmersion D z) 1

/-- The regular Gysin class evaluated at one and with support enlarged to the curve.
The unique normalized family is selected from regular_immersion_class_calculus;
precomposition with supportedConstantUnit is the canonical forget-support operation.
No trace or cohomology class is supplied as arbitrary input.
Source: ILO XVII 3.4.1.3, p.272, and XVI 2.3.1
(blueprint: lem-per-sepclosed-regular-proper-curve-trace). -/
def sepclosedCurvePointClass (k : Type u) [Field k] (D : Scheme.{u})
    (f : D ⟶ Spec (.of k)) [IsProper f] (ℓ : ℕ) (hℓ : ℓ.Prime)
    (n : ℕ) (hn : 1 ≤ n) (hD : IsUnit ((ℓ ^ n : ℕ) : Γ(D, ⊤)))
    (z : closedPoints D) (hreg : SepclosedCurvePointRegular D z) :
    Ext (regularClassTwist ℓ n D 0) (regularClassTwist ℓ n D 1) 2 :=
  letI : IsNoetherian D := isNoetherian_of_locallyOfFiniteType f
  letI : IsClosedImmersion (D.fromSpecResidueField z.val) :=
    sepclosedCurvePointImmersion D z
  (Ext.mk₀ (supportedConstantUnit (regularClassCoefficients ℓ n)
    (D.fromSpecResidueField z.val))).comp
      (Classical.choose (regular_immersion_class_calculus ℓ hℓ).exists
        n hn (D.fromSpecResidueField z.val) 1 hreg hD 0) (zero_add 2)

/-- The canonical trace isomorphism, characterized by the residue degrees of all
closed-point Gysin classes. The Ext group is ordinary small-etale H²(D, Λ(1)),
and the isomorphism is linear over the same lifted Z/(ℓ^n) as those classes.
The unit proof hD merely permits evaluation of the published Gysin family: it exists
by mapping the invertible ℓ from k to Γ(D, ⊤), then taking its nth power.
Source: ILO XVII, proof of Proposition 3.4.1.3, printed pp.271--272
(blueprint: lem-per-sepclosed-regular-proper-curve-trace).

Proof:
1. Properness gives Noetherianity (lem-weil-pbc-finite-type-over-noetherian).
At a closed point the regular one-dimensional local ring is a DVR
(lem-sc-regular-dim1-dvr); spread its uniformizer to obtain a Cartier divisor.
Its residue degree is finite by lem-weil-pbc-zariski-lemma.
2. Pass to an algebraic closure K, reduce D_K and normalize to C. The maps to D
are universal homeomorphisms: det-curve-invariance-inseparable-closure,
lem-per-normalization-field-extension-homeomorphism, rem-pc-regular-normal,
lem-sc-normalization-over-normal-locus and lem-weil-pbc-reduction-universal-homeomorphism.
Properness and smooth regular normalization follow from lem-pc-degree-base-change,
lem-weil-pbc-closed-immersion-proper and lem-sc-normalization-properties.
3. Ordinary etale invariance and lem-asd-etale-finite-twist-pullback give the
isomorphism alpha on H² (thm-weil-pbc-universal-homeomorphism-invariance).
4. On C, lem-sc-second-kummer-divisors and det-cor-jacobian-torsion-pic identify
H² with Pic/N and degree modulo N. This is def-wf-degree-normalized-curve-trace.
5. If m is the generic multiplicity of D_K, degree base change, the weighted
component formula (lem-trf-degree-weighted-irreducible-components), and
lem-per-birational-curve-degree-invariance give deg_k(L) = m deg_K(u*L).
The dense normal locus used here is supplied by
lem-weil-pbc-reduced-algebraic-normalization-field-change. For O(z), this is
m deg_K(u*O(z)) = [κ(z):k], retaining every divisor multiplicity.
6. A closed point exists by lem-sc-quasi-compact-kolmogorov-closed-point and
lem-sc-scheme-sober. Its finite residue extension is purely inseparable by
lem-kun-sep-closed-finite-extension-purely-inseparable. The pth-root tower of
lem-weil-pbc-purely-inseparable-pth-root-tower shows that its degree, and hence m,
is prime to ℓ. In characteristic zero the degree is one.
7. Define the trace as m times the smooth degree-normalized trace composed with
alpha. All three factors are invertible, giving a Λ-linear isomorphism.
8. The positive codimension-one sign of lem-per-regular-immersion-class-calculus
identifies the enlarged Gysin class with c₁(O(z)). Cartier-preserving pullback in
lem-asd-ordinary-supported-kummer identifies its pullback with c₁(u*O(z)). Step 5
therefore gives exactly the residue degree as its trace.
9. This degree is a unit for a closed point, so its class generates H². A linear
map with the required values is unique. Thus all algebraic-closure and auxiliary
choices disappear, and this is the canonical trace characterized in the source. -/
theorem sepclosed_regular_proper_curve_trace
    (k : Type u) [Field k] [IsSepClosed k] (D : Scheme.{u})
    (f : D ⟶ Spec (.of k)) [IsProper f] [IsIntegral D]
    (hregular : IsRegularScheme D) (hdim : topologicalKrullDim D = 1)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (n : ℕ) (hn : 1 ≤ n) (hℓk : IsUnit (ℓ : k)) :
    ∃! tr : Ext (regularClassTwist ℓ n D 0) (regularClassTwist ℓ n D 1) 2
        ≃ₗ[regularClassCoefficients ℓ n] regularClassCoefficients ℓ n,
      ∀ (hD : IsUnit ((ℓ ^ n : ℕ) : Γ(D, ⊤))) (z : closedPoints D),
        ∃ hreg : SepclosedCurvePointRegular D z,
          tr (sepclosedCurvePointClass k D f ℓ hℓ n hn hD z hreg) =
            (f.residueDegree z.val : regularClassCoefficients ℓ n) := by
  sorry

end AlgebraicGeometry.Etale
