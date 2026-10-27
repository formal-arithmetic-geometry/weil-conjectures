/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q12
-/
module

public import Sheaf.AlgebraicGeometry.ArtinDeformationTestCategory
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology

import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import WeilConjectures.RingTheory.PowerSeriesQuotientVariables
import WeilConjectures.RingTheory.PowerSeriesCompleteOverCompleteBase
import WeilConjectures.RingTheory.PowerSeriesAdicEvaluation
import WeilConjectures.RingTheory.PowerSeriesCombinedIdealCoefficients
import Sheaf.RingTheory.CompleteLocalCotangentSurjectivity

/-! # Smooth complete local functors and power series

Source: Stacks Project, Formal Deformation Theory, Tags 06HL and 06ST
(blueprint: lem-sfb-complete-local-smooth-power-series).

The Artinian test category and marked local maps are the existing shared definitions.
Local maps are automatically continuous for the maximal-ideal-adic topologies.
The tangent identification below specifies the second coordinate of every dual-number
point on every representative. It therefore retains the usual tangent vector operations.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open CategoryTheory

namespace AlgebraicGeometry.ArtinDeformation

variable {k : Type u} [Field k]

/-- The specified coefficient-field augmentation. Source: Stacks, Tag 06HL
(blueprint: lem-sfb-complete-local-smooth-power-series). -/
def completeAugmentation (A : CompleteLocalAlgebra k k) : A.ring →ₐ[k] k :=
  A.residueEquiv.toAlgHom.comp (Ideal.Quotient.mkₐ k (IsLocalRing.maximalIdeal A.ring))

/-- Relations defining the relative cotangent quotient, pulled back to the maximal
ideal, with scalars restricted to k. Source: Stacks, Tag 06HL
(blueprint: lem-sfb-complete-local-smooth-power-series). -/
def relativeCotangentRelations (B A : CompleteLocalAlgebra k k) (f : B.ring →ₐ[k] A.ring) :
    Submodule k (IsLocalRing.maximalIdeal A.ring) :=
  Submodule.comap ((IsLocalRing.maximalIdeal A.ring).restrictScalars k).subtype
    (((IsLocalRing.maximalIdeal B.ring).map f.toRingHom ⊔
      IsLocalRing.maximalIdeal A.ring ^ 2).restrictScalars k)

/-- The actual quotient m_A / (m_B A + m_A²). Source: Stacks, Tag 06HL
(blueprint: lem-sfb-complete-local-smooth-power-series). -/
abbrev RelativeCotangent (B A : CompleteLocalAlgebra k k) (f : B.ring →ₐ[k] A.ring) :=
  IsLocalRing.maximalIdeal A.ring ⧸ relativeCotangentRelations B A f

/-- The square-zero Artinian lifting test for h_A → h_B, expanded on compatible
pairs of points. Source: Stacks, Tag 06HL and Remark compare-smooth-schlessinger
(blueprint: lem-sfb-complete-local-smooth-power-series). -/
def IsFormallySmoothOnArtin (B A : CompleteLocalAlgebra k k)
    (f : B.ring →ₐ[k] A.ring) : Prop :=
  ∀ (R R' : TestCategory k k) (p : R' ⟶ R),
    Function.Surjective (map p) → (RingHom.ker (map p).toRingHom) ^ 2 = ⊥ →
    ∀ (a : LocalMap A R) (b : LocalMap B R'),
      a.hom.comp f = (map p).comp b.hom →
      ∃ a' : LocalMap A R', (map p).comp a'.hom = a.hom ∧ a'.hom.comp f = b.hom

/-- The relative tangent fibre over the constant B-point of the dual numbers.
Source: Stacks, Tag 06ST (blueprint: lem-sfb-complete-local-smooth-power-series). -/
def RelativeTangentPoints (B A : CompleteLocalAlgebra k k) (f : B.ring →ₐ[k] A.ring) :=
  {a : LocalMap A (squareZeroTest (R := k) (k := k) k) //
    a.hom.comp f = (Algebra.ofId k (ring (squareZeroTest (R := k) (k := k) k))).comp
      (completeAugmentation B)}

/-- Formal smoothness is equivalent to the power series presentation with exactly the
relative cotangent dimension, and the tangent fibre is canonically its dual.
Source: Stacks, Tags 06HL and 06ST
(blueprint: lem-sfb-complete-local-smooth-power-series).

Proof:
1. Artinian local rings have nilpotent maximal ideal by
lem-weil-pbc-artinian-local-noetherian-nilpotent. Factor an arbitrary Artinian
surjection with kernel J through J^j/J^(j+1); these kernels square to zero.
2. For r the relative cotangent dimension, T = B[[X_1,...,X_r]] is Noetherian
and local by lem-weil-pbc-power-series-noetherian and -local-ring. Its maximal
ideal is m_B T + (X), by -quotient-variables, and it is complete by
lem-weil-pbc-power-series-complete-over-complete-base. This includes r = 0.
3. A power series presentation solves every lifting problem by lifting the images
of X_i to the target maximal ideal and applying
lem-weil-pbc-power-series-adic-evaluation. Uniqueness gives the prescribed reduction.
4. Conversely choose lifts of a basis of V = m_A/(m_B A + m_A²). Noetherianity
makes V finite dimensional. Identify A/(m_B A + m_A²) and
T/(m_B T + m_T²) with k plus their square-zero relative cotangent spaces, using
lem-weil-pbc-power-series-combined-ideal-coefficients for constant and linear terms.
5. Lift this map first to T/m_T² and successively to T/m_T^n; these are Artinian
local by lem-weil-pbc-noetherian-local-quotient-artinian-local. Completeness gives
f : A → T. It is local, continuous and an isomorphism on relative cotangent spaces.
6. By lem-sfb-complete-local-cotangent-surjectivity, f is onto. Lift the variables
to A and use -power-series-adic-evaluation to construct a section s. Uniqueness
gives f s = 1. The relative cotangent map of s is inverse to that of f; applying
the same surjectivity criterion to s makes it bijective. Both maps are continuous.
7. A dual-number point is a ↦ residue(a) + ε d(a). Multiplication is precisely
the residue-Leibniz rule. It kills m_A² and, over the constant B-point, m_B A.
It therefore gives a unique linear form on V. Conversely a linear form gives this
point by applying it to a minus its specified residue lifted along k → A.
These constructions are inverse and preserve addition and scalar multiplication,
as is witnessed by the second-coordinate formula in the conclusion. -/
theorem formallySmoothOnArtin_iff_powerSeries
    (B A : CompleteLocalAlgebra k k) (f : B.ring →ₐ[k] A.ring)
    [IsLocalHom f.toRingHom]
    (hf : @Continuous B.ring A.ring (IsLocalRing.maximalIdeal B.ring).adicTopology
      (IsLocalRing.maximalIdeal A.ring).adicTopology f)
    (hres : (completeAugmentation A).comp f = completeAugmentation B) :
    (IsFormallySmoothOnArtin B A f ↔
      ∃ e : A.ring ≃ₐ[k]
          MvPowerSeries (Fin (Module.finrank k (RelativeCotangent B A f))) B.ring,
        (∀ b : B.ring, e (f b) = MvPowerSeries.C b) ∧
        @Continuous A.ring _ (IsLocalRing.maximalIdeal A.ring).adicTopology
          (IsLocalRing.maximalIdeal _).adicTopology e ∧
        @Continuous _ A.ring (IsLocalRing.maximalIdeal _).adicTopology
          (IsLocalRing.maximalIdeal A.ring).adicTopology e.symm) ∧
    (∃ e : RelativeTangentPoints B A f ≃ Module.Dual k (RelativeCotangent B A f),
      ∀ (a : RelativeTangentPoints B A f) (x : IsLocalRing.maximalIdeal A.ring),
        e a ((relativeCotangentRelations B A f).mkQ x) = (a.val.hom x).snd) := by
  sorry

/-- An unobstructed functor prorepresented by A has power series representing ring;
its tangent set is identified with the dual cotangent space, so the displayed
number of variables is its tangent dimension. A family of equivalences commuting
with all test maps is exactly the prorepresenting natural isomorphism, written
without choosing a second model of the functor h_A.
Source: Stacks, Tags 06HL and 06ST, specialization B = k
(blueprint: lem-sfb-complete-local-smooth-power-series).

Proof (step 8 of the node): transport unobstructedness through the natural
prorepresenting equivalences. The k-point functor has one point, so this is the
lifting test of step 1 with base k. Apply steps 2--6 with m_k = 0. Step 7 identifies
the tangent space with the dual of m_A/m_A²; its dimension equals the cotangent
dimension by finite dimensionality. Compose this identification with the given
prorepresenting equivalence at the dual numbers. This also covers dimension zero. -/
theorem prorepresented_unobstructed_powerSeries
    (A : CompleteLocalAlgebra k k) (F : TestCategory k k ⥤ Type v)
    (eF : ∀ R : TestCategory k k, LocalMap A R ≃ F.obj R)
    (hnat : ∀ (R R' : TestCategory k k) (p : R' ⟶ R)
      (a' : LocalMap A R') (a : LocalMap A R),
      (map p).comp a'.hom = a.hom → F.map p (eF R' a') = eF R a)
    (hunobstructed : ∀ (R R' : TestCategory k k) (p : R' ⟶ R),
      Function.Surjective (map p) → (RingHom.ker (map p).toRingHom) ^ 2 = ⊥ →
      Function.Surjective (F.map p)) :
    (∃ e : A.ring ≃ₐ[k]
        MvPowerSeries (Fin (Module.finrank k (IsLocalRing.maximalIdeal A.ring).Cotangent)) k,
      @Continuous A.ring _ (IsLocalRing.maximalIdeal A.ring).adicTopology
        (IsLocalRing.maximalIdeal _).adicTopology e ∧
      @Continuous _ A.ring (IsLocalRing.maximalIdeal _).adicTopology
        (IsLocalRing.maximalIdeal A.ring).adicTopology e.symm) ∧
    (∃ e : F.obj (squareZeroTest (R := k) (k := k) k) ≃
        Module.Dual k (IsLocalRing.maximalIdeal A.ring).Cotangent,
      ∀ (a : LocalMap A (squareZeroTest (R := k) (k := k) k))
        (x : IsLocalRing.maximalIdeal A.ring),
        e (eF _ a) ((IsLocalRing.maximalIdeal A.ring).toCotangent x) = (a.hom x).snd) := by
  sorry

end AlgebraicGeometry.ArtinDeformation
