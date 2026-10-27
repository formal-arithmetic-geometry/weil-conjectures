module

public import WeilConjectures.RingTheory.AssociatedGradedRing
public import WeilConjectures.RingTheory.EssentiallySmooth
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.Ideal.GoingDown
import WeilConjectures.RingTheory.DimensionAtPointComponents
import WeilConjectures.RingTheory.DimensionAtPointLocalRingTrdeg
import WeilConjectures.RingTheory.FiniteTypeDomainDimensionTrdeg
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.AdicCompletion.Completeness
import WeilConjectures.RingTheory.SmoothFibreRegularLocal
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.FiniteType
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Tangent cones of essentially smooth local extensions

Source: Stacks Project, Algebra, Tags 00T7 and 00ON, for local smooth charts and
local dimension; the coefficient-compatible presentation and finite-jet calculation
in the node supply the graded comparison, not either tag alone
(blueprint: lem-trf-smooth-local-tangent-cone-extension).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open scoped TensorProduct

/-- The usual degree-zero scalar action on a local ring's associated graded ring,
transported through the definition `ResidueField A = A / maximalIdeal A`.
Source: the associated-graded algebra convention in Stacks Project, Algebra, Lemma 05GH
(blueprint: lem-trf-smooth-local-tangent-cone-extension). -/
noncomputable instance IsLocalRing.associatedGradedAlgebra
    {A : Type u} [CommRing A] [IsLocalRing A] :
    Algebra (IsLocalRing.ResidueField A)
      (Ideal.associatedGraded (IsLocalRing.maximalIdeal A)) :=
  inferInstanceAs (Algebra (A ⧸ IsLocalRing.maximalIdeal A)
    (Ideal.associatedGraded (IsLocalRing.maximalIdeal A)))

namespace Algebra

/-- The tangent cone of an essentially smooth local extension is the polynomial algebra
on the closed-fibre dimension over the residue-field extension of the base tangent cone.
Source: Stacks Project, Algebra, Tags 00T7, 00ON, 00TT, 00P0 and 00P1, together with
the coefficient-compatible completed presentation and finite-jet argument of the node
(blueprint: lem-trf-smooth-local-tangent-cone-extension).

The equivalence is oriented from the displayed polynomial algebra to the tangent cone.
Its first condition says that every monomial with a homogeneous pure-tensor coefficient
of degree `d` has image homogeneous of degree `d + b.degree`. These monomials additively
span the homogeneous pieces, so this is precisely preservation of the total grading,
with every variable of degree one and residue-field scalars of degree zero. A bijective
map preserving this direct-sum grading has grading-preserving inverse. The second
condition fixes its restriction to the base by sending every representative `a` to
its actual image under `algebraMap A B`. Thus no arbitrary comparison map is substituted.

Proof: (1) Choose a smooth finite-type chart `P` and a prime `N` with `B = P_N`
using def-weil-pbc-essentially-smooth-ring-map. Essential finite type over the field
implies Noetherianity by lem-wf-affine-noetherian-components and
lem-weil-pbc-localization-noetherian. Smoothness, localization and transitivity give
flatness by lem-weil-pbc-smooth-ring-map-flat, lem-weil-pbc-localization-flat and
lem-pc-module-flat-transitive. The smooth-fibre theorem
lem-weil-pbc-smooth-fibre-regular-local makes `F` regular local of finite dimension `s`.

(2) Apply lem-trf-relative-cohen-flat-presentation: with compatible coefficient sections,
the completions are `K[[X]]/I` and `L[[X,T]]/(I)`, compatibly with the actual map from `A`.
(3) Modulo the `N`th maximal-ideal power, collect the `T` monomials of degree less than
`N`; their coefficients are `L` tensored with the corresponding quotients of `K[[X]]/I`
by powers `N - |b|`. Finite truncation reduces the relations to polynomial relations;
lem-weil-pbc-module-over-field-flat and lem-weil-pbc-flat-tensor-exact identify images
and kernels after coefficient extension. The transition deletes degree `N` terms and
reduces the other coefficients. (4) Taking consecutive kernels identifies each graded
piece, and power-series convolution identifies multiplication. The completion quotients
from lem-weil-pbc-module-completion-complete identify these pieces with those of `A`
and `B`. The constant `T` monomial gives the asserted restriction to the base.

(5) For a local domain `D` essentially of finite type over the rationals,
lem-weil-pbc-dimension-at-point-components,
lem-weil-pbc-finite-type-domain-dimension-trdeg and
lem-weil-pbc-dimension-at-point-local-ring-trdeg give its dimension as fraction-field
transcendence degree minus residue-field transcendence degree. Apply this to the
minimal-prime quotients. (6) Put `t = trdeg_K L`. The local fibre topological dimension
`r` of the smooth chart is locally constant by
sbc-lem-smooth-relative-dimension-locally-constant, and the local-ring formula gives
`r = s + t`. (7) Flat going down (lem-sc-flat-going-down) makes the contraction of
each minimal prime minimal. Faithful flatness
(lem-weil-pbc-flat-local-hom-faithfully-flat) lifts every minimal prime downstairs;
choose a minimal prime below the lift by lem-weil-pbc-prime-contains-minimal-prime.
Its contraction is the original prime. (8) For such a pair, the corresponding prime
of `P` is minimal and its generic-component fibre local ring is zero-dimensional.
The local-ring formula and smooth local constancy identify its residue-field
transcendence degree with `r`. (9) Substitute these formulas into the dimension
calculation in (5), using lem-sbc-transcendence-degree-tower: the dimension difference
is `r - t = s`. The contraction and lifting in (7) give both inclusions of the sets.
No uniqueness of a minimal-prime lift or equality of the residue fields is used. -/
theorem smooth_local_tangent_cone_extension
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [Algebra ℚ A] [Algebra ℚ B]
    [EssFiniteType ℚ A] [EssFiniteType ℚ B]
    [Algebra A B] [IsLocalHom (algebraMap A B)]
    (hsmooth : EssentiallySmooth A B) :
    IsRegularLocalRing (B ⧸ (IsLocalRing.maximalIdeal A).map (algebraMap A B)) ∧
    ∃ s : ℕ,
      ringKrullDim (B ⧸ (IsLocalRing.maximalIdeal A).map (algebraMap A B)) =
        (s : WithBot ℕ∞) ∧
      (∃ e : MvPolynomial (Fin s)
          (IsLocalRing.ResidueField B ⊗[IsLocalRing.ResidueField A]
            Ideal.associatedGraded (IsLocalRing.maximalIdeal A)) ≃ₐ[IsLocalRing.ResidueField B]
          Ideal.associatedGraded (IsLocalRing.maximalIdeal B),
        (∀ (d : ℕ) (b : Fin s →₀ ℕ) (c : IsLocalRing.ResidueField B)
            (x : Ideal.associatedGradedPiece (IsLocalRing.maximalIdeal A) d),
          ∃ y : Ideal.associatedGradedPiece (IsLocalRing.maximalIdeal B) (d + b.degree),
            e (MvPolynomial.monomial b
                (c ⊗ₜ[IsLocalRing.ResidueField A]
                  DirectSum.of (Ideal.associatedGradedPiece (IsLocalRing.maximalIdeal A)) d x)) =
              DirectSum.of (Ideal.associatedGradedPiece (IsLocalRing.maximalIdeal B))
                (d + b.degree) y) ∧
        (∀ (d : ℕ) (a : (IsLocalRing.maximalIdeal A ^ d : Ideal A)),
          ∃ b : (IsLocalRing.maximalIdeal B ^ d : Ideal B),
            b.val = algebraMap A B a.val ∧
            e (MvPolynomial.C
                (1 ⊗ₜ[IsLocalRing.ResidueField A]
                  DirectSum.of (Ideal.associatedGradedPiece (IsLocalRing.maximalIdeal A)) d
                    (Submodule.Quotient.mk a))) =
              DirectSum.of (Ideal.associatedGradedPiece (IsLocalRing.maximalIdeal B)) d
                (Submodule.Quotient.mk b))) ∧
      {r : WithBot ℕ∞ | ∃ q : Ideal B, q ∈ minimalPrimes B ∧ ringKrullDim (B ⧸ q) = r} =
        {r : WithBot ℕ∞ | ∃ p : Ideal A, p ∈ minimalPrimes A ∧
          ringKrullDim (A ⧸ p) + (s : WithBot ℕ∞) = r} := by
  sorry

end Algebra
