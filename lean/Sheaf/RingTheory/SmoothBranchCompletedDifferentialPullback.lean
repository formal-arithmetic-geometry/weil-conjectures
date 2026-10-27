module

public import Sheaf.RingTheory.CompletionKaehlerDifferentialComparison
public import WeilConjectures.AlgebraicGeometry.Curve
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.LinearAlgebra.TensorProduct.Tower
import Sheaf.SixFunctors.TraceFormula.FormalPowerSeriesContinuousFree
import Sheaf.RingTheory.FormalRelativeDerivationExpansion
import Sheaf.AlgebraicGeometry.SmoothDifferentialsFreeRankFibreDimension
import Mathlib.RingTheory.Etale.Kaehler

/-! # Completed differential pullback to a smooth branch

Source: Stacks Project, curves.tex, Tags 0C4D and 0C4B, completed Jacobian
calculation and coordinate changes. The smooth-branch and rational naturality
refinement is the explicit auxiliary argument of the DAG
(blueprint: lem-trf-smooth-branch-completed-differential-pullback).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open scoped TensorProduct BigOperators
open AlgebraicGeometry

namespace Algebra

/-- Completed pullback, rational localization, formal Jacobian relations, and invariance
under every change of uniformizer. The free modules `T dt` and `L dt` are represented
by their coefficient rings. `E` has coefficients in `T`; `eT` reads those coefficients
as power series. An affine neighbourhood `Spec B` of the smooth rational point
presents `D` as `B_q`; neither the original curve nor the neighbourhood must be
connected. All localizations can be any models of the specified localization.

The completion map is specified by extension and adic continuity. `beta` is specified
on arbitrary differential tensors by the algebraic differential map; `betaR` is its
canonical semilinear scalar restriction along the completion map. Rational scalar
extension compatibility is stated on every pure tensor `(c, omega)`. These tensors
generate the scalar extension, so this states equality of the full maps.

In the final clause the rings with parameters `t` and `s` are two copies of the same
power-series or Laurent-series type. `Es` and `betas` are the maps for parameter `s`
precomposed with scalar transport. Thus they are semilinear for `sigma` composed with
`eT`. The identities for all inputs state the three whole naturality squares.

Source: Stacks Project, curves.tex, Tags 0C4D and 0C4B
(blueprint: lem-trf-smooth-branch-completed-differential-pullback).

Proof:
1. Apply lem-trf-completion-kahler-differential-comparison to an affine neighbourhood
   of the smooth rational point. Transport its continuous differentials along `eT`.
   The one-variable case of lem-trf-formal-power-series-continuous-free supplies E
   and the termwise derivative formula, both on D and on its entire completion.
2. By lem-weil-pbc-smooth-differentials-free-rank-fibre-dimension, differentials on
   a sufficiently small affine neighbourhood are free of finite rank d. Localize
   using lem-weil-pbc-kahler-differentials-localization. Completion and E show d=1
   by invariance of free rank. If b is a basis, E(b) has unit coefficient. Localizing
   again to F gives F b; its map to L is multiplication by that unit followed by
   the field embedding. It is injective and becomes an isomorphism over L. Leibniz
   on a quotient a/c proves that its differential formula is the quotient rule.
3. Universality of def-weil-pbc-kahler-differentials gives the differential map for
   alpha. Extend scalars and compose with E to obtain beta and betaR. The comparison
   theorem supplies the continuous extension dA. Both proposed formulas on R are
   continuous: locality preserves ideal powers, and differentiation lowers order
   by at most one. They agree on A by step 1. Approximation modulo ideal powers
   and separatedness of the power-series ring prove equality throughout R.
4. Apply step 3 to the images of the variables. Apply
   lem-trf-formal-relative-derivation-expansion to the presentation followed by the
   completed branch map and termwise differentiation. The image of each relation
   is zero, so its formal derivative expansion gives the displayed Jacobian sum.
5. On da times an arbitrary Laurent coefficient, beta and the composite through
   the rational differentials both give that coefficient times alpha(a)'. The
   differential symbols generate, proving compatibility on the whole module.
6. A power-series algebra isomorphism carries the maximal ideal onto itself, so
   v=s*w with w(0) nonzero; hence v' is a unit in every characteristic. Extend
   sigma uniquely to fraction fields. Formal relative derivation expansion proves
   the power-series chain rule, and quotient differentiation proves it on L.
7. Set nu(c)=tau(c)*v'. Its inverse sends d to tau inverse of d/v', so nu is an
   invertible semilinear map preserving the power-series lattice. On dd, da and dz,
   the chain rule proves respectively the E, beta and delta naturality squares.
   Their differential generators span, so the identities hold on every input.
-/
theorem smooth_branch_completed_differential_pullback
    (k S A B D F : Type u) [Field k] [IsAlgClosed k]
    [CommRing S] [Algebra k S]
    (hS : (algebraMap k S).FiniteType) (m : Ideal S) [m.IsMaximal]
    (residueS : m.ResidueField ≃ₐ[k] k)
    [CommRing A] [Algebra S A] [IsLocalization.AtPrime A m]
    [Algebra k A] [IsScalarTower k S A] [IsLocalRing A]
    [CommRing B] [Algebra k B]
    (hcurve : IsCurve (Spec.map (CommRingCat.ofHom (algebraMap k B))))
    (hsmooth : AlgebraicGeometry.Smooth (Spec.map (CommRingCat.ofHom (algebraMap k B))))
    (hdim : topologicalKrullDim (Spec (CommRingCat.of B)) = 1)
    (q : Ideal B) [q.IsMaximal] (residueB : q.ResidueField ≃ₐ[k] k)
    [CommRing D] [IsDomain D] [IsDiscreteValuationRing D]
    [Algebra B D] [IsLocalization.AtPrime D q]
    [Algebra k D] [IsScalarTower k B D]
    [Algebra A D] [IsScalarTower k A D] [IsLocalHom (algebraMap A D)]
    [Field F] [Algebra D F] [IsFractionRing D F]
    [Algebra k F] [IsScalarTower k D F]
    (eT : LocalCompletion D ≃ₐ[k] PowerSeries k)
    [Algebra F (LaurentSeries k)]
    (hF : ∀ d : D, algebraMap F (LaurentSeries k) (algebraMap D F d) =
      algebraMap (PowerSeries k) (LaurentSeries k)
        (eT (algebraMap D (LocalCompletion D) d))) :
    ∃ ahat : LocalCompletion A →ₐ[k] LocalCompletion D,
      (∀ a : A, ahat (algebraMap A (LocalCompletion A) a) =
        algebraMap D (LocalCompletion D) (algebraMap A D a)) ∧
      (∀ r : ℕ, ∃ N : ℕ,
        (((IsLocalRing.maximalIdeal A).map (algebraMap A (LocalCompletion A))) ^ N).map
            ahat.toRingHom ≤
          ((IsLocalRing.maximalIdeal D).map (algebraMap D (LocalCompletion D))) ^ r) ∧
      ∃ (E : CompletedDifferentials k D ≃ₗ[LocalCompletion D] LocalCompletion D)
        (dD : Derivation k (LocalCompletion D) (CompletedDifferentials k D))
        (dA : Derivation k (LocalCompletion A) (CompletedDifferentials k A)),
        IsCompletedDifferentialExtension k D dD ∧
        IsCompletedDifferentialExtension k A dA ∧
        (∀ d : D, eT (E (1 ⊗ₜ[D] KaehlerDifferential.D k D d)) =
          PowerSeries.derivative k (eT (algebraMap D (LocalCompletion D) d))) ∧
        (∀ h : LocalCompletion D, eT (E (dD h)) = PowerSeries.derivative k (eT h)) ∧
        ∃ (delta : KaehlerDifferential k F →ₗ[F] LaurentSeries k)
          (EL : LaurentSeries k ⊗[F] KaehlerDifferential k F ≃ₗ[LaurentSeries k]
            LaurentSeries k),
          (∀ z : F, delta (KaehlerDifferential.D k F z) =
            LaurentSeries.derivative k (algebraMap F (LaurentSeries k) z)) ∧
          Function.Injective delta ∧
          (∀ (c : LaurentSeries k) (w : KaehlerDifferential k F),
            EL (c ⊗ₜ[F] w) = c * delta w) ∧
          ∃ (beta : LocalCompletion D ⊗[A] KaehlerDifferential k A →ₗ[LocalCompletion D]
              LocalCompletion D)
            (betaR : CompletedDifferentials k A →ₛₗ[ahat.toRingHom] LocalCompletion D),
            (∀ (c : LocalCompletion D) (w : KaehlerDifferential k A),
              beta (c ⊗ₜ[A] w) =
                E (c ⊗ₜ[D] KaehlerDifferential.map k k A D w)) ∧
            (∀ (r : LocalCompletion A) (w : KaehlerDifferential k A),
              betaR (r ⊗ₜ[A] w) = ahat r * beta (1 ⊗ₜ[A] w)) ∧
            (∀ h : LocalCompletion A,
              eT (betaR (dA h)) = PowerSeries.derivative k (eT (ahat h))) ∧
            (∀ (n s : ℕ) (p : MvPowerSeries (Fin n) k →ₐ[k] LocalCompletion A)
                (g : Fin s → MvPowerSeries (Fin n) k),
              Function.Surjective p →
              RingHom.ker p.toRingHom = Ideal.span (Set.range g) →
              (∀ j : Fin s, MvPowerSeries.constantCoeff (g j) = 0) →
              (∀ r : ℕ, ∃ N : ℕ,
                ((Ideal.span (Set.range (MvPowerSeries.X : Fin n →
                    MvPowerSeries (Fin n) k))) ^ N).map p.toRingHom ≤
                  ((IsLocalRing.maximalIdeal A).map (algebraMap A (LocalCompletion A))) ^ r) →
              (∀ i : Fin n, eT (betaR (dA (p (MvPowerSeries.X i)))) =
                PowerSeries.derivative k (eT (ahat (p (MvPowerSeries.X i))))) ∧
              ∀ j : Fin s,
                ∑ i : Fin n, eT (ahat (p (MvPowerSeries.pderiv k i (g j)))) *
                  PowerSeries.derivative k (eT (ahat (p (MvPowerSeries.X i)))) = 0) ∧
            (∀ (w : KaehlerDifferential k A) (c : LaurentSeries k),
              c * algebraMap (PowerSeries k) (LaurentSeries k)
                  (eT (beta (1 ⊗ₜ[A] w))) =
                c * delta (KaehlerDifferential.map k k D F
                  (KaehlerDifferential.map k k A D w))) ∧
            ∀ sigma : PowerSeries k ≃ₐ[k] PowerSeries k,
              ∃ tau : LaurentSeries k ≃ₐ[k] LaurentSeries k,
                (∀ f : PowerSeries k, tau (algebraMap (PowerSeries k) (LaurentSeries k) f) =
                  algebraMap (PowerSeries k) (LaurentSeries k) (sigma f)) ∧
                (∀ tau' : LaurentSeries k ≃ₐ[k] LaurentSeries k,
                  (∀ f : PowerSeries k, tau' (algebraMap (PowerSeries k) (LaurentSeries k) f) =
                    algebraMap (PowerSeries k) (LaurentSeries k) (sigma f)) → tau' = tau) ∧
                IsUnit (PowerSeries.derivative k (sigma PowerSeries.X)) ∧
                (∀ h : LaurentSeries k,
                  tau (LaurentSeries.derivative k h) *
                      algebraMap (PowerSeries k) (LaurentSeries k)
                        (PowerSeries.derivative k (sigma PowerSeries.X)) =
                    LaurentSeries.derivative k (tau h)) ∧
                ∃ nu : @LinearEquiv _ _ _ _ tau.toRingHom tau.symm.toRingHom
                    (RingHomInvPair.of_ringEquiv tau.toRingEquiv)
                    (RingHomInvPair.of_ringEquiv_symm tau.toRingEquiv)
                    (LaurentSeries k) (LaurentSeries k) _ _ _ _,
                  (∀ h : LaurentSeries k, nu h = tau h *
                    algebraMap (PowerSeries k) (LaurentSeries k)
                      (PowerSeries.derivative k (sigma PowerSeries.X))) ∧
                  nu '' Set.range (algebraMap (PowerSeries k) (LaurentSeries k)) =
                    Set.range (algebraMap (PowerSeries k) (LaurentSeries k)) ∧
                  ∃ (Es : @LinearEquiv _ _ _ _ (eT.trans sigma).toRingHom
                      (eT.trans sigma).symm.toRingHom
                      (RingHomInvPair.of_ringEquiv (eT.trans sigma).toRingEquiv)
                      (RingHomInvPair.of_ringEquiv_symm (eT.trans sigma).toRingEquiv)
                      (CompletedDifferentials k D) (PowerSeries k) _ _ _ _)
                    (betas : LocalCompletion D ⊗[A] KaehlerDifferential k A
                      →ₛₗ[(eT.trans sigma).toRingHom] PowerSeries k)
                    (deltas : KaehlerDifferential k F →ₗ[k] LaurentSeries k),
                    (∀ d : D, Es (1 ⊗ₜ[D] KaehlerDifferential.D k D d) =
                      PowerSeries.derivative k
                        (sigma (eT (algebraMap D (LocalCompletion D) d)))) ∧
                    (∀ a : A, betas (1 ⊗ₜ[A] KaehlerDifferential.D k A a) =
                      PowerSeries.derivative k (sigma (eT
                        (algebraMap D (LocalCompletion D) (algebraMap A D a))))) ∧
                    (∀ (f : F) (w : KaehlerDifferential k F),
                      deltas (f • w) = tau (algebraMap F (LaurentSeries k) f) * deltas w) ∧
                    (∀ z : F, deltas (KaehlerDifferential.D k F z) =
                      LaurentSeries.derivative k (tau (algebraMap F (LaurentSeries k) z))) ∧
                    (∀ w : CompletedDifferentials k D,
                      nu (algebraMap (PowerSeries k) (LaurentSeries k) (eT (E w))) =
                        algebraMap (PowerSeries k) (LaurentSeries k) (Es w)) ∧
                    (∀ w : LocalCompletion D ⊗[A] KaehlerDifferential k A,
                      nu (algebraMap (PowerSeries k) (LaurentSeries k) (eT (beta w))) =
                        algebraMap (PowerSeries k) (LaurentSeries k) (betas w)) ∧
                    ∀ w : KaehlerDifferential k F, nu (delta w) = deltas w := by
  sorry

end Algebra
