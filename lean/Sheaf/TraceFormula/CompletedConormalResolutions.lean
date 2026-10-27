/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import Sheaf.RingTheory.CompletionKaehlerDifferentialComparison
public import Sheaf.AlgebraicGeometry.PureDimension
public import WeilConjectures.RingTheory.CompleteIntersectionOverField
public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import Mathlib.RingTheory.Extension.Cotangent.Basic
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.MvPowerSeries.Derivative
public import Mathlib.RingTheory.MvPowerSeries.PiTopology
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Homology.Double
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import WeilConjectures.RingTheory.RegularSequenceConormal
import WeilConjectures.RingTheory.ReducedNoetherianTotalRingFractions
import WeilConjectures.AlgebraicGeometry.TildePreservesFiniteLimits
import Sheaf.TraceFormula.CompletedJacobianDifferentials
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Completed algebraic and continuous formal conormal resolutions

Source: Stacks Project, Algebra, Tags 00LN, 00RX, 00RT, 00RU, 00MC and 02LX;
Varieties, Tag 0C52, for the continuous presentation convention.
(blueprint: lem-trf-completed-conormal-resolutions).

The conormal modules are the actual `Algebra.Extension.Cotangent` modules.
Tensor factors put the extending ring first, using the shared base-change convention.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry

/-- The assertion that the specified two-term row sheafifies to an augmented resolution
in degrees minus one and zero. The component in degree zero is the given augmentation,
and its image is an isomorphism in the shared derived category of sheaves on Spec R.
Source: Stacks, 01HV, 01ID and 05RU
(blueprint: lem-trf-completed-conormal-resolutions). -/
def IsCompletedConormalSheafResolution {R : Type u} [CommRing R]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (Spec (.of R)).toRingedSpace))]
    {U V M : ModuleCat.{u} R} (f : U ⟶ V) (q : V ⟶ M) : Prop :=
  ∃ C : CochainComplex
      (SheafOfModules.{u} (moduleRings (Spec (.of R)).toRingedSpace)) ℤ,
    (∀ i : ℤ, i ≠ -1 → i ≠ 0 → IsZero (C.X i)) ∧
    ∃ (eNeg : C.X (-1) ≅ (tilde.functor (.of R)).obj U)
      (e₀ : C.X 0 ≅ (tilde.functor (.of R)).obj V),
      C.d (-1) 0 = eNeg.hom ≫ (tilde.functor (.of R)).map f ≫ e₀.inv ∧
      ∃ ε : C ⟶ (CochainComplex.singleFunctor
          (SheafOfModules.{u} (moduleRings (Spec (.of R)).toRingedSpace)) 0).obj
          ((tilde.functor (.of R)).obj M),
        QuasiIso ε ∧ IsIso (DerivedCategory.Q.map ε) ∧
        ε.f 0 ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          ((tilde.functor (.of R)).obj M)).hom = e₀.hom ≫ (tilde.functor (.of R)).map q

/-- The algebraic and continuous formal conormal rows resolve the same completed
Kähler differential module, with equation and coordinate bases and exact generic fibres.

Source: Stacks Project, Algebra, Tags 00LN (regular implies quasi-regular), 00RX
(polynomial differentials), 00RT (localization), 00RU (quotient differential sequence),
00MC (faithful flatness of completion), 02LX (total fractions); Varieties, 0C52.
(blueprint: lem-trf-completed-conormal-resolutions).

Proof:
1. Finite type over a field, localization and completion preserve Noetherianity
   (lem-weil-pbc-finite-type-algebra-noetherian,
   lem-weil-pbc-localization-noetherian, lem-weil-pbc-adic-completion-noetherian).
   Apply lem-weil-pbc-local-completion-faithfully-flat to the local ring A.
2. Polynomial differentials and their localization give the coordinate basis
   (lem-weil-pbc-polynomial-ring-kahler-basis,
   lem-weil-pbc-kahler-differentials-localization). The regular-sequence conormal
   basis theorem gives the equation bases of I/I² and J/J²
   (lem-weil-pbc-regular-sequence-conormal-free). Tensor the algebraic bases with R.
3. The quotient differential sequence and tensor right exactness give the algebraic
   row and its prescribed augmentation (lem-weil-pbc-jacobi-zariski-differential-maps,
   lem-weil-pbc-tensor-right-exact). In particular the coordinate differentials
   generate N, so N is finite.
4. Apply lem-trf-completion-kahler-differential-comparison with residue field k and
   its structural section, then lem-trf-completed-jacobian-differentials to π.
   This gives the unique continuous extension and the right exact formal row.
   The Leibniz rule for def-trf-formal-power-series-partial-derivative shows that
   derivatives of J² vanish modulo J; thus the formula holds on every conormal class.
5. For an allowed field L, lem-trf-generic-completed-differential-rank gives cokernel
   dimension d. Tensor right exactness gives the two right exact rows. Their dimensions
   are (m-d,m,d) and (c,n,d). Rank-nullity twice makes both left arrows injective
   (lem-weil-pbc-idempotent-charpoly-rank-nullity). This also applies to every R_p at
   a minimal prime p, which the generic rank theorem identifies as an allowed field.
6. A kernel vector in either free source is therefore zero at all minimal primes.
   The reduced Noetherian total-fractions theorem
   (lem-weil-pbc-reduced-noetherian-total-ring-fractions) makes its coordinates zero
   in Q(R). A coordinate zero in Q(R) is killed by a nonzerodivisor, so is zero in R.
   Both rows are consequently short exact over R.
7. Tilde preserves finite limits and all small colimits
   (lem-sc-tilde-preserves-finite-limits, lem-weil-pbc-affine-tilde-gamma-adjunction).
   Thus the sheafified rows are short exact. Each augmented two-term complex has
   H⁻¹=0, H⁰ equal to the stated target via q, and zero cohomology otherwise.
   Its augmentation is a quasi-isomorphism and becomes an isomorphism in the derived
   category (def-weil-abstract-derived-category).
-/
theorem completedConormalResolutions
    {k S : Type u} [Field k] [PerfectField k] [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] [_root_.IsReduced S]
    (d : ℕ) (hpure : (Spec (.of S)).IsPureDimension d)
    (hlci : Algebra.IsLocalCompleteIntersection k S)
    (p : Ideal S) [p.IsMaximal] (hresidue : Nonempty ((S ⧸ p) ≃ₐ[k] k))
    [_root_.IsReduced (Algebra.LocalCompletion (Localization.AtPrime p))]
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      (moduleRings (Spec (.of (Algebra.LocalCompletion (Localization.AtPrime p)))).toRingedSpace))]
    (m : ℕ) (P : Algebra.Extension.{u} k (Localization.AtPrime p))
    (q : Ideal (MvPolynomial (Fin m) k)) [q.IsMaximal]
    (hq : Nonempty ((MvPolynomial (Fin m) k ⧸ q) ≃ₐ[k] k))
    [Algebra (MvPolynomial (Fin m) k) P.Ring]
    [IsScalarTower k (MvPolynomial (Fin m) k) P.Ring]
    [IsLocalization.AtPrime P.Ring q]
    (hdm : d ≤ m) (h : Fin (m - d) → P.Ring)
    (hh : RingTheory.Sequence.IsRegular P.Ring (List.ofFn h))
    (hI : P.ker = Ideal.span (Set.range h))
    (n c : ℕ) (hcd : c + d = n)
    (π : MvPowerSeries (Fin n) k →ₐ[k] Algebra.LocalCompletion (Localization.AtPrime p))
    (hπ : Function.Surjective π) (hlocal : IsLocalHom π.toRingHom)
    (hcontinuous : @Continuous _ _
      (@MvPowerSeries.WithPiTopology.instTopologicalSpace (Fin n) k ⊤)
      ((IsLocalRing.maximalIdeal (Localization.AtPrime p)).map
        (algebraMap (Localization.AtPrime p)
          (Algebra.LocalCompletion (Localization.AtPrime p)))).adicTopology π)
    (g : Fin c → MvPowerSeries (Fin n) k)
    (hg : RingTheory.Sequence.IsRegular (MvPowerSeries (Fin n) k) (List.ofFn g))
    (hgin : ∀ j : Fin c, g j ∈
      Ideal.span (Set.range (MvPowerSeries.X : Fin n → MvPowerSeries (Fin n) k)))
    (hJ : RingHom.ker π.toRingHom = Ideal.span (Set.range g)) :
    IsNoetherianRing S ∧ IsNoetherianRing (Localization.AtPrime p) ∧
    IsNoetherianRing (Algebra.LocalCompletion (Localization.AtPrime p)) ∧
    (algebraMap (Localization.AtPrime p)
      (Algebra.LocalCompletion (Localization.AtPrime p))).Flat ∧
    Function.Surjective (PrimeSpectrum.comap (algebraMap (Localization.AtPrime p)
      (Algebra.LocalCompletion (Localization.AtPrime p)))) ∧
    Module.Finite (Localization.AtPrime p) (KaehlerDifferential k (Localization.AtPrime p)) ∧
    Submodule.span (Localization.AtPrime p)
      (Set.range (fun i : Fin m ↦ KaehlerDifferential.D k (Localization.AtPrime p)
        (algebraMap P.Ring (Localization.AtPrime p)
          (algebraMap (MvPolynomial (Fin m) k) P.Ring (MvPolynomial.X i))))) = ⊤ ∧
    ∃ D : Derivation k (Algebra.LocalCompletion (Localization.AtPrime p))
        (Algebra.CompletedDifferentials k (Localization.AtPrime p)),
      Algebra.IsCompletedDifferentialExtension k (Localization.AtPrime p) D ∧
      (∀ D' : Derivation k (Algebra.LocalCompletion (Localization.AtPrime p))
          (Algebra.CompletedDifferentials k (Localization.AtPrime p)),
        Algebra.IsCompletedDifferentialExtension k (Localization.AtPrime p) D' → D' = D) ∧
      ∃ (δ : (Algebra.Extension.ofSurjective π hπ).Cotangent →ₗ[
          Algebra.LocalCompletion (Localization.AtPrime p)]
          (Fin n → Algebra.LocalCompletion (Localization.AtPrime p)))
        (qT : (Fin n → Algebra.LocalCompletion (Localization.AtPrime p)) →ₗ[
          Algebra.LocalCompletion (Localization.AtPrime p)]
          Algebra.CompletedDifferentials k (Localization.AtPrime p)),
        (∀ z : (Algebra.Extension.ofSurjective π hπ).ker,
          δ (Algebra.Extension.Cotangent.mk z) = fun i ↦ π (MvPowerSeries.pderiv k i z.val)) ∧
        (∀ i : Fin n, qT (Pi.single i 1) = D (π (MvPowerSeries.X i))) ∧
        (∀ i : Fin m,
          LinearMap.baseChange (Algebra.LocalCompletion (Localization.AtPrime p)) P.toKaehler
            ((1 : Algebra.LocalCompletion (Localization.AtPrime p)) ⊗ₜ[Localization.AtPrime p]
              ((1 : Localization.AtPrime p) ⊗ₜ[P.Ring] KaehlerDifferential.D k P.Ring
                (algebraMap (MvPolynomial (Fin m) k) P.Ring (MvPolynomial.X i)))) =
            (1 : Algebra.LocalCompletion (Localization.AtPrime p)) ⊗ₜ[Localization.AtPrime p]
              KaehlerDifferential.D k (Localization.AtPrime p)
                (algebraMap P.Ring (Localization.AtPrime p)
                  (algebraMap (MvPolynomial (Fin m) k) P.Ring (MvPolynomial.X i)))) ∧
        Function.Injective (LinearMap.baseChange
          (Algebra.LocalCompletion (Localization.AtPrime p)) P.cotangentComplex) ∧
        Function.Exact (LinearMap.baseChange
          (Algebra.LocalCompletion (Localization.AtPrime p)) P.cotangentComplex)
          (LinearMap.baseChange (Algebra.LocalCompletion (Localization.AtPrime p)) P.toKaehler) ∧
        Function.Surjective (LinearMap.baseChange
          (Algebra.LocalCompletion (Localization.AtPrime p)) P.toKaehler) ∧
        Function.Injective δ ∧ Function.Exact δ qT ∧ Function.Surjective qT ∧
        (∃ b : Module.Basis (Fin (m - d)) (Algebra.LocalCompletion (Localization.AtPrime p))
            (Algebra.LocalCompletion (Localization.AtPrime p) ⊗[Localization.AtPrime p]
              P.Cotangent),
          ∀ j : Fin (m - d), ∃ z : P.ker, z.val = h j ∧
            b j = (1 : Algebra.LocalCompletion (Localization.AtPrime p)) ⊗ₜ[
              Localization.AtPrime p] Algebra.Extension.Cotangent.mk z) ∧
        (∃ b : Module.Basis (Fin m) (Algebra.LocalCompletion (Localization.AtPrime p))
            (Algebra.LocalCompletion (Localization.AtPrime p) ⊗[Localization.AtPrime p]
              P.CotangentSpace),
          ∀ i : Fin m, b i = (1 : Algebra.LocalCompletion (Localization.AtPrime p)) ⊗ₜ[
            Localization.AtPrime p] ((1 : Localization.AtPrime p) ⊗ₜ[P.Ring]
              KaehlerDifferential.D k P.Ring
                (algebraMap (MvPolynomial (Fin m) k) P.Ring (MvPolynomial.X i)))) ∧
        (∃ b : Module.Basis (Fin c) (Algebra.LocalCompletion (Localization.AtPrime p))
            (Algebra.Extension.ofSurjective π hπ).Cotangent,
          ∀ j : Fin c, ∃ z : (Algebra.Extension.ofSurjective π hπ).ker,
            z.val = g j ∧ b j = Algebra.Extension.Cotangent.mk z) ∧
        (∃ b : Module.Basis (Fin n) (Algebra.LocalCompletion (Localization.AtPrime p))
            (Fin n → Algebra.LocalCompletion (Localization.AtPrime p)),
          ∀ i : Fin n, b i = Pi.single i 1) ∧
        IsCompletedConormalSheafResolution
          (ModuleCat.ofHom (LinearMap.baseChange
            (Algebra.LocalCompletion (Localization.AtPrime p)) P.cotangentComplex))
          (ModuleCat.ofHom (LinearMap.baseChange
            (Algebra.LocalCompletion (Localization.AtPrime p)) P.toKaehler)) ∧
        IsCompletedConormalSheafResolution (ModuleCat.ofHom δ) (ModuleCat.ofHom qT) ∧
        ∀ (L : Type v) [Field L]
          [Algebra k L] [Algebra (Algebra.LocalCompletion (Localization.AtPrime p)) L]
          [IsScalarTower k (Algebra.LocalCompletion (Localization.AtPrime p)) L]
          [Algebra (Localization.AtPrime p) L]
          [IsScalarTower (Localization.AtPrime p)
            (Algebra.LocalCompletion (Localization.AtPrime p)) L],
          (∃ a : PrimeSpectrum (Localization.AtPrime p),
            a.asIdeal ∈ minimalPrimes (Localization.AtPrime p) ∧
            RingHom.ker (algebraMap (Localization.AtPrime p) L) = a.asIdeal ∧
            ∃ U : (Spec (.of S)).Opens,
              PrimeSpectrum.comap (algebraMap S (Localization.AtPrime p)) a ∈ U ∧
              SmoothOfRelativeDimension d
                (U.ι ≫ Spec.map (CommRingCat.ofHom (algebraMap k S)))) →
          Function.Injective (LinearMap.baseChange L
            (LinearMap.baseChange (Algebra.LocalCompletion (Localization.AtPrime p))
              P.cotangentComplex)) ∧
          Function.Exact (LinearMap.baseChange L
            (LinearMap.baseChange (Algebra.LocalCompletion (Localization.AtPrime p))
              P.cotangentComplex))
            ((TensorProduct.AlgebraTensorModule.cancelBaseChange (Localization.AtPrime p)
              (Algebra.LocalCompletion (Localization.AtPrime p)) L L
              (KaehlerDifferential k (Localization.AtPrime p))).toLinearMap.comp
                (LinearMap.baseChange L
                  (LinearMap.baseChange (Algebra.LocalCompletion (Localization.AtPrime p))
                    P.toKaehler))) ∧
          Function.Surjective
            ((TensorProduct.AlgebraTensorModule.cancelBaseChange (Localization.AtPrime p)
              (Algebra.LocalCompletion (Localization.AtPrime p)) L L
              (KaehlerDifferential k (Localization.AtPrime p))).toLinearMap.comp
                (LinearMap.baseChange L
                  (LinearMap.baseChange (Algebra.LocalCompletion (Localization.AtPrime p))
                    P.toKaehler))) ∧
          Function.Injective (LinearMap.baseChange L δ) ∧
          Function.Exact (LinearMap.baseChange L δ)
            ((TensorProduct.AlgebraTensorModule.cancelBaseChange (Localization.AtPrime p)
              (Algebra.LocalCompletion (Localization.AtPrime p)) L L
              (KaehlerDifferential k (Localization.AtPrime p))).toLinearMap.comp
                (LinearMap.baseChange L qT)) ∧
          Function.Surjective
            ((TensorProduct.AlgebraTensorModule.cancelBaseChange (Localization.AtPrime p)
              (Algebra.LocalCompletion (Localization.AtPrime p)) L L
              (KaehlerDifferential k (Localization.AtPrime p))).toLinearMap.comp
                (LinearMap.baseChange L qT)) ∧
          FiniteDimensional L (L ⊗[Localization.AtPrime p]
            KaehlerDifferential k (Localization.AtPrime p)) ∧
          Module.finrank L (L ⊗[Localization.AtPrime p]
            KaehlerDifferential k (Localization.AtPrime p)) = d := by
  sorry

end AlgebraicGeometry
