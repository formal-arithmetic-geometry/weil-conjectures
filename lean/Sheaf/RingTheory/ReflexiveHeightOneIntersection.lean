module

public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Ideal.Height
import WeilConjectures.RingTheory.NormalDomainPrincipalQuotientAssociatedHeight
import WeilConjectures.RingTheory.InjectivePiLocalizationAssociatedPrimes
import Mathlib.RingTheory.Noetherian.Basic
import Sheaf.LinearAlgebra.Dual.TorsionFreeBidualInjective
import Mathlib.RingTheory.Flat.Localization
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Localization.AtPrime.Basic
import WeilConjectures.AlgebraicGeometry.Regular
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.LinearAlgebra.FreeModule.PID

/-!
# Reflexivity and the intersection of height-one localizations

Source: Stacks Project, More on Algebra, Tag 0AVB, equivalence of (1) and (3)
(blueprint: lem-per-reflexive-height-one-intersection-criterion).
-/

@[expose] public section

universe u v

namespace Module

/-- A finite module over a Noetherian normal domain is reflexive exactly when it is
 torsion free and equals the intersection of its height-one localizations in its generic
 fibre. Source: Stacks Project, More on Algebra, Tag 0AVB, equivalence of (1) and (3)
(blueprint: lem-per-reflexive-height-one-intersection-criterion).

The common ambient module is `FractionRing A ⊗[A] M`. The equivalence
`LocalizedModule.equivTensorProduct` sends `m/s` to `(1/s) ⊗ m`.
`LocalizedModule.liftOfLE` sends each prime-local fraction `m/s` to the same generic
fraction. Thus the two ranges are precisely the images specified in the node.
In a domain, height one means a nonzero prime with no prime strictly between zero and it.
The infimum over no such primes is the whole generic fibre.

Proof, following the seven steps of the node:
1. If `a/b` belongs to all height-one local rings, every associated prime of `A/bA`
   has height one by `lem-weil-pbc-normal-domain-principal-quotient-associated-height`.
   At such a prime write `a/b = c/s`, with `s` outside the prime. Then `sa = bc`.
   The associated-prime zero test of
   `lem-weil-pbc-module-injects-localizations-associated-primes` gives `a ∈ bA`.
   Hence `A` is the intersection of its height-one local rings, including an empty one.
2. Evaluate functionals on a finite generating family to embed `M*` into a finite power
   of `A`; `lem-weil-pbc-noetherian-submodule-finite` makes `M*` finite. The bidual is
   torsion free because `A` is a domain. By `lem-per-torsion-free-bidual-injective`,
   evaluation is injective exactly when `M` is torsion free. The zero criterion of
   `def-weil-pbc-module-localization` then embeds `M` and its prime localizations in
   the generic fibre whenever `M` is torsion free.
3. Use `lem-weil-pbc-localization-tensor-over-base` to identify base change with
   localization. Localization is flat by `lem-weil-pbc-localization-flat`.
   Apply `lem-weil-pbc-flat-base-change-hom-finitely-presented` twice, to `M` and `M*`.
   This identifies the localized dual and bidual with the local dual and bidual.
   The formulas `φ/s : m/t ↦ φ(m)/(st)` and `z/s : φ/t ↦ z(φ)/(st)` show that
   evaluation commutes with localization and passage to the fraction field.
4. For a finite free module with basis `eᵢ` and coordinate functionals `εᵢ`, evaluation
   has inverse `z ↦ ∑ᵢ z(εᵢ)eᵢ`, including the empty basis. The generic fibre has a
   finite basis by `lem-per-division-ring-finite-basis`. Its evaluation is therefore
   invertible. Since the bidual is torsion free, step 3 embeds it in the generic fibre,
   carrying evaluation of `m` to `m/1`.
5. If `M` is reflexive and `x` is in every height-one localization, every functional on
   `M` takes `x` into every height-one local ring, hence into `A` by step 1. These values
   define an element of the bidual whose generic image is `x`. Reflexivity supplies
   `m` mapping to it, so `x = m/1`. The opposite inclusion comes from localization.
6. For a height-one prime, the local ring is Noetherian by
   `lem-weil-pbc-localization-noetherian`, normal by
   `lem-weil-pbc-localization-normal-domain`, and local by
   `def-weil-pbc-localization-at-prime`. The chain description in
   `lem-weil-pbc-localization-dimension-chains-below-prime` makes its dimension one.
   Thus `lem-sc-normal-dim1-dvr` gives a DVR (`def-sc-discrete-valuation-ring`).
   The prime localization of `M` is finite and torsion free by the fractions criterion,
   so `lem-sc-dvr-fg-torsionfree-free` makes it finite free. Its evaluation is invertible.
7. Conversely assume torsion freeness and the intersection equality. The generic image
   of an element of the bidual lies in every prime localization by steps 3 and 6.
   The intersection condition therefore supplies an element of `M` with that image.
   Injectivity of the bidual's generic map identifies its evaluation with the original
   bidual element. Evaluation is thus surjective, and is injective by step 2.
   If there are no height-one primes, the intersection hypothesis says that `M` already
   equals the generic fibre, and the same reasoning applies without local conditions. -/
theorem isReflexive_iff_isTorsionFree_and_heightOne_intersection
    (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    (M : Type v) [AddCommGroup M] [Module A M] [Module.Finite A M] :
    Module.IsReflexive A M ↔ Module.IsTorsionFree A M ∧
      LinearMap.range
        (LinearMap.comp
          ((LocalizedModule.equivTensorProduct (nonZeroDivisors A) M).toLinearMap.restrictScalars A)
          (LocalizedModule.mkLinearMap (nonZeroDivisors A) M)) =
        ⨅ (p : PrimeSpectrum A) (_ : p.asIdeal.height = 1),
          LinearMap.range
            (LinearMap.comp
              (LinearMap.restrictScalars A
                (LocalizedModule.equivTensorProduct (nonZeroDivisors A) M).toLinearMap)
              (LocalizedModule.liftOfLE p.asIdeal.primeCompl (nonZeroDivisors A)
                p.asIdeal.primeCompl_le_nonZeroDivisors)) := by
  sorry

end Module
