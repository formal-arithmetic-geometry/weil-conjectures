/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q75
-/
module

public import Sheaf.AlgebraicGeometry.PureDimension
public import Sheaf.RingTheory.FormalLocalPresentation
public import Sheaf.RingTheory.CompletedJacobianPresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.LinearAlgebra.Dimension.Basic
public import WeilConjectures.Mathlib.Topology.KrullDimension
import WeilConjectures.AlgebraicGeometry.Morphisms.SlicingFlat
import WeilConjectures.AlgebraicGeometry.EquidimensionalOpenLocalDimension
import Sheaf.AlgebraicGeometry.SmoothDifferentialsFreeRankFibreDimension
import WeilConjectures.Mathlib.RingTheory.Nilpotent.GeometricallyReduced
import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.RingTheory.KrullDimension.Zero
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.Spectrum.Prime.Noetherian

/-! # Generic ranks of completed differentials

Source: Stacks Project, varieties.tex, Tags 056V and 0A21; algebra.tex, Tags 00HS and
00EU; morphisms.tex, Tag 02G1. This is the generic-rank input to the completed conormal
comparison (blueprint: lem-trf-generic-completed-differential-rank).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u w

open scoped TensorProduct
open AlgebraicGeometry CategoryTheory

namespace Algebra

/-- Generic differentials have rank equal to the pure dimension, before and after completion.
`Module.rank` over the asserted fields is vector-space dimension, so its equality to the
finite cardinal `d` also asserts finite dimensionality. Tensor factors are written with the
scalar ring first, using the canonical symmetry. `topologicalKrullDimAt` is the dimension
of open neighbourhoods, not the dimension of the generic local ring.

The last clause quantifies over a map from the completion. Its restriction to the local
ring is encoded by the `A`-algebra structure on `L`; the scalar tower makes this a map over
`k`. The localization algebra map in the factorization hypothesis necessarily agrees with
this restriction on `A`, so it expresses actual factorization through the generic point.

Source: Stacks Project, varieties.tex, Tags 056V (lemma-geometrically-reduced-dense-smooth-open)
and 0A21 (lemma-dimension-locally-algebraic), (3), (5); algebra.tex, Tags 00HS and 00EU;
morphisms.tex, Tag 02G1 (blueprint: lem-trf-generic-completed-differential-rank).

Proof:
1. Finite type over the Noetherian field makes `S` Noetherian, with finitely many components
   (lem-wf-affine-noetherian-components), and finitely presented
   (lem-weil-pbc-finite-type-noetherian-finite-presentation). Perfectness and reducedness
   give reducedness after every field extension (lem-weil-pbc-perfect-reduced-tensor).
   Apply lem-weil-pbc-affine-scheme-reduced-iff to interpret this on spectra.
2. The smooth open is dense (lem-pur-geometrically-reduced-dense-smooth-open). Removing all
   other components gives a nonempty open in each component; density forces it to meet the
   smooth locus, hence the component's generic point is smooth. Pure dimension and
   lem-sbc-equidimensional-open-local-dimension give local topological dimension `d`.
3. Primes of `A = S_m` correspond to primes of `S` contained in `m`
   (lem-weil-pbc-primes-of-localization), and preserve minimality. Localization preserves
   reducedness (lem-weil-pbc-localization-preserves-reduced); localization at a minimal
   prime is a field (lem-weil-pbc-minimal-prime-reduced-localization-field). Successive
   fractions identify it with `S_q`. On a smooth affine neighbourhood, differentials are
   free of rank `d` (lem-weil-pbc-smooth-differentials-free-rank-fibre-dimension).
   The affine stalk localization (lem-weil-pbc-affine-open-stalk-localization) and
   localization of differentials (lem-weil-pbc-kahler-differentials-localization) identify
   its tensor with `N` tensor the generic local field. Thus the latter has dimension `d`.
4. Localization is Noetherian (lem-weil-pbc-localization-noetherian), so completion is flat
   (lem-weil-pbc-noetherian-completion-flat). Going down (lem-sc-flat-going-down) contracts
   every minimal prime of the completion to a minimal prime of `A`. Reducedness makes the
   completed generic localization a field. Fractions give the displayed local ring map;
   its kernel is a proper ideal of a field, hence zero.
5. Tensor associativity identifies the localized completed differential module with
   `N` tensor the completed generic field and with the scalar extension of the generic
   vector space from step 3. The balancing maps send `(n tensor r) tensor e` to
   `n tensor (r * e)`, with inverse `n tensor e` mapped to `(n tensor 1) tensor e`.
   Extending the finite basis from step 3 gives dimension `d`, including `d = 0`
   (def-weil-module-base-change).
6. For the last clause, the factorization gives an action through the generic local field
   from step 3. The same tensor maps and extension of its basis give dimension `d` over
   `L`. Neither injectivity of the map from the completion nor a claim about algebraic
   differentials of the completion is used (def-weil-module-base-change).
-/
theorem generic_completed_differential_rank
    {k S : Type u} [Field k] [PerfectField k] [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] [IsReduced S]
    (d : ℕ) (hpure : (Spec (CommRingCat.of S)).IsPureDimension d)
    (m : Ideal S) [m.IsMaximal] (hresidue : Nonempty (m.ResidueField ≃ₐ[k] k))
    [IsReduced (LocalCompletion (Localization.AtPrime m))] :
    (∀ (K : Type (max u w)) [Field K] [Algebra k K], IsReduced (K ⊗[k] S)) ∧
    (∀ q : PrimeSpectrum S, q.asIdeal ∈ minimalPrimes S →
      (∃ U : (Spec (CommRingCat.of S)).Opens, q ∈ U ∧
        AlgebraicGeometry.Smooth (U.ι ≫ Spec.map (CommRingCat.ofHom (algebraMap k S)))) ∧
      topologicalKrullDimAt q = (d : WithBot ℕ∞)) ∧
    (∀ a : PrimeSpectrum (Localization.AtPrime m),
      a.asIdeal ∈ minimalPrimes (Localization.AtPrime m) →
      IsField (Localization.AtPrime a.asIdeal) ∧
      Module.rank (Localization.AtPrime a.asIdeal)
        ((Localization.AtPrime a.asIdeal) ⊗[Localization.AtPrime m]
          KaehlerDifferential k (Localization.AtPrime m)) = (d : Cardinal)) ∧
    (∀ p : PrimeSpectrum (LocalCompletion (Localization.AtPrime m)),
      p.asIdeal ∈ minimalPrimes (LocalCompletion (Localization.AtPrime m)) →
      p.asIdeal.comap (algebraMap (Localization.AtPrime m)
        (LocalCompletion (Localization.AtPrime m))) ∈ minimalPrimes (Localization.AtPrime m) ∧
      IsField (Localization.AtPrime p.asIdeal) ∧
      Function.Injective (Localization.localRingHom
        (p.asIdeal.comap (algebraMap (Localization.AtPrime m)
          (LocalCompletion (Localization.AtPrime m)))) p.asIdeal
        (algebraMap (Localization.AtPrime m) (LocalCompletion (Localization.AtPrime m))) rfl) ∧
      Module.rank (Localization.AtPrime p.asIdeal)
        ((Localization.AtPrime p.asIdeal) ⊗[LocalCompletion (Localization.AtPrime m)]
          CompletedDifferentials k (Localization.AtPrime m)) = (d : Cardinal)) ∧
    (∀ (L : Type (max u w)) [Field L] [Algebra k L]
      [Algebra (Localization.AtPrime m) L] [IsScalarTower k (Localization.AtPrime m) L]
      (_θ : LocalCompletion (Localization.AtPrime m) →ₐ[Localization.AtPrime m] L),
      (∃ a : PrimeSpectrum (Localization.AtPrime m),
        a.asIdeal ∈ minimalPrimes (Localization.AtPrime m) ∧
        (∃ U : (Spec (CommRingCat.of S)).Opens,
          PrimeSpectrum.comap (algebraMap S (Localization.AtPrime m)) a ∈ U ∧
          AlgebraicGeometry.Smooth (U.ι ≫ Spec.map (CommRingCat.ofHom (algebraMap k S)))) ∧
        topologicalKrullDimAt
          (PrimeSpectrum.comap (algebraMap S (Localization.AtPrime m)) a) =
          (d : WithBot ℕ∞) ∧
        Nonempty (Localization.AtPrime a.asIdeal →ₐ[Localization.AtPrime m] L)) →
      Module.rank L (L ⊗[Localization.AtPrime m]
        KaehlerDifferential k (Localization.AtPrime m)) = (d : Cardinal)) := by
  sorry

end Algebra
