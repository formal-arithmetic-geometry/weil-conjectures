/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q90
-/
module

public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.AdicCompletion.Completeness
import WeilConjectures.RingTheory.FiniteModuleComplete
import Sheaf.RingTheory.FiniteOverCompleteRing

/-!
# Completed differentials of a finite formal parameter map

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Exposé IV, 1.2.5 and 2.1.12,
pp. 49 and 52--53 (blueprint: lem-per-finite-formal-map-differential-cokernel).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace KaehlerDifferential

/-- Completed differentials for a supplied local finite formal parameter map.
The supplied map `φ` is encoded by the algebra structure on `B` over the power series ring;
`IsScalarTower` says that it is a `k`-algebra map. The existential right arrow `q` is specified
by completing the universal differential map: its composite with the completion inclusion
of the relative differential module is exactly `AdicCompletion.map` of that universal map.
Completeness of the relative module makes this specification unique. The first arrow is
written explicitly on coefficient tuples, so its range is precisely the span of the `dbᵢ`.

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Exposé IV, 1.2.5 and 2.1.12,
pp. 49 and 52--53 (blueprint: lem-per-finite-formal-map-differential-cokernel).

Proof:
1. Choose generators `xⱼ` of the maximal ideal by Noetherianity. Leibniz gives
   `δ(n^r) ⊆ n^(r-1)V` for every derivation and positive `r`. Using the coefficient
   field to lift residues, write `b = a + ∑ aⱼ xⱼ mod n²`. Thus the `dxⱼ` generate
   `Ω[B/k]/nΩ[B/k]`.
2. By lem-weil-pbc-module-completion-complete (Stacks 05GG), the completion is complete
   and its reduction modulo `n` is the preceding quotient. Topological Nakayama,
   lem-weil-pbc-finite-over-complete-ring (Stacks 031D), shows that the images of the
   `dxⱼ` generate the completion. Hence it is finite and the completion map is onto.
3. Finite power-series-module generators of `B` have relative differentials generating
   `Ω[B/R]`. This module is finite over `B`, hence complete by
   lem-weil-pbc-finite-module-complete-over-complete-noetherian (Stacks 00MA).
4. Complete the universal map `Ω[B/k] → Ω[B/R]` and invert the completion equivalence
   of its target, obtaining `q`. This is the displayed compatibility equation. Universal
   differential symbols give surjectivity. The `dbᵢ` map to zero. Quotient the completed
   module by their span to obtain a finite, complete and separated module `Q`.
5. The induced `k`-derivation into `Q` kills each `bᵢ`. Truncate a formal series in
   degree `m`; its tail is in `(T)^(m+1)`, hence maps into `n^(m+1)` by localness.
   The derivation estimate and separatedness show that the induced derivation kills
   every formal series, so it is an `R`-derivation. For `e = 0` all series are constant.
6. The universal property gives `Ω[B/R] → Q`, inverse to the map induced by `q`:
   check both composites on universal differential symbols, which generate since the
   completion map is onto. Thus the kernel of `q` is exactly the span of the `dbᵢ`,
   the image of the explicitly written first arrow. -/
theorem finite_formal_map_differential_cokernel
    (k : Type u) [Field k] (B : Type v) [CommRing B] [Algebra k B]
    [IsLocalRing B] [IsNoetherianRing B]
    [IsAdicComplete (IsLocalRing.maximalIdeal B) B]
    (hres : Function.Bijective
      ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal B)).comp (algebraMap k B)))
    (e : ℕ) [Algebra (MvPowerSeries (Fin e) k) B]
    [IsScalarTower k (MvPowerSeries (Fin e) k) B]
    [IsLocalHom (algebraMap (MvPowerSeries (Fin e) k) B)]
    [Module.Finite (MvPowerSeries (Fin e) k) B] :
    Module.Finite B
      (AdicCompletion (IsLocalRing.maximalIdeal B) (KaehlerDifferential k B)) ∧
    Module.Finite B (KaehlerDifferential (MvPowerSeries (Fin e) k) B) ∧
    IsAdicComplete (IsLocalRing.maximalIdeal B)
      (KaehlerDifferential (MvPowerSeries (Fin e) k) B) ∧
    ∃ q : AdicCompletion (IsLocalRing.maximalIdeal B) (KaehlerDifferential k B) →ₗ[B]
        KaehlerDifferential (MvPowerSeries (Fin e) k) B,
      (∀ z, AdicCompletion.of (IsLocalRing.maximalIdeal B)
          (KaehlerDifferential (MvPowerSeries (Fin e) k) B) (q z) =
        AdicCompletion.map (IsLocalRing.maximalIdeal B)
          (KaehlerDifferential.map k (MvPowerSeries (Fin e) k) B B) z) ∧
      Function.Exact
        (fun c : Fin e → B ↦ ∑ i, c i •
          AdicCompletion.of (IsLocalRing.maximalIdeal B) (KaehlerDifferential k B)
            (KaehlerDifferential.D k B
              (algebraMap (MvPowerSeries (Fin e) k) B (MvPowerSeries.X i)))) q ∧
      Function.Surjective q := by
  sorry

end KaehlerDifferential
