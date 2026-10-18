/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q85
-/
module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
import Sheaf.RingTheory.ParameterIdealFormalNormalization
import Sheaf.RingTheory.PowerSeriesRingSubfields
import Sheaf.RingTheory.PBasisComplementMonomialBasis
import WeilConjectures.FieldTheory.PBasisDifferentialsBasis
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Etale.Kaehler

/-!
# Stabilized generic rank of completed differentials over cofinite coefficient subfields

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose IV, 2.1.5--2.1.6,
printed pages 50--51, equations (2.a) and (2.b), and Proposition 1.2.4
(blueprint: lem-per-cofinite-pbasis-completed-generic-rank).
-/

@[expose] public section

set_option autoImplicit false

universe u v w z

open scoped TensorProduct

namespace RingTheory

/-- The completed differentials over a cofinite coefficient subfield have generic rank
`d + J.card` once the finite deleted set `J` contains a fixed finite exceptional set.
The coefficient field is represented by its algebra map into `A`; its composite with
reduction to the residue field is bijective. The algebra on each `F J` is explicitly the
composite of its subfield inclusion with this fixed coefficient map by `hcomp`.
The tensor factors are reversed using the canonical symmetry of tensor products.

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose IV, 2.1.5--2.1.6,
printed pages 50--51, equations (2.a) and (2.b), using Proposition 1.2.4;
EGA 0_IV, 21.9.4 for the completed differential comparison
(blueprint: lem-per-cofinite-pbasis-completed-generic-rank).

Proof:
1. Choose a system of `d` parameters by
   lem-weil-pbc-noetherian-local-system-of-parameters. Apply case (a) of
   lem-per-parameter-ideal-formal-normalization to the given coefficient field.
   A domain is reduced and equidimensional, so this gives a finite injective map
   `R = k[[t_1,...,t_d]]` into `A` and a finite fraction field extension `L/K`.
2. Put `R_J = F J[[t_1^p,...,t_d^p]]` and let `K_J` be its fraction field in `K`.
   lem-weil-pbc-power-series-ring-subfields gives finiteness of `R` over `R_J`,
   containment of `K^p` in each `K_J`, their intersection `K^p`, and the reverse
   directedness under unions. Localization gives finiteness of `K/K_J`: the finite
   dimensional localization is a domain over a field and hence itself a field.
3. By lem-weil-pbc-p-basis-complement-monomial-basis, the bounded coefficient
   monomials on `J` form an `F J`-basis of `k`. Expand series coefficientwise and group
   variable exponents modulo `p`. The coefficient monomials times the bounded parameter
   monomials form an `R_J`-basis of `R` and a `K_J`-basis of `K`; denominators are
   cleared using `f/g = f*g^(p-1)/g^p` and `g^p` in `R_J`. Thus the deleted coefficient
   elements together with the parameters are a relative p-basis. Apply
   lem-weil-pbc-p-basis-differentials-basis to obtain dimension `d + J.card`.
4. Apply lem-per-cofinite-subfields-finite-extension-differential-rank to `L/K`
   and the nonempty family `K_J`. It supplies `J0` such that, whenever `J0` is contained
   in `J`, the differential dimensions of `L/K_J` and `K/K_J` coincide.
5. The finite coefficient basis also makes `R` finite free over `F J[[t_1,...,t_d]]`.
   Consequently `A` is finite over this ring; its evaluation is local and continuous.
   lem-per-pth-power-series-completed-differential-comparison identifies the maximal
   ideal completion of the differentials of `A/F J` with the differentials of `A/R_J`.
6. Localize using lem-weil-pbc-kahler-differentials-localization. Derivations on `L`
   killing `R_J` kill its fraction field `K_J` by the inverse rule; universality of
   def-weil-pbc-kahler-differentials identifies these with the differentials of `L/K_J`.
   Taking dimensions and applying steps 3 and 4 gives the asserted rank for every
   finite `J` containing `J0`. -/
theorem cofinitePBasisCompletedGenericRank
    (A : Type u) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (p : ℕ) [Fact p.Prime] [CharP A p]
    (d : ℕ) (hd : 1 ≤ d) (hdim : ringKrullDim A = d)
    (k : Type v) [Field k] [CharP k p] [Algebra k A]
    (hres : Function.Bijective ((IsLocalRing.residue A).comp (algebraMap k A)))
    (E : Type w) (β : E → k)
    (hpb : ∃ b : Module.Basis {a : E →₀ ℕ // ∀ i : E, a i < p}
      (Subfield.closure (Set.range (fun x : k ↦ x ^ p))) k,
      ∀ a, b a = (a : E →₀ ℕ).prod (fun i e ↦ β i ^ e))
    (F : Finset E → Subfield k)
    (hF : ∀ J, F J = Subfield.closure
      (Set.range (fun x : k ↦ x ^ p) ∪ {x : k | ∃ i : E, i ∉ J ∧ β i = x}))
    [∀ J : Finset E, Algebra (F J) A]
    (hcomp : ∀ (J : Finset E) (x : F J), algebraMap (F J) A x = algebraMap k A (x : k))
    (L : Type z) [Field L] [Algebra A L] [IsFractionRing A L] :
    ∃ J0 : Finset E, ∀ J : Finset E, J0 ⊆ J →
      Module.rank L (L ⊗[A]
        AdicCompletion (IsLocalRing.maximalIdeal A) (KaehlerDifferential (F J) A)) =
        (d + J.card : ℕ) := by
  sorry

end RingTheory
