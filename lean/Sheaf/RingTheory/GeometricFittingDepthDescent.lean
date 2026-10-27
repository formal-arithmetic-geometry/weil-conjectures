/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q54
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Sheaf.RingTheory.PresentationFittingIdeal
public import WeilConjectures.RingTheory.Depth
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.RingTheory.Kaehler.TensorProduct
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Sheaf.RingTheory.GeometricFieldStalkDescent
import WeilConjectures.RingTheory.FlatLocalDepthFormula
import WeilConjectures.RingTheory.AdicCompletionNoetherian

/-!
# Descent of geometric Fitting and depth conditions

Source: Stacks Project, Curves, Tag 0C4D (lemma-nodal), arbitrary-field descent
paragraphs; Algebra, Tags 00RV, 00RT and 0337
(blueprint: lem-trf-geometric-fitting-depth-descent).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open scoped TensorProduct

namespace Algebra

/-- The geometric maximal first Fitting ideal and depth one descend to the original
local ring and its completion, with finite separable residue field and the canonical
residue isomorphism. Source: Stacks Project, Curves, Tag 0C4D (lemma-nodal),
arbitrary-field descent paragraphs; Algebra, Tags 00RV, 00RT and 0337
(blueprint: lem-trf-geometric-fitting-depth-descent).

The arbitrary generating surjections `π` and `ρ` compute the two first Fitting ideals
using `LinearMap.presentationFittingIdeal`. Their independence is precisely
`lem-trf-fitting-ideal-independence-base-change`. The right-factor algebra structure
on `S ⊗[k] Ω` is explicit in the type of `ρ`. The completion depth is written as ideal
depth for the extended maximal ideal; Tag 05GI identifies this with its maximal ideal.
The final equality characterizes the isomorphism as induced by the residue map.

Proof plan, following the nine steps of the node:
1. Differentiating algebra generators and using the additive and Leibniz relations
   (`def-weil-pbc-kahler-differentials`) proves finiteness of `Ω[S⁄k]`, even with no generators.
2. Differential base change (`lem-weil-pbc-kahler-differentials-base-change`) and
   `lem-trf-fitting-ideal-independence-base-change` identify the geometric ideal with
   the extension of `J`. Contraction along localization and then `hq` give `J ≤ p`.
3. `lem-trf-geometric-field-stalk-descent` gives finiteness of `S/p`, maximality of `q`,
   and the structural residue identification with `Ω`. Thus `B/J_B = Ω` by `hfit`.
4. Set `T = S/J`. Tensor right exactness (`lem-weil-pbc-tensor-right-exact`) identifies
   `T ⊗[k] Ω` with `(S ⊗[k] Ω)/JC`: the tensor image of `J` is exactly `JC`.
5. The quotient fraction maps identify its local ring at `q/JC` with `B/J_B`.
   Apply the conditional clause of `lem-trf-geometric-field-stalk-descent` to `T`,
   obtaining its residue isomorphism and separability of `S/p`.
6. The same fraction maps give `A/J_A = T_(p/J)`. Their composite is the residue map
   `s/u ↦ (s mod p)/(u mod p)`, hence its kernel is both `J_A` and the maximal ideal.
7. The structural residue identification embeds `S/p` in `Ω` and expresses `q` as
   the evaluation kernel. `lem-trf-separable-evaluation-local-base-change` gives a
   faithfully flat local map of Noetherian local rings `A → B` with closed fibre `Ω`.
8. A field has depth zero: the empty sequence is regular and a positive sequence
   in its zero maximal ideal starts with zero. Apply
   `lem-weil-pbc-flat-local-depth-formula` and `hdepth` to obtain depth one for `A`.
9. `lem-weil-pbc-local-completion-local-ring`,
   `lem-weil-pbc-adic-completion-noetherian` and
   `lem-weil-pbc-noetherian-completion-flat` give a flat local Noetherian completion
   with residue field `S/p`. Its depth is one by the same flat local depth formula.
-/
theorem geometric_fitting_depth_descent
    (k : Type u) (Ω : Type v) (S : Type w)
    [Field k] [Field Ω] [CommRing S] [Algebra k Ω] [IsAlgClosure k Ω]
    [Algebra k S] [Algebra.FiniteType k S]
    (p : Ideal S) [p.IsMaximal] (q : PrimeSpectrum (S ⊗[k] Ω))
    (hq : q.asIdeal.comap (algebraMap S (S ⊗[k] Ω)) = p)
    (d e : ℕ) (π : (Fin d → S) →ₗ[S] KaehlerDifferential k S)
    (hπ : Function.Surjective π)
    (ρ : (Fin e → S ⊗[k] Ω) →ₗ[S ⊗[k] Ω]
      @KaehlerDifferential Ω (S ⊗[k] Ω) _ _ Algebra.TensorProduct.rightAlgebra)
    (hρ : Function.Surjective ρ)
    (hfit : Ideal.map (algebraMap (S ⊗[k] Ω) (Localization.AtPrime q.asIdeal))
      (ρ.presentationFittingIdeal 1) = IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal))
    (hdepth : IsLocalRing.depth (R := Localization.AtPrime q.asIdeal)
      (Localization.AtPrime q.asIdeal) = 1) :
    Module.Finite k (S ⧸ p) ∧ Algebra.IsSeparable k (S ⧸ p) ∧
      Ideal.map (algebraMap S (Localization.AtPrime p)) (π.presentationFittingIdeal 1) =
        IsLocalRing.maximalIdeal (Localization.AtPrime p) ∧
      IsLocalRing.depth (R := Localization.AtPrime p) (Localization.AtPrime p) = 1 ∧
      (Ideal.map
        (algebraMap (Localization.AtPrime p)
          (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime p))
            (Localization.AtPrime p)))
        (IsLocalRing.maximalIdeal (Localization.AtPrime p))).depth
          (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime p))
            (Localization.AtPrime p)) = 1 ∧
      ∃ E : (Localization.AtPrime p ⧸
          Ideal.map (algebraMap S (Localization.AtPrime p)) (π.presentationFittingIdeal 1)) ≃+*
            (S ⧸ p),
        E.toRingHom.comp
          (Ideal.Quotient.mk
            (Ideal.map (algebraMap S (Localization.AtPrime p)) (π.presentationFittingIdeal 1))) =
          (IsLocalization.AtPrime.equivQuotMaximalIdeal p
            (Localization.AtPrime p)).symm.toRingHom.comp
              (IsLocalRing.residue (Localization.AtPrime p)) := by
  sorry

end Algebra
