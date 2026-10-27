/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q41
-/
module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.LinearAlgebra.Basis.Defs
import Sheaf.RingTheory.LocalGeneratingTuples
import Sheaf.RingTheory.RegularSequenceGradedPolynomial
import Sheaf.RingTheory.QuasiRegularNoetherianLocal

/-!
# Lifting regular generators through an isomorphism of generator spaces

Source: Stacks Project, More on Algebra, Tag 066A (part (1)), and Algebra,
Tags 00LN, 061S and 00DV; the specified generator-space lifting consequence
(blueprint: lem-trf-lift-regular-generators-through-fibre).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace Ideal

/-- A canonical isomorphism of generator spaces lifts every residue basis to generators
whose images are regular. The first conclusion expresses the basis of the target generator
space by transporting a basis through `β`; its scalar field is identified by `σ`.
The equations on `σ` and `β` specify the maps induced by `c` on every representative.

Source: Stacks Project, More on Algebra, Tag 066A (lemma-independence-of-generators),
part (1), together with Algebra Tags 00LN, 061S and 00DV
(blueprint: lem-trf-lift-regular-generators-through-fibre).

Proof:
1. Apply lem-trf-regular-ideal-residue-basis-prescribed-generator over `S` to `y`.
   Its residue classes are a basis over `S/n`, hence over `R/m` through `σ`.
2. Transport this basis back through `β` and choose representatives in `I`.
   This gives a basis with `r` entries and lifts. Now fix any such basis and any lifts.
3. Apply lem-weil-pbc-nakayama-local-generators to the finite module `I` over `R`.
   The lifts generate `I`, so their images generate `I.map c`. They belong to `n`
   since `I` lies in `m` and `c` is local.
4. Apply lem-pur-local-generating-tuples over `S` to the two generating tuples of
   `I.map c`. An invertible matrix changes `y` into the tuple of images of the lifts.
   Reducing that matrix and its inverse modulo `I.map c` still gives inverse matrices.
5. By lem-pur-regular-sequence-graded-polynomial the canonical polynomial map to the
   associated graded ring for `y` is an isomorphism. The invertible linear substitution
   from step 4 identifies it with the canonical map for the new tuple, on both
   coefficients and variables. Hence the latter map is also an isomorphism.
6. Apply lem-pur-quasi-regular-noetherian-local to the new tuple to obtain regularity.
   Its generation property was established in step 3. If `r = 0`, the original tuple
   gives `I.map c = 0`; then `β` and Nakayama give `I = 0`. Empty bases and lifts exist,
   and the empty target sequence is regular since `S` is nonzero. -/
theorem lift_regular_generators_through_fibre
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [IsNoetherianRing R] [IsNoetherianRing S]
    [IsLocalRing R] [IsLocalRing S] (c : R →+* S) [IsLocalHom c]
    (σ : (R ⧸ IsLocalRing.maximalIdeal R) ≃+* (S ⧸ IsLocalRing.maximalIdeal S))
    (hσ : ∀ a : R, σ (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) a) =
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal S) (c a))
    (I : Ideal R) (hI : I ≤ IsLocalRing.maximalIdeal R) (hIfg : I.FG)
    (β : (I ⧸ (IsLocalRing.maximalIdeal R • (⊤ : Submodule R I))) →ₛₗ[σ.toRingHom]
      ((I.map c) ⧸ (IsLocalRing.maximalIdeal S • (⊤ : Submodule S (I.map c)))))
    (hβbij : Function.Bijective β)
    (hβ : ∀ a : I, β (Submodule.Quotient.mk a) =
      Submodule.Quotient.mk (⟨c a, Ideal.mem_map_of_mem c a.property⟩ : I.map c))
    (r : ℕ) (y : Fin r → I.map c)
    (hy : ∀ i : Fin r, (y i).val ∈ IsLocalRing.maximalIdeal S)
    (hyreg : RingTheory.Sequence.IsRegular S (List.ofFn (fun i ↦ (y i).val)))
    (hygen : Ideal.span (Set.range (fun i ↦ (y i).val)) = I.map c) :
    (∃ b : Module.Basis (Fin r) (R ⧸ IsLocalRing.maximalIdeal R)
        (I ⧸ (IsLocalRing.maximalIdeal R • (⊤ : Submodule R I))),
      ∀ i : Fin r, β (b i) = Submodule.Quotient.mk (y i)) ∧
    (∀ (b : Module.Basis (Fin r) (R ⧸ IsLocalRing.maximalIdeal R)
          (I ⧸ (IsLocalRing.maximalIdeal R • (⊤ : Submodule R I))))
        (f : Fin r → I),
      (∀ i : Fin r, Submodule.Quotient.mk (f i) = b i) →
      Ideal.span (Set.range (fun i ↦ (f i).val)) = I ∧
      RingTheory.Sequence.IsRegular S (List.ofFn (fun i ↦ c (f i))) ∧
      Ideal.span (Set.range (fun i ↦ c (f i))) = I.map c) ∧
    (∃ (b : Module.Basis (Fin r) (R ⧸ IsLocalRing.maximalIdeal R)
          (I ⧸ (IsLocalRing.maximalIdeal R • (⊤ : Submodule R I))))
        (f : Fin r → I),
      ∀ i : Fin r, Submodule.Quotient.mk (f i) = b i) := by
  sorry

end Ideal
