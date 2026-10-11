/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Mathlib.RingTheory.Localization.Free
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Spreading a prescribed residue basis

Source: Stacks Project, Algebra, proof of Tag 0GWM, with prescribed lifts;
Tags 00DV (8) and 05G8 establish the local isomorphism
(blueprint: lem-weil-pbc-prescribed-residue-basis-spreads).
-/

@[expose] public section

universe u v

open scoped TensorProduct

namespace Module.FinitePresentation

/-- A prescribed residue basis spreads when the prime localization is free of the same rank.
Source: Stacks Project, Algebra, proof of Tag 0GWM, adapted to prescribed lifts
(blueprint: lem-weil-pbc-prescribed-residue-basis-spreads).

Proof: (1) Define the map from `A^r` to `M` sending the standard vectors to `m i`.
Its localization has image the span of `m i / 1`
[def-weil-finitely-generated-module, def-weil-pbc-module-localization,
def-weil-pbc-free-module]. (2) Identify the residue base change with that of the localized
module [lem-weil-pbc-localization-tensor-product, def-weil-pbc-localization-at-prime,
def-weil-module-base-change]. Nakayama (Tag 00DV (8)) makes the localized map surjective
[lem-weil-pbc-nakayama-local-generators]. (3) A basis of the prime localization identifies
this map with a surjective endomorphism of a finite free module, hence an isomorphism by
Tag 05G8 [def-weil-pbc-free-module,
lem-weil-pbc-finite-module-surjective-endomorphism-bijective]. (4) Spread this isomorphism
to some `f` outside `p` using finite presentation of `M` and finiteness of `A^r`
[lem-weil-pbc-finite-to-finitely-presented-map-iso-at-prime-spreads]. (5) Identify the
localization of `A^r` at `f` with `A_f^r`; the resulting isomorphism sends each standard
vector to `m i / 1`, giving exactly the required basis
[def-weil-pbc-module-localization-away, def-weil-pbc-free-module]. -/
theorem exists_basis_away_of_prescribed_residue_basis
    {A : Type u} [CommRing A] {M : Type v} [AddCommGroup M] [Module A M]
    [Module.FinitePresentation A M] (p : Ideal A) [p.IsPrime] (r : ℕ) (m : Fin r → M)
    (hres : ∃ b : Module.Basis (Fin r) p.ResidueField (p.ResidueField ⊗[A] M),
      ∀ i : Fin r, b i = (1 : p.ResidueField) ⊗ₜ[A] m i)
    (hfree : Nonempty (Module.Basis (Fin r) (Localization.AtPrime p)
      (LocalizedModule p.primeCompl M))) :
    ∃ f : A, f ∉ p ∧
      ∃ b : Module.Basis (Fin r) (Localization.Away f) (LocalizedModule.Away f M),
        ∀ i : Fin r, b i = LocalizedModule.mkLinearMap (Submonoid.powers f) M (m i) := by
  sorry

end Module.FinitePresentation
