/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Sheaf.RingTheory.CoverModuleExact

/-!
# Exactness of the formal glueing complex

Source: Stacks Project, More on Algebra, Lemma 05EK and equation `glueing-complex`
(blueprint: lem-weil-pbc-formal-glueing-complex-exact).
-/

@[expose] public section

universe u v w

open scoped TensorProduct

namespace RingTheory

/-- The formal glueing complex is exact for a flat map inducing an isomorphism modulo
`I = (f₁, …, fₜ)`. Scalar extension is written `S ⊗[R] M`, as in the recorded dependency
`def-weil-module-base-change`; tensor commutativity identifies it with `M ⊗[R] S`.
The map `η` is `m ↦ 1 ⊗ m`. Its localized map renders `mᵢ ⊗ 1` in `(M ⊗ S)_fᵢ`.
The canonical overlap maps `ρ` are the universal lifts of `m ↦ m/1`.
Source: Stacks Project, More on Algebra, Lemma 05EK and equation `glueing-complex`
(blueprint: lem-weil-pbc-formal-glueing-complex-exact).

Proof (the node's eight steps, following the second computational proof of 05EK):
1. A module element vanishes in every localization at `fᵢ` precisely when some power
   of `I` annihilates it. Fraction equality gives individual annihilating powers;
   the pigeonhole argument for monomials in the generators gives an annihilating
   power of `I`. Conversely, `Iⁿ x = 0` implies `fᵢⁿ x = 0` for every `i`.
2. Localize `η`. By `lem-weil-pbc-localization-module-tensor`, its fraction formula
   agrees with tensoring with 1 under the canonical localization/base-change comparison.
3. Each first component of `β (α m)` is `(1 ⊗ m)/1 - (1 ⊗ m)/1`; each overlap
   component is `m/1 - m/1`. Thus the image of `α` lies in the kernel of `β`.
4. If `α m = 0`, step 1 makes `m` I-power torsion and `η m = 0`. Injectivity on
   torsion from `lem-weil-pbc-torsion-submodule-flat-base-change-iso` gives `m = 0`.
5. For a kernel element `(m', (sᵢ))`, choose common denominators `sᵢ = mᵢ/fᵢⁿ`.
   Enlarge `n` and rescale the numerators to obtain identities in the original modules:
   `fᵢⁿ m' = η mᵢ` and `fⱼⁿ mᵢ = fᵢⁿ mⱼ`. Put `gᵢ = fᵢⁿ`.
6. For any module `P`, let `Z(P)` consist of families with `gⱼ xᵢ = gᵢ xⱼ`, and
   let `δ(x) = (gᵢ x)`. In `H(P) = Z(P)/δ(P)`, `gₖ (xᵢ) = δ(xₖ)`, so all
   generators `gₖ` annihilate `H(P)`. A power of `I` lies in their ideal; hence
   `H(P)` is I-power torsion. Let `ξ` be the class of `(mᵢ)` in `H(M)`.
7. Flat tensor exactness (`lem-weil-pbc-flat-tensor-exact`) and commutation with finite
   products (`lem-weil-pbc-tensor-finite-product`) embed `Z(M) ⊗ S` into `(M ⊗ S)ᵗ`.
   Step 5 identifies the image of `(mᵢ) ⊗ 1` with the image of `δ ⊗ 1` applied to
   `m'`. Thus `ξ ⊗ 1 = 0`. The torsion base-change isomorphism
   `lem-weil-pbc-torsion-module-flat-base-change-iso` gives `ξ = 0`; choose `m` with
   `mᵢ = fᵢⁿ m` for all `i`.
8. Subtract `α m`. The remainder is `(m'', 0)` with `m''` I-power torsion, by step 1.
   The torsion-submodule base-change isomorphism gives I-power torsion `x` with
   `η x = m''`; its localizations vanish. The remainder is therefore `α x`, so the
   original kernel element is `α (m + x)`. Together with steps 3 and 4 this proves
   both injectivity and equality of kernel and image. For `t = 0`, `I = 0` and the
   quotient hypothesis makes `φ` an isomorphism, giving both clauses directly. -/
theorem formalGlueingComplexExact {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] (φ : R →+* S) (hflat : φ.Flat)
    (t : ℕ) (f : Fin t → R)
    (hquot : Function.Bijective
      (Ideal.quotientMap ((Ideal.span (Set.range f)).map φ) φ Ideal.le_comap_map))
    (M : Type w) [AddCommGroup M] [Module R M] :
    letI : Algebra R S := φ.toAlgebra
    let η : M →ₗ[R] S ⊗[R] M := TensorProduct.mk R S M 1
    let ρ := fun (a h : R) (ha : a ∣ h) ↦
      IsLocalizedModule.lift (Submonoid.powers a)
        (LocalizedModule.mkLinearMap (Submonoid.powers a) M)
        (LocalizedModule.mkLinearMap (Submonoid.powers h) M)
        (localizationAway_map_units_of_dvd (M := M) a h ha)
    let α : M → (S ⊗[R] M) × (∀ i : Fin t, LocalizedModule.Away (f i) M) :=
      fun m ↦ (η m, fun i ↦ LocalizedModule.mkLinearMap (Submonoid.powers (f i)) M m)
    let β : (S ⊗[R] M) × (∀ i : Fin t, LocalizedModule.Away (f i) M) →
        (∀ i : Fin t, LocalizedModule.Away (f i) (S ⊗[R] M)) ×
          (∀ i j : Fin t, LocalizedModule.Away (f i * f j) M) :=
      fun p ↦
        (fun i ↦ LocalizedModule.mkLinearMap (Submonoid.powers (f i)) (S ⊗[R] M) p.1 -
          IsLocalizedModule.map (Submonoid.powers (f i))
            (LocalizedModule.mkLinearMap (Submonoid.powers (f i)) M)
            (LocalizedModule.mkLinearMap (Submonoid.powers (f i)) (S ⊗[R] M)) η (p.2 i),
         fun i j ↦ ρ (f i) (f i * f j) (dvd_mul_right (f i) (f j)) (p.2 i) -
          ρ (f j) (f i * f j) (dvd_mul_left (f j) (f i)) (p.2 j))
    Function.Injective α ∧ Function.Exact α β := by
  sorry

end RingTheory
