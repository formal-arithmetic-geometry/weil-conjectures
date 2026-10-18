/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N3
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.RingHom.Flat
import Sheaf.FieldTheory.FiniteExtensionTensorAlgebraicClosureReduced

/-!
# Descent of a geometric field stalk

Source: Stacks Project, Varieties, Tag 0384; Algebra, Tags 030W and 00FY;
Curves, Tag 0C4D, arbitrary-field descent paragraph
(blueprint: lem-trf-geometric-field-stalk-descent).
-/

@[expose] public section

universe u v w

open scoped TensorProduct

namespace Algebra

/-- A geometric field stalk of a finite type algebra descends to its finite separable
residue field. Source: Stacks Project, Varieties, Tag 0384; Algebra, Tags 030W and 00FY;
Curves, Tag 0C4D, arbitrary-field descent paragraph
(blueprint: lem-trf-geometric-field-stalk-descent).

The structural maps from `Ω` use the right tensor factor, `a ↦ 1 ⊗ a`.
Bijectivity of such a structural ring homomorphism is exactly identification with `Ω`
as an `Ω`-algebra. The final map is the residue map of `T_p`, followed by the canonical
identification of its residue field with `T / p`.

Proof:
1. The maximal quotient `F = T / p` is a field and remains finite type over `k`.
   Zariski's lemma (`lem-weil-pbc-zariski-lemma`) makes it finite dimensional.
2. The inclusion `T → T ⊗[k] Ω` is faithfully flat by
   `lem-weil-pbc-field-extension-base-change-faithfully-flat`. Surjectivity on spectra
   (`lem-weil-pbc-faithfully-flat-surjective-spectrum`) gives a prime over `p`.
3. For any such prime `q`, the quotient by `q` is a quotient of `F ⊗[k] Ω`.
   A finite `k`-basis of `F` tensored with `1` spans this tensor product over `Ω`.
   The quotient is a finite dimensional domain, hence a field by
   `lem-weil-pbc-finite-dimensional-domain-is-field`; therefore `q` is maximal.
4. Every element of this finite field extension of `Ω` satisfies a polynomial.
   Factor that polynomial using `lem-weil-alg-closed-linear-factorization`; evaluating
   shows the element is a scalar. Thus its structural map from `Ω` is bijective.
   Localizing this field gives the same field, hence also identifies `κ(q)` with `Ω`.
5. Put `A = T_p`, `B = (T ⊗[k] Ω)_q`. The induced map `A → B` is local. By
   `lem-weil-pbc-localization-flat`, `lem-weil-pbc-flat-ring-map-comp`, and
   `lem-weil-pbc-flat-over-localization`, it is flat. Then
   `lem-weil-pbc-flat-local-hom-faithfully-flat` makes it faithfully flat, and
   `lem-weil-pbc-faithfully-flat-ideal-contraction` applied to zero makes it injective.
6. If the structural map `Ω → B` is bijective, `B` is a field. Locality and
   injectivity imply the maximal ideal of `A` is zero. Its surjective residue map
   therefore is bijective, and the canonical residue identification gives `A ≅ F`.
7. For every field extension `H/Ω`, `B ⊗[Ω] H ≅ H` is reduced. Apply
   `lem-trf-geometric-reducedness-local-base-change` (Tags 0384 and 035W) to descend
   geometric reducedness to `A`. In particular `A ⊗[k] Ω`, hence `F ⊗[k] Ω`, is reduced.
8. Apply `lem-pc-finite-extension-tensor-algebraic-closure-reduced-separable` to `F/k`.
   Its conclusion is separability in the general field-extension sense. Finiteness
   implies algebraicity, so the transcendence basis is empty, and this is the
   separable algebraic extension `Algebra.IsSeparable k F` required here. -/
theorem geometric_field_stalk_descent
    (k : Type u) (Ω : Type v) (T : Type w)
    [Field k] [Field Ω] [CommRing T] [Algebra k Ω] [IsAlgClosure k Ω]
    [Algebra k T] [Algebra.FiniteType k T] (p : Ideal T) [p.IsMaximal] :
    Module.Finite k (T ⧸ p) ∧
      (∃ q : PrimeSpectrum (T ⊗[k] Ω),
        q.asIdeal.comap (algebraMap T (T ⊗[k] Ω)) = p) ∧
      (∀ q : PrimeSpectrum (T ⊗[k] Ω),
        q.asIdeal.comap (algebraMap T (T ⊗[k] Ω)) = p →
        q.asIdeal.IsMaximal ∧
          Function.Bijective
            ((algebraMap (T ⊗[k] Ω) q.asIdeal.ResidueField).comp
              (Algebra.TensorProduct.includeRight : Ω →ₐ[k] T ⊗[k] Ω).toRingHom)) ∧
      ((∃ q : PrimeSpectrum (T ⊗[k] Ω),
        q.asIdeal.comap (algebraMap T (T ⊗[k] Ω)) = p ∧
          Function.Bijective
            ((algebraMap (T ⊗[k] Ω) (Localization.AtPrime q.asIdeal)).comp
              (Algebra.TensorProduct.includeRight : Ω →ₐ[k] T ⊗[k] Ω).toRingHom)) →
        Function.Bijective
          ((IsLocalization.AtPrime.equivQuotMaximalIdeal p
            (Localization.AtPrime p)).symm.toRingHom.comp
            (IsLocalRing.residue (Localization.AtPrime p))) ∧
          Algebra.IsSeparable k (T ⧸ p)) := by
  sorry

end Algebra
