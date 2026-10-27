/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q129
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.Localization.Away.Basic
public import Sheaf.RingTheory.ModuleSurjectivityFieldExtensionNeighbourhood

/-!
# Finite type near a contracted prime after a field extension

Source: Stacks Project, Varieties, Tag 0C4Y (1), auxiliary consequence using the
coefficient-subalgebra argument of Algebra, Tag 00QP. This is an agent-written
adaptation under the explicitly assumed module-neighbourhood principle, not a
verbatim Stacks lemma (blueprint: lem-sc-finite-type-field-extension-neighbourhood).
-/

@[expose] public section

universe u v w x y z

namespace RingHom

open scoped TensorProduct

/-- Finite type on one principal open after field extension descends near the
contracted prime, assuming neighbourhood descent of module surjectivity.
Source: Stacks Project, Tags 0C4Y (1) and 00QP, agent-written adaptation
(blueprint: lem-sc-finite-type-field-extension-neighbourhood).

The module scalar extension is represented by `(C ⊗[k] K) ⊗[C] M`, as in
`LinearMap.exists_localizedMap_away_surjective_of_fieldExtension`: the canonical
identification with `M ⊗[k] K` sends `(c ⊗ λ) ⊗ m` to `(c • m) ⊗ λ`.

Proof:
1. Choose finite algebra generators y_i of the localization of B tensor_k K at u.
   Write y_i = z_i/u^{n_i}, express u and the z_i as finite sums of pure tensors,
   and collect their B-coefficients t_j. This uses the finite-type, localization,
   and tensor-product definitions; empty lists are allowed.
2. Let C = alpha(A)[t_j] inside B. This is a k-algebra. The chosen expressions lift
   u and z_i to v and w_i in C tensor_k K. The localized inclusion F sends
   a/v^n to iota_K(a)/u^n. Its image contains A tensor_k K and all y_i, so is the
   entire target. No injectivity after tensoring is needed.
3. Contract qK to a prime P of C tensor_k K. Since v maps to u, v is outside P.
   Regard C -> B as a C-linear map. Its scalar extension localized at v is F.
   Apply the assumed principle, in the form of
   `lem-sc-module-surjectivity-field-extension-neighbourhood`, to obtain d in C
   with d tensor 1 outside P and a surjection C_d -> B_c, where c is the image
   of d. Thus c tensor 1 is outside qK, or equivalently c is outside its
   contraction q. No module finiteness is required.
4. Every element of B_c is therefore a polynomial in t_j/1 and 1/c with
   coefficients in alpha(A). These finitely many elements generate B_c as an
   A-algebra, giving the required finite-type ring map. -/
theorem exists_finiteType_away_of_fieldExtension
    {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    {A : Type w} {B : Type x} [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
    (hdesc : ∀ (C : Type x) [CommRing C] [Algebra k C]
      (M : Type (max x y)) (N : Type (max x z)) [AddCommGroup M] [AddCommGroup N]
      [Module C M] [Module C N] (φ : M →ₗ[C] N)
      (v : C ⊗[k] K) (P : Ideal (C ⊗[k] K)) [P.IsPrime], v ∉ P →
      Function.Surjective
        (LocalizedModule.map (Submonoid.powers v) (φ.baseChange (C ⊗[k] K))) →
      ∃ d : C, algebraMap C (C ⊗[k] K) d ∉ P ∧
        Function.Surjective (LocalizedModule.map (Submonoid.powers d) φ))
    (α : A →ₐ[k] B) (qK : Ideal (B ⊗[k] K)) [qK.IsPrime]
    (u : B ⊗[k] K) (hu : u ∉ qK)
    (hfinite : RingHom.FiniteType
      ((algebraMap (B ⊗[k] K) (Localization.Away u)).comp
        (Algebra.TensorProduct.map α (AlgHom.id k K)).toRingHom)) :
    ∃ c : B, c ∉ Ideal.comap (algebraMap B (B ⊗[k] K)) qK ∧
      RingHom.FiniteType ((algebraMap B (Localization.Away c)).comp α.toRingHom) := by
  sorry

end RingHom
