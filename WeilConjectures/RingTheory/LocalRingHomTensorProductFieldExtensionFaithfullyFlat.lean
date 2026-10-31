/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-!
# Faithful flatness of localized field extension base change

Source: Stacks Project, Varieties, Tag 0C4Y, Lemma `lemma-change-fields-flat`, part (1)
(blueprint: lem-sc-etale-local-ring-stalk-faithfully-flat).
-/

@[expose] public section

set_option autoImplicit false

universe u v w x

open scoped TensorProduct

namespace Localization

/-- Stacks Project, Varieties, Tag 0C4Y, part (1)
(blueprint: lem-sc-etale-local-ring-stalk-faithfully-flat).
For a field extension `K/k`, a commutative `k`-algebra `A`, and a finitely presented
`A`-algebra `B`, the map on local rings at corresponding primes of `B` and `B ⊗[k] K`
is faithfully flat. The `k`-algebra structure on `B` is the one induced through `A`.

Proof: First, `lem-weil-pbc-field-extension-base-change-faithfully-flat` applied to `B`
gives faithful flatness of `B → B ⊗[k] K`. Second, the contraction equality says that
`qK` lies over `q`; `lem-weil-pbc-flat-local-ring-maps` therefore gives flatness and
localness of the induced localized map. Third, both localizations are local rings,
so the first clause of `lem-pc-local-flat-faithful-flat-reflects-surjective`
(Stacks Tag 00HR) implies that this flat local homomorphism is faithfully flat. -/
theorem localRingHom_tensorProduct_fieldExtension_faithfullyFlat
    {k : Type u} {K : Type v} {A : Type w} {B : Type x}
    [Field k] [Field K] [Algebra k K] [CommRing A] [Algebra k A]
    [CommRing B] [Algebra A B] [Algebra k B] [IsScalarTower k A B]
    [Algebra.FinitePresentation A B]
    (q : Ideal B) [q.IsPrime] (qK : Ideal (B ⊗[k] K)) [qK.IsPrime]
    (h : q = qK.comap (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[k] K)) :
    (Localization.localRingHom q qK Algebra.TensorProduct.includeLeftRingHom h).FaithfullyFlat := by
  have hf : (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[k] K).FaithfullyFlat := by
    change (algebraMap B (B ⊗[k] K)).FaithfullyFlat
    rw [RingHom.faithfullyFlat_algebraMap_iff]
    infer_instance
  let f := Localization.localRingHom q qK Algebra.TensorProduct.includeLeftRingHom h
  let : Algebra (Localization.AtPrime q) (Localization.AtPrime qK) := f.toAlgebra
  have : Module.Flat (Localization.AtPrime q) (Localization.AtPrime qK) :=
    hf.flat.localRingHom qK q h
  have : IsLocalHom (algebraMap (Localization.AtPrime q) (Localization.AtPrime qK)) :=
    inferInstanceAs (IsLocalHom f)
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

end Localization
