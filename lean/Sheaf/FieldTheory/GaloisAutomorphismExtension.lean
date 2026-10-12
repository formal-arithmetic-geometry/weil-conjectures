/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T2
-/
module

public import Mathlib.FieldTheory.IsSepClosed

/-!
# Extending an automorphism of a separable closure

Source: Stacks Project, Tag 03QW, discussion of the action on geometric stalks.
-/

@[expose] public section

universe u

/-- Source: Stacks Project, Tag 03QW, construction of the Galois action on stalks.
(blueprint: lem-exc-galois-automorphism-extension).

Proof: The algebraic closure of K inside Omega is an algebraic closure of Ks.
Extend g to an automorphism of it by the extension theorem for embeddings into
an algebraic closure; the resulting endomorphism is surjective because this is
an algebraic normal extension. Choose a transcendence basis of Omega over this
algebraic closure. Acting on coefficients and fixing the basis gives an
isomorphism of the rational function field. Omega is its algebraic closure,
so this isomorphism extends to an automorphism of Omega. It fixes K, agrees
with g on the embedded Ks, and hence has the asserted restriction. If Omega
is algebraic over K, the transcendence basis is empty and the first extension
already gives the result. The argument works in positive characteristic too:
the purely inseparable part of the algebraic closure has unique extensions. -/
theorem exists_algEquiv_extending_separableClosure
    (K Ks Ω : Type u) [Field K] [Field Ks] [Field Ω]
    [Algebra K Ks] [IsSepClosure K Ks] [Algebra Ks Ω] [Algebra K Ω]
    [IsScalarTower K Ks Ω] [IsAlgClosed Ω] (g : Gal(Ks/K)) :
    ∃ τ : Ω ≃ₐ[K] Ω,
      (algebraMap Ks Ω).comp g.toRingHom =
        τ.toRingHom.comp (algebraMap Ks Ω) := by sorry
