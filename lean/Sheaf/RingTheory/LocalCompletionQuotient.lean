/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs

/-!
# Completion of a quotient of a Noetherian local ring

Source: Stacks Project, Algebra, Tag 00MA, parts (2) and (3), and the proof of
Tag 00MB; the module/ring completion identification used in Tag 0325
(blueprint: lem-weil-pbc-local-completion-quotient).
-/

universe u v

namespace AdicCompletion

/-- For a surjection `φ : A →+* B`, completion at the image of the maximal ideal is
completion of `A` modulo the extended kernel. The maps `θk` are the induced surjections
on quotient rings. Their compatibility with evaluations specifies `θ` coordinatewise;
the last equation says that the quotient isomorphism is induced by this same `θ`.
Source: Stacks Project, Algebra, Tag 00MA (2), (3), Tag 00MB, and Tag 0325
(blueprint: lem-weil-pbc-local-completion-quotient).

Proof:
1. Regard `B` as an `A`-module via `φ`. Surjectivity gives `m^k B = n^k`, where
   `m` is the maximal ideal of `A` and `n = m.map φ`. Thus the module completion of `B`
   at `m` is its ring completion at `n` (def-weil-pbc-adic-completion). The quotient maps
   induced by `φ` are surjective and compatible. They define the coordinatewise ring map
   `θ`, which commutes with the canonical maps from `A` and `B`.
2. Noetherianity makes `J = ker φ` finite, and `A` and `B` are cyclic `A`-modules
   (def-weil-pbc-noetherian-ring, def-weil-finitely-generated-module).
   Apply lem-weil-pbc-completion-exact-finite-modules (00MA (2)) to `0 → J → A → B → 0`.
   This makes `θ` surjective and identifies its kernel with the image of the completion
   of `J` in the completion of `A`.
3. By lem-weil-pbc-completion-finite-module-tensor (00MA (3)), the completed `J` is
   the tensor product of the completed `A` with `J` (def-weil-module-base-change).
   Naturality identifies its image with the finite sums `Σ y_i * cA(j_i)`, exactly the
   ideal `J.map cA`. This is the image identification used in the proof of 00MB.
4. The ring homomorphism theorem gives the quotient isomorphism, sending the class of
   `x` to `θ x`. -/
theorem exists_local_completion_quotient
    (A : Type u) (B : Type v) [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsLocalRing A]
    (φ : A →+* B) (hφ : Function.Surjective φ) :
    let m := IsLocalRing.maximalIdeal A
    let n := m.map φ
    let Ahat := AdicCompletion m A
    let Bhat := AdicCompletion n B
    let cA := algebraMap A Ahat
    let cB := algebraMap B Bhat
    let Jhat := (RingHom.ker φ).map cA
    (∀ k : ℕ, (m ^ k).map φ = n ^ k) ∧
    ∃ θ : Ahat →+* Bhat,
      (∀ k : ℕ, ∃ θk : (A ⧸ m ^ k) →+* (B ⧸ n ^ k),
        Function.Surjective θk ∧
        θk.comp (Ideal.Quotient.mk (m ^ k)) = (Ideal.Quotient.mk (n ^ k)).comp φ ∧
        (evalₐ n k).toRingHom.comp θ = θk.comp (evalₐ m k).toRingHom) ∧
      θ.comp cA = cB.comp φ ∧
      Function.Surjective θ ∧
      RingHom.ker θ = Jhat ∧
      ∃ e : (Ahat ⧸ Jhat) ≃+* Bhat,
        ∀ x : Ahat, e (Ideal.Quotient.mk Jhat x) = θ x := by
  sorry

end AdicCompletion
