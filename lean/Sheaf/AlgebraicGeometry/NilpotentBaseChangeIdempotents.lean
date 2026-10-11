/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Sheaf.AlgebraicGeometry.Thickening
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.Algebra.Ring.Idempotent

/-!
# Idempotents under nilpotent base change

Source: Stacks Project, More on Morphisms, Tags 09ZU and 04EX; Derived Categories of Schemes,
proof of Tag 0G7X, using Algebra, Tag 00EE
(blueprint: lem-weil-pbc-base-change-nilpotent-thickening-idempotents).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Base change by a nilpotent quotient is a finite order thickening, and restriction
of global sections uniquely lifts idempotents.
Source: Stacks Project, Tags 09ZU, 04EX, and the equal-topological-spaces step of the proof
of Tag 0G7X, with Tag 00EE.
(blueprint: lem-weil-pbc-base-change-nilpotent-thickening-idempotents).

Proof plan:
1. Apply `lem-weil-pbc-quotient-base-change-closed-immersion-ideal` to `g` and `J`.
The first projection is a closed immersion with defining ideal sheaf `J O_Y`; on each
affine open with ring `B` its ideal is `JB`.
2. The same lemma identifies the `N`th power with `J^N O_Y`, which vanishes by the
hypothesis. Thus the ideal sheaf has `N`th power zero, giving a finite order thickening.
3. On every affine open, `JB` lies in every prime because its generators are nilpotent.
By `lem-weil-pbc-closed-immersion-image-zero-locus`, the closed immersion is surjective.
A surjective closed embedding is a homeomorphism.
4. By `lem-weil-pbc-scheme-clopen-idempotent`, idempotent global sections correspond
bijectively to clopen subsets, compatibly with pullback. Inverse image along the
homeomorphism is a bijection on clopen subsets. Hence each idempotent on the base change
has exactly one idempotent lift. This does not require surjectivity on all global sections. -/
theorem nilpotent_baseChange_idempotents
    (A : Type u) [CommRing A] (J : Ideal A) (N : ℕ) (hN : 1 ≤ N) (hJ : J ^ N = ⊥)
    (Y : Scheme.{u}) (g : Y ⟶ Spec (CommRingCat.of A)) :
    let q := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))
    let Y₀ := pullback g q
    let i : Y₀ ⟶ Y := pullback.fst g q
    IsClosedImmersion i ∧ i.ker ^ N = ⊥ ∧ IsFiniteOrderThickening i ∧
      IsHomeomorph i ∧
      (∀ e₀ : Γ(Y₀, ⊤), IsIdempotentElem e₀ →
        ∃! e : {e : Γ(Y, ⊤) // IsIdempotentElem e},
          (Scheme.Γ.map i.op).hom e.val = e₀) := by
  sorry

end AlgebraicGeometry
