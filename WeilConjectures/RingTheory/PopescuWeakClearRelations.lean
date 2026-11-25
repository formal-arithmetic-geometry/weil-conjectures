/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Extension.Presentation.Submersive
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.MvPolynomial.Localization

/-!
# Clearing auxiliary relation certificates

For equations `f` generating the localized kernel of a presentation over `R_p`, each auxiliary
relation `g_j` vanishing in the target satisfies `s_j g_j ∈ (f)` for some `s_j` outside `p`.

## References

* [Stacks, Tag 07F9] (the denominator-clearing paragraphs of the proof)
-/

@[expose] public section

universe u v

namespace Algebra

open MvPolynomial

/-- Clear auxiliary relation certificates for equations generating the localized kernel. -/
theorem exists_cleared_submersive_relations
    {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime]
    {D : Type v} [CommRing D] [Algebra (Localization.AtPrime p) D]
    [Algebra R D] [IsScalarTower R (Localization.AtPrime p) D]
    (n m c t : ℕ)
    (P : SubmersivePresentation (Localization.AtPrime p) D
      (Fin (n + m)) (Fin c))
    (f : Fin c → MvPolynomial (Fin (n + m)) R)
    (hkernel : Ideal.map (MvPolynomial.map (algebraMap R (Localization.AtPrime p)))
      (Ideal.span (Set.range f)) = RingHom.ker (aeval P.val))
    (g : Fin t → MvPolynomial (Fin n) R)
    (hg : ∀ j, aeval (fun i : Fin n ↦ P.val (Fin.castAdd m i)) (g j) = 0) :
    ∃ (s : Fin t → R),
      (∀ j, s j ∉ p) ∧
      (∀ j : Fin t, MvPolynomial.C (s j) *
        rename (Fin.castLE (Nat.le_add_right n m)) (g j) ∈ Ideal.span (Set.range f)) := by
  classical
  let := MvPolynomial.algebraMvPolynomial (σ := Fin (n + m))
    (R := R) (S := Localization.AtPrime p)
  have hmem (j : Fin t) :
      algebraMap (MvPolynomial (Fin (n + m)) R)
        (MvPolynomial (Fin (n + m)) (Localization.AtPrime p))
        (rename (Fin.castLE (Nat.le_add_right n m)) (g j)) ∈
      Ideal.map (algebraMap (MvPolynomial (Fin (n + m)) R)
        (MvPolynomial (Fin (n + m)) (Localization.AtPrime p)))
        (Ideal.span (Set.range f)) := by
    rw [MvPolynomial.algebraMap_def, hkernel, RingHom.mem_ker,
      MvPolynomial.aeval_map_algebraMap, MvPolynomial.aeval_rename]
    exact hg j
  have hex (j : Fin t) : ∃ s : R, s ∉ p ∧
      C s * rename (Fin.castLE (Nat.le_add_right n m)) (g j) ∈
        Ideal.span (Set.range f) := by
    obtain ⟨a, ha, hmul⟩ :=
      (IsLocalization.algebraMap_mem_map_algebraMap_iff
        (p.primeCompl.map (C (σ := Fin (n + m))))
        (MvPolynomial (Fin (n + m)) (Localization.AtPrime p))
        (Ideal.span (Set.range f)) _).mp (hmem j)
    obtain ⟨s, hs, rfl⟩ := ha
    exact ⟨s, hs, hmul⟩
  choose s hs hmul using hex
  exact ⟨s, hs, hmul⟩

end Algebra
