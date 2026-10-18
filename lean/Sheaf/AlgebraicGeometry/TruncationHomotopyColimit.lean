/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q23
-/
module

public import Sheaf.CategoryTheory.TruncationsAndHomotopyColimits
public import Sheaf.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
import Sheaf.Algebra.Homology.ComplexColimitHomotopyColimit
import WeilConjectures.AlgebraicGeometry.DerivedCategories

/-!
# Recovery of an etale complex from its upper truncations

Source: Weil conjectures blueprint, sec-smooth-purity, sk-prop-sf-kunneth-ordinary,
node order 1720 (blueprint: lem-kun-hocolim-truncations); Stacks Project, Tags 0118 and 0949.

The homotopy colimit is given by a chosen telescope triangle, as in
`CategoryTheory.IsSequentialHomotopyColimit`. The conclusion asserts existence of the
comparison induced by the canonical truncation inclusions and that this comparison is an
isomorphism.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace AlgebraicGeometry.Etale

/-- Recovery from the bounded-above good truncations: the comparison from their
sequential telescope to `E`, induced by their inclusions, is an isomorphism.
The natural numbers form a cofinal sequence of upper cutoffs in the integers.
Source: blueprint sec-smooth-purity, sk-prop-sf-kunneth-ordinary, node order 1720;
Stacks Project, Tags 0118 and 0949 (blueprint: lem-kun-hocolim-truncations).

Proof:
1. Represent `E` by a cochain complex `C` of etale module sheaves
   (def-weil-pbc-derived-categories). Realize its good truncations by `C.truncLE N`,
   with terms `C^i` below `N`, `ker d^N` at `N`, and zero above `N`
   (def-kun-truncations, def-sbc-standard-tstructure-derived-category).
2. For each degree `i`, choose a natural number `M > i + 1`. The terms and
   differentials of all later truncations agree with those of `C`. Their degreewise
   colimit is therefore `C`; the resulting isomorphisms commute with differentials
   because all inclusions are chain maps.
3. Apply lem-kun-complex-colimit-hocolim to this sequence. Its canonical cone map
   to the termwise colimit is a quasi-isomorphism. Compose with the complex
   isomorphism of step 2 and localize to obtain the canonical comparison to `E`.
   Its source is the telescope with its actual coprojections. Transport between
   coproduct choices and distinguished cone triangles to obtain the canonical
   comparison induced by the truncation cocone; this comparison is invertible in
   the derived category. -/
theorem isIso_truncationHomotopyColimit_comparison
    (Λ : Type (u + 1)) [CommRing Λ] (T : Scheme.{u}) (E : DerivedCategoryModule Λ T)
    (B : Cofan (fun n : ℕ ↦ (_root_.DerivedCategory.TStructure.t.truncLE (n : ℤ)).obj E))
    (hB : IsColimit B) (H : DerivedCategoryModule Λ T)
    (p : B.pt ⟶ H) (q : H ⟶ B.pt⟦(1 : ℤ)⟧)
    (hT : Triangle.mk
      (𝟙 B.pt - Cofan.IsColimit.desc hB (fun n : ℕ ↦
        (_root_.DerivedCategory.TStructure.t.natTransTruncLEOfLE (n : ℤ) (n + 1 : ℕ)
          (Int.ofNat_le.mpr (Nat.le_succ n))).app E ≫ B.inj (n + 1))) p q ∈
      distTriang (DerivedCategoryModule Λ T)) :
    ∃ c : H ⟶ E, (∀ n : ℕ, B.inj n ≫ p ≫ c =
      (_root_.DerivedCategory.TStructure.t.truncLEι (n : ℤ)).app E) ∧ IsIso c := by
  sorry

end AlgebraicGeometry.Etale
