module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-!
# Chow's lemma over a quasi-compact quasi-separated base

Source: Stacks Project, Lemma Tag 0202 (blueprint: `lem-weil-pbc-chow-finite-type`).

## Main statements

* `exists_chow_finite_type` states Chow's lemma for a separated finite type
  morphism over a quasi-compact quasi-separated scheme.
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry

/-- Chow's lemma for a separated morphism of finite type over a quasi-compact
quasi-separated base (Stacks Project, Tag 0202; (blueprint: lem-weil-pbc-chow-finite-type)):
there are `n`, a proper surjective `π : X' ⟶ X` and an immersion `j : X' ⟶ ℙⁿ_S` over `S`.

Proof sketch: by Stacks 01ZJ, `f` factors as a closed immersion `i : X ⟶ Y` followed by a
separated morphism `g : Y ⟶ S` of finite presentation; a solution for `g` pulls back along `i`
to one for `f` (proper, surjective and closed immersions are stable under base change). Write
`S` as a limit of Noetherian schemes `S_j` of finite type over `ℤ` with affine transition maps
(01ZA), descend `g` to a finitely presented `g_j : Y_j ⟶ S_j` (01ZM), separated for large `j`
(01ZQ), apply Chow's lemma over the Noetherian `S_j` (0200), and base change the resulting
proper surjective `π_j` and immersion `ι : Y'_j ⟶ ℙⁿ_{S_j}` back to `S`, using
`ℙⁿ_{S_j} ×_{S_j} S ≅ ℙⁿ_S`. -/
theorem exists_chow_finite_type {S X : Scheme.{u}} (f : X ⟶ S)
    [CompactSpace S] [QuasiSeparatedSpace S] [IsSeparated f]
    [LocallyOfFiniteType f] [QuasiCompact f] :
    ∃ (n : ℕ) (X' : Scheme.{u}) (π : X' ⟶ X)
      (j : X' ⟶ ProjectiveSpace (ULift.{u} (Fin (n + 1))) S),
      IsProper π ∧ Surjective π ∧ IsImmersion j ∧
        j ≫ ProjectiveSpace (ULift.{u} (Fin (n + 1))) S ↘ S = π ≫ f := by
  sorry

end AlgebraicGeometry
