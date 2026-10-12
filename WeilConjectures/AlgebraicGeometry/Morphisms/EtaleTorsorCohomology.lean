/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

/-!
# Naturality of the torsor attached to an étale `H¹`-class

Let `M` be a finite abelian group and `Y` a scheme. Every class `ξ ∈ H¹(Y_ét, M)` of the
constant sheaf `M` is the class of an `M`-torsor `t` over `Y`
(`AlgebraicGeometry.Scheme.EtaleTorsor.exists_quotientEquivSheafH`), and the classification
is natural in `Y`: the pullback of `ξ` along a morphism `f : Y' ⟶ Y` is the class of the
pulled-back torsor `t ×_Y Y'`. Since a torsor has class zero exactly when it has a section,
the pullback of `ξ` along `f` vanishes exactly when `f` lifts to the total space of `t`.

This is the form in which the vanishing theorem `sk-thm-vanishing` uses the classification:
it kills a class of `H¹` by pulling it back to a cover over which the torsor acquires a
section.

## Main definitions

- `AlgebraicGeometry.Scheme.EtaleTorsor.pullbackSheafTorsor`: for an `M`-torsor `P` over `Y`
  and `f : Y' ⟶ Y`, the sheaf of lifts `U ⟶ P` of `U ⟶ Y' ⟶ Y` on the small étale site of
  `Y'`, as a torsor under `U ↦ C(U, M)`.

## Main statements

- `AlgebraicGeometry.Scheme.EtaleTorsor.exists_forall_cohomologyMap_eq_zero_iff`: a class of
  `H¹(Y_ét, M)` is represented by an `M`-torsor `t`, in the sense that it dies after pullback
  along `f` exactly when `f` lifts to `t`.

## Implementation notes

Write `t` as the torsor of local lifts of a global section `s` of `Q` along `I ⟶ Q`, for an
injective resolution `0 → M → I → Q → 0`; then `ξ = δ(s)`. The pullback `f^*` is exact, so the
pullback of `ξ` is `δ'(s')` for the pulled-back sequence `0 → f^*M → f^*I → f^*Q → 0` and the
pulled-back section `s'`, and it vanishes iff the torsor of local lifts of `s'` to `f^*I` has a
global section. This torsor is identified with the torsor of lifts of `f` to `P`
(`AlgebraicGeometry.Scheme.EtaleTorsor.pullbackSheafTorsor`) by the equivariant map which sends
a lift `φ : U ⟶ P` to the pullback along `φ` of the tautological lift `x₀ ∈ I(P)` of `s`. The
pullback of sections is described only through the unit `I ⟶ f_* f^* I` of the adjunction
`f^* ⊣ f_*`, and its compatibility with constant sections comes from the definition of the
comparison `f^* M ≅ M` (`AlgebraicGeometry.Scheme.upperStarConstantSheafIso`) by uniqueness of
adjoints.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite


namespace AlgebraicGeometry.Scheme.EtaleTorsor

variable {M : Type (u + 1)} [AddCommGroup M] [Finite M] {Y : Scheme.{u}}

variable (M) in
/-- Blueprint `sk-prop-input-torsors` (naturality): Torsors and étale H^1

Let `M` be a finite abelian group and `ξ ∈ H¹(Y_ét, M)` a class of the constant sheaf `M` on a
scheme `Y`. Then there is an `M`-torsor `t` over `Y` representing `ξ` naturally: for every
morphism `f : Y' ⟶ Y`, the pullback of `ξ` along `f` vanishes exactly when `f` lifts to the
total space of `t`, that is, exactly when the pulled-back torsor `t ×_Y Y'` is trivial.

Writing `t` as the torsor of local lifts of a section `s` for an injective resolution
`0 → M → I → Q → 0`, so that `ξ = δ(s)`, the pullback of `ξ` is `δ'(s')` for the pulled-back
sequence (`AlgebraicGeometry.Scheme.EtaleTorsor.cohomologyMap_δ`); it vanishes iff `s'` lifts,
iff the torsor of local lifts of `s'` has a global section, and this torsor is the torsor of
lifts of `f` to `t`
(`AlgebraicGeometry.Scheme.EtaleTorsor.pullbackSheafTorsor_equiv_pullbackLifts`).
-/
@[stacks 02NE]
theorem exists_forall_cohomologyMap_eq_zero_iff
    (ξ : Sheaf.H ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of M)) 1) :
    ∃ t : EtaleTorsor M Y, ∀ ⦃Y' : Scheme.{u}⦄ (f : Y' ⟶ Y),
      Etale.cohomologyMap f _ 1 ξ = 0 ↔ ∃ s : Y' ⟶ t.P, s ≫ t.π = f := by
  -- TEMPORARY (torsors, run 9): the proof draft is being repaired; see the WIP commits.
  sorry

end AlgebraicGeometry.Scheme.EtaleTorsor
