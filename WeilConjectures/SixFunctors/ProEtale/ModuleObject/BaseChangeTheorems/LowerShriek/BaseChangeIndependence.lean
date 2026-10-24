/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil conjectures project
-/
module

public import WeilConjectures.Compactification.OverRefinementBaseChange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ClopenLowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.ExchangeFormalism

/-!

# Independence of the compact-support base change from the compactification

Let `sq : IsPullback g' f' f g` be a cartesian square of separated `k`-schemes of finite type.
The compact-support base change `Ex_! : Rf_! ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_!` on bounded constructible
`ℚ̄_ℓ`-sheaves (`ProEtale.CondensedRing.boundedConstructibleLowerShriekBaseChange_padicAlgCl`) is
defined through the chosen compactification `c_f` of `f` and its base change. This file shows
that it can be computed through any compactification `c` of `f` and any compactification `c'`
of `f'` lying over `c` along a morphism `h : c'.Z ⟶ c.Z` with cartesian squares
(`ProEtale.CondensedRing.boundedConstructibleLowerShriekBaseChange_padicAlgCl_eq`): it is the
compact-support exchange map of the pair `(c, c')`
(`ProEtale.CondensedRing.boundedConstructibleLowerShriekOfCompactificationBaseChange`), conjugated
by the comparison isomorphisms `Rf_! ≅ Rf_!^c` and `Rf'_!^{c'} ≅ Rf'_!` of the independence of the
lower shriek from the compactification (blueprint `fix-lem-exchanges`, clause (4):
"`Ex_!` is independent of the chosen compactification and compatible with the refinement
comparison isomorphisms").

The proof is formal: the compact-support exchange maps are those of the exchange formalism
`ProEtale.CondensedRing.boundedConstructibleExchangeFormalism`, which are compatible with the
comparisons along refinements
(`CategoryTheory.ExchangeFormalism.shriekBaseChange_refinementComparison`),
and the comparisons of compactifications are computed along common refinements (blueprint
`prop-compactification-coherence-detailed`).

-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  [IsFinitenessCoefficient ℓ Λ]

/-- The formalism `boundedConstructibleExchangeFormalism`, for the coefficient ring `Λ`. -/
local notation "𝔽" => boundedConstructibleExchangeFormalism Λ ℓ k

variable {X Y X' Y' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

section Compactification

variable (c : Compactification f.left) (c' : Compactification f'.left)
  (h : c'.overObj ⟶ c.overObj) (hi : IsPullback g' c'.overI c.overI h)
  (hp : IsPullback h c'.overG c.overG g)

/-- The *compact-support exchange map* `Rf_!^c ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_!^{c'}` of a compactification
`c` of `f` and a compactification `c'` of `f'` lying over it along `h : c'.Z ⟶ c.Z` with cartesian
squares: the base change map `Lg^* Rp_* ⟶ Rp'_* Lh^*` of the proper square applied after `i_!`,
followed by the inverse of the extension-by-zero exchange morphism of the open square (the
compact-support exchange map `CategoryTheory.ExchangeFormalism.shriekBaseChange` of the exchange
formalism). -/
noncomputable def boundedConstructibleLowerShriekOfCompactificationBaseChange :
    boundedConstructibleLowerShriekOfCompactification Λ ℓ c ⋙
        boundedConstructibleUpperStar Λ ℓ g ⟶
      boundedConstructibleUpperStar Λ ℓ g' ⋙
        boundedConstructibleLowerShriekOfCompactification Λ ℓ c' :=
  haveI := isIso_baseChange_boundedConstructibleExchangeFormalism Λ ℓ hi
  ((𝔽).shriekBaseChange (SepFinType.homMk c.overI) (SepFinType.homMk c.overG)
    (SepFinType.homMk c'.overI) (SepFinType.homMk c'.overG) (SepFinType.homMk g')
    (SepFinType.homMk h) (SepFinType.homMk g) (SepFinType.homMk_comp_homMk hi.w)
    (SepFinType.homMk_comp_homMk hp.w)).natTrans

/-- The compact-support base-change morphism for the compactification `c` and its base change is
the compact-support exchange map of the pair. -/
lemma boundedConstructibleLowerShriekOfCompactificationBaseChangePasting_eq_baseChange
    (sq : IsPullback g' f' f g) :
    boundedConstructibleLowerShriekOfCompactificationBaseChangePasting Λ ℓ c sq =
      boundedConstructibleLowerShriekOfCompactificationBaseChange Λ ℓ c
        (c.ofIsPullback sq.overLeft) (c.overBaseChangeFst sq)
        (c.overBaseChange_isPullback_i sq) (c.overBaseChange_isPullback_g sq) := by
  have := isIso_baseChange_boundedConstructibleExchangeFormalism Λ ℓ
    (c.overBaseChange_isPullback_i sq)
  rw [boundedConstructibleLowerShriekOfCompactificationBaseChangePasting_eq,
    boundedConstructibleLowerShriekOfCompactificationBaseChange,
    ExchangeFormalism.shriekBaseChange, boundedConstructibleBaseChange_eq_pfBaseChange,
    boundedConstructibleOpenImmersionLowerShriekBaseChangeIso_hom_eq]
  rfl

end Compactification

end AlgebraicGeometry.ProEtale.CondensedRing
