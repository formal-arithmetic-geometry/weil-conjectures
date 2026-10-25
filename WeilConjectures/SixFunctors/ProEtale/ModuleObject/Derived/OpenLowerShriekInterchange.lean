/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenClosed
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenClosedComplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenLowerShriekBaseChange

/-!

# Interchanging proper direct image and extension by zero

Let `Λ` be a commutative condensed ring. All schemes are separated and of finite type over a
field `k` of characteristic `p > 0` with `p ≠ ℓ`, and all morphisms are morphisms of
`Over (Spec (.of k))`. For a cartesian square
```
X' --i'--> Z'
|p         |p'
v          v
X  --j---> Z
```
with `j` and `i'` open immersions, the exchange morphism `Rp_* ⋙ j_! ⟶ i'_! ⋙ Rp'_*`
(`ProEtale.CondensedRing.boundedConstructibleLowerStarOpenImmersionLowerShriekExchange'`) is an
isomorphism when `p'` is proper, for the coefficient rings `E̲` of a finite extension `E` of
`ℚ_ℓ` and `ℚ̲̄_ℓ`
(`ProEtale.CondensedRing.isIso_boundedConstructibleLowerStarOpenImmersionLowerShriekExchange'`
and `..._padicAlgCl`). This is the `E`-coefficient analogue of part (3) of the blueprint
lemma on interchanging proper direct image and extension by zero, which is formalised for finite
coefficients as `AlgebraicGeometry.Etale.existsUnique_openImmersionLowerShriekLowerStarExchange`.

## Proof

Let `c : Zc ⟶ Z` be the closed complement of `j` (`overClosedComplement`). The
restrictions `Lj^*` and `Lc^*` jointly reflect isomorphisms
(`ProEtale.CondensedRing.isIso_of_isIso_boundedConstructibleUpperStar_map_of_isCompl`).

* Over `X`: by the mate calculus of `WeilConjectures.CategoryTheory.Adjunction.ExchangeMate`,
  `Lj^*` of the exchange morphism, composed with the unit of `j_! ⊣ Lj^*` and the base-change
  morphism `Lj^* Rp'_* ⟶ Rp_* Li'^*`, is `Rp_*` of the unit of `i'_! ⊣ Li'^*`. Both units are
  isomorphisms since the extensions by zero are fully faithful, and the base-change morphism is
  an isomorphism by proper base change.
* Over `Zc`: both sides vanish. `Lc^* j_! = 0` since `Zc` misses `X`, and by proper base change
  along `c`, `Lc^* Rp'_* (i'_! K) ≅ Rq_* Lc'^* (i'_! K) = 0`, where `c' : Zc' ⟶ Z'` is the
  base change of `c` (`overPullbackObj`), whose range misses `X'`.

The only sorried inputs are proper base change
(`ProEtale.CondensedRing.isIso_boundedConstructibleBaseChange_of_isProper` and its
`_padicAlgCl` version) and the preservation of bounded constructible complexes by the six
functors (`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`).

-/

@[expose] public section

universe u

open scoped CategoryTheory.Obj

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

include ℓ k

/-! ### The exchange morphism is an isomorphism -/

section Interchange

variable {X Z X' Z' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Z.hom]
  [QuasiCompact Z.hom] [IsSeparated Z.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Z'.hom] [QuasiCompact Z'.hom] [IsSeparated Z'.hom]
  {p : X' ⟶ X} {i' : X' ⟶ Z'} {j : X ⟶ Z} {p' : Z' ⟶ Z}
  [IsOpenImmersion j.left] [IsOpenImmersion i'.left] [IsProper p'.left]

/-- **Interchanging proper direct image and extension by zero**, for any coefficient ring `Λ`
satisfying proper base change for the two cartesian squares involved: the square itself, and
the base change of `p'` along the closed complement of `j`. -/
theorem isIso_boundedConstructibleLowerStarOpenImmersionLowerShriekExchange'_of_isIso
    [IsFinitenessCoefficient ℓ Λ]
    (sq : IsPullback p i' j p')
    (h₁ : IsIso (boundedConstructibleBaseChange Λ ℓ sq.flip.toCommSq))
    (h₂ : IsIso (boundedConstructibleBaseChange Λ ℓ
      (isPullback_overPullbackFst_overPullbackSnd p' (overClosedComplement j)).toCommSq)) :
    IsIso (boundedConstructibleLowerStarOpenImmersionLowerShriekExchange' Λ ℓ sq) := by
  have : QuasiCompact (j.left ≫ Z.hom) := by
    rw [Over.w j]
    infer_instance
  have : QuasiCompact j.left := QuasiCompact.of_comp j.left Z.hom
  have hK (K : Dᵇc(X'.left)⟦Λ⟧) :
      IsIso ((boundedConstructibleLowerStarOpenImmersionLowerShriekExchange' Λ ℓ sq).app K) := by
    refine isIso_of_isIso_boundedConstructibleUpperStar_map_of_isCompl Λ ℓ
      (overClosedComplement j) j (isCompl_range_overClosedComplement j) _ ?_ ?_
    · -- Over the open `X`, by the mate calculus and proper base change.
      rw [boundedConstructibleLowerStarOpenImmersionLowerShriekExchange'_eq_exchangeRight]
      have : IsIso ((Adjunction.exchangeRight
          (boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ p')
          (boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ p)
          (boundedConstructiblePullbackSquareComparison Λ ℓ sq.toCommSq.flip)).app
            ((boundedConstructibleOpenImmersionLowerShriek Λ ℓ i').obj K)) := by
        rw [← boundedConstructibleBaseChange_eq_exchangeRight]
        infer_instance
      exact Adjunction.isIso_map_exchangeRight_app
        (boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ p)
        (boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ p')
        (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ j)
        (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ i') _ _
        (boundedConstructibleOpenImmersionLowerShriekBaseChangeIso'_inv Λ ℓ sq) K
    · -- Over the closed complement both sides vanish.
      have hS : IsZero ((boundedConstructibleUpperStar Λ ℓ (overClosedComplement j)).obj
          ((boundedConstructibleOpenImmersionLowerShriek Λ ℓ j).obj
            ((boundedConstructibleLowerStar Λ ℓ p).obj K))) :=
        isZero_boundedConstructibleUpperStar_obj_openImmersionLowerShriek Λ ℓ j
          (overClosedComplement j) (isCompl_range_overClosedComplement j).disjoint.symm _
      have hT : IsZero ((boundedConstructibleUpperStar Λ ℓ (overClosedComplement j)).obj
          ((boundedConstructibleLowerStar Λ ℓ p').obj
            ((boundedConstructibleOpenImmersionLowerShriek Λ ℓ i').obj K))) :=
        ((boundedConstructibleLowerStar Λ ℓ
          (overPullbackSnd p' (overClosedComplement j))).map_isZero
          (isZero_boundedConstructibleUpperStar_obj_openImmersionLowerShriek Λ ℓ i'
            (overPullbackFst p' (overClosedComplement j))
            (disjoint_range_overPullbackFst_overClosedComplement sq.toCommSq) K)).of_iso
          (asIso ((boundedConstructibleBaseChange Λ ℓ
            (isPullback_overPullbackFst_overPullbackSnd p' (overClosedComplement j)).toCommSq).app
              ((boundedConstructibleOpenImmersionLowerShriek Λ ℓ i').obj K)))
      exact ⟨⟨hT.to_ _, hS.eq_of_src _ _, hT.eq_of_src _ _⟩⟩
  exact NatIso.isIso_of_isIso_app _

end Interchange

section Coefficients

variable (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
  {X Z X' Z' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Z.hom]
  [QuasiCompact Z.hom] [IsSeparated Z.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Z'.hom] [QuasiCompact Z'.hom] [IsSeparated Z'.hom]
  {p : X' ⟶ X} {i' : X' ⟶ Z'} {j : X ⟶ Z} {p' : Z' ⟶ Z}
  [IsOpenImmersion j.left] [IsOpenImmersion i'.left] [IsProper p'.left]

omit [MonObj Λ] [IsCommMonObj Λ] in
/-- **Interchanging proper direct image and extension by zero** for bounded constructible
`E`-sheaves (the `E`-coefficient analogue of part (3) of the interchange lemma): the exchange
morphism `Rp_* ⋙ j_! ⟶ i'_! ⋙ Rp'_*` of a cartesian square with `p'` proper is an
isomorphism. Over the open `X ⊆ Z` it is the identification
`Lj^* ⋙ Rp'_* ≅ Rp_* ⋙ Li'^*`, and over the closed complement `Z ∖ X` the stalks of
`Rp'_*(i'_! K)` are, by proper base change, the cohomology of the fibres of `p'` over `Z ∖ X`,
which do not meet `X' ⊆ Z'`, with coefficients in `i'_! K`,
hence vanish. (In the blueprint the square is cartesian by part (1), from the density of `X'`
in `Z'`.) -/
theorem isIso_boundedConstructibleLowerStarOpenImmersionLowerShriekExchange'
    (sq : IsPullback p i' j p') :
    IsIso (boundedConstructibleLowerStarOpenImmersionLowerShriekExchange'
      (Profinite.continuousMapRingObj E) ℓ sq) :=
  isIso_boundedConstructibleLowerStarOpenImmersionLowerShriekExchange'_of_isIso _ ℓ sq
    (isIso_boundedConstructibleBaseChange_of_isProper ℓ E sq.flip)
    (isIso_boundedConstructibleBaseChange_of_isProper ℓ E
      (isPullback_overPullbackFst_overPullbackSnd p' (overClosedComplement j)))

omit [MonObj Λ] [IsCommMonObj Λ] in
/-- **Interchanging proper direct image and extension by zero** for bounded constructible
`ℚ̄_ℓ`-sheaves (the `ℚ̄_ℓ`-analogue of part (3) of the interchange lemma): the exchange morphism
`Rp_* ⋙ j_! ⟶ i'_! ⋙ Rp'_*` of a cartesian square with `p'` proper is an isomorphism. -/
theorem isIso_boundedConstructibleLowerStarOpenImmersionLowerShriekExchange'_padicAlgCl
    (sq : IsPullback p i' j p') :
    IsIso (boundedConstructibleLowerStarOpenImmersionLowerShriekExchange'
      (Profinite.padicAlgClRingObj ℓ) ℓ sq) :=
  isIso_boundedConstructibleLowerStarOpenImmersionLowerShriekExchange'_of_isIso _ ℓ sq
    (isIso_boundedConstructibleBaseChange_of_isProper_padicAlgCl ℓ sq.flip)
    (isIso_boundedConstructibleBaseChange_of_isProper_padicAlgCl ℓ
      (isPullback_overPullbackFst_overPullbackSnd p' (overClosedComplement j)))

end Coefficients

end ProEtale.CondensedRing

end AlgebraicGeometry
