/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenClosed
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionEssImage
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
and `..._padicAlgCl`). This is part (3) of the blueprint lemma
`det-sf-comp-composition-interchange`.

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

/-! ### The closed complement and base change in the category over a scheme -/

section Over

variable {S : Scheme.{u}}

/-- The closed complement of an open immersion `j : X ⟶ Z` of `S`-schemes, as an object of
`Over S`. -/
noncomputable def overClosedComplementObj {X Z : Over S} (j : X ⟶ Z)
    [IsOpenImmersion j.left] : Over S :=
  Over.mk (j.left.closedComplement ≫ Z.hom)

/-- The closed immersion of the closed complement of an open immersion `j : X ⟶ Z` of
`S`-schemes, as a morphism of `Over S`. -/
noncomputable def overClosedComplement {X Z : Over S} (j : X ⟶ Z)
    [IsOpenImmersion j.left] : (overClosedComplementObj j) ⟶ Z :=
  Over.homMk j.left.closedComplement rfl

section ClosedComplement

variable {X Z : Over S} (j : X ⟶ Z) [IsOpenImmersion j.left]

/-- The underlying morphism of schemes of `overClosedComplement j` is the closed complement of
`j`. -/
@[simp] lemma overClosedComplement_left :
    (overClosedComplement j).left = j.left.closedComplement := rfl

/-- The closed complement of an open immersion is a closed immersion. -/
instance : IsClosedImmersion (overClosedComplement j).left :=
  inferInstanceAs (IsClosedImmersion j.left.closedComplement)

/-- The closed complement of an `S`-scheme locally of finite type is locally of finite type. -/
instance [LocallyOfFiniteType Z.hom] : LocallyOfFiniteType (overClosedComplementObj j).hom :=
  inferInstanceAs (LocallyOfFiniteType (j.left.closedComplement ≫ Z.hom))

/-- The closed complement of a quasi-compact `S`-scheme is quasi-compact. -/
instance [QuasiCompact Z.hom] : QuasiCompact (overClosedComplementObj j).hom :=
  inferInstanceAs (QuasiCompact (j.left.closedComplement ≫ Z.hom))

/-- The closed complement of a separated `S`-scheme is separated. -/
instance [IsSeparated Z.hom] : IsSeparated (overClosedComplementObj j).hom :=
  inferInstanceAs (IsSeparated (j.left.closedComplement ≫ Z.hom))

/-- The closed complement of `j` is supported on the complement of the range of `j`. -/
lemma range_overClosedComplement :
    Set.range (overClosedComplement j).left.base = (Set.range j.left.base)ᶜ :=
  j.left.range_closedComplement

/-- The ranges of the closed complement of `j` and of `j` are complementary. -/
lemma isCompl_range_overClosedComplement :
    IsCompl (Set.range (overClosedComplement j).left.base) (Set.range j.left.base) := by
  rw [range_overClosedComplement]
  exact isCompl_compl.symm

end ClosedComplement

/-- The fibre product `Y ×_Z W` of morphisms `f : Y ⟶ Z` and `g : W ⟶ Z` of `S`-schemes, as an
object of `Over S` through the second projection. -/
noncomputable def overPullbackObj {Y Z W : Over S} (f : Y ⟶ Z) (g : W ⟶ Z) : Over S :=
  Over.mk (pullback.snd f.left g.left ≫ W.hom)

/-- The first projection `Y ×_Z W ⟶ Y`, as a morphism of `Over S`. -/
noncomputable def overPullbackFst {Y Z W : Over S} (f : Y ⟶ Z) (g : W ⟶ Z) :
    overPullbackObj f g ⟶ Y :=
  Over.homMk (pullback.fst f.left g.left) (by
    simp only [overPullbackObj, Over.mk_hom]
    rw [← Over.w f, pullback.condition_assoc, Over.w g])

/-- The second projection `Y ×_Z W ⟶ W`, as a morphism of `Over S`. -/
noncomputable def overPullbackSnd {Y Z W : Over S} (f : Y ⟶ Z) (g : W ⟶ Z) :
    overPullbackObj f g ⟶ W :=
  Over.homMk (pullback.snd f.left g.left) rfl

section Pullback

variable {Y Z W : Over S} (f : Y ⟶ Z) (g : W ⟶ Z)

/-- The underlying morphism of `overPullbackFst f g` is the first projection. -/
@[simp] lemma overPullbackFst_left : (overPullbackFst f g).left = pullback.fst f.left g.left :=
  rfl

/-- The underlying morphism of `overPullbackSnd f g` is the second projection. -/
@[simp] lemma overPullbackSnd_left : (overPullbackSnd f g).left = pullback.snd f.left g.left :=
  rfl

/-- The square of the fibre product in `Over S` is cartesian. -/
lemma isPullback_overPullbackFst_overPullbackSnd :
    IsPullback (overPullbackFst f g) (overPullbackSnd f g) f g :=
  IsPullback.of_map (Over.forget S) (Over.OverMorphism.ext pullback.condition)
    (IsPullback.of_hasPullback f.left g.left)

/-- The base change of a proper morphism to an `S`-scheme locally of finite type is locally of
finite type over `S`. -/
instance [IsProper f.left] [LocallyOfFiniteType W.hom] :
    LocallyOfFiniteType (overPullbackObj f g).hom :=
  inferInstanceAs (LocallyOfFiniteType (pullback.snd f.left g.left ≫ W.hom))

/-- The base change of a proper morphism to a quasi-compact `S`-scheme is quasi-compact over
`S`. -/
instance [IsProper f.left] [QuasiCompact W.hom] : QuasiCompact (overPullbackObj f g).hom :=
  inferInstanceAs (QuasiCompact (pullback.snd f.left g.left ≫ W.hom))

/-- The base change of a proper morphism to a separated `S`-scheme is separated over `S`. -/
instance [IsProper f.left] [IsSeparated W.hom] : IsSeparated (overPullbackObj f g).hom :=
  inferInstanceAs (IsSeparated (pullback.snd f.left g.left ≫ W.hom))

end Pullback

/-- In a commutative square of `S`-schemes
```
X' --i'--> Z'
|p         |p'
v          v
X  --j---> Z
```
with `j` an open immersion, the base change of the closed complement of `j` along `p'` misses
the range of `i'`. -/
lemma disjoint_range_overPullbackFst_overClosedComplement {X Z X' Z' : Over S} {p : X' ⟶ X}
    {i' : X' ⟶ Z'} {j : X ⟶ Z} {p' : Z' ⟶ Z} [IsOpenImmersion j.left] (sq : CommSq p i' j p') :
    Disjoint (Set.range i'.left.base)
      (Set.range (overPullbackFst p' (overClosedComplement j)).left.base) := by
  rw [Set.disjoint_left]
  rintro _ ⟨x, rfl⟩ ⟨y, hy⟩
  have h₁ := congrArg (fun φ : X' ⟶ Z ↦ φ.left x) sq.w
  have h₂ := congrArg (fun φ ↦ φ y) (pullback.condition (f := p'.left)
    (g := (overClosedComplement j).left))
  simp only [Over.comp_left, Scheme.Hom.comp_apply] at h₁ h₂
  rw [overPullbackFst_left] at hy
  exact (isCompl_range_overClosedComplement j).disjoint.ne_of_mem ⟨_, rfl⟩ ⟨_, rfl⟩
    (h₁.trans ((congrArg p'.left hy).symm.trans h₂)).symm

end Over

namespace ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  [IsFinitenessCoefficient ℓ Λ]

include ℓ k

/-! ### The extension by zero is fully faithful -/

section FullyFaithful

variable {U X : Over (Spec (.of k))}
  [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom] [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom]
  (j : U ⟶ X) [IsOpenImmersion j.left]

/-- The extension by zero `j_!` along an open immersion is fully faithful on bounded
constructible complexes: so is the levelwise `D((j)_!open⟦Λ⟧)` on the ambient derived
categories, the unit of `D(j_!) ⊣ D(j^*)` being an isomorphism. -/
noncomputable def fullyFaithfulBoundedConstructibleOpenImmersionLowerShriek :
    (boundedConstructibleOpenImmersionLowerShriek Λ ℓ j).FullyFaithful :=
  have : IsIso (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j.left).unit :=
    Adjunction.isIso_mapDerivedCategoryAdjunction_unit _
  Functor.FullyFaithful.ofCompFaithful (G := (boundedConstructible _).ι)
    (((ObjectProperty.fullyFaithfulι _).comp
      (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j.left).fullyFaithfulLOfIsIsoUnit).ofIso
        (boundedConstructibleOpenImmersionLowerShriekCompatibility Λ ℓ j).symm)

/-- The unit `K ⟶ Lj^* j_! K` of the adjunction `j_! ⊣ Lj^*` on bounded constructible complexes
is an isomorphism, `j_!` being fully faithful. -/
instance isIso_boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction_unit :
    IsIso (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ j).unit :=
  have := (fullyFaithfulBoundedConstructibleOpenImmersionLowerShriek Λ ℓ j).full
  have := (fullyFaithfulBoundedConstructibleOpenImmersionLowerShriek Λ ℓ j).faithful
  inferInstance

end FullyFaithful

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
`E`-sheaves (blueprint `det-sf-comp-composition-interchange`, part (3)): the exchange morphism
`Rp_* ⋙ j_! ⟶ i'_! ⋙ Rp'_*` of a cartesian square with `p'` proper is an isomorphism. Over the
open `X ⊆ Z` it is the identification `Lj^* ⋙ Rp'_* ≅ Rp_* ⋙ Li'^*`, and over the closed
complement `Z ∖ X` the stalks of `Rp'_*(i'_! K)` are, by proper base change, the cohomology of
the fibres of `p'` over `Z ∖ X`, which do not meet `X' ⊆ Z'`, with coefficients in `i'_! K`,
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
`ℚ̄_ℓ`-sheaves (blueprint `det-sf-comp-composition-interchange`, part (3)): the exchange morphism
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
