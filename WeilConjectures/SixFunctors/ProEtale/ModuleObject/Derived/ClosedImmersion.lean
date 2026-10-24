/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenClosed
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionEssImage
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.ClosedImmersion

/-!

# Full faithfulness of `Ri_*` and `j_!` on derived categories of module objects

Let `Λ` be a commutative condensed ring, `i : Z ⟶ X` a closed immersion and `j : U ⟶ X` an open
immersion. This file proves:

* the derived pushforward `Ri_*` is fully faithful, i.e. the counit `Li^* Ri_* ⟶ 𝟭` is an
  isomorphism, on `D(Mod_{Λ_Z})`
  (`ProEtale.CondensedRing.isIso_derivedUpperStarLowerStarAdjunction_counit_of_isClosedImmersion`)
  and on bounded constructible complexes
  (`ProEtale.CondensedRing.isIso_boundedConstructibleUpperStarLowerStarAdjunction_counit`);
* the extension by zero `j_!` on bounded constructible complexes is fully faithful, i.e. the unit
  `𝟭 ⟶ Lj^* j_!` is an isomorphism
  (`isIso_boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction_unit`);
* `Lj^* Ri_* = 0` on bounded constructible complexes when the ranges of `i` and `j` are disjoint
  (`ProEtale.CondensedRing.isZero_boundedConstructibleUpperStar_obj_lowerStar_obj`), by adjunction
  from `Li^* j_! = 0`.

The pushforward `i_*` on module objects is fully faithful
(`ProEtale.CondensedRing.fullyFaithfulLowerStarOfIsClosedImmersion`) and preserves K-injective
complexes, being right adjoint to the exact functor `i^*`, so its right derived functor is fully
faithful (`CategoryTheory.Functor.full_rightDerivedFunctor`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

section Derived

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

instance : ((i)_*⟦Λ⟧).PreservesKInjectiveComplexes :=
  (upperStarLowerStarAdjunction Λ i).preservesKInjectiveComplexes

/-- The derived pushforward `Ri_*` along a closed immersion is fully faithful on module objects
over `Λ`: the counit `Li^* Ri_* ⟶ 𝟭` is an isomorphism. -/
instance isIso_derivedUpperStarLowerStarAdjunction_counit_of_isClosedImmersion :
    IsIso (derivedUpperStarLowerStarAdjunction Λ i).counit :=
  (derivedUpperStarLowerStarAdjunction Λ i).counit_isIso_of_R_fully_faithful

end Derived

section BoundedConstructible

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

include ℓ k

/-- The derived pushforward `Ri_*` along a closed immersion is fully faithful on bounded
constructible complexes: the counit `Li^* Ri_* ⟶ 𝟭` is an isomorphism. -/
instance isIso_boundedConstructibleUpperStarLowerStarAdjunction_counit
    [IsFinitenessCoefficient ℓ Λ] {Z X : Over (Spec (.of k))}
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (i : Z ⟶ X) [IsClosedImmersion i.left] :
    IsIso (boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ i).counit := by
  have h : (boundedConstructibleLowerStar Λ ℓ i ⋙ (boundedConstructible _).ι).FullyFaithful :=
    ((ObjectProperty.fullyFaithfulι _).comp
      (Functor.FullyFaithful.ofFullyFaithful _)).ofIso
      (boundedConstructibleLowerStarCompatibility Λ ℓ i).symm
  have h' := h.ofCompFaithful
  have := h'.full
  have := h'.faithful
  exact (boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ i).counit_isIso_of_R_fully_faithful

/-- The extension by zero `j_!` along an open immersion is fully faithful on bounded
constructible complexes: the unit `𝟭 ⟶ Lj^* j_!` is an isomorphism. -/
instance isIso_boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction_unit
    {U X : Over (Spec (.of k))}
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (j : U ⟶ X) [IsOpenImmersion j.left] :
    IsIso (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ j).unit := by
  have : IsIso (openImmersionLowerShriekUpperStarAdjunction Λ j.left).unit :=
    (openImmersionLowerShriekUpperStarAdjunction Λ j.left).unit_isIso_of_L_fully_faithful
  have : IsIso (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j.left).unit :=
    Adjunction.isIso_mapDerivedCategoryAdjunction_unit _
  have h₀ := (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j.left).fullyFaithfulLOfIsIsoUnit
  have h : (boundedConstructibleOpenImmersionLowerShriek Λ ℓ j ⋙
      (boundedConstructible _).ι).FullyFaithful :=
    ((ObjectProperty.fullyFaithfulι _).comp h₀).ofIso
      (boundedConstructibleOpenImmersionLowerShriekCompatibility Λ ℓ j).symm
  have h' := h.ofCompFaithful
  have := h'.full
  have := h'.faithful
  exact (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ
    j).unit_isIso_of_L_fully_faithful

/-- **`Lj^* Ri_*` vanishes on bounded constructible complexes** when the ranges of the open
immersion `j` and of `i` are disjoint: by the adjunctions `j_! ⊣ Lj^*` and `Li^* ⊣ Ri_*`, a
morphism `M ⟶ Lj^* Ri_* N` is a morphism `Li^* j_! M ⟶ N`, and `Li^* j_! = 0`
(`ProEtale.CondensedRing.isZero_boundedConstructibleUpperStar_obj_openImmersionLowerShriek`). -/
lemma isZero_boundedConstructibleUpperStar_obj_lowerStar_obj [IsFinitenessCoefficient ℓ Λ]
    {Z U X : Over (Spec (.of k))}
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (j : U ⟶ X) [IsOpenImmersion j.left] (i : Z ⟶ X)
    (hji : Disjoint (Set.range j.left.base) (Set.range i.left.base)) (N : Dᵇc(Z.left)⟦Λ⟧) :
    IsZero ((boundedConstructibleUpperStar Λ ℓ j).obj
      ((boundedConstructibleLowerStar Λ ℓ i).obj N)) := by
  set adjj := boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ j
  set adji := boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ i
  rw [IsZero.iff_id_eq_zero]
  refine (adjj.homEquiv _ _).symm.injective ((adji.homEquiv _ _).symm.injective ?_)
  exact (isZero_boundedConstructibleUpperStar_obj_openImmersionLowerShriek Λ ℓ j i hji
    _).eq_of_src _ _

end BoundedConstructible

end AlgebraicGeometry.ProEtale.CondensedRing
