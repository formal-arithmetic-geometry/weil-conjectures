/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NF
-/
module

public import Sheaf.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import Mathlib.Algebra.Homology.ShortComplex.Ab

/-!
# Derived categories with allowable torsion

Source: blueprint `sec-smooth-base-change/sk-rem-rest/`
`sbc-def-derived-categories-with-allowable-torsion.md`
(blueprint: sbc-def-derived-categories-with-allowable-torsion).

The full subcategories are realized inside the unbounded derived category by intersection
with its bounded and bounded-below object properties. This gives the same full subcategories
as first passing to `D^b` or `D^+`. All coefficients here are abelian groups.
-/

@[expose] public section

universe u

open CategoryTheory Limits ZeroObject

namespace AlgebraicGeometry.Etale

/-- The allowable-torsion condition on an abelian etale sheaf: every geometric stalk element
has a positive annihilator with prime divisors in `P`. Nonprime members of `P` are irrelevant.
Source: blueprint `sec-smooth-base-change/sk-rem-rest/`
`sbc-def-derived-categories-with-allowable-torsion.md`
(blueprint: sbc-def-derived-categories-with-allowable-torsion). -/
def allowableTorsionSheafProperty (T : Scheme.{u}) (P : Set ℕ) :
    ObjectProperty (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  fun F ↦ ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ T)
    (x : ((Scheme.pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})).obj F),
    ∃ n : ℕ, 0 < n ∧ (∀ p : ℕ, p.Prime → p ∣ n → p ∈ P) ∧ n • x = 0

private instance allowableTorsionSheafProperty_isClosedUnderSubobjects
    (T : Scheme.{u}) (P : Set ℕ) :
    (allowableTorsionSheafProperty T P).IsClosedUnderSubobjects := by
  have : AB5OfSize.{u, u} AddCommGrpCat.{u + 1} := AB5OfSize_shrink.{u, u, u + 1, u + 1} _
  constructor
  intro F G f _ hG Ω _ _ s x
  let L := (Scheme.pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})
  have hi : Function.Injective (L.map f) :=
    (AddCommGrpCat.mono_iff_injective _).mp inferInstance
  obtain ⟨n, hn, hp, hx⟩ := hG Ω s (L.map f x)
  refine ⟨n, hn, hp, hi ?_⟩
  simpa only [map_nsmul, map_zero] using hx

private instance allowableTorsionSheafProperty_isClosedUnderQuotients
    (T : Scheme.{u}) (P : Set ℕ) :
    (allowableTorsionSheafProperty T P).IsClosedUnderQuotients := by
  constructor
  intro F G f _ hF Ω _ _ s x
  let L := (Scheme.pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})
  have hs : Function.Surjective (L.map f) :=
    (AddCommGrpCat.epi_iff_surjective _).mp inferInstance
  obtain ⟨y, rfl⟩ := hs x
  obtain ⟨n, hn, hp, hy⟩ := hF Ω s y
  refine ⟨n, hn, hp, ?_⟩
  rw [← map_nsmul, hy, map_zero]

private instance allowableTorsionSheafProperty_containsZero
    (T : Scheme.{u}) (P : Set ℕ) : (allowableTorsionSheafProperty T P).ContainsZero := by
  refine ⟨0, isZero_zero _, ?_⟩
  intro Ω _ _ s x
  have : Subsingleton (((Scheme.pointSmallEtale s).sheafFiber
      (A := AddCommGrpCat.{u + 1})).obj (0 : Sheaf T.smallEtaleTopology _)) :=
    AddCommGrpCat.subsingleton_of_isZero (Functor.map_isZero _ (isZero_zero _))
  refine ⟨1, Nat.one_pos, ?_, ?_⟩
  · intro p hp hdiv
    exact False.elim (hp.not_dvd_one hdiv)
  · exact Subsingleton.elim _ _

private instance allowableTorsionSheafProperty_isClosedUnderExtensions
    (T : Scheme.{u}) (P : Set ℕ) :
    (allowableTorsionSheafProperty T P).IsClosedUnderExtensions := by
  have : AB5OfSize.{u, u} AddCommGrpCat.{u + 1} := AB5OfSize_shrink.{u, u, u + 1, u + 1} _
  constructor
  intro S hS h₁ h₃ Ω _ _ s x
  let L := (Scheme.pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})
  have hLS := hS.map_of_exact L
  obtain ⟨n, hn, hnp, hx⟩ := h₃ Ω s (L.map S.g x)
  have hx' : (S.map L).g (n • x) = 0 := by
    change L.map S.g (n • x) = 0
    rw [map_nsmul]
    exact hx
  obtain ⟨y, hy⟩ := ((S.map L).ab_exact_iff.mp hLS.exact) (n • x) hx'
  obtain ⟨m, hm, hmp, hy₀⟩ := h₁ Ω s y
  refine ⟨m * n, Nat.mul_pos hm hn, ?_, ?_⟩
  · intro p hp hdiv
    rcases hp.dvd_mul.mp hdiv with hpm | hpn
    · exact hmp p hp hpm
    · exact hnp p hp hpn
  · calc
      (m * n) • x = m • (n • x) := (smul_smul m n x).symm
      _ = m • (S.map L).f y := by rw [hy]
      _ = 0 := by
        change m • L.map S.f y = 0
        rw [← map_nsmul, hy₀, map_zero]

/-- Bounded-below objects with allowable-torsion cohomology, viewed in `D(T_et)`.
Source: blueprint `sec-smooth-base-change/sk-rem-rest/`
`sbc-def-derived-categories-with-allowable-torsion.md`
(blueprint: sbc-def-derived-categories-with-allowable-torsion). -/
def allowableTorsionPlusProperty (T : Scheme.{u}) (P : Set ℕ) :
    ObjectProperty (DerivedCategory (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})) :=
  DerivedCategory.homologyProperty (allowableTorsionSheafProperty T P) ⊓
    DerivedCategory.TStructure.t.plus

/-- Bounded objects with allowable-torsion cohomology, viewed in `D(T_et)`.
Source: blueprint `sec-smooth-base-change/sk-rem-rest/`
`sbc-def-derived-categories-with-allowable-torsion.md`
(blueprint: sbc-def-derived-categories-with-allowable-torsion). -/
def allowableTorsionBoundedProperty (T : Scheme.{u}) (P : Set ℕ) :
    ObjectProperty (DerivedCategory (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})) :=
  DerivedCategory.homologyProperty (allowableTorsionSheafProperty T P) ⊓
    DerivedCategory.TStructure.t.bounded

/-- Strict fullness of the bounded-below allowable-torsion class.
Source: blueprint `sec-smooth-base-change/sk-rem-rest/`
`sbc-def-derived-categories-with-allowable-torsion.md`
(blueprint: sbc-def-derived-categories-with-allowable-torsion).
Proof: an isomorphism induces isomorphisms on all cohomology sheaves and their geometric
stalks. Transport each positive annihilator across these additive isomorphisms.
The bounded-below condition is invariant under isomorphisms by the standard t-structure. -/
@[instance] theorem allowableTorsionPlusProperty_isClosedUnderIsomorphisms
    (T : Scheme.{u}) (P : Set ℕ) :
    (allowableTorsionPlusProperty T P).IsClosedUnderIsomorphisms := by
  unfold allowableTorsionPlusProperty
  infer_instance

/-- Strict fullness of the bounded allowable-torsion class.
Source: blueprint `sec-smooth-base-change/sk-rem-rest/`
`sbc-def-derived-categories-with-allowable-torsion.md`
(blueprint: sbc-def-derived-categories-with-allowable-torsion).
Proof: isomorphisms preserve cohomology and geometric stalks, hence each positive allowable
annihilator. The bounded condition is invariant under isomorphisms. -/
@[instance] theorem allowableTorsionBoundedProperty_isClosedUnderIsomorphisms
    (T : Scheme.{u}) (P : Set ℕ) :
    (allowableTorsionBoundedProperty T P).IsClosedUnderIsomorphisms := by
  unfold allowableTorsionBoundedProperty
  infer_instance

/-- The bounded-below allowable-torsion class inherits its triangulated structure.
Source: blueprint `sec-smooth-base-change/sk-rem-rest/`
`sbc-def-derived-categories-with-allowable-torsion.md`
(blueprint: sbc-def-derived-categories-with-allowable-torsion).
Proof: zero has annihilator 1. Subgroups and quotients inherit allowable annihilators.
In an extension, kill the image of an element by an allowable n, then kill its lift in
the subgroup by an allowable m. Their product mn kills the original element and has
only allowable prime factors. Exactness of geometric stalks
(`prop-weil-pbc-geometric-stalks-exact`, finite-limit preservation and the skyscraper
adjunction) therefore makes allowable-torsion sheaves a weak Serre class.
Apply `cohomology_in_weak_serre_subcategory` to this class and take its bounded-below
intersection clause (`lem-sbc-cohomology-in-weak-serre-subcategory`). -/
@[instance] theorem allowableTorsionPlusProperty_isTriangulated
    (T : Scheme.{u}) (P : Set ℕ) :
    (allowableTorsionPlusProperty T P).IsTriangulated := by
  unfold allowableTorsionPlusProperty
  -- The source library already proves the cohomology-in-weak-Serre-class criterion.
  infer_instance

/-- The bounded allowable-torsion class inherits its triangulated structure.
Source: blueprint `sec-smooth-base-change/sk-rem-rest/`
`sbc-def-derived-categories-with-allowable-torsion.md`
(blueprint: sbc-def-derived-categories-with-allowable-torsion).
Proof: zero is killed by 1; kernels and cokernels inherit allowable annihilators stalkwise.
For an extension, annihilators n of the image and m of the resulting subgroup element
multiply to an allowable annihilator mn. Exactness of geometric stalks
(`prop-weil-pbc-geometric-stalks-exact`) gives weak Serre closure for the sheaf class.
Apply the bounded intersection clause of `cohomology_in_weak_serre_subcategory`
(`lem-sbc-cohomology-in-weak-serre-subcategory`). -/
@[instance] theorem allowableTorsionBoundedProperty_isTriangulated
    (T : Scheme.{u}) (P : Set ℕ) :
    (allowableTorsionBoundedProperty T P).IsTriangulated := by
  unfold allowableTorsionBoundedProperty
  -- Intersect the homology subcategory with the bounded t-structure subcategory.
  infer_instance

/-- `D^+_{P-tor}(T_et)`, with the inherited shifts and distinguished triangles.
Source: blueprint `sec-smooth-base-change/sk-rem-rest/`
`sbc-def-derived-categories-with-allowable-torsion.md`
(blueprint: sbc-def-derived-categories-with-allowable-torsion). -/
abbrev AbelianDerivedCategoryPlusTorsionOfPrimes (T : Scheme.{u}) (P : Set ℕ) : Type _ :=
  (allowableTorsionPlusProperty T P).FullSubcategory

/-- `D^b_{P-tor}(T_et)`, with the inherited shifts and distinguished triangles.
Source: blueprint `sec-smooth-base-change/sk-rem-rest/`
`sbc-def-derived-categories-with-allowable-torsion.md`
(blueprint: sbc-def-derived-categories-with-allowable-torsion). -/
abbrev AbelianDerivedCategoryBoundedTorsionOfPrimes (T : Scheme.{u}) (P : Set ℕ) : Type _ :=
  (allowableTorsionBoundedProperty T P).FullSubcategory

end AlgebraicGeometry.Etale
