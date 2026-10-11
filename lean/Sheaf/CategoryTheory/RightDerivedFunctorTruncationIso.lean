/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Preadditive.LeftExact

/-!
# Low-degree cohomology of a right derived functor

Source: Stacks Project, Derived Categories, Lemma 05TC, part (2), with the cone of a morphism
in place of the upper truncation (blueprint: lem-weil-pbc-derived-functor-truncation-iso).

## Main statements

* `CategoryTheory.Functor.isIso_homologyFunctor_rightDerivedFunctorPlus_map`:
  a cohomology isomorphism through degree `n`, monic in degree `n + 1`, remains a cohomology
  isomorphism through degree `n` after applying the right derived functor.
* `CategoryTheory.Functor.isIso_homologyFunctor_rightDerivedFunctorPlus_truncLEι`:
  the canonical lower truncation induces an isomorphism on degree-`n` derived cohomology.

`rightDerivedFunctorPlus` is the existing right derived functor on bounded-below derived
categories. It can be computed on bounded-below complexes of injectives, which are
K-injective; thus it realizes the resolution convention of `def-sp-kinjective-bridge`.
`TStructure.t.onPlus` is the induced standard t-structure on the bounded-below subcategory.
-/

@[expose] public section

universe u₁ u₂ v₁ v₂ w₁ w₂

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

/-- A left exact additive functor between Grothendieck abelian categories preserves
cohomology isomorphisms through degree `n` under its right derived functor, provided the
original map is also monic on cohomology in degree `n + 1`.
Source: Stacks, Derived Categories, Lemma 05TC (2), applied to the cone of the morphism
(blueprint: lem-weil-pbc-derived-functor-truncation-iso).

Proof:
1. Complete `c` to a distinguished triangle `L → M → C → L[1]`. The bounded-below
subcategory is triangulated (`def-weil-pbc-bounded-derived-subcategories`). The long exact
cohomology sequence (`lem-sf-derived-homology-long-exact`) shows `H^j(C) = 0` for `j ≤ n`:
`H^j(c)` is surjective, so the map `H^j(M) → H^j(C)` is zero and the connecting map
`H^j(C) → H^(j+1)(L)` is monic. Its image is the kernel of `H^(j+1)(c)`, which is zero
by the isomorphism hypothesis when `j < n`, and by the monomorphism hypothesis when `j = n`.
2. The right derived functor is triangulated
(`lem-weil-pbc-derived-direct-image-triangulated`), so applying it gives a distinguished
triangle with first arrow `Rv(c)`.
3. Negative vanishing (`lem-weil-pbc-derived-functor-negative-vanishing`) at the lower bound
`n + 1` shows `H^j(Rv C) = 0` for all `j ≤ n`.
4. In the resulting long exact sequence, the outer terms `H^(j-1)(Rv C)` and `H^j(Rv C)`
vanish for `j ≤ n`. Thus `H^j(Rv(c))` is both monic and epic, hence an isomorphism.
5. For the canonical truncation, `lem-weil-pbc-truncation-cohomology` gives the isomorphism
hypotheses and zero source in degree `n + 1`, hence the monomorphism hypothesis. Applying
steps 1-4 gives the truncation corollary below. -/
theorem isIso_homologyFunctor_rightDerivedFunctorPlus_map
    {A : Type u₁} [Category.{v₁} A] [Abelian A] [IsGrothendieckAbelian.{v₁} A]
    {B : Type u₂} [Category.{v₂} B] [Abelian B] [IsGrothendieckAbelian.{v₂} B]
    [HasDerivedCategory.{w₁} A] [HasDerivedCategory.{w₂} B]
    (v : A ⥤ B) [v.Additive] [PreservesFiniteLimits v]
    (n : ℤ) {L M : DerivedCategory.Plus A} (c : L ⟶ M)
    (hiso : ∀ i : ℤ, i ≤ n → IsIso ((DerivedCategory.Plus.homologyFunctor A i).map c))
    (hmono : Mono ((DerivedCategory.Plus.homologyFunctor A (n + 1)).map c)) :
    ∀ j : ℤ, j ≤ n →
      IsIso ((DerivedCategory.Plus.homologyFunctor B j).map (v.rightDerivedFunctorPlus.map c)) :=
  sorry

/-- The canonical truncation `τ≤n K → K` induces an isomorphism on degree-`n` cohomology
after applying the right derived functor of a left exact additive functor.
Source: Stacks, Derived Categories, Lemma 05TC (2)
(blueprint: lem-weil-pbc-derived-functor-truncation-iso).

Proof: The induced standard t-structure gives the canonical truncation of any bounded-below
object; it agrees with the canonical truncation of a bounded-below representing complex
(`def-sbc-standard-tstructure-derived-category`). Its cohomology map is an isomorphism in
all degrees `i ≤ n`, and its source has zero cohomology in degree `n + 1`
(`lem-weil-pbc-truncation-cohomology`), so that degree's map is monic. Apply
`isIso_homologyFunctor_rightDerivedFunctorPlus_map` with `c` this canonical map and `j = n`.
The proof of that statement completes `c` to its cone triangle, uses its long exact sequence
to show the cone vanishes through degree `n`, applies triangulatedness and negative
vanishing of the right derived functor, and uses the resulting long exact sequence to
obtain the required isomorphism. -/
theorem isIso_homologyFunctor_rightDerivedFunctorPlus_truncLEι
    {A : Type u₁} [Category.{v₁} A] [Abelian A] [IsGrothendieckAbelian.{v₁} A]
    {B : Type u₂} [Category.{v₂} B] [Abelian B] [IsGrothendieckAbelian.{v₂} B]
    [HasDerivedCategory.{w₁} A] [HasDerivedCategory.{w₂} B]
    (v : A ⥤ B) [v.Additive] [PreservesFiniteLimits v]
    (n : ℤ) (K : DerivedCategory.Plus A) :
    IsIso ((DerivedCategory.Plus.homologyFunctor B n).map
      (v.rightDerivedFunctorPlus.map ((DerivedCategory.TStructure.t.onPlus.truncLEι n).app K))) :=
  sorry

end CategoryTheory.Functor
