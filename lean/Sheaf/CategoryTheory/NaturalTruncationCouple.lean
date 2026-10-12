/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P3
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Sheaf.CategoryTheory.DerivedCoupleFunctoriality
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs

import Sheaf.CategoryTheory.TruncationHypercohomology
import Sheaf.CategoryTheory.TruncationTriangle
import Sheaf.CategoryTheory.RightDerivedFunctorTruncationIso
import Sheaf.CategoryTheory.DerivedCategory.ShiftIdentification
import Sheaf.CategoryTheory.KInjectiveBridge
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus

/-! # Individual natural truncation couples

Source: Stacks Project, Tags 015J, 05TC and 08J5; the individual construction and naturality
in steps 1, 3 and 4 of lem-pc-coproduct-truncation-couple.
(blueprint: lem-pc-natural-bounded-below-truncation-couples).
-/

@[expose] public section

universe v uA uB wA wB

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Choose truncation couples for individual derived objects with a fixed lower bound.
The comparisons commute with every individual morphism. No coproduct is involved.

Source: Stacks Project, Tags 015J, 05TC and 08J5; steps 1, 3 and 4 of
lem-pc-coproduct-truncation-couple.
(blueprint: lem-pc-natural-bounded-below-truncation-couples).

Proof:
1. Represent each object by its canonical lower truncation at `a`, then take a
bounded-below injective resolution (`CochainComplex.Plus.exists_quasiIso_injective`).
The derived localization comparison identifies
its cohomology and morphisms with those of the original object. Apply
`exists_truncationHypercohomology` to obtain its type-zero exact couple. This gives
D-vanishing below `a` and E-vanishing at negative first indices.
2. The inclusion of the upper truncation at `n` induces an isomorphism on degree
`n` cohomology after RF, by `isIso_homologyFunctor_rightDerivedFunctorPlus_truncLEι`.
Compose this with the localization and Plus compatibility comparisons to get `eD`.
3. The natural single-functor shift comparison, RF shift comparison and homology
shift comparison identify E at `(p,r)` with H^p RF(H^r(-)[0]); this is the first
shift identification, without the final comparison to ordinary right derived functors.
Compose with the localization comparison to obtain `eE`.
4. Represent a given morphism by a map between the chosen injective resolutions.
Naturality of the canonical truncation triangles, including the boundary map,
after applying RF and homology proves the alpha, f and g squares. These constitute
`T`. Naturality of the truncation inclusion proves the D equation. Naturality of
the three shift comparisons proves the E equation. All comparisons are invertible,
so writing these squares using inverses gives the displayed formulas. Zero objects
and morphisms require no exception; no smallness or coproduct assumption is used.
Choices witness only this existential proposition, and define no library object. -/
theorem exists_natural_boundedBelow_truncation_couples
    {A : Type uA} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]
    [HasDerivedCategory.{wA} A]
    {B : Type uB} [Category.{v} B] [Abelian B] [IsGrothendieckAbelian.{v} B]
    [HasDerivedCategory.{wB} B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] (a : ℤ) :
    let L := {M : DerivedCategory A // ∀ r : ℤ, r < a →
      IsZero ((DerivedCategory.homologyFunctor A r).obj M)}
    ∃ (Z : L → BigradedExactCouple B 0)
      (eD : ∀ (M : L) (n : ℤ), (Z M).D 0 n ≅
        (F.rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor B n).obj M.val)
      (eE : ∀ (M : L) (p : ℕ) (r : ℤ), (Z M).E p r ≅
        (DerivedCategory.singleFunctor A 0 ⋙ F.rightDerivedFunctor ⋙
          DerivedCategory.homologyFunctor B (p : ℤ)).obj
            ((DerivedCategory.homologyFunctor A r).obj M.val)),
      (∀ (M : L) (p r : ℤ), r < a → IsZero ((Z M).D p r)) ∧
      (∀ (M : L) (p r : ℤ), p < 0 → IsZero ((Z M).E p r)) ∧
      ∀ (M N : L) (c : M.val ⟶ N.val),
        ∃ T : BigradedExactCouple.CoupleMorphism (Z M) (Z N),
          (∀ n : ℤ, T.tD 0 n ≫ (eD N n).hom = (eD M n).hom ≫
            (F.rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor B n).map c) ∧
          (∀ (p : ℕ) (r : ℤ), T.tE p r ≫ (eE N p r).hom = (eE M p r).hom ≫
            (DerivedCategory.singleFunctor A 0 ⋙ F.rightDerivedFunctor ⋙
              DerivedCategory.homologyFunctor B (p : ℤ)).map
                ((DerivedCategory.homologyFunctor A r).map c)) := by sorry

end CategoryTheory
