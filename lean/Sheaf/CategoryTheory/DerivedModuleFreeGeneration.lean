/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Retract
import Sheaf.Algebra.Homology.FilteredFreeResolution
import Sheaf.CategoryTheory.DerivedModuleDirectSums

/-! # Generation of a module derived category by shifts of the ring

Source: literature/stacks-project/more-algebra.tex, Remark 15.60.11 (Tag 09PB)
(blueprint: lem-pc-derived-module-free-generation).

The property in the conclusion is the semantic description of the smallest full
subcategory containing the shifts of the free rank-one module and closed under
set-indexed coproducts, distinguished triangles, and retracts.
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Every object of the derived category of `R`-modules is generated from the shifts
of the free rank-one module `R[0]` (`singleFunctor 0`) by coproducts indexed in the
modules' universe, distinguished triangles (third vertex), and retracts. `R` is
commutative, as rings are in the source.
Source: More on Algebra, Remark 15.60.11 (Tag 09PB),
(blueprint: lem-pc-derived-module-free-generation).

Proof:
1. Represent `K` by a cochain complex and use
   `lem-pc-derived-filtered-free-resolution` to choose a quasi-isomorphic free
   resolution with an exhaustive filtration starting at zero, termwise split
   inclusions, and successive quotients that are sums of shifts of `R`.
2. The empty coproduct puts zero in `P`. By `lem-pc-derived-module-direct-sums`,
   each quotient and every shift of it is a coproduct of the prescribed generators
   in the derived category. Use `lem-weil-pbc-complex-ses-triangle` on each
   filtration short exact sequence. Rotate the triangle to place the shifted
   quotient first, the preceding filtration term second, and the next term third.
   Induction proves `P` for every filtration term and all its shifts.
3. The telescope sequence is exact: `1 - shift` on the sum of the filtration
   terms is injective (inspect the least nonzero summand), and its cokernel is
   their union, the free resolution. Apply `lem-weil-pbc-complex-ses-triangle`.
   By `lem-pc-derived-module-direct-sums`, both telescope vertices satisfy `P`,
   so the resolution, as the third vertex, satisfies `P`.
4. The resolution is isomorphic to `K` after localization. An isomorphism makes
   `K` a retract of the resolution, so retract closure gives `P K`. -/
theorem derivedModuleFreeGeneration (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{max u v} R)]
    (K : DerivedCategory (ModuleCat.{max u v} R)) :
    ∀ (P : ObjectProperty (DerivedCategory (ModuleCat.{max u v} R))),
      (∀ (n : ℤ), P (((DerivedCategory.singleFunctor
        (ModuleCat.{max u v} R) 0).obj (ModuleCat.of R (ULift.{v} R)))⟦n⟧)) →
      (∀ {I : Type (max u v)} (F : I → DerivedCategory (ModuleCat.{max u v} R))
        (S : DerivedCategory (ModuleCat.{max u v} R))
        (ι : ∀ i : I, F i ⟶ S), IsColimit (Cofan.mk S ι) →
        (∀ i : I, P (F i)) → P S) →
      (∀ (T : Pretriangulated.Triangle (DerivedCategory (ModuleCat.{max u v} R))),
        T ∈ Pretriangulated.distinguishedTriangles →
        P T.obj₁ → P T.obj₂ → P T.obj₃) →
      (∀ {X Y : DerivedCategory (ModuleCat.{max u v} R)},
        Retract X Y → P Y → P X) →
      P K := by
  sorry

end CategoryTheory
