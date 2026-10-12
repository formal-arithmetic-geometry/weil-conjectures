/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Sheaf.RingTheory.GRing
public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.IsLimit
import Sheaf.FieldTheory.SeparableExtension
import Sheaf.RingTheory.FilteredColimitOfFactorization
import Sheaf.RingTheory.PopescuFinalSolve
import Sheaf.RingTheory.PopescuReduceToField
import Sheaf.RingTheory.PopescuResolution
import Sheaf.RingTheory.PopescuResolveCharP
import Sheaf.RingTheory.PopescuResolveSeparable
import Sheaf.RingTheory.SingularIdeal

/-!
# Popescu smoothing

Source: Stacks Project, Smoothing Ring Maps, Theorem 07GC; Morphisms, Lemma 01V6
(blueprint: lem-weil-pbc-popescu-smoothing).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace RingHom

/-- A regular map of Noetherian rings presents its target as a filtered colimit of smooth
algebras, with the colimit universal property in commutative rings. The regular map
`φ : R → Λ` is the structure map `algebraMap R Λ` of an `[Algebra R Λ]` instance, as in the
landed Popescu modules. `R` and `Λ` share the universe `u` because the smoothness clause is
stated for `Spec.map` of a ring map in `CommRingCat.{u}`; the index category lives there too.
Source: Stacks Project, Theorem 07GC and Lemma 01V6
(blueprint: lem-weil-pbc-popescu-smoothing).

Proof:
1. By `lem-weil-pbc-popescu-reduce-to-field` (07F5), reduce to a field `k` and a
Noetherian geometrically regular `k`-algebra. Taking the trivial purely inseparable extension
shows its prime localizations are regular local rings.
2. Use `lem-weil-pbc-factorization-criterion-filtered-colimit` (07C3): it suffices to
factor each map from a finitely presented `k`-algebra through a smooth `k`-algebra. Smooth
algebras can be represented by polynomial quotients, so the resulting indexing category is small.
3. At a prime minimal over the radical of the extended singular ideal, resolve the local
problem using `lem-weil-pbc-popescu-resolve-separable` (07FE) in characteristic zero, with
`lem-weil-pbc-char-zero-field-extension-separable`; in positive characteristic use
`lem-weil-pbc-popescu-resolve-char-p` (07FJ).
4. Among radicals of extended singular ideals for finitely presented factorizations, choose a
maximal one by `lem-weil-pbc-noetherian-ideal-set-maximal`. If it is proper, choose a minimal
prime above it by `lem-weil-pbc-minimal-prime-over-proper-ideal`. The resolution of step 3
strictly enlarges the radical, contradicting maximality. Thus some radical is the unit ideal.
5. The singular ideal then also extends to the unit ideal. Apply
`lem-weil-pbc-popescu-final-solve` (07EU), and compose with the original factorization.
This establishes the criterion of step 2; step 1 returns the result for the original base ring.
6. Apply `lem-weil-pbc-smooth-ring-map-iff-smooth-affine` (01V6) to each stage and
`lem-weil-pbc-filtered-colimit-algebras-elementwise` (1) to obtain the colimit in rings.
-/
theorem popescu_smoothing {R Λ : Type u} [CommRing R] [CommRing Λ] [Algebra R Λ]
    [IsNoetherianRing R] [IsNoetherianRing Λ] (hφ : (algebraMap R Λ).IsRegular) :
    ∃ (J : Type u) (_ : SmallCategory J) (_ : IsFiltered J)
      (B : J ⥤ CommAlgCat.{u} R),
      (∀ j : J, AlgebraicGeometry.Smooth
        (Spec.map (CommRingCat.ofHom (algebraMap R (B.obj j))))) ∧
      ∃ ι : B ⟶ (Functor.const J).obj (CommAlgCat.of R Λ),
        Nonempty (IsColimit ((forget₂ (CommAlgCat.{u} R) CommRingCat.{u}).mapCocone
          { pt := CommAlgCat.of R Λ, ι := ι })) := by
  sorry

end RingHom
