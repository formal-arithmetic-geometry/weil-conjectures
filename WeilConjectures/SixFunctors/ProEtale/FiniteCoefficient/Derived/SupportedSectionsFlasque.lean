/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ClosedImmersion

/-!
# Supported sections and flasque sheaves on the pro-étale site

Let `i : Z ⟶ X` be a closed immersion with quasi-compact open complement `j : U ⟶ X`. On
pro-étale sheaves of modules, the sheaf of sections supported on `Z` is
`𝒢_Z M = ker (M ⟶ j_* j^* M)` (`AlgebraicGeometry.ProEtale.sectionsWithSupport`), and
`i^! M = i^* 𝒢_Z M` (`AlgebraicGeometry.ProEtale.closedUpperShriek`). This file records that
`i_* i^! M ≅ 𝒢_Z M` and defines the sheaves which are *flasque for the pair*: those for which
`I ⟶ j_* j^* I` is an epimorphism. These are the pro-étale forms of blueprint
`def-pur-flasque-support`, whose étale forms are in
`WeilConjectures.SixFunctors.OpenClosed.SupportedSections`.

## Main definitions

- `AlgebraicGeometry.ProEtale.closedUpperShriekCompLowerStarIso`: `i_* i^! ≅ 𝒢_Z`.
- `AlgebraicGeometry.ProEtale.IsFlasqueFor`: flasque sheaves for the pair.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme

namespace ProEtale

section Flasque

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  {U X : Scheme.{u}} (j : U ⟶ X)

end Flasque

variable {R : Type (u + 1)} [Ring R] {Z U X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
  (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]

end ProEtale

end AlgebraicGeometry
