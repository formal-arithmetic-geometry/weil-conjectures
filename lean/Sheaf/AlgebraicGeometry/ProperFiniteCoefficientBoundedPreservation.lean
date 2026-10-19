/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Sheaf.Paper.ProjectionCompactification
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import Sheaf.AlgebraicGeometry.EtaleCompactificationConstructibility
import Sheaf.AlgebraicGeometry.FiniteTypeFibreDimensionBound
import Sheaf.AlgebraicGeometry.ProperTorsionDirectImageBound
import Sheaf.AlgebraicGeometry.SmoothBaseChange.HigherDirectImageForgetComparison
import WeilConjectures.AlgebraicGeometry.EtaleModuleSheavesGrothendieckAbelian
import Sheaf.AlgebraicGeometry.EtaleConstantModuleDirectImageLeftExact
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives
import WeilConjectures.CategoryTheory.TruncationTriangle
import Mathlib.CategoryTheory.Shift.ShiftSequence
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-!
# Proper direct image with arbitrary finite coefficients over Noetherian schemes

Source: Stacks Project, More on Etale Cohomology, Tag 0GL0,
`theorem-constructible-shriek`, with the identity-open compactification; Etale Cohomology,
Tag 095U, `lemma-cohomological-dimension-proper`; More on Etale Cohomology, Tag 0G2A,
`lemma-derived-lower-shriek-bounded`
(blueprint: lem-per-proper-finite-coefficient-bounded-preservation).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- Proper direct image preserves bounded constructibility for every finite commutative
coefficient ring on Noetherian schemes. Noetherian means a finite affine cover by spectra
of Noetherian rings, equivalently `AlgebraicGeometry.IsNoetherian`. There is no assumption
on the Krull dimensions of the schemes or invertibility of coefficients.

Source: Stacks Project, Tags 0GL0 and 095U; Tag 0G2A, proof of (3), proper case
(blueprint: lem-per-proper-finite-coefficient-bounded-preservation).

Proof plan, following the five steps of the node:
1. Finite affine covers give quasi-compactness (`lem-weil-pbc-affine-scheme-qcqs`)
and local Noetherianness (`pqf-def-locnoeth`), hence quasi-separatedness
(`lem-weil-pbc-locally-noetherian-quasi-separated`). Properness gives separatedness,
quasi-compactness and local finite type (`def-weil-proper-morphism`,
`def-weil-finite-type-morphism`). Over a locally Noetherian base, local finite type
implies local finite presentation (`pqf-lem-lft-fp-locnoeth`). Separatedness gives
quasi-separatedness (`lem-pc-separated-quasi-separated`), so the morphism is of finite
presentation (`def-weil-pbc-scheme-conventions`).
2. Choose a cohomological support interval [a,b] for L
(`def-weil-pbc-constructible-complexes`). For the identity-open compactification
(`def-weil-pbc-projection-compactification`), extension by zero is the identity termwise
from its sections and restrictions (`def-weil-pbc-extension-by-zero`). Thus the candidate
is Rf_*L. Apply `lem-weil-pbc-etale-compactification-constructibility` to obtain
constructibility of every cohomology sheaf, without coefficient invertibility.
3. The finite-type fibre-dimension bound (`lem-fin-finite-type-fibre-dimension-bound`)
provides one nonnegative d bounding all fibres, since the base is quasi-compact. No bound
on the dimensions of the source or target is used; empty fibres are allowed.
4. Finiteness of A gives a positive integer N killing 1 and hence every A-module section.
The proper torsion bound (`lem-kun-proper-torsion-cd-bound`) gives vanishing above 2d.
Use `lem-sbc-higher-direct-image-forget-comparison` to pass from abelian to module sheaves;
the forgetful functor reflects zero objects. Module sheaves are Grothendieck abelian
(`lem-weil-pbc-module-sheaves-grothendieck-abelian`), and direct image is additive left
exact (`lem-weil-pbc-module-direct-image-left-exact`). Negative vanishing
(`lem-weil-pbc-derived-functor-negative-vanishing`) gives the lower bound zero. Thus
Rf_* of a sheaf in degree zero is supported in [0,2d], also for the zero ring.
5. Enough injectives (`lem-weil-pbc-module-sheaves-enough-injectives`) and triangulatedness
(`lem-weil-pbc-derived-direct-image-triangulated`) allow application to the successive
truncation triangles (`lem-weil-pbc-truncation-triangle`). Start with the zero truncation
below a. For each r in [a,b], the third term is H^r(L)[-r]; step 4 and cohomological shifts
(`lem-sp-derived-cohomology-shift`) put its direct image in [r,r+2d]. Exactness of the long
cohomology sequence (`lem-sf-derived-homology-long-exact`) inductively bounds the middle
term in [a,b+2d]. The truncation at b is L. Together with step 2, this is exactly the
bounded-constructible predicate (`def-weil-pbc-constructible-complexes`). -/
theorem isBoundedConstructible_rightDerivedLowerStar_of_isProper_of_noetherian
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {Y S : Scheme.{u}} [IsNoetherian Y] [IsNoetherian S]
    (f : Y ⟶ S) [IsProper f]
    (L : DerivedCategoryModule A Y) (hL : DerivedCategory.isBoundedConstructible A Y L) :
    DerivedCategory.isBoundedConstructible A S
      ((rightDerivedLowerStar (ModuleCat.{u + 1} A) f).obj L) := by
  sorry

end AlgebraicGeometry.Etale
