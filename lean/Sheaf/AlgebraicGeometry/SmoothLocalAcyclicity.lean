/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NP
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Sheaf.AlgebraicGeometry.LocalAcyclicityAbelianSheaf
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.AlgebraicGeometry.StrictHenselization
import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization
import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.CategoryTheory.Limits.HasLimits
import Sheaf.Paper.StrictHenselizationFunctoriality
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import WeilConjectures.AlgebraicGeometry.ConstantSheafGeometricStalk
import WeilConjectures.AlgebraicGeometry.StrictlyHenselianSectionsStalk
import WeilConjectures.ConstructibleSheaf.Defs
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm
import Sheaf.AlgebraicGeometry.ExchangeStrictLocalCohomology
import Sheaf.AlgebraicGeometry.StrictHenselizationClosedLift
import Sheaf.AlgebraicGeometry.StrictLocalGeometricFibreTest
import Sheaf.AlgebraicGeometry.StrictlyHenselianConstantCohomology
import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem

/-!
# Smooth morphisms are universally locally acyclic

Source: Stacks Project, Tag 0GJQ, proposition-smooth-locally-acyclic
(blueprint: lem-weil-pbc-smooth-local-acyclicity).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- Smooth morphisms are universally locally acyclic, and in particular locally acyclic.
There is no properness or relative-dimension hypothesis.
Source: Stacks Project, Tag 0GJQ, proposition-smooth-locally-acyclic
(blueprint: lem-weil-pbc-smooth-local-acyclicity).

Proof:
1. Smoothness is stable under arbitrary base change (`lem-pc-proper-base-change` (2)),
so it suffices to prove local acyclicity for a smooth morphism.
2. Fix a geometric point x and a positive integer n prime to its residue characteristic.
Restrict the base to an affine basic open where n is invertible. This leaves the strict
localizations and their canonical map unchanged: pointed etale neighbourhoods refine
into these opens, and the inclusions are initial
(`lem-weil-pbc-colimit-initial-full-subcategory`,
`def-weil-pbc-strict-henselization-limit`,
`lem-weil-pbc-strict-henselization-functoriality`).
3. For any geometric point t of the strict localization of the base, apply smooth base
change to its composite into the base, with constant coefficients Z/n. This map is qcqs
(`lem-weil-pbc-qcqs-morphism-permanence`); its constant stalks are n-torsion
(`lem-weil-pbc-constant-sheaf-geometric-stalk`, `sbc-thm-smooth-base-change`).
4. The exchange isomorphism identifies the cohomology over the two strict localizations
(`lem-weil-pbc-exchange-strict-local-cohomology`). The geometric-fibre test then identifies
cohomology on the vanishing-cycle fibre with cohomology on t
(`lem-weil-pbc-strict-local-geometric-fibre-test`).
5. A geometric field is strictly henselian. Its constant cohomology vanishes in positive
degrees (`sbc-lem-strict-henselian-constant-cohomology`), and its constant-section map is
an isomorphism in degree zero (`lem-weil-pbc-strictly-henselian-sections-stalk`,
`lem-weil-pbc-constant-sheaf-geometric-stalk`). Inverse image preserves constant sheaves
(`lemma-constructible-pullback-constant`). By the constant-sheaf and inverse-image
adjunctions (`def-constructible-constant`, `def-weil-pbc-inverse-image`,
`def-weil-pbc-direct-image`), pullback sends each constant section to itself. Thus the
same constant-section identification and positive-degree vanishing hold on the fibre.
6. The canonical alpha first inverts the strict-local germ isomorphism and then restricts
to the fibre (`def-weil-pbc-local-acyclicity-abelian-sheaf`). The lift of x is the strict-local
closed point (`lem-weil-pbc-strict-henselization-functoriality`), and germ compatibility
(`lem-weil-pbc-inverse-image-stalk-germ`) identifies the section with germ m as the constant
section m. The adjunction calculation of step 5 shows its restriction is also constant m.
Hence alpha is precisely the degree-zero isomorphism above. All test points and n were
arbitrary, proving local acyclicity; step 1 gives universality. -/
theorem smooth_localAcyclicity {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f] :
    IsUniversallyLocallyAcyclic f ∧ IsLocallyAcyclic f := by
  sorry

end AlgebraicGeometry.Etale
