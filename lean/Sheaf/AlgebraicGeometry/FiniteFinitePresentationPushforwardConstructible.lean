/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NG
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import Sheaf.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.SixFunctors.Finite.BaseChange
import Sheaf.AlgebraicGeometry.ConstructibleEtaleModuleQcqsAffineLocal
import Sheaf.AlgebraicGeometry.FiniteIsQuasiFinite
import Sheaf.AlgebraicGeometry.QuasiFiniteAffineEtaleThickeningDecomposition
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import Sheaf.AlgebraicGeometry.FiniteEtalePushforwardConstructible
import Sheaf.AlgebraicGeometry.ConstructibleModuleSurjectiveDescent

/-!
# Finite finitely presented pushforward preserves constructibility

Source: Stacks Project, Etale Cohomology, Tag 095R, lemma-finite-pushforward-constructible
(blueprint: lem-weil-pbc-finite-fp-pushforward-constructible).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Finite finitely presented pushforward preserves constructible module sheaves on qcqs
schemes over a finite commutative coefficient ring.

Source: Stacks Project, Etale Cohomology, Tag 095R,
lemma-finite-pushforward-constructible, finite-ring and qcqs specialization
(blueprint: lem-weil-pbc-finite-fp-pushforward-constructible).

Proof:
1. Work over affine opens of Y, whose inverse images are affine by finiteness.
   Localize finite presentations to retain the finite-presentation hypotheses.
   Use lem-weil-pbc-constructible-etale-module-sheaf-comparison,
   prop-constructible-pullback and lem-weil-pbc-constructible-qcqs-affine-local.
   The restriction of direct image agrees with the restricted morphism's direct
   image, sectionwise or by lemma-weil-pbc-finite-exchange.
2. Apply pqf-lem-finite-qf and
   lem-weil-pbc-quasifinite-affine-etale-thickening-decomposition to obtain an
   affine surjection a : Y' → Y and a surjective closed immersion i : Z → X'
   for X' = X ×_Y Y', such that e : Z → Y' is finite etale.
   By lem-weil-pbc-finite-morphism-permanence, X' is affine and finite over Y';
   Z is affine as a closed subscheme. No flatness of a is needed.
3. Pull back F to F' on X' and then to H on Z. Both are constructible by
   prop-constructible-pullback and the module-sheaf comparison, with unchanged
   constant coefficient ring (def-weil-pbc-inverse-image).
4. By sbc-lem-thickening-etale-site, i induces an equivalence of etale topoi.
   It preserves constant rings and products, hence module objects and their
   morphisms, and identifies F' with i_*H through the adjunction unit.
   The sectionwise composition isomorphism identifies f'_*F' with e_*H.
5. Apply lem-weil-pbc-finite-etale-pushforward-constructible to e and H.
   Transport constructibility to f'_*F' by lemma-constructible-iso-invariance
   and lem-weil-pbc-constructible-etale-module-sheaf-comparison.
6. Finite exchange identifies a^*(f_*F) with f'_*F'. Apply
   lem-weil-pbc-constructible-module-surjective-descent to the affine surjection a.
   The affine-local criterion from step 1 finishes the original qcqs case. -/
theorem isConstructibleEtaleModuleSheaf_lowerStar_of_finite_finitePresentation
    {X Y : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y] (f : X ⟶ Y) [IsFinite f]
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : IsConstructibleEtaleModuleSheaf F) :
    IsConstructibleEtaleModuleSheaf ((Etale.lowerStar (ModuleCat.{u + 1} Λ) f).obj F) := by
  sorry

end AlgebraicGeometry.Scheme
