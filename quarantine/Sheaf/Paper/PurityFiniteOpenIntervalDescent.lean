/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q36
-/
module

public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.AlgebraicGeometry.IntrinsicConstructibleIntervals
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Mathlib.AlgebraicGeometry.OpenImmersion
import Sheaf.AlgebraicGeometry.ProEtaleStalkConservative
import Sheaf.AlgebraicGeometry.ProEtalePullbackLocallyConstant
import Sheaf.CategoryTheory.ConstantLeftModuleInverseImage
import Sheaf.AlgebraicGeometry.ProEtaleInverseImageStalk
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
import Sheaf.AlgebraicGeometry.ProEtaleObjectInverseImageRestriction
import WeilConjectures.AlgebraicGeometry.EtaleStratificationLocalGluingCore
import Sheaf.Paper.ProEtaleFiniteModelStalks
import Sheaf.AlgebraicGeometry.ProEtaleConstantSheafStalk
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Sheaf.Paper.ProEtaleLocallyConstantSheafOfUniverses
import Sheaf.Paper.SfCommonStageWeilCohomology
import WeilConjectures.CategoryTheory.SiteMorphismComposition
import Mathlib.Topology.Constructible
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Properties

/-!
# Constructible interval descent on a finite open cover

Source: blueprint main-20261015, thm-pur-general-admissibility.proof.md, Step 4;
Stacks Project, etale-cohomology.tex, Tags 095E and 095F
(blueprint: lem-pur-finite-open-interval-descent).
-/

@[expose] public section
set_option autoImplicit false
universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme

namespace WeilConjectures

/-- Constructible cohomological bounds descend on a finite open cover, without any
boundedness, etale-origin or Tor assumption on the ambient complex. The second clause
allows different bounded constructible intervals on different cover members. The last
clause records the empty-scheme convention as a categorical zero object.
Source: blueprint main-20261015, thm-pur-general-admissibility, Step 4; Stacks Project,
etale-cohomology.tex, Tags 095E/095F
(blueprint: lem-pur-finite-open-interval-descent).

Proof:
1. Finite type over the field makes X Noetherian and quasi-separated, by
lem-weil-pbc-finite-type-over-noetherian and lem-weil-pbc-locally-noetherian-quasi-separated.
Use lem-weil-pbc-affine-opens-basis and quasi-compactness to refine to a finite affine
cover subordinate to the given cover; no separatedness or affine intersections are needed.
2. By lem-weil-proetale-weakly-etale-localization and
lem-sfb-proetale-object-inverse-image-restriction, pullback to an open is site restriction.
By lem-pur-site-restriction-module-adjunction-exact it is exact, so termwise restriction
computes derived restriction on arbitrary complexes and commutes with every cohomology
sheaf (def-weil-derived-cohomology-sheaves).
3. The open cover is a pro-etale cover: on every affine open choose a finite affine
refinement. Outside [r,s] all restricted cohomology sheaves vanish. Apply covering-family
vanishing in lem-cbc-proetale-stalk-conservative, without geometric-stalk conservativity.
4. Local constancy with finite stalks is preserved by any scheme pullback. Indeed choose
trivializing members (def-weil-proetale-locally-constant-sheaf), discard empty ones, and
use lem-pur-proetale-inverse-image-stalk, lem-pe-constant-left-module-inverse-image and
lem-weil-proetale-constant-sheaf-stalk to see the constant models are finite. Base change
of their covers (lem-exc-proetale-pullback-locally-constant) and
lem-weil-pbc-proetale-finite-model-stalks prove the assertion.
5. Intersect each chart's finite constructible locally closed partition with the finite
affine refinement. Noetherianity makes these strata constructible. Inverse images compose
by lem-weil-pbc-site-morphism-composition and lem-pe-constant-left-module-inverse-image,
so step 4 preserves the required local constancy and finite stalks on these strata.
6. Apply lem-weil-pbc-etale-stratification-local-gluing-core to get a finite global
immersed stratification factoring through chart strata. Pull back along these actual
factorizations and use step 4. This proves constructibility of each cohomology sheaf.
7. Step 3 gives vanishing outside the finite interval; steps 5--6 give constructibility
inside it, and zero sheaves are constructible. This is exactly
 def-weil-finite-torsion-constructibility and def-weil-constructible-intervals.
8. For bounded constructible restrictions and a nonempty finite index set choose local
intervals, take their minimum lower and maximum upper endpoints, and apply steps 1--7.
For the empty scheme the empty family covers the final pro-etale object. Cover detection
makes every module sheaf zero and every derived morphism invertible, hence F is zero.
Its cohomology vanishes in every degree and the empty partition is constructible. This
also handles the empty cover and every displayed interval. -/
theorem purityFiniteOpenIntervalDescent
    (P : PurityFiniteSetting.{u})
    (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of P.field.k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of P.field.k))]
    (J : Type v) [Finite J] (U : J → X.Opens)
    (hcover : ∀ x : X, ∃ t : J, x ∈ U t)
    (F : proEtaleDerivedCategory X P.Ring) :
    (∀ r s : ℤ, r ≤ s →
      (∀ t : J, constructibleInterval P.coefficients.l P.extension P.level P.level_pos
        (U t).toScheme r s
        ((proEtaleConstantRingDerivedPullback P.Ring (U t).ι).obj F)) →
      constructibleInterval P.coefficients.l P.extension P.level P.level_pos X r s F) ∧
    ((∀ t : J, intrinsicFiniteTorsionConstructible P.coefficients.l P.extension
      P.level P.level_pos (U t).toScheme
        ((proEtaleConstantRingDerivedPullback P.Ring (U t).ι).obj F)) →
      intrinsicFiniteTorsionConstructible P.coefficients.l P.extension
        P.level P.level_pos X F) ∧
    (IsEmpty X → IsZero F) := by
  sorry

end WeilConjectures
