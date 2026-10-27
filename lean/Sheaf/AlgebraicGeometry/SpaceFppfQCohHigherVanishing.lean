/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N5
-/
module

public import Sheaf.AlgebraicGeometry.SpaceFppfRingedComparison

import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.CategoryTheory.Sites.ModuleDerivedEvaluationSlice
import Sheaf.AlgebraicGeometry.AlgebraicSpaceModulePullbackQuasiCoherent
import Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv
import Mathlib.AlgebraicGeometry.Cover.Open
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-! # Higher big-fppf direct images of quasi-coherent modules vanish

Source: Stacks Project, More on Cohomology of Spaces, Tag 0DGN(7),
lemma-review-quasi-coherent (blueprint: lem-sfb-space-fppf-qcoh-higher-vanishing).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- A quasi-coherent small-étale module, extended by tensor-pullback sections to the
big fppf site, is acyclic for the module restriction direct image in positive degrees.
The chosen big site and its ring sheaf are normalized by their exact covering and
section formulas. `IsSpaceFppfSectionExtension` specifies the given module sheaf on
all spaces and all restriction maps, rather than assuming any acyclicity property.
Coefficient carriers are raised to `u+1` so that injective resolutions exist on the
chosen small big site; the target is the same small étale ringed topos with its
canonical lifted ring. No quasi-compactness, separation or finite-generation condition
is imposed on either the space or the module.

Source: Stacks Project, More on Cohomology of Spaces, Tag 0DGN(7),
lemma-review-quasi-coherent (blueprint: lem-sfb-space-fppf-qcoh-higher-vanishing).

Proof:
1. Module sheaves on the small big site form a Grothendieck abelian category and
   have enough injectives (prop-pur-kinjective-resolutions-exist,
   lem-sp-grothendieck-enough-injectives). The ringed higher-image cohomology-presheaf
   theorem identifies R^q a_* with the sheafification of the derived module sections
   on étale objects (lem-sfb-ringed-site-higher-image-cohomology-sheafification).
   The slice comparison lem-pe-ringed-site-derived-evaluation-slice identifies these
   groups with abelian cohomology of the localized fppf site.
2. Over an affine scheme étale chart U, identify the slice with spaces over U.
   Every such space has an étale scheme atlas. Covering refinement and composition
   (lem-sfb-space-fppf-covering-calculus) identify the induced topology on schemes
   with the scheme fppf topology. The dense-subsite equivalence
   lem-pc-fppf-dense-sheaf-equivalence gives an equivalence of abelian sheaves.
3. That equivalence is exact, preserves injectives by transporting their extension
   property, and preserves sections at the common terminal scheme U. Transport an
   abelian injective resolution to identify the two cohomology groups
   (lem-weil-pbc-site-sheaves-enough-injectives). No preservation of injectives by
   the forgetful functor from modules to abelian sheaves is needed.
4. Tensor pullback preserves quasi-coherence
   (lem-sfb-space-module-pullback-quasicoherent). The scheme Zariski/étale equivalence
   lem-trf-scheme-zariski-etale-quasi-coherent-equivalence supplies a quasi-coherent
   Zariski module on U. Its section extension is the restricted given fppf module:
   def-sfb-space-module-tensor-composition identifies pullbacks, and the normalized
   restriction maps are exactly tensor pullback. Apply
   lem-sfb-affine-scheme-fppf-qcoh-acyclic to obtain zero in every positive degree.
5. Every étale space object admits an étale scheme atlas and an affine refinement
   (def-trf-algebraic-space, lem-trf-space-enlarged-etale-ringed-site-model,
   lem-pc-fppf-affine-open-cover). The cohomology presheaf therefore vanishes on a
   covering of every object. Every map from it to a module sheaf is zero by
   separatedness, so its sheafification is zero
   (def-weil-presheaf-modules-sheafification). This includes the empty space, whose
   empty covering forces zero modules. The result follows from step 1.
-/
theorem space_fppf_qcoh_higher_vanishing
    {S : Scheme.{u}} (W : AlgebraicSpace S) (B : SpaceFppfSite W)
    (R : SpaceFppfRings B) (M : W.Modules) (hM : M.IsQuasicoherent)
    (F : SheafOfModules.{u + 1} R.rings) (_hF : IsSpaceFppfSectionExtension R M F)
    (i : ℕ) (hi : 0 < i) :
    IsZero ((R.directImage.rightDerived i).obj F) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
