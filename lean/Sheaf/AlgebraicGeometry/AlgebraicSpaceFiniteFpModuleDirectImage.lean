/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N5
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

import Sheaf.AlgebraicGeometry.SpaceLocalPropertiesChartTest
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Sheaf.AlgebraicGeometry.SpaceAffineModuleBaseChange
import Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleModulePushforwardRestriction
import Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
import Sheaf.AlgebraicGeometry.ChartwiseEtalePermanence

/-! # Finite presentation under finite finitely presented direct image

Source: Stacks Project, Descent on Spaces, Tag 0610,
lemma-finite-finitely-presented-module; Cohomology of Spaces, Tag 07U8,
lemma-affine-base-change (quasi-coherence clause)
(blueprint: lem-sfb-space-finite-fp-module-direct-image).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- A finite finitely presented morphism has quasi-coherent module direct image and
preserves and reflects finite presentation of quasi-coherent modules.
Source: Stacks Project, Descent on Spaces, Tag 0610; Cohomology of Spaces, Tag 07U8
(blueprint: lem-sfb-space-finite-fp-module-direct-image).

Proof:
1. Choose a surjective etale scheme atlas V of Y and form U = X ×_Y V. Finiteness
makes U a scheme and U → V finite. The fibre-product covering theorem makes U → X
surjective etale. The local-properties chart test gives local finite presentation of
U → V. Affine-morphism permanence gives quasi-compactness and separatedness of this
finite scheme morphism. Restriction of the local presentations makes M|U quasi-coherent.
2. Every affine scheme test of f is finite over an affine scheme, hence affine. Thus f
is affine, and lem-sfb-space-affine-module-base-change gives quasi-coherence of f_*M.
The etale-module-pushforward-restriction theorem identifies (f_*M)|V with the direct
image of M|U, including its scalar action and compatible-section projections.
3. The scheme Zariski-etale quasi-coherent equivalence identifies M|U with the etale
extension of a Zariski module F. Its quasi-compact separated pushforward comparison
identifies the etale direct image with the extension of the Zariski direct image of F.
The exact-finiteness comparison equates finite presentation on the two sites.
The scheme finite-pushforward preservation and reflection lemmas (Tag 05B4) now give
finite presentation of M|U if and only if that of (f_*M)|V.
4. Finite presentation is local on the small etale site: restrict each finite free
presentation to an atlas in one direction and compose its covering families with the
atlas in the other. Chartwise-etale permanence and etale module restriction justify
these operations on the structure sheaves. Apply this to both atlases to obtain the
claimed equivalence, together with quasi-coherence from step 2. No finite atlas,
Noetherian hypothesis, flatness, or absolute quasi-compactness is used. -/
theorem finite_fp_moduleDirectImage
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (hf : IsRepresentableWith (fun _ _ p ↦ IsFinite p.left) f.hom.hom)
    (hfp : MapIsLocallyOfFinitePresentation f ∧ MapIsQuasiCompact f.hom.hom ∧
      MapIsQuasiCompact (pullback.diagonal f.hom.hom))
    (M : X.Modules) [M.IsQuasicoherent] :
    ((moduleDirectImage f).obj M).IsQuasicoherent ∧
      (M.IsFinitePresentation ↔ ((moduleDirectImage f).obj M).IsFinitePresentation) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
