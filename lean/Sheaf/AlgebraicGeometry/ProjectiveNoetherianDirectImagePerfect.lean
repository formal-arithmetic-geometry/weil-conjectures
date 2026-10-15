/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NJ
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.Coherent
import Sheaf.AlgebraicGeometry.CechResolution
import WeilConjectures.AlgebraicGeometry.Cohomology.Projective
import Mathlib.RingTheory.Flat.Localization
import Sheaf.CategoryTheory.DerivedCategory.NoetherianFlatComplexPerfect

/-! # Perfect direct image for a projective Noetherian family

Source: blueprint sec-picard-framework/sk-thm-picard-semicon,
node lem-pc-projective-noetherian-rf-perfect, order 673
(blueprint: lem-pc-projective-noetherian-rf-perfect).
-/

@[expose] public section

universe u wX wS

open CategoryTheory

namespace AlgebraicGeometry

/-- A coherent module flat over a locally Noetherian base has perfect derived direct image
under a projective morphism. Source: blueprint sec-picard-framework/sk-thm-picard-semicon,
node lem-pc-projective-noetherian-rf-perfect, order 673.

Proof:
1. Perfectness is local on S. Restrict to an affine open Spec A with A Noetherian.
   Projectivity makes X quasi-compact and separated over this affine base. Choose a finite
   affine cover; its finite intersections are affine. The bounded alternating Cech complex
   computes the derived direct image (lem-pc-cech-resolution).
2. Each term is a finite direct sum of flat A-modules. On an affine intersection Spec B,
   write the restriction of G as the sheaf associated to M. For an injection N' into N,
   localize the kernel of M tensor_A N' to M tensor_A N at every prime q of B. Relative
   flatness makes M_q flat over A_p, where p is the inverse image of q, so every localized
   kernel vanishes. Thus the kernel vanishes and M is A-flat
   (lem-pc-affine-sections-flat-over-base).
3. Projective coherent finiteness gives finite cohomology modules over A
   (lem-pc-projective-coherent-finiteness). A bounded flat complex over a Noetherian ring
   with finite cohomology has a bounded finite projective representative
   (lem-pc-noetherian-flat-complex-perfect). This proves perfectness locally on S.
(blueprint: lem-pc-projective-noetherian-rf-perfect). -/
theorem isPerfect_projective_noetherian_derivedDirectImage
    {X S : Scheme.{u}} [IsLocallyNoetherian S] (f : X ⟶ S) [IsProjective f]
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wS} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    [∀ U : S.Opens,
      HasDerivedCategory.{wS} (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U))]
    (G : X.Modules) (hGcoherent : RingedSpace.IsCoherent X.toRingedSpace G)
    (hGflat : Scheme.Modules.IsFlatOver G f) :
    Scheme.IsPerfect S ((schemeDerivedDirectImage f).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj G)) := by
  sorry

end AlgebraicGeometry
