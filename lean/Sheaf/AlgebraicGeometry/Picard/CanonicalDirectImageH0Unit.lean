/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U3
-/
module

public import Sheaf.AlgebraicGeometry.Picard.CanonicalSingleDirectImageComparison
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage

/-! # Degree-zero normalization of the canonical direct-image unit

Source: Stacks Project, Tags 079V and 0A1G.
(blueprint: lem-pc-canonical-direct-image-h0-unit).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory Limits
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

/-- The H⁰ comparison for direct image takes the canonical single-module unit to
 the single-complex homology identification.
Source: Stacks Project, Tags 079V and 0A1G; Mathlib's injective-resolution
construction of `rightDerivedZeroIsoSelf`.
(blueprint: lem-pc-canonical-direct-image-h0-unit).

Proof: The universal-property factorization for
`rightDerivedFunctorPlusCompatibility` carries the unbounded right-derived unit
to the bounded-below unit. Evaluate it on the single complex of M. Naturality of
the bounded-below unit along the injective-resolution augmentation identifies its
H⁰, after `homologyRightDerivedFunctorPlusObjSingleFunctorIso`, with the classical
map `toRightDerivedZero`. The single-map direct-image comparison cancels the
single-complex comparison in this computation. Pushforward is left exact, so
`rightDerivedZeroIsoSelf` is inverse to `toRightDerivedZero`; their composite is
the identity. Consequently the displayed composite is the canonical single
homology identification, not an unspecified isomorphism. No positive-cohomology
vanishing is assumed. Zero modules and empty schemes use the same augmentation
and inverse-cancellation formulas. -/
theorem canonicalDirectImageH0Unit {X S : Scheme.{u}} (f : X ⟶ S)
    [HasInjectiveResolutions X.Modules] (M : X.Modules) :
    (DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0).map
        (canonicalSingleDirectImageMap f M) ≫
      (Functor.homologyRightDerivedFunctorObjSingleFunctorIso
        (RingedSpace.moduleDirectImage f.toLRSHom.toShHom) M 0 ≪≫
          (pushforward f).rightDerivedZeroIsoSelf.app M).hom =
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso
      (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0).app
        ((pushforward f).obj M)).hom := by sorry

end AlgebraicGeometry.Scheme.Modules
