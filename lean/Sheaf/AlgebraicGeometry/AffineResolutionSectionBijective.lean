/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Sheaf.AlgebraicGeometry.FlatBaseChangeOpenChoices
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

/-! # Bijectivity of the normalized affine section class map

Source: Stacks Project, Tags 01F4, 01XJ and 01E4.
(blueprint: lem-pc-affine-resolution-section-bijective)
-/

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] enoughInjectives

/-- The canonical restricted-resolution class map is bijective over an affine base open.
There is no Ext comparison or choice of cohomology coordinates in this assertion.
Source: Stacks Project, Tags 01F4 (2), 01XJ (1), 01E4 and 01E5.
(blueprint: lem-pc-affine-resolution-section-bijective)

Proof: Set U = f inverse V, g = f restricted to U -> V, and M = F restricted to U.
Restriction preserves quasi-coherence, and g is qcqs by base change. Its ordinary higher
images are quasi-coherent by 01XJ. Their positive cohomology vanishes because V is affine.
Thus the cocycle-defined Leray edge in 01F4 is invertible. Open restriction identifies its
target with sections over V of R^p f_* F. To identify the particular map, represent a
cohomology class by a cocycle in the global section complex of R.resolution. The equation
R.components sends this cocycle to its restriction in the original resolution I on U.
R.augmentation makes the induced comparison the identity on the resolved module, so the
resolution comparisons induce the same derived class. The cocycle formula for the edge
sends that representative to its class in the homology sheaf of f_* I. Exact evaluation
and the sheafification unit give precisely sectionCohomologyTheta by 01E4. Composing with
the inverse of I.isoRightDerivedObj gives the displayed map. Since all other maps are
isomorphisms, this class map is bijective. At p = 0 the argument is the augmentation
comparison; for empty V or zero F it is the unique map between zero groups. -/
theorem affine_resolutionSectionClass_bijective
    {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    (F : X.Modules) [F.IsQuasicoherent] (I : InjectiveResolution F)
    (p : ℕ) (V : S.Opens) (hV : IsAffineOpen V)
    (R : RestrictedResolutionSections I (f ⁻¹ᵁ V)) :
    Function.Bijective
      (resolutionSectionClass R.resolution
      (((pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex)
      V R.sections p ≫ Hom.app (I.isoRightDerivedObj (pushforward f) p).inv V) := by sorry

end AlgebraicGeometry.Scheme.Modules
