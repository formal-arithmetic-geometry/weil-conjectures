/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedArtinSchreier
public import WeilConjectures.AlgebraicGeometry.ArtinSchreierCover
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.CategoryTheory.RingObjects.GlobalSections
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence
public import WeilConjectures.CategoryTheory.ModuleObjects.RegularEnd
public import WeilConjectures.SmoothPurity.CondensedOrdinaryCompactSections
public import WeilConjectures.AlgebraicGeometry.ProEtale.Module.ProEtaleModuleObjects
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.AlgebraicGeometry.Scheme
import WeilConjectures.FourierTransform.ArtinSchreierCohomology
import WeilConjectures.Algebra.Homology.Coefficient.CoefficientRestrictionSectionsAcyclic
import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductEvaluation

/-! # Ordinary cohomology of a linear Artin–Schreier character

Source: latest blueprint, sec-fourier-transform/sk-lem-wft-character-integral,
lem-fd-cohomology-affine-line-character, statement and proof
(blueprint: lem-fd-cohomology-affine-line-character).

The input sheaf is the image of the specified prime-cover projector. Cohomology is
right derived global sections in the category of actual condensed coefficient modules.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ArtinSchreierTrace

/-- The global function ax on the geometric affine line. This is a specialization
of the scalar-section construction and the existing affine-space coordinate.
Source: blueprint lem-fd-cohomology-affine-line-character, the cover of ax
(blueprint: lem-fd-cohomology-affine-line-character). -/
abbrev geometricAffineLinearFunction (k K : Type u) [Field k] [Field K] [Algebra k K]
    (a : k) : Γ(AffineSpace PUnit (Spec (.of K)), ⊤) :=
  scalar K (AffineSpace PUnit (Spec (.of K))) (algebraMap k K a) *
    AffineSpace.coord (Spec (.of K)) PUnit.unit

end AlgebraicGeometry.ArtinSchreierTrace
