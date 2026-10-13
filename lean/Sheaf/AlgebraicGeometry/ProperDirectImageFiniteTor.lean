/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Sheaf.AlgebraicGeometry.FiniteTorDimensionOver
public import Sheaf.AlgebraicGeometry.FiniteTorDimension
public import Sheaf.AlgebraicGeometry.ClosedSubsetProperOverBase
public import Sheaf.AlgebraicGeometry.Coherent
public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.Algebra.Homology.BoundedAboveFlatRingedSpaceKFlat
import Sheaf.Algebra.Homology.BoundedFlatReplacement
import Sheaf.Algebra.Homology.KFlatPullback
import Sheaf.AlgebraicGeometry.DerivedDirectImageUniformTruncationBound
import Sheaf.AlgebraicGeometry.DerivedPullbackTensorQCoh
import Sheaf.AlgebraicGeometry.DirectImageBoundedCoherent
import Sheaf.AlgebraicGeometry.DirectImageQCSupportReduction
import Sheaf.AlgebraicGeometry.FlatComplexDerivedPullback
import Sheaf.AlgebraicGeometry.TorAmplitudeQCohTest
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections

/-! # Proper-support direct image of a finite-Tor complex

Source: Stacks Project, Derived Categories of Schemes, Lemma 36.27.1 (Tag 08EV),
proof from “Hence it suffices to show that Rf_*E has finite tor dimension” to the end
(blueprint: lem-pc-proper-direct-image-finite-tor).
-/

@[expose] public section

universe u₁ v₁
universe w₁

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- A bounded coherent complex with proper cohomological support and finite Tor dimension
over the inverse-image structure sheaf has a derived direct image of finite Tor dimension.
The proof is the finite-Tor part of Stacks Tag 08EV: reduce to a quasi-compact morphism,
compute the projection formula using bounded-above flat resolutions, apply the uniform
cohomological bound for direct image, and test arbitrary modules using quasi-coherent
modules. (blueprint: lem-pc-proper-direct-image-finite-tor)

Proof:
1. The proper-support reduction gives a quasi-compact open containing all supports and
   preserves the finite-Tor interval under restriction; the uniform direct-image bound
   then applies.
2. A bounded-above flat resolution of a test module computes both derived pullback and
   the tensor over the inverse-image structure sheaf, so the assumed interval controls
   the resulting complex.
3. The projection formula and the uniform direct-image bound give a finite interval for
   all quasi-coherent test modules; the quasi-coherent test criterion extends this to all
   modules, proving finite Tor dimension of the direct image.
-/
theorem hasFiniteTorDimension_schemeDerivedDirectImage_of_bounded_coherent_support
    (S : Scheme.{u₁}) [IsNoetherian S]
    (X : Scheme.{u₁}) (f : X ⟶ S) [LocallyOfFiniteType f]
    [HasDerivedCategory.{w₁} (SheafOfModules.{u₁} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w₁} (SheafOfModules.{u₁} (moduleRings S.toRingedSpace))]
    (E : schemeDerivedCategory X)
    (hbounded : ∃ a b : ℤ, a ≤ b ∧ ∀ i : ℤ, i < a ∨ b < i →
      IsZero ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u₁} (moduleRings X.toRingedSpace)) i).obj E))
    (hcoherent : ∀ i : ℤ,
      RingedSpace.IsCoherent X.toRingedSpace
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u₁} (moduleRings X.toRingedSpace)) i).obj E))
    (hsupport : ∀ i : ℤ,
      Scheme.Modules.HasSupportProperOver f
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u₁} (moduleRings X.toRingedSpace)) i).obj E))
    (hTor : HasFiniteTorDimensionOver f E) :
    HasFiniteTorDimension S ((schemeDerivedDirectImage f).obj E) := by
  sorry

end AlgebraicGeometry.Scheme
