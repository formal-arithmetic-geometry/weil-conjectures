/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C2
-/
module

public import Sheaf.AlgebraicGeometry.FiniteTorDimensionOver
public import Sheaf.AlgebraicGeometry.DerivedTensorCohomologyVanishes
public import Sheaf.AlgebraicGeometry.ClosedSubsetProperOverBase
public import Sheaf.AlgebraicGeometry.Coherent
public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.Algebra.Homology.BoundedAboveFlatRingedSpaceKFlat
import Sheaf.Algebra.Homology.BoundedFlatReplacement
import Sheaf.Algebra.Homology.KFlatPullback
import Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import Sheaf.AlgebraicGeometry.DerivedPullbackTensorQCoh
import Sheaf.AlgebraicGeometry.DirectImageQCSupportReduction
import Sheaf.AlgebraicGeometry.FlatComplexDerivedPullback

/-! # Uniform lower tensor bound for a proper-support direct image

Source: Stacks Project, Tag 08EV, proof, the quasi-compact support reduction,
projection formula, and the lower bound after applying the right-derived direct image.
(blueprint: lem-pc-proper-direct-image-tensor-lower-bound)
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Proper-support direct image gives a uniform lower bound after tensoring with
quasi-coherent modules. No upper bound or arbitrary-module test is asserted here.
Source: Stacks Project, Tag 08EV, proof, lower-bound argument; Tags 08EU and 08DZ.
(blueprint: lem-pc-proper-direct-image-tensor-lower-bound)

Proof:
1. Boundedness leaves finitely many nonzero cohomology sheaves. Their supports have
   proper union over S. Choose a quasi-compact open U containing this union. Restriction
   to U is exact, preserves coherence and the finite Tor interval over the inverse-image
   structure sheaf, and leaves the derived direct image unchanged. The restricted morphism
   is quasi-compact and quasi-separated, since S is Noetherian and f locally of finite type.
   This is the geometric and exact-restriction argument of directImage_qc_support_reduction;
   choose a derived localization on U and compare it with the fixed localizations on X and S.
2. Fix a quasi-coherent module F on S. Resolve F by a bounded-above flat complex L
   zero in positive degrees, using bounded flat replacement. Its termwise pullback
   represents Lf*F and is K-flat. Associativity of tensor identifies
   E tensor^L_{O_X} Lf*F with E tensor^L_{f^{-1}O_S} f^{-1}F: inverse image is exact,
   the inverse images of the flat terms of L are flat, and bounded-above flat complexes
   are K-flat. Thus the finite Tor interval [a,b] of E bounds this object, uniformly in F.
3. E has quasi-coherent cohomology, and derived pullback and tensor preserve this property.
   The projection formula identifies Rf*E tensor^L F with the derived direct image
   of the object in step 2. A bounded-below K-injective resolution can be taken zero
   below a; termwise direct image remains zero below a. Its cohomology consequently
   vanishes there. Transport back through the support-reduction isomorphism and choose
   a K-flat representative of Rf*E to express this vanishing with the stated predicate.
   The integer a comes from E's finite Tor interval, so it is independent of F. -/
theorem exists_schemeDerivedDirectImage_tensor_lower_bound
    (S : Scheme.{u}) [IsNoetherian S]
    (X : Scheme.{u}) (f : X ⟶ S) [LocallyOfFiniteType f]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    (E : schemeDerivedCategory X)
    (hbounded : ∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i →
      IsZero ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).obj E))
    (hcoherent : ∀ i : ℤ,
      RingedSpace.IsCoherent X.toRingedSpace
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).obj E))
    (hsupport : ∀ i : ℤ,
      Scheme.Modules.HasSupportProperOver f
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).obj E))
    (hTor : HasFiniteTorDimensionOver f E) :
    ∃ a : ℤ, ∀ F : SheafOfModules.{u} (moduleRings S.toRingedSpace),
      F.IsQuasicoherent → ∀ i : ℤ, i < a →
        schemeDerivedTensorCohomologyVanishes S ((schemeDerivedDirectImage f).obj E) F i := by sorry

end AlgebraicGeometry.Scheme
