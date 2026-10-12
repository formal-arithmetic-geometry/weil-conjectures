/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H3
-/
module

public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Mathlib.Topology.QuasiSeparated

import Sheaf.AlgebraicGeometry.SupportedPerfectDetectorAffine
import Sheaf.AlgebraicGeometry.SupportedOpenPushforward
import Sheaf.Algebra.Homology.OpenRestrictionAdjunctionExact
import Sheaf.AlgebraicGeometry.DerivedDirectImagePreservesQCoh
import Sheaf.AlgebraicGeometry.SupportedDerivedRestrictionZero
import Sheaf.AlgebraicGeometry.DerivedRestrictionIsIsoOpenCover

/-! # A supported Koszul relative detector

Source: Stacks Project, Tag 0A9A, induction step.
(blueprint: lem-pc-supported-koszul-relative-detector).
-/

@[expose] public section

set_option autoImplicit false

universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- The Koszul object on the affine complement detects supported objects zero on U.
Source: Stacks Project, Tag 0A9A, affine and supported Koszul construction paragraphs.
(blueprint: lem-pc-supported-koszul-relative-detector).

Proof: Put S = T intersect (X minus U), closed in X and contained in V. Its complement
in V is W = (U intersect V) union (V minus T), quasi-compact by quasi-separatedness,
compactness of U, and compactness of X minus T. Apply the already stated affine
supported perfect detector on V with support S to obtain B, perfect and quasi-coherent.
Its extension by zero A
is isomorphic to derived open pushforward, hence perfect and supported on S by supported
open pushforward. Quasi-compactness of the affine inclusion and quasi-separatedness
of X make its direct image preserve quasi-coherent cohomology. Restriction of A to U
is zero because S is disjoint from U. For C supported on T with C restricted to U zero,
its cohomology on V is supported on S. Exact extension-by-zero adjunction transfers
orthogonality to all shifts of A to orthogonality of C restricted to V to all shifts
of B. The affine Koszul detector therefore makes C restricted to V zero. Since C is
zero on U already, stalkwise homology detection on the cover U,V makes C zero globally.
If U is top take the zero Koszul object; if U is empty this is affine detection.
If T is empty, every supported object is already zero. No right adjoint is used here. -/
theorem exists_supported_koszul_relative_detector
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (T : Set X) (hT : IsClosed T) (hTc : IsCompact Tᶜ)
    (U : X.Opens) (V : X.affineOpens) (hU : IsCompact (U : Set X))
    (hcover : U ⊔ (V : X.Opens) = ⊤) :
    ∃ A : schemeDerivedQCohCategory X, Scheme.IsPerfect X A.obj ∧
      (∀ (n : ℤ) (x : X), x ∉ T →
        Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj A.obj).val.presheaf x))) ∧
      IsZero ((SheafOfModules.overFunctor.{u}
        (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj A.obj) ∧
      ∀ C : schemeDerivedQCohCategory X,
        (∀ (n : ℤ) (x : X), x ∉ T →
        Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj C.obj).val.presheaf x))) →
        IsZero ((SheafOfModules.overFunctor.{u}
          (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj C.obj) →
        (∀ n : ℤ, Subsingleton (A.obj⟦n⟧ ⟶ C.obj)) → IsZero C.obj := by sorry

end AlgebraicGeometry
