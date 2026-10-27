/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P5
-/
module

public import Sheaf.Paper.SupportedModelHull
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-! # Restriction stability of supported model hulls

Source: steps 2--3 of lem-sfb-supported-hull-proetale-descent, an agent-formulated
obligation in the ordinary coefficient setting of HRS Sections 3--4.
(blueprint: lem-sfb-supported-model-hull-pullback).
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Degree-zero supported hull membership is stable under qcqs pro-etale restriction.
No admissibility condition on the commutative condensed coefficient ring is needed.

Source: steps 2--3 of lem-sfb-supported-hull-proetale-descent; exact localization,
module base-change mates and internal/section-module transport.
(blueprint: lem-sfb-supported-model-hull-pullback)

Proof: identify the site of W with the localization of the site of T at r. On
section-ring modules inverse image is restriction of sections and hence exact and
product preserving. Its left adjunction makes it preserve colimits. Termwise
restriction therefore preserves ordinary derived products, shifts, triangles and
retracts, and takes strict filtered diagrams with common lower bound to diagrams
with the same bound. Base-change every edge of a support chain. Quasi-compact opens
remain such, and the complement of a closed edge is the pullback of its original
quasi-compact open complement. All chain vertices are qcqs, by induction using
closed-subset compactness and the affine-cover criterion. The module base-change
mates identify restriction of the supported extension with extension of the
restriction. Restricting the cover and the finite scalar presentation proves that
its final module is still a finite scalar local model. Thus the inverse image of
any admissible target class is an admissible source class. Apply the intersection
property to obtain stability for all derived objects, and the exact-single
comparison to obtain the displayed degree-zero assertion. This uses no descent of
hull membership. Empty schemes, identity restrictions and zero models are included.
-/
theorem supportedModelHull_pullback_single
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (W T : Scheme.{u})
    [CompactSpace W] [QuasiSeparatedSpace W] [CompactSpace T] [QuasiSeparatedSpace T]
    (r : W ⟶ T) [WeaklyEtale r] [QuasiCompact r] [QuasiSeparated r]
    (N : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T))
    (hN : supportedModelHull Λ T ((DerivedCategory.singleFunctor _ 0).obj N)) :
    supportedModelHull Λ W ((DerivedCategory.singleFunctor _ 0).obj
      ((CondensedRing.upperStar Λ r).obj N)) := by sorry

end AlgebraicGeometry.ProEtale
