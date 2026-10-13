/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D3
-/
module

public import Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.Algebra.Module.Torsion.Free

import Sheaf.AlgebraicGeometry.Morphisms.NormalizationStalkBaseChange

/-! # Torsion-freeness of normalization stalks over a punctured DVR

Source: Stacks Project, Tags 0307, 035I and 0539.
-/

@[expose] public section
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- The relative normalization of a finite etale cover of an open has torsion-free
stalks over any DVR stalk at a point outside that open.

Source: Stacks Project, Tag 0307 (localization of integral closure), Tag 035I
(relative normalization), and Tag 0539 (the subsequent torsion-free flatness criterion).
(blueprint: lem-sbc-punctured-dvr-normalization-stalk-torsion-free)

Proof: Base change along Spec O_{X,s} -> X, where s is the image of x. Relative
normalization commutes with this localization (0307). Since s is outside U, its
inverse image in the DVR spectrum omits the closed point, hence is either empty
or the generic point. In the empty case its normalization is empty and there is
no x. Otherwise the base-changed cover is a finite etale scheme over the fraction
field K of the DVR R, hence affine with a finite K-algebra B. The relative
normalization is Spec of the integral closure C of R in B. The inclusion C -> B
makes C torsion-free as an R-module: each nonzero element of R becomes invertible
in K and acts injectively on B. Localizing C at any source prime preserves this
injectivity, so its local rings are torsion-free over R. The base-change comparison
identifies the local ring at the point over x with the original source stalk, and
identifies the R-action with the displayed stalk map. Thus the original stalk is
torsion-free. No finiteness of the normalization is needed; etaleness also ensures
that the generic algebra has no nilpotents, although torsion-freeness uses only its
K-module structure. -/
theorem punctured_dvr_normalization_stalk_torsionFree
    {X : Scheme.{u}} [IsLocallyNoetherian X] (U : X.Opens)
    {P : Scheme.{u}} (p : P ⟶ U.toScheme) [IsFinite p] (hetale : Etale p)
    (x : (p ≫ U.ι).normalization)
    (hs : (p ≫ U.ι).fromNormalization x ∉ U)
    [IsDomain (X.presheaf.stalk ((p ≫ U.ι).fromNormalization x))]
    [IsDiscreteValuationRing (X.presheaf.stalk ((p ≫ U.ι).fromNormalization x))] :
    letI := ((p ≫ U.ι).fromNormalization.stalkMap x).hom.toAlgebra
    Module.IsTorsionFree (X.presheaf.stalk ((p ≫ U.ι).fromNormalization x))
      ((p ≫ U.ι).normalization.presheaf.stalk x) := by sorry

end AlgebraicGeometry.Scheme
