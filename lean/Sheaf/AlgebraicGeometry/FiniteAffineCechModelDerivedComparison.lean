/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N3
-/
module

public import Sheaf.AlgebraicGeometry.FiniteAffineCechModel
public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

/-! # Derived comparison for the specified finite affine Čech model

Source: Stacks Project, Tags 01XB, 01XD and 01FK.
(blueprint: lem-pc-finite-affine-cech-model-derived-comparison).
-/

@[expose] public section

set_option autoImplicit false

universe u wX wT

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The specified section complex computes derived direct image over an affine base.
Neither properness, finite presentation nor relative flatness is required.
Source: Stacks Project, Tags 01XB, 01XD and 01FK.
(blueprint: lem-pc-finite-affine-cech-model-derived-comparison).

Proof: separatedness over the affine base makes every nonempty finite intersection
of members of V affine. Form the augmented alternating sheaf Čech resolution with
terms the finite products of open pushforwards of the restrictions of F. Inserting
a covering index on each cover member contracts the augmentation, so it is a
quasi-isomorphism. Each intersection map to T is affine, hence its quasi-coherent
module is direct-image acyclic by 01XB. Finite products preserve this acyclicity.
The acyclic resolution comparison identifies its pushed complex with Rf_*F[0].
The ordered comparison 01FK identifies the signed differential with the increasing
order-embedding tuples in alternatingCechComplex. On the canonical affine chart
T -> Spec Gamma(T,O), the tilde-Gamma comparison identifies every pushed term and
every restriction with the associated section module. Restriction of scalars along
GammaSpecIso and pullback of the resulting complex are exactly the operations in
finiteAffineCechModel. These termwise identifications therefore give a chain
isomorphism, whose localization composed with the acyclic-resolution comparison
gives the asserted derived isomorphism. Localization uniqueness transports this
comparison to the two independently supplied localizations. If r=0 the covering
condition forces X empty; the zero resolution and zero section complex give the
same comparison. Empty intersections and zero rings also give zero terms. -/
theorem finiteAffineCechModel_derivedComparison
    {X T : Scheme.{u}} (f : X ⟶ T) [IsAffine T] [IsSeparated f] [QuasiCompact f]
    (F : X.Modules) [F.IsQuasicoherent]
    [HasDerivedCategory.{wX}
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wT}
      (SheafOfModules.{u} (moduleRings T.toRingedSpace))]
    {r : ℕ} (V : Fin r → X.Opens) (hV : ∀ i, IsAffineOpen (V i))
    (hcover : iSup V = ⊤) :
    Nonempty ((DerivedCategory.Q
      (C := SheafOfModules.{u} (moduleRings T.toRingedSpace))).obj
        (finiteAffineCechModel f F V) ≅
      (schemeDerivedDirectImage f).obj ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj F)) := by sorry

end AlgebraicGeometry.Scheme.Modules
