/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H2
-/
module

public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
public import Sheaf.AlgebraicGeometry.DirectImageAlgebraDerivedCategory
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Sheaf.AlgebraicGeometry.FinitePushforwardDerivedHomQCoherent
import Sheaf.AlgebraicGeometry.FiniteSheafHomAffineAdjoint
import Sheaf.AlgebraicGeometry.DerivedRHomAlgebraModule

/-! # Quasi-coherence of a specified finite scalar right adjoint

Source: Stacks Project, Tag 0AX2, comparison of right adjoints
(blueprint: lem-sc-finite-scalar-right-adjoint-qcoh).
-/

@[expose] public section

universe u wX wY wA

open CategoryTheory

namespace AlgebraicGeometry

/-- Any specified right adjoint of derived scalar restriction has quasi-coherent
cohomology at a bounded-below quasi-coherent input.
Source: Stacks Project, Tag 0AX2, with Tags 0BV0 and 0AX3
(blueprint: lem-sc-finite-scalar-right-adjoint-qcoh).

Proof: Let B be the direct-image algebra with structure map f.c. The affine sheaf-Hom
adjunction computes the right adjoint of scalar restriction by the B-valued complex
Hom(B,I(K)), where I(K) is a K-injective resolution. Exactness of restriction identifies
its derived functor with the specified left adjoint. This Hom complex is also the
construction of derivedRHomAlgebraModule, with the same algebra action, so localization
and uniqueness of derived functors identify those right adjoints. Finite pushforward of
the structure sheaf is coherent on the Noetherian target and hence pseudo-coherent.
The finite-pushforward derived-Hom quasi-coherence theorem puts this value at K in
D+_QCoh(B). Uniqueness of right adjoints identifies it with the value of the specified
rhoR at K. Apply the homology functors to this isomorphism and transport quasi-coherence
of each cohomology module. Only quasi-coherence is asserted, so no bound needs to be
chosen or transported. For zero objects and shifts the same adjunction and Hom
calculation apply. -/
theorem finite_scalar_right_adjoint_qcoh {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsFinite f] [IsNoetherian X] [IsNoetherian Y]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [HasDerivedCategory.{wA} (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace f)))]
    (ρR : DerivedCategory (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ⥤
      DerivedCategory (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace f))))
    (adjA : (SheafOfModules.restrictScalars
          (R := moduleRings Y.toRingedSpace)
          (R' := moduleRings (directImageAlgebraSpace f))
          ⟨Functor.whiskerRight f.c (forget₂ CommRingCat RingCat)⟩).rightDerivedFunctor ⊣ ρR)
    (K : schemeDerivedQCohCategory Y) (hK : ∃ n : ℤ, K.obj.IsGE n) :
    directImageAlgebraDerivedQCohProperty f (ρR.obj K.obj) := by sorry

end AlgebraicGeometry
