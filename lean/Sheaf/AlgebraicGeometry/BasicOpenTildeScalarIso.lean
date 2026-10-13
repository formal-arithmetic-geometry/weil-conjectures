/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K3
-/
module

public import Sheaf.Paper.DerivedHomMayerVietoris
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Homology.Linear

/-! # Scalar multiplication on a sheafified complex over a basic open

Source: Stacks Project, Tag 01HR (standard opens of an affine scheme),
and Tag 09IR (restriction of the Koszul complex).
(blueprint: lem-k3-basic-open-tilde-scalar-iso).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Multiplication by a on any sheafified complex is invertible over D(a).
Source: Stacks Project, Tag 01HR, and the local vanishing argument of Tag 09IR.
(blueprint: lem-k3-basic-open-tilde-scalar-iso).

Proof: On D(a), the image of a is a unit in the structure sheaf. Its inverse
restricts compatibly to every smaller open. In each degree, multiply sections
by that inverse; these linear maps respect restriction, hence give morphisms
of module sheaves. Under tilde, the image of a times the identity is precisely
multiplication by the structure-sheaf section a, by the localization formula
for tilde.map. Both composites are the identity, sectionwise. The inverse
maps commute with the differentials, since the latter are linear over the
structure sheaf. They therefore give the inverse chain map. This argument
applies to arbitrary complexes, without exactness or finite-generation
hypotheses. If D(a) is empty, all module sheaves on it are zero and the
same assertion holds, including a=0 and the zero ring. -/
theorem basicOpen_tilde_scalar_isIso
    (A : Type u) [CommRing A] (a : A) (K : CochainComplex (ModuleCat.{u} A) ℤ) :
    IsIso
      (((SheafOfModules.overFunctor.{u}
        (moduleRings (Spec (.of A)).toRingedSpace)
        (PrimeSpectrum.basicOpen a)).mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((@Functor.mapHomologicalComplex ℤ (ModuleCat.{u} A)
          (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
          _ _ _ _ (tilde.functor (.of A))
          ⟨fun _ _ ↦ tilde.map_zero⟩ (ComplexShape.up ℤ)).map
          (a • 𝟙 K))) := by sorry

end AlgebraicGeometry
