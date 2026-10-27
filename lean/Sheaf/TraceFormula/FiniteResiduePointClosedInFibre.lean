/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Finite residue field points are closed in fibres

Source: literature/stacks-project/morphisms.tex, Tags 01TE and 01TF
(blueprint: lem-trf-finite-residue-point-closed-in-fibre).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

/--
If `f : X ⟶ S` is locally of finite type and the residue-field extension at `x`
over `f x` is finite-dimensional, then the point induced by `x` in the
scheme-theoretic fibre over `f x` is closed.

Source: Stacks Project, Morphisms, Tags 01TE and 01TF
(blueprint: lem-trf-finite-residue-point-closed-in-fibre).

Proof:
1. The composite of `f.asFiberHom x : Spec κ(x) ⟶ f.fiber (f x)` with
   the fibre structure map is `Spec.map (f.residueFieldMap x)`. The given
   finite-dimensional extension is a finite-type algebra, so this composite
   is locally of finite type. Cancellation makes `f.asFiberHom x` locally
   of finite type as well.
2. The fibre is Jacobson because it is locally of finite type over a field.
   A locally finite type morphism from the spectrum of a field to a Jacobson
   scheme is finite. Its image is therefore closed.
3. The image of `f.asFiberHom x` is exactly `{f.asFiber x}`.
-/
theorem isClosed_singleton_asFiber_of_finiteDimensional
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (x : X)
    (hfinite : @FiniteDimensional (S.residueField (f x)) (X.residueField x) _ _
      (f.residueFieldMap x).hom.toAlgebra.toModule) :
    IsClosed ({f.asFiber x} : Set (f.fiber (f x))) := by
  let := (f.residueFieldMap x).hom.toAlgebra
  have := hfinite
  have : LocallyOfFiniteType
      (f.asFiberHom x ≫ f.fiberToSpecResidueField (f x)) := by
    rw [f.asFiberHom_fiberToSpecResidueField]
    apply (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
    change Algebra.FiniteType (S.residueField (f x)) (X.residueField x)
    infer_instance
  have : LocallyOfFiniteType (f.asFiberHom x) :=
    locallyOfFiniteType_of_comp _ (f.fiberToSpecResidueField (f x))
  have : IsFinite (f.asFiberHom x) :=
    isFinite_iff_locallyOfFiniteType_of_jacobsonSpace.mpr inferInstance
  simpa only [f.range_asFiberHom x] using (f.asFiberHom x).isClosedMap.isClosed_range

end AlgebraicGeometry.Scheme.Hom
