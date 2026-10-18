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
import Sheaf.AlgebraicGeometry.FibreStalkQuotient
import Sheaf.AlgebraicGeometry.ClosedPointField

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
1. Form the scheme-theoretic fibre `f.fiber (f x)`.  Base change preserves
   local finite type, so its projection to `Spec (S.residueField (f x))` is
   locally of finite type.  Write `ξ = f.asFiber x` for the point induced by
   `x`.
2. For a specialization of `ξ`, choose an affine open neighbourhood.  The
   affine-pair criterion identifies this open's coordinate algebra as a
   finitely generated algebra over `S.residueField (f x)`.  The fibre stalk
   quotient and residue-field naturality identify the residue field at `ξ`
   with `X.residueField x`, carrying the stated finite-dimensional structure.
   The finite-type-over-a-field closed-point criterion therefore makes `ξ`
   closed in the affine open.
3. Every specialization of `ξ` is consequently equal to `ξ`; the affine-open
   neighbourhood argument shows that the singleton of `ξ` is closed in the
   whole fibre.
-/
theorem isClosed_singleton_asFiber_of_finiteDimensional
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (x : X)
    (hfinite : @FiniteDimensional (S.residueField (f x)) (X.residueField x) _ _
      (f.residueFieldMap x).hom.toAlgebra.toModule) :
    IsClosed ({f.asFiber x} : Set (f.fiber (f x))) := by
  sorry

end AlgebraicGeometry.Scheme.Hom
