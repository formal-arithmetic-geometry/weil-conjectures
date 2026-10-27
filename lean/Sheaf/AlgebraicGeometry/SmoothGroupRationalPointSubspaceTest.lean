/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q32
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Monoidal.Grp
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Ring
public import Sheaf.AlgebraicGeometry.LinearGroupSchemes
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
import WeilConjectures.Mathlib.RingTheory.Nullstellensatz

/-! # Rational points detect stable subspaces

Source: Milne, Algebraic Groups (2017), Proposition 4.3 and Corollaries 4.4--4.5,
printed p.85; Propositions 1.10--1.12 for schematic density.
(blueprint: lem-sfb-smooth-group-rational-point-subspace-test)

A basis identifies GL(V) with the existing general linear group scheme, also for the empty
basis. Scalar extension is Mathlib's submodule `W.baseChange A` inside `A ⊗[k] V`, canonically
identified by tensor symmetry with the image of `W ⊗[k] A` in `V ⊗[k] A`.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory
open scoped MonObj

namespace AlgebraicGeometry.GeneralLinearGroup

/-- A subspace of a finite-dimensional rational representation of a smooth affine finite-type
algebraic group is preserved by every rational point if and only if every algebra-valued point
preserves its scalar extension, with equality of submodules on both sides.

Source: Milne, Algebraic Groups (2017), Proposition 4.3 and Corollaries 4.4--4.5, printed p.85;
Propositions 1.10--1.12 (blueprint: lem-sfb-smooth-group-rational-point-subspace-test).

Proof:
1. Specialize the all-algebra condition to A=k and identify the scalar extensions with the
   original spaces. If V=0, both conditions hold, since W=0 and GL(V) is trivial.
2. Otherwise choose an adapted basis whose first r vectors span W. The inclusion of W is split,
   including after tensoring. Pull the matrix coordinates x_ij back along rho to regular
   functions b_ij on G, using `def-sc-general-linear-group`. Preservation of W after extension
   to A is equivalent to the vanishing of the evaluated b_ij for i>r and j<=r.
3. Smoothness makes G reduced by `sbc-lem-smooth-geometrically-reduced`. Finite type gives
   affine charts with finitely generated coordinate algebras (`def-weil-finite-type-morphism`);
   their rings are reduced by `def-pc-reduced-scheme`.
4. Rational-point stability makes each b_ij vanish at every k-point of every chart. Apply
   clause (2) of `lem-wf-affine-nullstellensatz-vanishing` to obtain b_ij=0 on each chart.
   The sheaf property then gives b_ij=0 globally.
5. Evaluation at any algebra-valued point gives preservation by containment. Apply it also
   to the inverse point and use the homomorphism law to obtain equality. This also includes
   W=0, W=V and the zero algebra; in those cases the coordinate equations are empty or the
   scalar extensions are zero. The initial basis is arbitrary: a change to the adapted basis
   conjugates all matrices and transports the same submodules. -/
theorem map_subspace_eq_iff_forall_algebra
    {k : Type u} [Field k] [IsAlgClosed k]
    (G : Over (Spec (.of k))) [GrpObj G] [IsAffine G.left]
    [Smooth G.hom] [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]
    {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    {m : Type u} [Fintype m] [DecidableEq m] (b : Module.Basis m k V)
    (ρ : G ⟶ GeneralLinearGroup m k) [IsMonHom ρ] (W : Submodule k V) :
    (∀ g : AlgebraicGeometry.points G k,
      W.map (Matrix.toLin b b (homMulEquiv m k k (g ≫ ρ))) = W) ↔
    ∀ (A : Type u) [CommRing A] [Algebra k A] (g : AlgebraicGeometry.points G A),
      (W.baseChange A).map (Matrix.toLin (b.baseChange A) (b.baseChange A)
        (homMulEquiv m k A (g ≫ ρ))) = W.baseChange A := by
  sorry

end AlgebraicGeometry.GeneralLinearGroup
