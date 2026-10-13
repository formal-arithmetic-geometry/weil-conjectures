/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module

/-! # Quasi-coherence of the annihilator subsheaf
Source: Stacks Project, Tag 01PO, proof of clause (1).
-/

@[expose] public section

universe u
open CategoryTheory TopologicalSpace Opposite
open scoped AlgebraicGeometry
namespace AlgebraicGeometry

/-- A subsheaf with the affine-annihilator image is quasi-coherent for a finite-type ideal.
Source: Stacks Project, Tag 01PO, proof of (1).
(blueprint: lem-weil-pbc-annihilator-quasicoherent).

Proof: work on an affine open Spec A, writing F = M tilde and the ideal as I tilde.
Use the assumed image formula on every principal open. Put M' = {m : I m = 0}.
The inclusion (M')_f into M_f is injective by exactness of localization, and its
image is killed by I_f. Conversely write an element killed by I_f as m/f^n.
Choose finitely many generators g_i of I, using finite type on this affine open.
For every i, clear a power f^e_i in g_i m/f^n = 0. Choose e at least every e_i.
Then f^e m lies in M', and m/f^n = (f^e m)/f^(n+e) lies in (M')_f. For the
empty generator family use e = 0. These image identifications commute with
restriction and identify G on the principal-open basis with the tilde of M'.
Both maps into F are injective, so the identifications are unique and glue.
Thus G is locally a tilde sheaf and is quasi-coherent.
-/
theorem annihilator_subsheaf_quasicoherent (X : Scheme.{u}) (J : X.IdealSheafData)
    [J.toModules.IsFiniteType] (F : X.Modules) [F.IsQuasicoherent]
    (G : X.Modules) (ι : G ⟶ F) [Mono ι]
    (himage : ∀ (U : X.affineOpens) (s : Γ(F, U.1)),
      s ∈ Set.range (ι.app U.1) ↔ ∀ a ∈ J.ideal U, a • s = 0) :
    G.IsQuasicoherent := by
  sorry

end AlgebraicGeometry
