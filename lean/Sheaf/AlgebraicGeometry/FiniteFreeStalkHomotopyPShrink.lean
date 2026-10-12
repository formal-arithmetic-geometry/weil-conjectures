/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U1
-/
module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.AlgebraicGeometry.Stalk
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf

/-! # Spreading a homotopy of a bounded finite free complex

Source: lem-pc-perfect-locus, extension of finite calculations near a point.
(blueprint: lem-pc-finite-free-stalk-homotopy-p-only)
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.Modules

/-- A stalk homotopy of two fixed endomorphisms spreads near the point.

Source: blueprint sec-picard-framework/sk-thm-picard-perfect/lem-pc-perfect-locus,
proof, extension of the finite calculation to a neighbourhood; expanded in
lem-pc-finite-free-stalk-homotopy-pair-shrink, steps 1--3.
(blueprint: lem-pc-finite-free-stalk-homotopy-p-only).

Proof: Choose the termwise finite bases supplied by hfree and a homotopy in hP.
Restriction and pullback carry these bases to finite bases; over Spec O_{Y,y}
the coefficients of its components are elements of O_{Y,y}. By hge and hle,
only the reverse-degree components with both degrees in [0,d] can be nonzero.
There are finitely many such components and finitely many entries in each.
Represent their entries by structure-sheaf sections on neighbourhoods of y
inside V, and intersect these neighbourhoods. Use the bases to make these
sections into sheaf-module morphisms, setting all other components to zero.
For each degree in [0,d], the matrix of a-dh-hd-b has zero germs because hP
is a homotopy of the specified maps. The germ equality criterion gives a
smaller neighbourhood where each entry is zero. Intersect the finitely many
neighbourhoods once more. The resulting components satisfy Homotopy.comm;
outside [0,d] the source terms are zero, so the equations hold automatically.
Only reverse-degree components were retained, so Homotopy.zero also holds.
This constructs the required homotopy after restriction. Rank zero and d=0
cause no difficulty: empty matrices or the empty list of reverse components
have no coefficients to lift, and only the fixed-map equations remain. -/
theorem exists_shrink_homotopy_P_of_stalk
    {Y : Scheme.{u}} (P : CochainComplex Y.Modules ℤ) (d : ℕ)
    (hge : P.IsStrictlyGE 0) (hle : P.IsStrictlyLE d)
    (hfree : ∀ n : ℤ, ∃ s : ℕ, Nonempty
      (P.X n ≅ SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin s))))
    (y : Y) (V : Y.Opens) (hyV : y ∈ V)
    (a b : (((restrictFunctor V.ι).mapHomologicalComplex _).obj P) ⟶
      (((restrictFunctor V.ι).mapHomologicalComplex _).obj P))
    (hP : Nonempty (Homotopy
      (((Modules.pullback (V.fromSpecStalkOfMem y hyV)).mapHomologicalComplex _).map a)
      (((Modules.pullback (V.fromSpecStalkOfMem y hyV)).mapHomologicalComplex _).map b))) :
    ∃ (W : Y.Opens) (hWV : W ≤ V), y ∈ W ∧
      Nonempty (Homotopy
        (((restrictFunctor (Y.homOfLE hWV)).mapHomologicalComplex _).map a)
        (((restrictFunctor (Y.homOfLE hWV)).mapHomologicalComplex _).map b)) := by
  sorry


end AlgebraicGeometry.Scheme.Modules
