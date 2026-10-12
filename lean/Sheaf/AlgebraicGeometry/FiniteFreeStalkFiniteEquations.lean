/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P3
-/
module

public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free

/-! # Finitely many equations of maps between finite free sheaves

Source: lem-pc-perfect-locus, finite matrix calculation, expanded in
lem-pc-finite-free-stalk-degreewise-shrink, steps 1 and 2.
(blueprint: lem-pc-finite-free-stalk-finite-equations)
-/

@[expose] public section
set_option autoImplicit false
universe u v
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.Modules

/-- Finitely many equations of module maps between finite free sheaves hold near a point
if they hold after pullback to its stalk scheme.

Source: lem-pc-perfect-locus, finite matrix calculation, expanded in
lem-pc-finite-free-stalk-degreewise-shrink, steps 1 and 2.

Proof: Restriction preserves zero objects and finite free sheaves. For each pair of
nonzero objects choose finite bases on U and form the matrices of f i minus g i.
The pullback equality implies that the pullback matrices are zero. Pullback of
free matrices applies the scheme map to every coefficient; for the map from the
stalk scheme this is the structure-sheaf germ map, identified with global sections
of Spec O_{Y,y}. Thus every coefficient has zero germ. The germ equality criterion
gives a neighbourhood inside U where each coefficient is zero. There are only
finitely many indices and matrix entries, so intersect all these neighbourhoods.
On the intersection the matrices, and hence the maps, agree. A zero source or
target has only one map and needs no shrinking. Empty index sets and rank-zero
terms require no equations, and one may take V = U.
(blueprint: lem-pc-finite-free-stalk-finite-equations) -/
theorem exists_shrink_finite_free_map_eq
    {Y : Scheme.{u}} {ι : Type v} [Finite ι] (A B : ι → Y.Modules)
    (hA : ∀ i, IsZero (A i) ∨ ∃ s : ℕ, Nonempty
      (A i ≅ SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin s))))
    (hB : ∀ i, IsZero (B i) ∨ ∃ s : ℕ, Nonempty
      (B i ≅ SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin s))))
    (y : Y) (U : Y.Opens) (hyU : y ∈ U)
    (f g : ∀ i, (restrictFunctor U.ι).obj (A i) ⟶
      (restrictFunctor U.ι).obj (B i))
    (h : ∀ i, (Modules.pullback (U.fromSpecStalkOfMem y hyU)).map (f i) =
      (Modules.pullback (U.fromSpecStalkOfMem y hyU)).map (g i)) :
    ∃ (V : Y.Opens) (_ : y ∈ V) (hVU : V ≤ U),
      ∀ i, (restrictFunctor (Y.homOfLE hVU)).map (f i) =
        (restrictFunctor (Y.homOfLE hVU)).map (g i) := by sorry

end AlgebraicGeometry.Scheme.Modules
