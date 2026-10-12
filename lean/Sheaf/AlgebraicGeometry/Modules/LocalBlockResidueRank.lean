/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G2
-/
module

public import Mathlib.AlgebraicGeometry.ResidueField
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf

/-! # Residue rank of a local block form -/

@[expose] public section

universe u

open CategoryTheory Limits SheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

/-- The residue rank of a local block form is the size of its invertible block plus
that of its complementary block.

Source: `thm-pc-semicontinuity-base-change`, proof (3), reduced-ring normal form;
`lem-pc-complementary-block-residue-vanishes`, steps 1 and 2.
(blueprint: lem-pc-local-block-residue-rank)

Proof: Write k = κ_U(x) and pull the displayed normal form back along
Spec k → U. The restriction-pullback comparison and the pullback composition
isomorphism identify the left side with the fibre of φ at j(x). The residue-field
map for the open immersion U → Z → Y is an isomorphism, so extending scalars
from κ_Y(j(x)) to k does not change its rank. The pulled-back eM, eN, eS and eT
are isomorphisms and preserve image dimension. Pullback preserves biproducts;
the image of the pulled-back diagonal map is the direct sum of the image of f
and the image of δ. Since f is invertible its image has dimension a. The matrix
of the second summand is freeMatrix δ evaluated at x, by freeMatrix_pullback
and the canonical identification Γ(Spec k, O) = k. Additivity of finite vector
space dimension gives the equality. This argument also applies to a = 0 and
empty complementary indices; if U is empty there is no point x. -/
theorem local_block_residue_rank
    {Y Z : Scheme.{u}} {M N : Y.Modules} {m n : ℕ}
    (eM : M ≅ free (R := Y.ringCatSheaf) (ULift.{u} (Fin m)))
    (eN : N ≅ free (R := Y.ringCatSheaf) (ULift.{u} (Fin n)))
    (φ : M ⟶ N) (j : Z ⟶ Y) [IsOpenImmersion j] (a : ℕ) (U : Z.Opens)
    (eS : ((Modules.pullback j).obj M).restrict U.ι ≅
      free (ULift.{u} (Fin a)) ⊞ free (ULift.{u} (Fin (m - a))))
    (eT : ((Modules.pullback j).obj N).restrict U.ι ≅
      free (ULift.{u} (Fin a)) ⊞ free (ULift.{u} (Fin (n - a))))
    (f : free (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin a)) ⟶
      free (ULift.{u} (Fin a))) [IsIso f]
    (δ : free (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin (m - a))) ⟶
      free (ULift.{u} (Fin (n - a))))
    (hform : (restrictFunctor U.ι).map ((Modules.pullback j).map φ) =
      eS.hom ≫ biprod.map f δ ≫ eT.inv)
    (x : U.toScheme) : ((freeMatrix (eM.inv ≫ φ ≫ eN.hom)).map
        (Y.Γevaluation (j.base x.1))).rank =
      a + ((freeMatrix δ).map (U.toScheme.Γevaluation x)).rank := by sorry

end AlgebraicGeometry.Scheme.Modules
