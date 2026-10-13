/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.FreeComplex
import WeilConjectures.AlgebraicGeometry.Modules.LocalInvertibleMinorBlockData
import WeilConjectures.AlgebraicGeometry.Modules.LocalInvertibleMinorBlockIso

/-! # Local free decompositions with an invertible pivot block

Source: `thm-pc-semicontinuity-base-change`, proof (3), choosing a nonvanishing minor.
(blueprint: lem-pc-local-invertible-minor-block)
-/

@[expose] public section

universe u

open CategoryTheory Limits SheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

/-- A specified minor nonvanishing at a point gives local bases with an invertible
leading block. No reducedness or rank bound at other points is required.

Source: `thm-pc-semicontinuity-base-change`, proof (3), pivot-minor step in the
normal-form claim. (blueprint: lem-pc-local-invertible-minor-block)

Proof: Set A = freeMatrix (eM.inv ≫ φ ≫ eN.hom). Near j(z), the determinant
of the chosen a by a minor is a unit: restrict to its basic open and then to an
affine neighbourhood of j(z) contained in the image of j. The selected rows and
columns are distinct, since repeated rows or columns would give determinant zero
in the residue field at j(z). Thus a ≤ m,n. Extend the two selected lists to
permutations of the full finite index sets, with the unused coordinates last.
Restrict eM and eN, identify pullback with restriction along the open immersion,
and split these reordered free sheaves into their selected and complementary
coordinates. The leading block is precisely the selected minor matrix over the
restricted ring. Its inverse is the adjugate divided by its unit determinant;
this matrix defines an inverse sheaf map, since the two matrix products are the
identity on every further open. Pull back the neighbourhood to Z. This gives
U, the two isomorphisms and the asserted IsIso. If a = 0 the determinant is 1
and the pivot map is the identity of the zero free sheaf. -/
theorem exists_local_invertible_minor_block
    {Y Z : Scheme.{u}} {M N : Y.Modules} {m n : ℕ}
    (eM : M ≅ free (R := Y.ringCatSheaf) (ULift.{u} (Fin m)))
    (eN : N ≅ free (R := Y.ringCatSheaf) (ULift.{u} (Fin n)))
    (φ : M ⟶ N) (j : Z ⟶ Y) [IsOpenImmersion j] (a : ℕ) (z : Z)
    (rows : Fin a → ULift.{u} (Fin n)) (cols : Fin a → ULift.{u} (Fin m))
    (hminor : j.base z ∈
      Y.basicOpen ((freeMatrix (eM.inv ≫ φ ≫ eN.hom)).submatrix rows cols).det) :
    ∃ U : Z.Opens, z ∈ U ∧
      ∃ (eS : ((Modules.pullback j).obj M).restrict U.ι ≅
          free (ULift.{u} (Fin a)) ⊞ free (ULift.{u} (Fin (m - a))))
        (eT : ((Modules.pullback j).obj N).restrict U.ι ≅
          free (ULift.{u} (Fin a)) ⊞ free (ULift.{u} (Fin (n - a)))),
        IsIso (biprod.inl ≫ eS.inv ≫
          (restrictFunctor U.ι).map ((Modules.pullback j).map φ) ≫
          eT.hom ≫ biprod.fst) := by
  obtain ⟨U, hz, eS, eT, hblock, hunit⟩ := exists_local_invertible_minor_block_data
    eM eN φ j a z rows cols hminor
  refine ⟨U, hz, eS, eT, ?_⟩
  apply local_invertible_minor_block_isIso
  rw [hblock]
  exact hunit

end AlgebraicGeometry.Scheme.Modules
