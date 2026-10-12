/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D2
-/
module

public import Mathlib.AlgebraicGeometry.Properties
public import WeilConjectures.AlgebraicGeometry.Modules.FreeComplex

/-! # Homology of a complex with constant differential ranks over a reduced scheme

Source: the reduced-ring normal-form claim and its application in the proof of
`thm-pc-semicontinuity-base-change`, part (3).
(blueprint: lem-pc-constant-rank-complex-homology)
-/

@[expose] public section

universe u

open CategoryTheory SheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

/-- Constant ranks of the two adjacent differentials over a reduced scheme imply finite
local freeness of the homology on an open subscheme. It suffices to test each point over
one field extension of its residue field.

Source: `thm-pc-semicontinuity-base-change`, proof of (3), the normal-form claim and the
following kernel/image argument.
(blueprint: lem-pc-constant-rank-complex-homology)

Proof: Work on an affine open of the open subscheme and use the given bases for the three
terms. The field-valued point over every point detects the ranks in the residue field:
extension of fields preserves matrix rank. All minors of size a+1 of the outgoing matrix,
and of size b+1 of the incoming matrix, vanish in all residue fields. They lie in every
prime ideal and hence in the nilradical; reducedness makes them zero. At each point an
appropriate maximal minor is nonzero. Invert these two minors on a principal neighbourhood.
For each differential separately, permute the rows and columns to put the invertible minor
in the upper left block. Elementary invertible row and column operations give the blocks
I and the Schur complement. The larger minors vanish, so every entry of the Schur complement
is zero, giving the normal form diag(I,0). Rank zero uses the empty minor 1 and forces every
entry to vanish. Thus the outgoing kernel Z and incoming image B are finite free direct
summands of the middle term, of ranks r(q)-a and b. The complex identity gives B contained
in Z. A retraction from the middle term to B restricts to a retraction from Z, so Z/B is
finite projective of rank r(q)-a-b. A finite projective module is locally free; refine the
neighbourhoods to trivialize it. The two ranks satisfy a+b <= r(q) by the complex identity
over each residue field, so natural subtraction gives the stated rank. Affine sheafification
is exact and open restriction preserves homology, identifying this quotient with the
homology of the pulled-back complex. These neighbourhoods cover the open subscheme; on an
empty open the assertion is vacuous. -/
theorem isFiniteLocallyFreeOfRank_homology_pullback_of_constantRank
    {Y Z : Scheme.{u}} [IsReduced Y] {P : CochainComplex Y.Modules ℤ} {r : ℤ → ℕ}
    (e : ∀ n, P.X n ≅ free (R := Y.ringCatSheaf) (ULift.{u} (Fin (r n))))
    (q : ℤ) (j : Z ⟶ Y) [IsOpenImmersion j] (a b : ℕ)
    (hrank : ∀ z : Z, ∃ (R : CommRingCat.{u}) (_ : IsField R) (g : Spec R ⟶ Y),
      Set.range g.base = {j.base z} ∧
      ((freeMatrix ((e q).inv ≫ P.d q (q + 1) ≫ (e (q + 1)).hom)).map g.appTop).rank = a ∧
      ((freeMatrix ((e (q - 1)).inv ≫ P.d (q - 1) q ≫ (e q).hom)).map g.appTop).rank = b) :
    ((((Modules.pullback j).mapHomologicalComplex _).obj P).homology q).IsFiniteLocallyFreeOfRank
       (r q - a - b) := by sorry

end AlgebraicGeometry.Scheme.Modules
