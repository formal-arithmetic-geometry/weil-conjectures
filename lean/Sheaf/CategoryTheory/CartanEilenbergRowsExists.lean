/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S2
-/
module

public import Sheaf.CategoryTheory.CartanEilenbergRows
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Abelian.Injective.Resolution
import Sheaf.CategoryTheory.Abelian.HorseshoePrescribedResolutions

/-! # Injective resolutions of the alternating exact rows

Source: Stacks Project, Derived Categories, Lemma 015I, proof Steps 1--4
(blueprint: lem-sp-cartan-eilenberg-rows-exists).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

universe u v

/-- The alternating cycle/term/boundary and boundary/cycle/homology rows admit
compatible resolutions. This constructs rows, not their horizontal complex.

Source: Stacks Project, Derived Categories, Lemma 015I, proof Steps 1--4,
using the prescribed-end version of the horseshoe lemma, Tag 013T
(blueprint: lem-sp-cartan-eilenberg-rows-exists).

Proof:
1. Write the two short exact sequences Z^p(K) -> K^p -> B^(p+1)(K) and
   B^p(K) -> Z^p(K) -> H^p(K). Start with an injective resolution of Z^0(K).
2. Choose a resolution of B^1(K). The prescribed horseshoe lemma produces
   a resolution of K^0 and a short exact row with the chosen outer columns.
   Choose a resolution of H^1(K); apply it again to obtain a resolution of
   Z^1(K), reusing the preceding resolution of B^1(K). Iterate on natural
   degrees, alternating these two applications. All row maps commute with
   augmentations and each chosen column has injective terms and is a resolution.
3. In negative horizontal degrees take zero complexes. Take the degree-zero
   boundary column to be zero, and identify H^0(K) with Z^0(K). The vanishing
   hypothesis makes these choices compatible with both rows at the boundary.
4. Apply the exact single-degree-zero functor to the source rows to identify
   their cycles, images and homology with those of the prolonged complex S.
   Transfer the object augmentations along these canonical isomorphisms.
   The row squares give commZ, commD and commH. Factoring d_K through its image
   and cycles gives comm. Exactness of the rows in the category of vertical
   complexes follows from their degreewise short exactness. -/
theorem exists_cartanEilenberg_rows
    (B : Type u) [Category.{v} B] [Abelian B] [EnoughInjectives B]
    (K : CochainComplex B ℤ) (hK : ∀ p : ℤ, p < 0 → IsZero (K.X p)) :
    let S := ((CochainComplex.single₀ B).mapHomologicalComplex (ComplexShape.up ℤ)).obj K
    ∃ R : CartanEilenbergRows S,
      (∀ p : ℤ, p < 0 → IsZero (R.A p)) ∧
      (∀ p : ℤ, QuasiIso (R.jA p) ∧ QuasiIso (R.jZ p) ∧
        QuasiIso (R.jD p) ∧ QuasiIso (R.jH p)) ∧
      (∀ (p : ℤ) (q : ℕ), Injective ((R.A p).X q) ∧
        Injective ((R.Z p).X q) ∧ Injective ((R.D p).X q) ∧
        Injective ((R.H p).X q)) := by sorry

end CategoryTheory
