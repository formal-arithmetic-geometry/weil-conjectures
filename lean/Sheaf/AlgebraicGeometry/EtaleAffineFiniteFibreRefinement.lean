/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q13
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import WeilConjectures.AlgebraicGeometry.IsLocallyQuasiFiniteResLE
import WeilConjectures.AlgebraicGeometry.QuasiFiniteLocallyQuasiFinite
import WeilConjectures.AlgebraicGeometry.Morphisms.ProperQuasiFinite

/-! # Finite-fibre affine refinement of an etale source

Source: Stacks Project, Descent, Tag 03X4, finite-fibres paragraph; Topologies, Tag 0218;
Morphisms, Tags 01TH, 01SH, 01S7, 01TJ and 02NH
(blueprint: lem-a1-etale-affine-finite-fibre-refinement).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

/-- An arbitrary surjective etale source over an affine scheme has a finite affine open
refinement on which a locally quasi-finite composite to an affine scheme is quasi-finite
with finite fibres. The fibre of the target map is exactly the union of the images of
these finite fibres, and is finite.

Source: Stacks Project, Descent, Tag 03X4, finite-fibres paragraph, expanded using
Topologies, Tag 0218, and Morphisms, Tags 01TH, 01SH, 01S7, 01TJ and 02NH
(blueprint: lem-a1-etale-affine-finite-fibre-refinement).

Proof:
1. Cover `X` by affine opens using `lem-weil-pbc-affine-opens-basis`. Their images under
   `q` are open by `lem-weil-pbc-etale-morphism-open-map` and cover `W` by surjectivity.
   Since `W` is affine, `lem-weil-pbc-affine-scheme-qcqs` gives quasi-compactness; select
   finitely many of these images covering `W`. For empty `W`, the family may be empty.
2. For each selected open, `lem-weil-pbc-lqf-restriction-to-opens` preserves local
   quasi-finiteness of `q ≫ h`. The restricted source and `Z` are affine, so
   `lem-weil-pbc-morphism-affine-schemes-affine` makes the restricted composite affine.
   Clause (3) of `lem-weil-pbc-affine-morphism-permanence` makes it quasi-compact.
   Apply `pqf-lem-qf-locqf-qc` to obtain quasi-finiteness, and the forward implication of
   `pqf-lem-qf-finitefibres` to obtain finite fibres.
3. For `z : Z`, each displayed image lies in the fibre of `h`. Conversely, a point of
   that fibre lies in some selected image by the cover, and any preimage in that open
   lies over `z`. This proves the set equality. Each term is an image of a finite set;
   their finite union is finite. The empty family gives the equality of empty sets.
-/
theorem exists_etale_affine_finite_fibre_refinement
    {X W Z : Scheme.{u}} [IsAffine W] [IsAffine Z]
    (q : X ⟶ W) [Etale q] [Surjective q] (h : W ⟶ Z)
    (hcomp : (q ≫ h).IsLocallyQuasiFinite) :
    ∃ (m : ℕ) (A : Fin m → X.Opens),
      (∀ j : Fin m, IsAffineOpen (A j)) ∧
      (⋃ j : Fin m, q '' (A j : Set X)) = Set.univ ∧
      (∀ j : Fin m, ((A j).ι ≫ q ≫ h).IsQuasiFinite ∧
        ((A j).ι ≫ q ≫ h).HasFiniteFibres) ∧
      (∀ z : Z, h ⁻¹' {z} =
        ⋃ j : Fin m, ((A j).ι ≫ q) '' (((A j).ι ≫ q ≫ h) ⁻¹' {z})) ∧
      h.HasFiniteFibres := by
  sorry

end AlgebraicGeometry.Scheme.Hom
