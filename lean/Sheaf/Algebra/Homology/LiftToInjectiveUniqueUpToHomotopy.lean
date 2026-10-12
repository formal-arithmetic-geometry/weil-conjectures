/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.Algebra.Homology.QuasiIso
import Sheaf.Algebra.Homology.MappingCylinderSplitFactorization

/-! # Uniqueness up to homotopy of lifts into an injective complex

Source: Stacks Project, Derived Categories, Lemma 13.18.7 (Tag 013S),
`lemma-morphisms-equal-up-to-homotopy`
(blueprint: lem-weil-pbc-lift-to-injective-unique-up-to-homotopy).
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

/-- Maps into a bounded below complex of injectives are homotopic whenever their
composites with a quasi-isomorphism are homotopic.
Source: Stacks Project, Derived Categories, Lemma 13.18.7 (Tag 013S)
(blueprint: lem-weil-pbc-lift-to-injective-unique-up-to-homotopy).

Proof:
1. Apply `lem-weil-pbc-complex-mapping-cylinder-split-factorization` to alpha,
   obtaining alpha' : K -> L', pi : L' -> L and s : L -> L' with alpha' termwise
   split injective, alpha' followed by pi equal to alpha, s followed by pi the
   identity and pi followed by s homotopic to the identity.
2. By `lem-weil-pbc-homotopic-maps-equal-cohomology`, pi and s induce mutually
   inverse cohomology maps. Thus pi is a quasi-isomorphism, and alpha' is one too,
   by functoriality of the cohomology in `def-weil-abstract-derived-category`.
3. Replace beta_i by pi followed by beta_i. A homotopy of these maps restricts
   along s to the required homotopy, since s followed by pi is the identity.
   Hence assume L is degreewise K plus M and alpha is the first inclusion.
4. The quotient M has the differential induced from L. The projection q : L -> M
   is a chain map, and 0 -> K -> L -> M -> 0 is degreewise split exact. Any
   chain map from L vanishing on K factors through q as a chain map from M.
5. By `lem-weil-pbc-complex-ses-homology-long-exact` and the isomorphisms induced
   by alpha, every cohomology object of M is zero, so M is acyclic.
6. Extend the given homotopy on K by zero on the complementary summands M.
   Subtract its boundary from beta_1 minus beta_2. The resulting chain map psi
   vanishes on K and hence factors as q followed by a chain map phi : M -> I.
7. Apply `lem-weil-pbc-acyclic-map-to-injective-nullhomotopy` to phi. Compose its
   nullhomotopy with q and add the extended homotopy from step 6. This gives
   the required homotopy on L, and step 3 returns it to the original complex.
-/
theorem homotopy_of_comp_quasiIso_of_injective
    {C : Type u} [Category.{v} C] [Abelian C]
    {K L I : CochainComplex C ℤ}
    (hI : ∃ a : ℤ, ∀ n : ℤ, n < a → IsZero (I.X n))
    [∀ n : ℤ, Injective (I.X n)]
    (α : K ⟶ L) [QuasiIso α]
    (β₁ β₂ : L ⟶ I) (h : Nonempty (Homotopy (α ≫ β₁) (α ≫ β₂))) :
    Nonempty (Homotopy β₁ β₂) := by
  sorry

end CochainComplex
