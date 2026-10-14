/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Sheaf.AlgebraicGeometry.FlatTelescopeStageMap

/-! # Split towers resolved by compact flat generators

Source: Stacks Project 03EW, 077J and the relative cone induction of 06XX,
as expanded in the first paragraph of the one-target refinement argument.
(blueprint: lem-sc-compact-flat-generator-tower-resolution).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CochainComplex.HomComplex
namespace AlgebraicGeometry

/-- A bounded-above tower admits a strict levelwise quasi-isomorphic resolution
by coproducts of compact flat generators, with degreewise split transitions.
Compactness here is explicitly finite support for maps into arbitrary coproducts.

Source: Stacks Project 03EW and 077J; relative cone induction of 06XX,
expanded in `lem-sc-flat-telescope-target-refinement`, first proof paragraph.

Proof. Use the affine-open extension-by-zero generators j_! O_U. They are flat;
their Hom functor is sections on U. Quasi-compactness of U makes a section of a
sheaf coproduct finitely supported, giving exactly the finite-subcoproduct
factorization in the conclusion. Arbitrary module sheaves are covered by sums
of these generators. Resolve L_0 -> E_0 downward with that resolving class.
Given L_n -> E_n, resolve the bounded-above cone of L_n -> E_(n+1) by Q.
Compose Q -> Cone -> L_n[1] and take its shifted cone to obtain L_(n+1).
Its terms are sums of the old generators and the generators of Q; the map from
L_n is degreewise split. The comparison triangle gives v_(n+1), initially
commuting up to homotopy. Extend the comparison homotopy along each degreewise
split inclusion and subtract its boundary to get strict commutation. The
comparison of triangles makes v_(n+1) a quasi-isomorphism. Each stage has an
upper bound, with no uniform bound required. Empty coproducts handle zero terms;
zero complexes and arbitrary transitions need no exceptions. This construction
uses no projectivity or lifting through a sheaf epimorphism.
(blueprint: lem-sc-compact-flat-generator-tower-resolution). -/
theorem exists_compact_flat_generator_tower_resolution (Y : Scheme.{u})
    (E : ℕ → CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (t : ∀ n : ℕ, E n ⟶ E (n + 1))
    (hb : ∀ n : ℕ, ∃ z : ℤ, ∀ i : ℤ, z < i → IsZero ((E n).X i)) :
    ∃ (L : ℕ → CochainComplex
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
      (l : ∀ n : ℕ, L n ⟶ L (n + 1)) (v : ∀ n : ℕ, L n ⟶ E n),
      (∀ n : ℕ, ∃ z : ℤ, ∀ i : ℤ, z < i → IsZero ((L n).X i)) ∧
      (∀ n : ℕ, QuasiIso (v n)) ∧
      (∀ n : ℕ, l n ≫ v (n + 1) = v n ≫ t n) ∧
      (∀ (n : ℕ) (i : ℤ), IsSplitMono ((l n).f i)) ∧
      ∀ (n : ℕ) (i : ℤ), ∃ (I : Type u)
        (G : I → SheafOfModules.{u} (moduleRings Y.toRingedSpace)),
        Nonempty ((L n).X i ≅ ∐ G) ∧
        (∀ j : I, SheafOfModules.IsFlat (G j)) ∧
        ∀ (j : I) (K : Type u)
          (H : K → SheafOfModules.{u} (moduleRings Y.toRingedSpace))
          (f : G j ⟶ ∐ H),
          ∃ (S : Finset K) (g : G j ⟶ ∐ (fun k : {k // k ∈ S} ↦ H k.1)),
            g ≫ Sigma.desc (fun k : {k // k ∈ S} ↦ Sigma.ι H k.1) = f := by sorry

end AlgebraicGeometry
