/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
import Sheaf.AlgebraicGeometry.KInjectiveResolutions

/-!
# Existence and uniqueness of K-injective resolutions on the small étale site

Source: blueprint `sec-curve-estimates/sk-prop-cd`,
proposition `prop-weil-pbc-kinjective-resolutions-exist`; Stacks Project, Tags 079P and 070I
(blueprint: prop-weil-pbc-kinjective-resolutions-exist).
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace CochainComplex

/-- Every complex of étale `R`-module sheaves has a K-injective resolution, functorially up
 to chain homotopy. Any two such resolutions are homotopy equivalent. Bounded-below
 complexes of injectives are K-injective.

Source: blueprint `sec-curve-estimates/sk-prop-cd`, proposition on K-injective resolutions;
Stacks Project, Tags 079P and 070I
(blueprint: prop-weil-pbc-kinjective-resolutions-exist).

Proof:
1. The module-sheaf category is Grothendieck abelian by
   `lem-weil-pbc-module-sheaves-grothendieck-abelian`. Apply
   `lem-weil-pbc-kinjective-functorial-existence` (Stacks 079P). The resulting replacement
   functor and natural quasi-isomorphism give the object and map assignments below.
   Strict functor laws imply their homotopy versions. Homotopic input maps induce homotopic
   output maps by the bijection on homotopy classes into a K-injective target (070I).
2. For two resolutions `s : K ⟶ I`, `t : K ⟶ J`, both images in the derived category are
   invertible. Lift their comparison isomorphism and its inverse using
   `lem-weil-pbc-kinjective-hom-derived`. Injectivity on homotopy classes says the composites
   are homotopic to the identities, giving a chain-homotopy equivalence.
   The comparison carries `s` to `t` up to homotopy: both composites lift the same derived
   morphism `Qt`, so injectivity on homotopy classes gives their equality.
3. Apply `lem-weil-pbc-bounded-below-injectives-kinjective`, i.e. Mathlib's
   `CochainComplex.isKInjective_of_injective`, to the given lower bound and injective terms. -/
theorem etale_kinjective_resolutions_exist (T : Scheme.{u}) (R : Type (u + 1)) [CommRing R] :
    (∃ (I : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} R)) ℤ →
          CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} R)) ℤ)
       (s : ∀ K, K ⟶ I K)
       (φ : ∀ {K L}, (K ⟶ L) → (I K ⟶ I L)),
       (∀ K, IsKInjectiveResolution T R (s K)) ∧
       (∀ K, Nonempty (Homotopy (φ (𝟙 K)) (𝟙 (I K)))) ∧
       (∀ {K L M} (f : K ⟶ L) (g : L ⟶ M),
         Nonempty (Homotopy (φ (f ≫ g)) (φ f ≫ φ g))) ∧
       (∀ {K L} (f g : K ⟶ L),
         Nonempty (Homotopy f g) → Nonempty (Homotopy (φ f) (φ g))) ∧
       (∀ {K L} (f : K ⟶ L), Nonempty (Homotopy (s K ≫ φ f) (f ≫ s L)))) ∧
    (∀ (K I J : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} R)) ℤ)
       (s : K ⟶ I) (t : K ⟶ J),
       IsKInjectiveResolution T R s → IsKInjectiveResolution T R t →
       Nonempty (HomotopyEquiv I J)) ∧
    (∀ (I : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} R)) ℤ)
       (d : ℤ), I.IsStrictlyGE d → (∀ n : ℤ, Injective (I.X n)) → I.IsKInjective) := by
  sorry

end CochainComplex
