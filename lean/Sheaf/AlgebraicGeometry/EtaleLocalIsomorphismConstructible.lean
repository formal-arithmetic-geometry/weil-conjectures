/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q142
-/
module

public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import Sheaf.AlgebraicGeometry.LocallyClosedStratification
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import Sheaf.AlgebraicGeometry.EtaleInverseImageCompositionModuleLinearCore
import WeilConjectures.ConstructibleSheaf.Defs

/-!
# Transfer of a constructible stratification through etale-local isomorphisms

Source: Stacks Project, Etale Cohomology, Tag 03RU, module-sheaf clause, and its
cover-refinement consequence on a fixed constructible stratification
(blueprint: lem-sf-etale-local-isomorphism-constructible).
-/

@[expose] public section

universe u v

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- A fixed constructible stratification for `G` also trivializes `F` when the two
module sheaves are isomorphic after inverse image to each member of an arbitrary
jointly surjective etale family. The conclusion uses the same `S`, including its
stratum schemes and immersions, and the finite-constant-value clause of
`IsConstructibleEtaleModuleSheaf`. No overlap compatibility is assumed.

Source: Stacks Project, Tag 03RU, module-sheaf clause
(blueprint: lem-sf-etale-local-isomorphism-constructible).

Proof:
1. Fix a stratum `i : Z ⟶ X`. Its given trivialization supplies an etale cover
   `v_b : V_b ⟶ Z` and finite modules `M_b`. The inverse-image/restriction comparison
   of lem-weil-pbc-etale-inverse-image-restriction identifies the local restriction
   with `v_b⁻¹ i⁻¹ G`. Naturality for multiplication by each scalar makes this
   comparison module-linear, using prop-weil-pbc-inverse-image-modules-exact;
   constant sections generate the constant ring sheaf by sheafification.
2. Pull the supplied covering back to each `V_b`. The maps
   `q_bj : W_bj = V_b ×_X U_j ⟶ V_b` form a cover by
   lem-weil-pbc-etale-covering-base-change. Their composites with `v_b` cover `Z`
   by lem-weil-pbc-etale-covering-composition, without extracting a finite subcover.
3. Write `r_bj : W_bj ⟶ U_j`. The module-linear composition comparisons of
   lem-weil-pbc-inverse-image-composition-module-linear-core, the given local
   isomorphism pulled back along `r_bj`, and the trivialization of step 1 give
   `(v_b q_bj)⁻¹ i⁻¹ F ≅ r_bj⁻¹ u_j⁻¹ F ≅ r_bj⁻¹ u_j⁻¹ G
     ≅ q_bj⁻¹ v_b⁻¹ i⁻¹ G ≅ q_bj⁻¹ (constant M_b) ≅ constant M_b`.
   The last arrow is lemma-constructible-pullback-constant for `ModuleCat Λ`.
4. Convert inverse image along the etale chart back to restriction using step 1's
   comparison. The resulting finite constant models witness exactly clause (b)
   of def-weil-pbc-etale-constructible-sheaf on this stratum. Repeat for every
   `k : Fin S.n`. The partition and constructible parts are the given ones;
   no gluing equation for the independently chosen trivializations is needed. -/
theorem etaleLocalIsomorphismConstructible
    {X : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
    (F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (S : LocallyClosedStratification X)
    (hSc : ∀ k : Fin S.n, Topology.IsConstructible (S.stratum k))
    (hG : ∀ k : Fin S.n,
      ∃ d : LocallyConstantDatum ((Etale.upperStar (ModuleCat.{u + 1} Λ)
          (S.immersion k)).obj G),
        ∀ b : d.cover.I₀, ∃ M : ModuleCat.{u + 1} Λ, Finite M ∧
          Nonempty ((((Etale.upperStar (ModuleCat.{u + 1} Λ) (S.immersion k)).obj G).over
              (d.cover.etalePrecoverageToEtale b)) ≅
            (constantSheaf ((S.domain k).smallEtaleTopology.over
              (d.cover.etalePrecoverageToEtale b)) (ModuleCat.{u + 1} Λ)).obj M))
    (J : Type v) (U : J → Scheme.{u}) (uMap : ∀ j : J, U j ⟶ X)
    (hEt : ∀ j : J, Etale (uMap j))
    (hcover : ∀ x : X, ∃ j : J, x ∈ Set.range (uMap j))
    (hiso : ∀ j : J, Nonempty
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) (uMap j)).obj F ≅
        (Etale.upperStar (ModuleCat.{u + 1} Λ) (uMap j)).obj G)) :
    ∀ k : Fin S.n,
      ∃ d : LocallyConstantDatum ((Etale.upperStar (ModuleCat.{u + 1} Λ)
          (S.immersion k)).obj F),
        ∀ b : d.cover.I₀, ∃ M : ModuleCat.{u + 1} Λ, Finite M ∧
          Nonempty ((((Etale.upperStar (ModuleCat.{u + 1} Λ) (S.immersion k)).obj F).over
              (d.cover.etalePrecoverageToEtale b)) ≅
            (constantSheaf ((S.domain k).smallEtaleTopology.over
              (d.cover.etalePrecoverageToEtale b)) (ModuleCat.{u + 1} Λ)).obj M) := by
  sorry

end AlgebraicGeometry.Scheme
