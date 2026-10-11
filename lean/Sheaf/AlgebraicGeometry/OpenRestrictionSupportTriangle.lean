/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U1
-/
import Sheaf.AlgebraicGeometry.DerivedOpenRestrictionMaps
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.Topology.QuasiSeparated

/-! # The support triangle for restriction to an open subscheme

Source: Stacks Project, Duality for Schemes, Tag 0E4G, proof of Lemma 48.4.3;
Derived Categories of Schemes, Lemma 36.4.1 and Definition 36.6.1
(blueprint: lem-sc-open-restriction-support-triangle).
-/

universe u w

open CategoryTheory CategoryTheory.Limits Pretriangulated

set_option autoImplicit false
set_option synthInstance.maxSize 2048

namespace AlgebraicGeometry

/-- Complete the open-restriction unit to a distinguished triangle with quasi-coherent
vertices. Its third vertex has cohomology supported on the closed complement and is
bounded below whenever the first vertex is bounded below.
Source: Stacks Project, Tag 0E4G, proof of Lemma 48.4.3; Lemma 36.4.1 and
Definition 36.6.1 (blueprint: lem-sc-open-restriction-support-triangle).

Proof:
1. Choose a K-injective representative I of K. Restriction preserves K-injectivity
   (lem-sc-derived-k-injective-restrict-open), and direct image is computed by applying
   j_* to the restricted representative (def-pc-ringed-spaces-derived-direct-image).
   Complete I → j_*j⁻¹I to its mapping-cone triangle (def-weil-abstract-derived-category).
   The middle vertex is quasi-coherent by lem-pc-derived-direct-image-preserves-qcoh;
   the cone is quasi-coherent by the cohomology exact sequence, using
   lem-weil-pbc-quasi-coherent-module-kernel,
   lem-weil-pbc-quasi-coherent-module-cokernel-image, and lem-pc-quasi-coherent-extension.
2. Restriction is exact (lem-sc-derived-open-restriction-adjunction-exact). The
   restricted unit is the identity on j⁻¹I since j⁻¹j_*j⁻¹I = j⁻¹I, as in Stacks 01LH
   and lem-pc-restrict-derived-direct-image-open. Thus the restricted cone is zero:
   every cohomology stalk at a point of V vanishes.
3. If K is bounded below, truncate below a lower bound a and choose a bounded-below
   injective resolution (lem-sc-bounded-below-injective-resolution-existence).
   It is K-injective (lem-weil-pbc-bounded-below-injectives-kinjective). Restriction
   and termwise direct image remain zero below a. Its cone is zero below a - 1,
   proving the conditional bounded-below assertion. -/
theorem openRestriction_support_triangle (Y : Scheme.{u})
    [CompactSpace Y] [QuasiSeparatedSpace Y] (V : Y.Opens)
    (hV : IsCompact (V : Set Y))
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))]
    (K : schemeDerivedCategory Y) (hK : schemeDerivedQCohProperty Y K) :
    ∃ (adj : (schemeOpenRestriction Y V).mapDerivedCategory ⊣ schemeDerivedDirectImage V.ι)
      (Q : schemeDerivedCategory Y)
      (β : (schemeDerivedDirectImage V.ι).obj
        ((schemeOpenRestriction Y V).mapDerivedCategory.obj K) ⟶ Q)
      (δ : Q ⟶ K⟦(1 : ℤ)⟧),
      Triangle.mk (adj.unit.app K) β δ ∈ distTriang (schemeDerivedCategory Y) ∧
      schemeDerivedQCohProperty Y
        ((schemeDerivedDirectImage V.ι).obj
          ((schemeOpenRestriction Y V).mapDerivedCategory.obj K)) ∧
      schemeDerivedQCohProperty Y Q ∧
      (∀ (n : ℤ) (x : Y), x ∈ V →
        Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) n).obj Q).val.presheaf x))) ∧
      ((∃ a : ℤ, K.IsGE a) → ∃ b : ℤ, Q.IsGE b) := by
  sorry

end AlgebraicGeometry
