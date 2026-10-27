/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q22
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Finite relative affine charts for a locally finite type morphism

Source: Stacks Project, Tag 0C4W, proof, first paragraph, in Situation
`situation-descent-property` of `limits.tex`.
(blueprint: lem-trf-lft-finite-relative-affine-atlas).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A locally finite type morphism of qcqs schemes over a qcqs base has finite nested
affine charts over affine base opens, with finite type coordinate maps compatible with
the structure maps. The coordinate rings are canonically `Γ(S, W j)`, `Γ(V, Y j)`,
and `Γ(U, X j k)`. The `appLE` composition equation expresses that the chart map is
an algebra map for the two base-algebra structures induced by `v` and `s`.

Source: Stacks Project, Tag 0C4W, proof, first paragraph, in Situation
`situation-descent-property` of `limits.tex`.

Proof:
1. By lem-weil-pbc-qcqs-morphism-permanence, compactness of U and
   quasi-separatedness of V imply quasi-compactness of g.
2. Apply lem-weil-pbc-affine-opens-basis at v(y) in S, then at y in the inverse
   image of the resulting affine base open. Compactness of V, as defined in
   def-weil-pbc-quasi-compact-scheme, gives finitely many such affine target opens.
3. Each inverse image of a target chart is quasi-compact by step 1. The affine
   charts in the locally finite type definition (def-weil-finite-type-morphism)
   have finite type coordinate maps. Retain a finite subcover of each inverse image.
4. Restrict g followed by v equals s to each source chart. By the functoriality
   and uniqueness in def-weil-affine-spectrum, the induced coordinate maps compose
   to the structure map and their spectra recover the restricted scheme map.
   Enumerate the finite covers by Fin m and Fin (n j); allow zero indices and rings.
(blueprint: lem-trf-lft-finite-relative-affine-atlas). -/
theorem exists_finite_relative_affine_atlas
    (S U V : Scheme.{u}) [CompactSpace S] [QuasiSeparatedSpace S]
    [CompactSpace U] [QuasiSeparatedSpace U] [CompactSpace V] [QuasiSeparatedSpace V]
    (s : U ⟶ S) (v : V ⟶ S) (g : U ⟶ V) (hcomp : g ≫ v = s)
    [LocallyOfFiniteType g] :
    QuasiCompact g ∧
      ∃ (m : ℕ) (n : Fin m → ℕ) (W : Fin m → S.Opens) (Y : Fin m → V.Opens)
        (X : (j : Fin m) → Fin (n j) → U.Opens),
        (∀ j, IsAffineOpen (W j)) ∧
        ∃ (hY : ∀ j, IsAffineOpen (Y j)) (hX : ∀ j k, IsAffineOpen (X j k)),
          (⨆ j, Y j) = ⊤ ∧ (∀ j, (⨆ k, X j k) = g ⁻¹ᵁ Y j) ∧
          ∃ (hYW : ∀ j, Y j ≤ v ⁻¹ᵁ W j)
            (hXY : ∀ j k, X j k ≤ g ⁻¹ᵁ Y j)
            (hXW : ∀ j k, X j k ≤ s ⁻¹ᵁ W j),
            ∀ j k, (g.appLE (Y j) (X j k) (hXY j k)).hom.FiniteType ∧
              v.appLE (W j) (Y j) (hYW j) ≫ g.appLE (Y j) (X j k) (hXY j k) =
                s.appLE (W j) (X j k) (hXW j k) ∧
              Spec.map (g.appLE (Y j) (X j k) (hXY j k)) ≫ (hY j).fromSpec =
                (hX j k).fromSpec ≫ g := by
  sorry

end AlgebraicGeometry
