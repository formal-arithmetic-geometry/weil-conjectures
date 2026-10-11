/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Topology.LocallyConstant.Algebra
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale

/-!
# Sections of a constant étale sheaf

Source: Stacks Project, Etale Cohomology, Remark 59.23.2 (Tag 03P5), using
Lemma 59.15.8 (Tag 03O3) and Groupoids, Example 39.5.6 (Tag 03YW).
(blueprint: lem-weil-pbc-constant-sheaf-sections-locally-constant)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- Sections of a constant étale sheaf are Zariski-locally constant maps, and the
comparison sends the canonical section induced by `e` to the constant map with value `e`.
Source: Stacks Project, Etale Cohomology, Remark 59.23.2 (Tag 03P5).
(blueprint: lem-weil-pbc-constant-sheaf-sections-locally-constant)

Proof:
1. Form the constant group scheme, the disjoint union of copies of `T` indexed by `E`
   (Groupoids, Example 39.5.6, Tag 03YW). By
   `lem-weil-pbc-constant-group-scheme-morphism-clopen`, its represented presheaf on
   an étale `U` consists of clopen decompositions indexed by `E`, equivalently maps
   from `U` to `E` with open fibres. The group law is pointwise addition, and the
   presheaf map from `E` sends `e` to the constant map with value `e`.
2. By `lem-weil-pbc-small-etale-representable-presheaf-sheaf` (Tag 03O3), this
   represented presheaf is a sheaf. The sheafification universal property factors
   the constant-presheaf map uniquely through the constant sheaf. Every represented
   section is constant on each nonempty piece of its clopen decomposition; these
   pieces form an étale cover. Thus local representatives give surjectivity and
   sheaf uniqueness gives injectivity (using
   `lem-weil-pbc-site-sheafification-sections-local`). The comparison is an
   isomorphism. Evaluate at the identity object over `T`; its factorization through
   the sheafification unit gives the displayed compatibility with constant maps. -/
theorem constantSheaf_sections_locallyConstant
    (T : Scheme.{u}) (E : Type u) [AddCommGroup E] :
    ∃ φ : AddEquiv
      (↑(((constantSheaf T.smallEtaleTopology (AddCommGrpCat.{u})).obj
        (AddCommGrpCat.of E)).obj.obj
          (Opposite.op (Scheme.Etale.mk (𝟙 T)))))
      (LocallyConstant T E),
      ∀ e : E,
        φ (((toSheafify T.smallEtaleTopology
          ((Functor.const T.Etaleᵒᵖ).obj (AddCommGrpCat.of E))).app
            (Opposite.op (Scheme.Etale.mk (𝟙 T)))) e) = LocallyConstant.const T e := by
  sorry

end AlgebraicGeometry
