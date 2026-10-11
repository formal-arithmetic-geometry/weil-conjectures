/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Cofinal finite affine étale coverings

Source: literature/stacks-project/etale-cohomology.tex, Section 59.51, Tag 03Q4
(label section-colimit), first paragraph
(blueprint: lem-weil-pbc-etale-qcqs-cofinal-finite-coverings).
-/

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/--
For a quasi-compact and quasi-separated scheme, every jointly surjective étale
family admits a finite affine étale refinement with quasi-compact pairwise
fibre products.

Source: literature/stacks-project/etale-cohomology.tex, Section 59.51, Tag 03Q4
(label section-colimit), first paragraph, using Topologies, Lemma Tag 0218 and
Sites, Lemma Tag 0738 (blueprint: lem-weil-pbc-etale-qcqs-cofinal-finite-coverings).
Proof:
1. Choose a finite affine open cover `U_j` of `U` using
   `lem-weil-pbc-qcqs-scheme-cofinal-finite-coverings` (Stacks, Tag 01IT and
   quasi-compactness). Only quasi-compactness is needed for this step.
2. Restrict the given covering to each `U_j` by scheme fibre products
   (`def-pc-fibre-product`). The projections remain étale and jointly surjective by
   `lem-weil-pbc-etale-covering-base-change` (Stacks, Tag 0217 (3)).
3. On each affine `U_j`, apply `lem-weil-pbc-etale-covering-affine-refinement`
   (Stacks, Tag 0218) to obtain finitely many affine opens of the restricted sources.
   Index their union by pairs `(j, k)` and compose their maps with `U_j → U`.
4. The composites are étale, since open immersions are étale and étale morphisms
   compose (`lem-weil-pbc-etale-composition-cancellation`). The fibre square gives
   their factorization through the selected `T_a → U` (`def-pc-fibre-product`).
   Their images cover each `U_j`, hence their union covers `U`.
5. Each affine `V_b` is quasi-compact by
   `lem-weil-pbc-spec-basic-opens-unit-ideal-quasi-compact` (iii). Since `U` is
   quasi-separated, `V_b → U` is quasi-compact by
   `lem-weil-pbc-qcqs-morphism-permanence` (1). Its base change to `V_b'` is
   quasi-compact by (3), and its source is quasi-compact by (2).
6. Thus every covering in the small étale site (`def-weil-pbc-etale-site`) has a
   finite affine refinement with quasi-compact pairwise fibre products. This is
   exactly cofinality under refinement, the condition used in Stacks, Tag 0738 (4).

Lean form: `U` is the object `Scheme.Etale.mk (𝟙 U)` of its small étale site
`U.smallEtaleTopology`; a family `(T_a → U)` of étale morphisms is a family of
objects `T a` of `U.Etale` with their (unique) maps to it, and it is jointly surjective
exactly when its sieve covers (`Scheme.ofArrows_mem_smallEtaleTopology_iff`). A
factorization of `V_b → U` through `T_{a(b)} → U` is a morphism `V b ⟶ T (a b)` of
`U.Etale`, and `V_b ×_U V_b'` is the scheme fibre product of the structure maps.
-/
theorem etale_qcqs_cofinal_finite_affine_coverings
    {U : Scheme.{u}} [CompactSpace U] [QuasiSeparatedSpace U]
    {A : Type v} (T : A → U.Etale) (f : ∀ a, T a ⟶ Scheme.Etale.mk (𝟙 U))
    (hf : Sieve.ofArrows T f ∈ U.smallEtaleTopology (Scheme.Etale.mk (𝟙 U))) :
    ∃ (B : Type w) (_ : Finite B) (a : B → A) (V : B → U.Etale)
      (v : ∀ b, V b ⟶ Scheme.Etale.mk (𝟙 U)),
      (∀ b, IsAffine (V b).left) ∧
      (∀ b, ∃ h : V b ⟶ T (a b), h ≫ f (a b) = v b) ∧
      Sieve.ofArrows V v ∈ U.smallEtaleTopology (Scheme.Etale.mk (𝟙 U)) ∧
      (∀ b b', CompactSpace (pullback (C := Scheme.{u}) (V b).hom (V b').hom)) := by
  sorry

end AlgebraicGeometry
