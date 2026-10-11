/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.CategoryTheory.Pi.Basic
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!
# Abelian etale sheaves on a finite coproduct

Source: Stacks Project, Etale Cohomology, proof of Lemma 0A5B, first paragraph,
finite disjoint-union reduction (blueprint: lem-weil-pbc-etale-sheaf-clopen-product).
-/

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Restriction to the clopen components of a finite coproduct is an equivalence of
abelian etale sheaf categories, and global sections are naturally the product of
component global sections. The coproduct is any coproduct cocone
`hc : IsColimit (Cofan.mk X ι)` (as in lem-weil-pbc-direct-image-split-cover-product), its
coprojections open and closed by `lem-weil-pbc-scheme-coproduct-family`; global sections
are sections at `Scheme.Etale.mk (𝟙 X)`. Source: Stacks Project, proof of Lemma 0A5B,
first paragraph
(blueprint: lem-weil-pbc-etale-sheaf-clopen-product).

Proof:
1. For an etale object U over the coproduct, pull back the coprojections to obtain
pairwise disjoint clopen U_i covering U (`lem-weil-pbc-scheme-coproduct-family`). The
sheaf equalizer condition (`def-weil-pbc-abelian-etale-sheaves`) gives F(U) = product F(U_i);
the empty covering gives F(empty) = 0.
2. Localization of the etale site at a component is its small etale site
(`lem-weil-pbc-etale-site-localization-open`). Inverse image is restriction, naturally
in the sheaf (`lem-weil-pbc-etale-inverse-image-restriction`), identifying F(U_i) with
sections of the component inverse image.
3. Conversely, reconstruct a sheaf from G_i by assigning to U the product of
G_i(U x_C C_i). Products preserve the sheaf equalizer condition. Disjointness and
G_i(empty) = 0 give the quasi-inverse identifications, using
`lem-weil-pbc-scheme-coproduct-family` and `def-weil-pbc-abelian-etale-sheaves`.
4. Naturality of the decomposition recovers morphisms componentwise. Evaluate at
U = C, using `lem-weil-pbc-etale-inverse-image-restriction`, to obtain the natural
isomorphism of global-sections functors. -/
theorem Etale.sheaf_clopen_product {I : Type v} [Finite I] {X : Scheme.{u}}
    (C : I → Scheme.{u}) (ι : ∀ i, C i ⟶ X) (hc : IsColimit (Cofan.mk X ι)) :
    let R := Functor.pi' (fun i ↦ Etale.upperStar AddCommGrpCat.{u + 1} (ι i))
    R.IsEquivalence ∧
      Nonempty
        ((sheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
            (op (Scheme.Etale.mk (𝟙 X))) ≅
          R ⋙ Functor.pi (fun i ↦
            (sheafSections (C i).smallEtaleTopology AddCommGrpCat.{u + 1}).obj
              (op (Scheme.Etale.mk (𝟙 (C i))))) ⋙ Pi.functor I) := by
  sorry

end AlgebraicGeometry
