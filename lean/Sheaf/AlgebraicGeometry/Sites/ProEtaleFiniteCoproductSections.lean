/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory

/-!
# Evaluation of sheaves on finite coproducts in the pro-etale site

This is the sheaf-theoretic core used by
`Sheaf.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductEvaluation`.
The geometric construction and the site-cover argument are separated so that the
latter can be proved independently.
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.ProEt

/-- Sections on a finite disjoint union are the product of the sections on its summands.

Source: Stacks Project, Tag 0F4P, proof of `lemma-weakly-contractible-cover`, and
Tag 0DB1, hypotheses (a)--(c) of `remark-take-unions-hypercovering-X`.
The proof uses the sheaf equalizer condition for the finite pro-etale covering by the
pairwise disjoint open summands: off-diagonal pullbacks are empty and diagonal pullbacks
are identities, so compatible tuples glue uniquely. The empty family is included; its
cover is the empty cover and the sheaf axiom gives a singleton of sections.
(blueprint: lem-weil-pbc-proetale-finite-coproduct-sections)
-/
theorem finite_coproduct_sheaf_core (X : Scheme.{u}) (I : Type v) [Finite I]
    (V : I → X.ProEt) (W : X.ProEt) (ι : ∀ i, V i ⟶ W)
    (e : (∐ fun i ↦ (V i).left) ≅ W.left)
    (hqc : ∀ i, CompactSpace (V i).left)
    (hqs : ∀ i, QuasiSeparatedSpace (V i).left)
    (hι : ∀ i, Sigma.ι (fun i ↦ (V i).left) i ≫ e.hom = (ι i).left) :
    (∀ F : Sheaf (topology X) (Type (max (u + 1) w)),
        Function.Bijective (fun s : F.obj.obj (op W) ↦
          fun i ↦ F.obj.map (ι i).op s)) ∧
      (IsEmpty I → IsEmpty W.left ∧
        ∀ F : Sheaf (topology X) (Type (max (u + 1) w)),
          Nonempty (Unique (F.obj.obj (op W)))) := by
  sorry

end AlgebraicGeometry.Scheme.ProEt
