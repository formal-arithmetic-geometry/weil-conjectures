/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import WeilConjectures.CategoryTheory.Comma.Over.DescentDatum
import Sheaf.AlgebraicGeometry.DescentPullbackCanonicalIso
import Sheaf.AlgebraicGeometry.FpqcSingletonFullyFaithful

/-!
# Full faithfulness of refinement for fpqc descent data

Source: Stacks Project, Descent, Lemma 35.35.11 (Tag 02W0), specialized to singleton
fpqc coverings (blueprint: lem-galois-fpqc-refinement-fully-faithful).
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits

/-- For singleton fpqc coverings `f` and `g` of `S`, with `g = h ≫ f`, descent data
pull back along `h`. Every morphism of the pulled-back data uniquely descends to a
morphism of the original data. The pullback objects and their data are described by
`IsPullback` and `Over.DescentDatum.IsBaseChange` respectively.

The proof of Stacks, Tag 02W0, forms `X' ×_S X`. Its projections to `X` and `X'` are
singleton fpqc coverings by base change (Tag 022D). The singleton full-faithfulness
theorem (Tag 0241) applies to both projections. The canonical comparison of pullbacks
(Tags 02VS and 023Y) identifies pullback along the projection to `X` with pullback
along `h` followed by the projection to `X'`. Given a morphism between the data pulled
back along `h`, fullness for the projection to `X` lifts its further pullback to a
morphism of the original data. Faithfulness for the projection to `X'` shows that this
lift pulls back to the given morphism. Faithfulness for the projection to `X` makes the
lift unique.

(blueprint: lem-galois-fpqc-refinement-fully-faithful) -/
theorem fpqcRefinementFullyFaithful {S X X' : Scheme.{u}}
    (f : X ⟶ S) (g : X' ⟶ S) (h : X' ⟶ X)
    (hf : Presieve.singleton f ∈ Scheme.fpqcPrecoverage S)
    (hg : Presieve.singleton g ∈ Scheme.fpqcPrecoverage S)
    (hcomp : h ≫ f = g) :
    (∀ (V : Over X) (D : Over.DescentDatum f V),
      ∃ (V' : Over X') (q : V'.left ⟶ V.left) (hq : q ≫ V.hom = V'.hom ≫ h)
        (D' : Over.DescentDatum g V'),
        IsPullback q V'.hom V.hom h ∧
          Over.DescentDatum.IsBaseChange hcomp hq D D') ∧
    (∀ (V W : Over X) (D : Over.DescentDatum f V) (E : Over.DescentDatum f W)
        (V' W' : Over X') (qV : V'.left ⟶ V.left) (qW : W'.left ⟶ W.left)
        (hqV : qV ≫ V.hom = V'.hom ≫ h) (hqW : qW ≫ W.hom = W'.hom ≫ h)
        (D' : Over.DescentDatum g V') (E' : Over.DescentDatum g W'),
      IsPullback qV V'.hom V.hom h → IsPullback qW W'.hom W.hom h →
      Over.DescentDatum.IsBaseChange hcomp hqV D D' →
      Over.DescentDatum.IsBaseChange hcomp hqW E E' →
      ∀ (u' : V' ⟶ W'),
        (∀ {T : Scheme.{u}} (a b : T ⟶ X') (hab : a ≫ g = b ≫ g)
            (x : Over.mk a ⟶ V'),
          (D'.transport a b hab x) ≫ u' =
            E'.transport a b hab (x ≫ u')) →
        ∃! (u : V ⟶ W),
          (∀ {T : Scheme.{u}} (a b : T ⟶ X) (hab : a ≫ f = b ≫ f)
              (x : Over.mk a ⟶ V),
            (D.transport a b hab x) ≫ u =
              E.transport a b hab (x ≫ u)) ∧
          u'.left ≫ qW = qV ≫ u.left) := by
  sorry

end AlgebraicGeometry
