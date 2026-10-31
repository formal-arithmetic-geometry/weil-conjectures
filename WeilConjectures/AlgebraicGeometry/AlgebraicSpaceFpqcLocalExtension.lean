/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AlgebraicSpace
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import WeilConjectures.CategoryTheory.Comma.Over.DescentDatum
import WeilConjectures.AlgebraicGeometry.FpqcDescentEtale
import WeilConjectures.AlgebraicGeometry.SeparatedLqfFpqcDescent
import WeilConjectures.SecPurity.QcMapAffineEtaleNeighbourhood

/-! # An étale local extension of an invariant section on an affine fpqc cover

Source: Stacks Project, Tag 0APL, Gabber's proof, the chart descent construction
(blueprint: lem-a1-algebraic-space-fpqc-etale-local-extension).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- An invariant section on an affine fpqc singleton extends over an étale cover of its
base. This assertion only constructs the local extension; global gluing and uniqueness
are separate steps.

Source: Stacks Project, Tag 0APL, proposition-sheaf-fpqc, Gabber's proof,
steps 3--5 of `lem-a1-algebraic-space-fpqc-sheaf`
(blueprint: lem-a1-algebraic-space-fpqc-etale-local-extension).

Proof: choose the affine étale neighbourhood `U → E` of the quasi-compact source of
`f`, and represent its pullback by `V → T'`, which is surjective, étale, separated and
locally quasi-finite. The equality of the two restrictions of `x` identifies the two
pullbacks of `V` over `T' ×_T T'` by retaining the `U` coordinate. Over the triple overlap,
both composites retain that coordinate, so the pullback universal property verifies the
cocycle. Effective fpqc descent of separated locally quasi-finite schemes gives `W → T`
and `V ≅ W ×_T T'`, inducing this datum. Étaleness descends fpqc; surjectivity follows
by lifting a point first to `T'`, then to `V`, and projecting to `W`. The map `V → U` is
invariant because the datum retains its `U` coordinate. The fpqc cover `V → W` therefore
descends it to `W → U` by scheme-valued fpqc descent. Its composite to `S` agrees with
the prescribed structure map after this cover, so scheme descent uniqueness makes it
an `S`-map. Composing with `U → E` gives `y`. The defining pullback square for `V`
gives exactly the displayed equality on `W ×_T T'`. The construction requires no
separatedness or finiteness of `E`, and no quasi-compactness of `V`.
-/
theorem exists_etale_local_extension_of_affine_fpqc
    {S : Scheme.{u}} (E : AlgebraicSpace S) {T T' : Over S}
    [IsAffine T.left] [IsAffine T'.left] (f : T' ⟶ T)
    [Flat f.left] [Surjective f.left] (x : E.obj.obj.obj (op T'))
    (hx : ∀ {Z : Over S} (g h : Z ⟶ T'), g ≫ f = h ≫ f →
      E.obj.obj.map g.op x = E.obj.obj.map h.op x) :
    ∃ (W : Over S) (p : W ⟶ T), Etale p.left ∧ Surjective p.left ∧
      ∃ y : E.obj.obj.obj (op W),
        E.obj.obj.map (pullback.fst p f).op y =
          E.obj.obj.map (pullback.snd p f).op x := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
