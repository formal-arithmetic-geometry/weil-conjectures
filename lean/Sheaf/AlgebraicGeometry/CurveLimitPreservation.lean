/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q134
-/
module

public import Sheaf.AlgebraicGeometry.ProperCurveModuli
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Category.Preorder

/-!
# Limit preservation for the groupoid of proper algebraic-space curves

Source: Stacks Project, quot.tex, Tag 0D55, lemma-curves-limits
(blueprint: lem-sfb-curve-limit-preservation).

The three clauses are essential surjectivity, fullness, and faithfulness of the natural
filtered 2-colimit functor. Pullbacks and their comparison isomorphisms are the canonical
ones in the category of presheaves over the represented base. The curve condition is the
existing `AlgebraicSpace.IsProperCurveFamily`, with algebraic-space sources throughout.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Regard a proper curve family as a presheaf over its represented base, retaining its
actual projection. Source: Stacks Project, quot.tex, situation-curves and Tag 0D55
(blueprint: lem-sfb-curve-limit-preservation). -/
def ProperCurveFamily.presheafOver {S : Scheme.{u}} {T : Over S}
    (X : ProperCurveFamily T) : Over (yoneda.obj T) :=
  Over.mk X.projection

/-- The canonical comparison between pullback directly to a cone point and pullback
through a later stage. This is the usual composition isomorphism of fibre products,
with the cone equation supplying the identification of the base maps.
Source: Stacks Project, quot.tex, Tag 0D55, and the cartesian base-change convention
(blueprint: lem-sfb-curve-limit-preservation). -/
def ProperCurveModuli.limitBaseChangeIso {S : Scheme.{u}} {I : Type u} [Preorder I]
    (D : Iᵒᵖ ⥤ Over S) (c : Cone D) {i j : I} (hij : i ≤ j)
    (X : Over (yoneda.obj (D.obj (op i)))) :
    (Over.pullback (yoneda.map (c.π.app (op i)))).obj X ≅
      (Over.pullback (yoneda.map (c.π.app (op j)))).obj
        ((Over.pullback (yoneda.map (D.map (homOfLE hij).op))).obj X) :=
  (eqToIso (by simp only [← Functor.map_comp, c.w (homOfLE hij).op]) :
    (Over.pullback (yoneda.map (c.π.app (op i)))).obj X ≅
      (Over.pullback (yoneda.map (c.π.app (op j)) ≫
        yoneda.map (D.map (homOfLE hij).op))).obj X) ≪≫
    (Over.pullbackComp (yoneda.map (c.π.app (op j)))
      (yoneda.map (D.map (homOfLE hij).op))).app X

/-- The natural filtered 2-colimit functor for proper algebraic-space curves is an
 equivalence, expressed by its three explicit descent clauses.
Source: Stacks Project, quot.tex, Tag 0D55, lemma-curves-limits
(blueprint: lem-sfb-curve-limit-preservation).

Proof:
1. By lem-sfb-fp-space-limit-category descend the underlying finitely presented algebraic
   space of a limiting family to an initial stage, together with its identification over
   the limit. No flatness, properness or dimension bound is claimed at that initial stage.
2. Apply lem-sfb-space-eventually-flat to make the model flat at every sufficiently late
   stage; the initial finite-presentation hypothesis is exactly the needed one.
3. Apply lem-sfb-space-eventually-proper to make the model proper at every sufficiently
   late stage. This applies without assuming the initial model separated or proper.
4. Apply lem-sfb-space-eventually-fibre-dimension with bound one. Directedness gives a
   common stage for the three eventual conditions. Finite presentation is preserved by
   base change. This proves object descent, the first conjunct.
5. For families at two stages, pass to a common stage. Descend a given limiting
   isomorphism and its inverse separately by lem-sfb-fp-space-limit-category. Their two
   composite identities hold over the limit; eventual equality from the same lemma makes
   both identities hold at a later common stage. The resulting inverse maps give the
   isomorphism in the second conjunct; the comparison isomorphisms express its pullback.
6. If two stage isomorphisms agree over the limit, eventual equality for their underlying
   maps makes them equal at a later stage. This is the third conjunct. Families and
   arrows originally at different stages can first be moved to a common stage. Arrows
   of the filtered 2-colimit are stage isomorphisms modulo this eventual equality, so
   the three conjuncts assert exactly that its natural functor is an equivalence. -/
theorem properCurve_limit_preservation
    (I : Type u) [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Over (Spec (.of (ULift.{u} ℤ))))
    (c : Cone D) (hc : IsLimit c)
    [∀ i : I, IsAffine (D.obj (op i)).left] :
    (∀ X : ProperCurveFamily c.pt,
      ∃ (i : I) (Y : ProperCurveFamily (D.obj (op i))),
        Nonempty ((Over.pullback (yoneda.map (c.π.app (op i)))).obj Y.presheafOver ≅
          X.presheafOver)) ∧
    (∀ (i j : I) (X : ProperCurveFamily (D.obj (op i)))
        (Y : ProperCurveFamily (D.obj (op j)))
        (a : (Over.pullback (yoneda.map (c.π.app (op i)))).obj X.presheafOver ≅
          (Over.pullback (yoneda.map (c.π.app (op j)))).obj Y.presheafOver),
      ∃ (k : I) (hik : i ≤ k) (hjk : j ≤ k)
        (b : (Over.pullback (yoneda.map (D.map (homOfLE hik).op))).obj X.presheafOver ≅
          (Over.pullback (yoneda.map (D.map (homOfLE hjk).op))).obj Y.presheafOver),
        ProperCurveModuli.limitBaseChangeIso D c hik X.presheafOver ≪≫
          (Over.pullback (yoneda.map (c.π.app (op k)))).mapIso b ≪≫
          (ProperCurveModuli.limitBaseChangeIso D c hjk Y.presheafOver).symm = a) ∧
    (∀ (i : I) (X Y : ProperCurveFamily (D.obj (op i)))
        (a b : X.presheafOver ≅ Y.presheafOver),
      (Over.pullback (yoneda.map (c.π.app (op i)))).mapIso a =
        (Over.pullback (yoneda.map (c.π.app (op i)))).mapIso b →
      ∃ (j : I) (hij : i ≤ j),
        (Over.pullback (yoneda.map (D.map (homOfLE hij).op))).mapIso a =
          (Over.pullback (yoneda.map (D.map (homOfLE hij).op))).mapIso b) := by
  sorry

end AlgebraicGeometry
