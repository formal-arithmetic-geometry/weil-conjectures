/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q127
-/
module

public import Sheaf.AlgebraicGeometry.SpaceGroupoidQuotientPresentation
public import Sheaf.AlgebraicGeometry.AlgebraicModuliStack
public import Sheaf.AlgebraicGeometry.GroupoidScheme
public import Sheaf.CategoryTheory.GroupoidStackificationLocalDescription
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers

/-! # The cartesian action groupoid of a quotient morphism

Source: Stacks Project, spaces-groupoids.tex, Tag 04Y4 and its preceding construction
(blueprint: lem-sfb-quotient-map-cartesian-action-groupoid).

A quotient is specified by `SpaceGroupoidQuotientPresentation`, retaining its arrow
comparison. The conclusion presents the actual 2-fibre product by the action groupoid.
Thus the quotient equivalence preserves both projections, including its specified
comparison arrow, without choosing another copy of the stackification.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w v' w'

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- Forget the vertical-isomorphism condition on a total-category 2-fibre product.
This is the actual inclusion in the comma category, not an independently chosen map.
Source: Stacks, Tag 003R, as used in Tag 04Y4
(blueprint: lem-sfb-quotient-map-cartesian-action-groupoid). -/
def quotientCartesianComma {S : Scheme.{u}}
    {D : BasedCategory.{v, w} (Over S)} {X : BasedCategory.{v', w'} (Over S)}
    {Y : BasedCategory (Over S)} (a : BasedFunctor D Y) (f : BasedFunctor X Y) :
    (moduliTwoFiberProduct a f).obj ⥤ Comma a.toFunctor f.toFunctor :=
  ObjectProperty.ι _

/-- A morphism of arbitrary algebraic-space groupoids induces a quotient morphism,
and its Limits.pullback by the target object space is presented by the specified action groupoid.
The Limits.pullback squares specify A = U ×_{U'} R' and B = R ×_{U'} R' uniquely up to their
unique projection-preserving isomorphisms. The auxiliary maps `d` and `m` are uniquely
specified maps into composition pullbacks. The final presentation is exactly the
canonical equivalence of Tag 04Y4: its two projection functors are fixed, and the last
formula fixes the comparison arrow to be the image of r', followed by the comparison
for the induced quotient morphism.

Source: Stacks Project, spaces-groupoids.tex, Tag 04Y4, including the construction
immediately preceding it (blueprint: lem-sfb-quotient-map-cartesian-action-groupoid).

Proof:
1. By lem-trf-space-fibre-products-etale-covers form the algebraic spaces A and B.
   Before stackification form D ×_{P'} P, where D is the discrete groupoid of U'.
2. Its objects are triples (u',u,r') with s'(r') = u' and t'(r') = f0(u).
   Forgetting u' identifies them with A. An arrow is (1,r) with
   c'(f1(r),r'2) = r'1, hence is uniquely (r,r'2) in B.
3. Transport identity, inverse and composition across these identifications. They give
   precisely the formulas below. Their groupoid laws follow from those in the raw
   2-product. The maps to U' agree on both ends, and all formulas commute with test-scheme
   restriction. Both projections and the comparison r' are preserved.
4. Extend the raw morphism by the universal property of stackification, obtaining f
   and alpha. The discrete groupoid D is already an fppf stack because U' is a sheaf.
   By lem-sfb-stackification-two-fibre-products, stackification of the raw 2-product
   is D ×_{[U'/R']} [U/R]. The local description of stackification gives exactly the
   arrow and local-object clauses of its quotient presentation. The raw functor gives
   the two projection equalities and the final comparison formula. No flatness or
   finiteness property is used. -/
theorem quotient_map_cartesian_action_groupoid {S : Scheme.{u}}
    (U R U' R' : AlgebraicSpace S)
    (s t : R.obj.obj ⟶ U.obj.obj) (e : U.obj.obj ⟶ R.obj.obj)
    (i : R.obj.obj ⟶ R.obj.obj) (c : Limits.pullback s t ⟶ R.obj.obj)
    (s' t' : R'.obj.obj ⟶ U'.obj.obj) (e' : U'.obj.obj ⟶ R'.obj.obj)
    (i' : R'.obj.obj ⟶ R'.obj.obj) (c' : Limits.pullback s' t' ⟶ R'.obj.obj)
    (f0 : U.obj.obj ⟶ U'.obj.obj) (f1 : R.obj.obj ⟶ R'.obj.obj)
    (hs : s ≫ f0 = f1 ≫ s') (ht : t ≫ f0 = f1 ≫ t')
    (he : e ≫ f1 = f0 ≫ e') (hi : i ≫ f1 = f1 ≫ i')
    (hc : ∀ z : Limits.pullback s t ⟶ Limits.pullback s' t',
      z ≫ Limits.pullback.fst s' t' = Limits.pullback.fst s t ≫ f1 →
      z ≫ Limits.pullback.snd s' t' = Limits.pullback.snd s t ≫ f1 → z ≫ c' = c ≫ f1)
    (X : BasedCategory.{v, w} (Over S)) (X' : BasedCategory.{v', w'} (Over S))
    (a : BasedFunctor (discreteModuli U.obj.obj) X)
    (a' : BasedFunctor (discreteModuli U'.obj.obj) X')
    (hX : SpaceGroupoidQuotientPresentation s t e i c X a)
    (hX' : SpaceGroupoidQuotientPresentation s' t' e' i' c' X' a') :
    ∃ (f : BasedFunctor X X')
      (α : ModuliTwoIso (a.comp f) ((discreteModuliMap f0).comp a')),
      (∀ (T : Over S) (r : yoneda.obj T ⟶ R.obj.obj)
        (r' : {r' : yoneda.obj T ⟶ R'.obj.obj //
          r' ≫ s' = (r ≫ s) ≫ f0 ∧ r' ≫ t' = (r ≫ t) ≫ f0}),
        r'.val = r ≫ f1 →
        f.map (spaceGroupoidPresentationArrow s t a hX.arrows
            (r ≫ s) (r ≫ t) ⟨r, rfl, rfl⟩) ≫
            α.val.hom.app (CostructuredArrow.mk (r ≫ t)) =
          α.val.hom.app (CostructuredArrow.mk (r ≫ s)) ≫
            spaceGroupoidPresentationArrow s' t' a' hX'.arrows
              ((r ≫ s) ≫ f0) ((r ≫ t) ≫ f0) r') ∧
      ∃ (A B : AlgebraicSpace S)
        (p : A.obj.obj ⟶ U.obj.obj) (q : A.obj.obj ⟶ R'.obj.obj)
        (j : B.obj.obj ⟶ R.obj.obj) (k : B.obj.obj ⟶ R'.obj.obj),
        IsPullback p q f0 t' ∧ IsPullback j k (s ≫ f0) t' ∧
        ∃ (sA tA : B.obj.obj ⟶ A.obj.obj) (eA : A.obj.obj ⟶ B.obj.obj)
          (iA : B.obj.obj ⟶ B.obj.obj) (cA : Limits.pullback sA tA ⟶ B.obj.obj)
          (d : B.obj.obj ⟶ Limits.pullback s' t')
          (m : Limits.pullback sA tA ⟶ Limits.pullback s t),
          d ≫ Limits.pullback.fst s' t' = j ≫ f1 ∧
          d ≫ Limits.pullback.snd s' t' = k ∧
          sA ≫ p = j ≫ s ∧ sA ≫ q = k ∧
          tA ≫ p = j ≫ t ∧ tA ≫ q = d ≫ c' ∧
          eA ≫ j = p ≫ e ∧ eA ≫ k = q ∧
          iA ≫ j = j ≫ i ∧ iA ≫ k = d ≫ c' ∧
          m ≫ Limits.pullback.fst s t = Limits.pullback.fst sA tA ≫ j ∧
          m ≫ Limits.pullback.snd s t = Limits.pullback.snd sA tA ≫ j ∧
          cA ≫ j = m ≫ c ∧ cA ≫ k = Limits.pullback.snd sA tA ≫ k ∧
          IsPresheafGroupoid sA tA eA iA cA ∧
          sA ≫ q ≫ s' = tA ≫ q ≫ s' ∧
          ∃ b : BasedFunctor (discreteModuli A.obj.obj) (moduliTwoFiberProduct a' f),
            ∃ hB : SpaceGroupoidQuotientPresentation sA tA eA iA cA
              (moduliTwoFiberProduct a' f) b,
            b.toFunctor ⋙ quotientCartesianComma a' f ⋙ Comma.fst a'.toFunctor f.toFunctor =
              (discreteModuliMap (q ≫ s')).toFunctor ∧
            b.toFunctor ⋙ quotientCartesianComma a' f ⋙ Comma.snd a'.toFunctor f.toFunctor =
              (discreteModuliMap p).toFunctor ⋙ a.toFunctor ∧
            (∀ (T : Over S) (r : yoneda.obj T ⟶ B.obj.obj),
              ∃ (hl : (b.obj (CostructuredArrow.mk (r ≫ sA))).obj.right =
                    a.obj (CostructuredArrow.mk ((r ≫ j) ≫ s)))
                (hr : (b.obj (CostructuredArrow.mk (r ≫ tA))).obj.right =
                    a.obj (CostructuredArrow.mk ((r ≫ j) ≫ t))),
                ((quotientCartesianComma a' f).map
                    (hB.arrows.val.hom.app (CostructuredArrow.mk r))).right =
                  eqToHom hl ≫ spaceGroupoidPresentationArrow s t a hX.arrows
                    ((r ≫ j) ≫ s) ((r ≫ j) ≫ t) ⟨r ≫ j, rfl, rfl⟩ ≫
                    eqToHom hr.symm) ∧
            ∀ (T : Over S) (x : yoneda.obj T ⟶ A.obj.obj),
              ∃ (hl : (b.obj (CostructuredArrow.mk x)).obj.left =
                    CostructuredArrow.mk (x ≫ q ≫ s'))
                (hr : (b.obj (CostructuredArrow.mk x)).obj.right =
                    a.obj (CostructuredArrow.mk (x ≫ p)))
                (r' : {r' : yoneda.obj T ⟶ R'.obj.obj //
                  r' ≫ s' = x ≫ q ≫ s' ∧ r' ≫ t' = (x ≫ p) ≫ f0}),
                r'.val = x ≫ q ∧
                (b.obj (CostructuredArrow.mk x)).obj.hom =
                  eqToHom (congrArg a'.obj hl) ≫
                    spaceGroupoidPresentationArrow s' t' a' hX'.arrows
                      (x ≫ q ≫ s') ((x ≫ p) ≫ f0) r' ≫
                    α.val.inv.app (CostructuredArrow.mk (x ≫ p)) ≫
                    f.map (eqToHom hr.symm) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
