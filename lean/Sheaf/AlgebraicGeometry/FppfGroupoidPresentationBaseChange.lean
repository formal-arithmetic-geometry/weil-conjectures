module

public import Sheaf.AlgebraicGeometry.SchemeGroupoidQuotientPresentation
public import Sheaf.AlgebraicGeometry.SpaceGroupoidQuotientPresentation
public import Sheaf.AlgebraicGeometry.OpenModuliSubstack
public import Sheaf.AlgebraicGeometry.AlgebraicModuliStack
public import Sheaf.CategoryTheory.GroupoidStackificationLocalDescription
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree

import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite

/-! # Invariant base change of a finite locally free scheme-groupoid quotient

Source: Stacks Project, groupoids-quotients.tex, Tag 0DTG
(blueprint: lem-sfb-fppf-groupoid-presentation-calculus).

We characterize the base-changed quotient by a quotient presentation on the actual
2-fibre product. This avoids choosing a stackification object. The algebraic spaces
`U'` and `R'` are specified by their presheaf pullback squares, so they need not be
schemes. Every operation is specified by its two coordinates, including composition.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open AlgebraicGeometry CategoryTheory.Limits

namespace CategoryTheory

/-- Quotient formation commutes with every invariant algebraic-space base change.
The existential map `f` is the extension of the invariant map to the quotient.
For every pair of algebraic spaces realizing the two pullbacks, the conclusion gives
exactly the base-changed groupoid operations and a quotient presentation of the
2-fibre product. Compatibility with its first projection identifies the quotient map
with the original atlas on the first coordinate. The objectwise equality in the
last clause specifies its second coordinate using the existing second projection.

Source: Stacks Project, groupoids-quotients.tex, Tag 0DTG
(blueprint: lem-sfb-fppf-groupoid-presentation-calculus).

Proof: regard the schemes U and R as their actual representable fppf sheaves, using
`def-trf-scheme-algebraic-space`. The scheme-groupoid laws give the same groupoid
on all test schemes. Invariance is precisely the equality of the two composites to B.
Apply `lem-sfb-quotient-stack-invariant-base-change` over Spec k. On test schemes,
objects of the two pullbacks are (u,b') and (r,b'); all operations retain b'. Thus
source, target, identity, inverse and composition have the coordinate formulas below.
The cited theorem identifies the quotient of this groupoid with the 2-fibre product,
with its original arrow identification and fppf local lifts of objects. In the
presentation interface this gives the asserted quotient presentation and compatibility
with the original atlas. The map to B is induced by invariance, and agrees with a on
that atlas. The same descent description gives the specified B' coordinate. No new
flatness argument is required: the cited base-change theorem has no flatness or
finiteness hypotheses, so in particular applies to the finite locally free s and t. -/
theorem fppf_groupoid_presentation_baseChange
    (k : Type u) [Field k] {U R : Over (Spec (.of k))}
    (s t : R ⟶ U) (e : U.left ⟶ R.left) (i : R.left ⟶ R.left)
    (c : pullback s.left t.left ⟶ R.left)
    [s.left.IsFiniteLocallyFree] [t.left.IsFiniteLocallyFree]
    (F : BasedCategory.{v, w} (Over (Spec (.of k))))
    (aF : BasedFunctor (discreteModuli (yoneda.obj U)) F)
    (hF : SchemeGroupoidQuotientPresentation s t e i c F aF)
    (B : AlgebraicSpace (Spec (.of k))) (a : yoneda.obj U ⟶ B.obj.obj)
    (ha : yoneda.map s ≫ a = yoneda.map t ≫ a) :
    ∃ f : BasedFunctor F (discreteModuli B.obj.obj),
      Nonempty (ModuliTwoIso (aF.comp f) (discreteModuliMap a)) ∧
      ∀ (B' U' R' : AlgebraicSpace (Spec (.of k)))
        (g : B'.obj.obj ⟶ B.obj.obj)
        (p : U'.obj.obj ⟶ yoneda.obj U) (b : U'.obj.obj ⟶ B'.obj.obj)
        (q : R'.obj.obj ⟶ yoneda.obj R) (d : R'.obj.obj ⟶ B'.obj.obj),
        IsPullback p b a g → IsPullback q d (yoneda.map s ≫ a) g →
        ∃ (s' t' : R'.obj.obj ⟶ U'.obj.obj)
          (e' : U'.obj.obj ⟶ R'.obj.obj) (i' : R'.obj.obj ⟶ R'.obj.obj)
          (c' : pullback s' t' ⟶ R'.obj.obj)
          (a' : BasedFunctor (discreteModuli U'.obj.obj)
            (moduliTwoFiberProduct f (discreteModuliMap g))),
          s' ≫ p = q ≫ yoneda.map s ∧ t' ≫ p = q ≫ yoneda.map t ∧
          s' ≫ b = d ∧ t' ≫ b = d ∧ e' ≫ d = b ∧ i' ≫ d = d ∧
          c' ≫ d = pullback.fst s' t' ≫ d ∧
          (∀ (T : Over (Spec (.of k))) (x : yoneda.obj T ⟶ U'.obj.obj),
            (yoneda.preimage (x ≫ e' ≫ q)).left =
              (yoneda.preimage (x ≫ p)).left ≫ e) ∧
          (∀ (T : Over (Spec (.of k))) (r : yoneda.obj T ⟶ R'.obj.obj),
            (yoneda.preimage (r ≫ i' ≫ q)).left =
              (yoneda.preimage (r ≫ q)).left ≫ i) ∧
          (∀ (T : Over (Spec (.of k))) (z : yoneda.obj T ⟶ pullback s' t')
            (z₀ : T.left ⟶ pullback s.left t.left),
            z₀ ≫ pullback.fst s.left t.left =
              (yoneda.preimage (z ≫ pullback.fst s' t' ≫ q)).left →
            z₀ ≫ pullback.snd s.left t.left =
              (yoneda.preimage (z ≫ pullback.snd s' t' ≫ q)).left →
            (yoneda.preimage (z ≫ c' ≫ q)).left = z₀ ≫ c) ∧
          ∃ (h' : SpaceGroupoidQuotientPresentation s' t' e' i' c'
              (moduliTwoFiberProduct f (discreteModuliMap g)) a')
            (ε : ModuliTwoIso
              (a'.comp (moduliTwoFiberFst f (discreteModuliMap g)))
              ((discreteModuliMap p).comp aF)),
            (∀ (T : Over (Spec (.of k))) (x y : yoneda.obj T ⟶ U'.obj.obj)
              (r' : {r : yoneda.obj T ⟶ R'.obj.obj // r ≫ s' = x ∧ r ≫ t' = y})
              (r₀ : {r : yoneda.obj T ⟶ yoneda.obj R //
                r ≫ yoneda.map s = x ≫ p ∧ r ≫ yoneda.map t = y ≫ p}),
              r'.val ≫ q = r₀.val →
              (moduliTwoFiberFst f (discreteModuliMap g)).map
                  (spaceGroupoidPresentationArrow s' t' a' h'.arrows x y r') ≫
                ε.val.hom.app (CostructuredArrow.mk y) =
              ε.val.hom.app (CostructuredArrow.mk x) ≫
                schemeGroupoidPresentationArrow s t aF hF.arrows (x ≫ p) (y ≫ p) r₀) ∧
            Nonempty (ModuliTwoIso
              (a'.comp (moduliTwoFiberSnd f (discreteModuliMap g)))
              (discreteModuliMap b)) := by
  sorry

end CategoryTheory
