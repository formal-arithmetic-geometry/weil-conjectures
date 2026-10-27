/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q85
-/
module

public import Sheaf.AlgebraicGeometry.ZariskiTorsorGroupoid
public import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids
public import Mathlib.GroupTheory.GroupAction.Defs
import Sheaf.CategoryTheory.SiteCoveringAxioms
import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite

/-! # Coarse descent through a Zariski torsor presentation

Source: Stacks Project, examples-stacks.tex, Tag 04UV; groupoids-quotients.tex,
Tags 048F and 048J, with the explicit Zariski descent argument
(blueprint: lem-sfb-zariski-torsor-categorical-coarse-descent).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.SchemeAction

/-- A categorical geometric quotient descends to the presented fibred groupoid.
Source: Stacks 04UV, 048F, 048J
(blueprint: lem-sfb-zariski-torsor-categorical-coarse-descent).
Proof:
1. Regard an algebraic space as its fppf sheaf. Zariski covers are fppf covers
   (lem-pc-zariski-coverings-are-fppf); the sheaf equalizer glues sections uniquely,
   including on an empty base. Yoneda (lem-pc-yoneda) identifies sections with maps.
2. On overlapping torsor charts, identity sections differ by a unique regular
   group element. Equivariance and invariance make their images in the target agree.
   The same calculation on a common refinement compares different choices of charts.
3. Glue these images. Their pullback to the torsor is the invariant map, by its
   invariance on each product chart. Conversely the identity sections force every
   possible descended element to have these local values, proving uniqueness.
4. Pulling charts back along a base arrow shows the descended sections commute
   with pullback. Thus they define a based functor, including on automorphisms.
5. Restrict a based functor to trivial torsors. Yoneda gives a map out of J.
   On G times J, right translation by the inverse group coordinate identifies
   the two trivial pairs; hence this map is invariant as a scheme-test map.
6. The identity section recovers the original invariant map. Local sections identify
   any torsor pair with a trivial pair, so unique gluing recovers the original
   functor. Precomposition by the cartesian equivalence e is a bijection too:
   a quasi-inverse gives an inverse, and vertical isomorphisms become identities
   in the discrete target. This proves the stated characterization of restriction.
7. Apply this construction to q. Uniqueness gives pi and its pullback formula.
   Restriction of b pi is b q. The assumed categorical property of q therefore
   gives the algebraic-space universal property of pi.
8. Over Spec of an algebraically closed field, a Zariski trivial torsor has a
   section since the base has one point. Its pair is a trivial pair P_x. Changing
   section changes x by the group action. Isomorphisms P_x to P_y are precisely
   right translations with x = a y. Thus the fibre skeleton is the orbit set,
   with the specified normalization on P_x. The equivalence e preserves and reflects
   these classes. The pullback formula sends this class to q(x), giving exactly
   the assumed orbit bijection and the recorded IsCoarseModuliScheme definition. -/
theorem zariski_torsor_categorical_coarse_descent
    (k : Type u) [Field k]
    (G J Q : Over (Spec (.of k))) [GrpObj G] [ModObj G J]
    (F : BasedCategory.{v, w} (Over (Spec (.of k)))) (hF : IsFibredInGroupoids F)
    (e : BasedFunctor F (zariskiTorsorGroupoid G J)) (he : e.toFunctor.IsEquivalence)
    (q : J ⟶ Q)
    (hq : ModObj.smul (M := G) (X := J) ≫ q = snd G J ≫ q)
    (hcat : ∀ (B : AlgebraicSpace (Spec (.of k)))
      (f : yoneda.obj J ⟶ B.obj.obj),
      yoneda.map (ModObj.smul (M := G) (X := J)) ≫ f = yoneda.map (snd G J) ≫ f →
        ∃! b : yoneda.obj Q ⟶ B.obj.obj, yoneda.map q ≫ b = f)
    (hgeom : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (a : Spec (.of Ω) ⟶ Spec (.of k)),
      Function.Surjective (fun x : Over.mk a ⟶ J ↦ x ≫ q) ∧
        ∀ x y : Over.mk a ⟶ J,
          (x ≫ q = y ≫ q ↔ ∃ g : Over.mk a ⟶ G, g • x = y)) :
    ∃ π : BasedFunctor F (discreteModuli (yoneda.obj Q)),
      (∀ X : F.obj,
        yoneda.map ((e.obj X).obj.projection ≫
          eqToHom ((e.w_obj X).trans (π.w_obj X).symm)) ≫ (π.obj X).hom =
          yoneda.map ((e.obj X).obj.map ≫ q)) ∧
      (∀ π' : BasedFunctor F (discreteModuli (yoneda.obj Q)),
        (∀ X : F.obj,
          yoneda.map ((e.obj X).obj.projection ≫
            eqToHom ((e.w_obj X).trans (π'.w_obj X).symm)) ≫ (π'.obj X).hom =
              yoneda.map ((e.obj X).obj.map ≫ q)) → π' = π) ∧
      (∀ B : AlgebraicSpace (Spec (.of k)),
        ∃ R : BasedFunctor F (discreteModuli B.obj.obj) ≃
          {f : yoneda.obj J ⟶ B.obj.obj //
            yoneda.map (ModObj.smul (M := G) (X := J)) ≫ f =
              yoneda.map (snd G J) ≫ f},
          (∀ (A : BasedFunctor F (discreteModuli B.obj.obj))
            (f : yoneda.obj J ⟶ B.obj.obj),
            (R A).val = f ↔
              ∃ AP : BasedFunctor (zariskiTorsorGroupoid G J) (discreteModuli B.obj.obj),
                e.comp AP = A ∧
                  (zariskiQuotientAtlas G J).comp AP = discreteModuliMap f) ∧
          ∀ b : yoneda.obj Q ⟶ B.obj.obj,
            (R (π.comp (discreteModuliMap b))).val = yoneda.map q ≫ b) ∧
      (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
        (a : Spec (.of Ω) ⟶ Spec (.of k)),
        Function.Bijective ((moduliFiberMap e (Over.mk a)).mapSkeleton.obj) ∧
          ∃ c : Skeleton (Functor.Fiber (zariskiTorsorGroupoid G J).p (Over.mk a)) ≃
            MulAction.orbitRel.Quotient (Over.mk a ⟶ G) (Over.mk a ⟶ J),
            (∀ x : Over.mk a ⟶ J,
              c (toSkeleton (zariskiTrivialFiber G J (Over.mk a) x)) =
                Quotient.mk (MulAction.orbitRel (Over.mk a ⟶ G) (Over.mk a ⟶ J)) x) ∧
            ∀ (X : Functor.Fiber F.p (Over.mk a)) (x : Over.mk a ⟶ J),
              c ((moduliFiberMap e (Over.mk a)).mapSkeleton.obj (toSkeleton X)) =
                Quotient.mk (MulAction.orbitRel (Over.mk a ⟶ G) (Over.mk a ⟶ J)) x →
              (moduliFiberMap π (Over.mk a)).mapSkeleton.obj (toSkeleton X) =
                toSkeleton (Functor.Fiber.mk (p := (discreteModuli (yoneda.obj Q)).p)
                  (a := CostructuredArrow.mk (yoneda.map (x ≫ q))) rfl)) ∧
      IsCoarseModuliScheme F Q π := by
  sorry

end AlgebraicGeometry.SchemeAction
