/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q35
-/
module

public import Sheaf.AlgebraicGeometry.SpaceGroupoidQuotientPresentation
public import Sheaf.AlgebraicGeometry.ModuliChartNormalization

/-! # The fibred groupoid associated to an algebraic-space groupoid

Source: Stacks Project, spaces-groupoids.tex, equation-quotient-stack and Tags 044Q,
044R, 044T, 04M9 (blueprint: def-sfb-space-groupoid-presheaf-presentation).

This interface describes the original presheaf groupoid up to equivalence over the
base. Every object is globally isomorphic to an original object. No descent or
stackification condition is imposed on this original category.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w v' w'

open AlgebraicGeometry CategoryTheory.Limits

namespace CategoryTheory

/-- A realization of the original presheaf groupoid as a category fibred in groupoids.
The object and arrow conditions identify every fibre with the given groupoid;
composition is the given map `c`, with the convention `c(q,r) = q` after `r`.
Naturality of the comparison retains pullback of arrows. Global essential
surjectivity allows replacement by an equivalent fibred groupoid, without adding
objects by descent.
Source: Stacks, spaces-groupoids.tex, equation-quotient-stack before Tag 044Q,
Tags 044R and 044T (blueprint: def-sfb-space-groupoid-presheaf-presentation). -/
structure SpaceGroupoidPresheafPresentation {S : Scheme.{u}} {U R : AlgebraicSpace S}
    (s t : R.obj.obj ⟶ U.obj.obj) (e : U.obj.obj ⟶ R.obj.obj) (j : R.obj.obj ⟶ R.obj.obj)
    (c : pullback s t ⟶ R.obj.obj)
    (P : BasedCategory.{v, w} (Over S))
    (a : BasedFunctor (discreteModuli U.obj.obj) P) where
  groupoid : AlgebraicSpace.IsPresheafGroupoid s t e j c
  fibred : IsFibredInGroupoids P
  arrows : ModuliTwoIso ((discreteModuliMap s).comp a) ((discreteModuliMap t).comp a)
  fully_faithful : ∀ (T : Over S) (x y : yoneda.obj T ⟶ U.obj.obj)
    (β : a.obj (CostructuredArrow.mk x) ⟶ a.obj (CostructuredArrow.mk y)),
    P.p.IsHomLift (𝟙 T) β →
      ∃! r : {r : yoneda.obj T ⟶ R.obj.obj // r ≫ s = x ∧ r ≫ t = y},
        spaceGroupoidPresentationArrow s t a arrows x y r = β
  objects : ∀ z : P.obj,
    ∃ (x : yoneda.obj (P.p.obj z) ⟶ U.obj.obj)
      (β : a.obj (CostructuredArrow.mk x) ≅ z),
        P.p.IsHomLift (𝟙 (P.p.obj z)) β.hom
  composition : ∀ (T : Over S) (x y z : yoneda.obj T ⟶ U.obj.obj)
    (r : {r : yoneda.obj T ⟶ R.obj.obj // r ≫ s = x ∧ r ≫ t = y})
    (q : {q : yoneda.obj T ⟶ R.obj.obj // q ≫ s = y ∧ q ≫ t = z})
    (d : {d : yoneda.obj T ⟶ R.obj.obj // d ≫ s = x ∧ d ≫ t = z})
    (p : yoneda.obj T ⟶ pullback s t),
    p ≫ pullback.fst s t = q.val →
    p ≫ pullback.snd s t = r.val → p ≫ c = d.val →
      spaceGroupoidPresentationArrow s t a arrows x y r ≫
        spaceGroupoidPresentationArrow s t a arrows y z q =
          spaceGroupoidPresentationArrow s t a arrows x z d

/-- The relation isomorphism after applying the specified functor `i`.
Its component at `r` is exactly `i` applied to the original arrow at `r`.
Source: Stacks, spaces-groupoids.tex, Tags 044T and 04M9
(blueprint: def-sfb-space-groupoid-presheaf-presentation). -/
def spaceGroupoidImageRelation {S : Scheme.{u}} {U R : AlgebraicSpace S}
    {s t : R.obj.obj ⟶ U.obj.obj} {P : BasedCategory.{v, w} (Over S)}
    {a : BasedFunctor (discreteModuli U.obj.obj) P}
    (η : ModuliTwoIso ((discreteModuliMap s).comp a) ((discreteModuliMap t).comp a))
    {Q : BasedCategory.{v', w'} (Over S)} (i : BasedFunctor P Q) :
    (discreteModuliMap s).comp (a.comp i) ≅ (discreteModuliMap t).comp (a.comp i) :=
  BasedNatIso.mkNatIso (Functor.isoWhiskerRight η.val i.toFunctor)
    (BasedCategory.whiskerRight (BasedNatIso.mkNatIso η.val η.property).hom i).isHomLift'

/-- The specified canonical map `r ↦ (s(r),t(r),i(r))` into the 2-fibre product.
The comparison is the image of the original arrow, not an arbitrary isomorphism.
Source: Stacks, spaces-groupoids.tex, Tag 04M9
(blueprint: def-sfb-space-groupoid-presheaf-presentation). -/
def spaceGroupoidKernelPairMap {S : Scheme.{u}} {U R : AlgebraicSpace S}
    {s t : R.obj.obj ⟶ U.obj.obj} {P : BasedCategory.{v, w} (Over S)}
    {a : BasedFunctor (discreteModuli U.obj.obj) P}
    (η : ModuliTwoIso ((discreteModuliMap s).comp a) ((discreteModuliMap t).comp a))
    {Q : BasedCategory.{v', w'} (Over S)} (i : BasedFunctor P Q) :
    BasedFunctor (discreteModuli R.obj.obj) (moduliTwoFiberProduct (a.comp i) (a.comp i)) :=
  moduliTwoFiberLift (discreteModuliMap s) (discreteModuliMap t)
    (spaceGroupoidImageRelation η i)

end CategoryTheory
