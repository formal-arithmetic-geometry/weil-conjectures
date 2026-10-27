/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q95
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite

/-!
# Weil restriction along finite locally free scheme morphisms

Source: Stacks Project, Criteria for Representability, Tag 05YF
(proposition-restriction-of-scalars-algebraic-space), specialized to scheme bases
(blueprint: lem-sfb-finite-locally-free-weil-restriction).

The equivalences describe the fibres of the structure map on scheme-valued points.
Their compatibility with restriction is stated explicitly using the canonical pullback map.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- Weil restriction of an arbitrary algebraic space along a finite locally free scheme
morphism is an algebraic space. The map `r` is its structure map to `T`; the equivalences
identify its points over `a : U ⟶ T` with maps `Z ×[T] U ⟶ E` over `Z`. The final equality
is naturality under precomposition by the canonical base-change map.
Source: Stacks Project, Criteria for Representability, Tags 05YF and 05YE
(blueprint: lem-sfb-finite-locally-free-weil-restriction).
Proof: (1) Regard `Z` and `T` as their actual representable algebraic spaces, using
[def-trf-scheme-algebraic-space]. Apply
[lem-sfb-finite-locally-free-relative-hom-space] to `E → T` and `Z → T`, obtaining
algebraic spaces `A = Hom_T(Z,E)` and `B = Hom_T(Z,Z)`.
(2) Postcomposition with `q` gives `A → B`; the canonical projection gives `T → B`.
Both maps preserve the structural map to `T`, and commute with restriction.
(3) Form `A ×[B] T` using [lem-trf-space-fibre-products-etale-covers]. Its points over
`a : U → T` are precisely maps `b : Z ×[T] U → E` with `b ≫ q = pr_Z`.
The inverse sends such a `b` to the matching pair `((a,b),a)`. These assignments commute
with base change because the projection and postcomposition with `q` do so.
Neither the construction nor this verification imposes any property on `q`, or requires
positive or constant rank for `p`. -/
theorem exists_finiteLocallyFree_weilRestriction {S : Scheme.{u}}
    (Z T : Over S) (p : Z ⟶ T) [Scheme.Hom.IsFiniteLocallyFree p.left]
    (E : AlgebraicSpace S) (q : E.obj.obj ⟶ yoneda.obj Z) :
    ∃ (R : AlgebraicSpace S) (r : R.obj.obj ⟶ yoneda.obj T)
      (e : ∀ (U : Over S) (a : U ⟶ T),
        {x : R.obj.obj.obj (op U) // r.app (op U) x = a} ≃
          {b : yoneda.obj (Limits.pullback p a) ⟶ E.obj.obj //
            b ≫ q = yoneda.map (pullback.fst p a)}),
      ∀ (U V : Over S) (v : V ⟶ U) (a : U ⟶ T)
        (x : {x : R.obj.obj.obj (op U) // r.app (op U) x = a})
        (y : {y : R.obj.obj.obj (op V) // r.app (op V) y = v ≫ a}),
        R.obj.obj.map v.op x.val = y.val →
          (e V (v ≫ a) y).val =
            yoneda.map (pullback.map p (v ≫ a) p a (𝟙 Z) v (𝟙 T)
              (by simp) (by simp)) ≫ (e U a x).val := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
