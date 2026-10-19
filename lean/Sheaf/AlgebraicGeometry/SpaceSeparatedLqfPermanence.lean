/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q01
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
import WeilConjectures.AlgebraicGeometry.SeparatedLqfBaseChange
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.OpenImmersion
import Sheaf.AlgebraicGeometry.AlgebraicSpace
import Sheaf.AlgebraicGeometry.IsLocallyQuasiFiniteEtaleSource

/-!
# Base change and open restriction of separated locally quasi-finite algebraic spaces

Source: Stacks Project, Morphisms of Spaces, Tags 03KL, 03KQ, 03XJ, 03XK and 03XL
(blueprint: lem-a1-space-separated-lqf-permanence).

Schemes over `S` are objects of `Over S`. Their representable fppf sheaves are the
subcanonical Yoneda sheaves. Chartwise local quasi-finiteness is expanded using the
Stacks scheme predicate, including its local finite-type requirement.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- Base change and every open subspace preserve separatedness and chartwise local
quasi-finiteness. The first three conjuncts concern `X_B`; the last concerns every open
`O`, including its scheme-representable case. Separatedness is tested by representing
every scheme pullback of the actual relative diagonal by a closed immersion.
Source: Stacks Project, Morphisms of Spaces, Tags 03KL, 03KQ, 03XJ, 03XK and 03XL
(blueprint: lem-a1-space-separated-lqf-permanence).

Proof:
1. Choose a representable surjective etale atlas `U → X` from def-trf-algebraic-space.
   The sheaf fibre product `X_B` is an algebraic space by
   lem-trf-space-fibre-products-etale-covers. The scheme `U_B = U ×_T B` is its
   surjective etale atlas: on scheme tests its pullback is the pullback of `U → X`.
   Its map to `B` is locally quasi-finite by lem-weil-pbc-separated-lqf-base-change(2).
2. For any representable etale chart `V → X_B`, put `W = V ×_(X_B) U_B`.
   Its maps to `V` and `U_B` are respectively surjective etale and etale scheme maps.
   Apply lem-a1-scheme-lqf-etale-source-locality first forward along `W → U_B`, then
   backward along `W → V`. This proves the chartwise assertion for `X_B → B`.
3. For an open inclusion `j : O → X_B`, every scheme test is an open immersion,
   hence etale by lem-weil-pbc-etale-composition-cancellation(1). A chart of `O`
   therefore composes to a representable etale chart of `X_B`, by testing on schemes
   and applying that lemma's composition clause (2). Apply step 2 to this composite.
4. The inclusion `j` is monic: two sections with equal image give two sections over
   the identity of the scheme open immersion obtained by testing `j`. They agree by
   lem-weil-pbc-open-immersion-monomorphism. The identity of `X_B` is monic as well.
5. For `Y = X_B` or `O`, a scheme test `D → Y ×_B Y` gives sections `y₁,y₂` with
   common image `β` in `B`. Their images `x₁,x₂` in `X` have the same image in `T`.
   After every further scheme test over `D`, equality of `x₁,x₂` is equivalent to
   equality of `(x₁,β),(x₂,β)` in `X_B`, and then to equality of `y₁,y₂` by step 4.
   Thus `D ×_(Y ×_B Y) Y` is naturally `D ×_(X ×_T X) X`, a scheme closed-immersed
   in `D` by the hypothesis. This proves both relative diagonal assertions, using
   def-pc-fibre-product, def-trf-algebraic-space and def-weil-closed-immersion.
6. If `O` is represented by `Z`, use its identity chart in step 3 to get local
   quasi-finiteness of `Z → B`. This chart is etale by def-weil-etale-morphism.
   Test step 5 on the scheme `Z ×_B Z` by the identity to obtain that the scheme
   diagonal is closed, precisely IsSeparated in def-weil-proper-morphism. -/
theorem space_separated_lqf_permanence {S : Scheme.{u}} (T B : Over S)
    (b : B ⟶ T) (X : AlgebraicSpace S)
    (f : X.obj ⟶ (Scheme.fppfTopology.over S).yoneda.obj T)
    (hqf : ∀ (V : Over S) (a : yoneda.obj V ⟶ X.obj.obj), IsEtale a →
      Scheme.Hom.IsLocallyQuasiFinite (yoneda.preimage (a ≫ f.hom)).left)
    (hsep : IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left)
      (pullback.diagonal f.hom)) :
    IsAlgebraicSpace (Limits.pullback f ((Scheme.fppfTopology.over S).yoneda.map b)) ∧
    (∀ (V : Over S)
      (a : yoneda.obj V ⟶ (Limits.pullback f ((Scheme.fppfTopology.over S).yoneda.map b)).obj),
      IsEtale a → Scheme.Hom.IsLocallyQuasiFinite
        (yoneda.preimage
          (a ≫ (pullback.snd f ((Scheme.fppfTopology.over S).yoneda.map b)).hom)).left) ∧
    IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left)
      (pullback.diagonal
        (pullback.snd f ((Scheme.fppfTopology.over S).yoneda.map b)).hom) ∧
    ∀ (O : AlgebraicSpace S)
      (j : O.obj ⟶ Limits.pullback f ((Scheme.fppfTopology.over S).yoneda.map b)),
      IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left) j.hom →
      (∀ (V : Over S) (a : yoneda.obj V ⟶ O.obj.obj), IsEtale a →
        Scheme.Hom.IsLocallyQuasiFinite
          (yoneda.preimage
            (a ≫ j.hom ≫
              (pullback.snd f ((Scheme.fppfTopology.over S).yoneda.map b)).hom)).left) ∧
      IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left)
        (pullback.diagonal
          (j.hom ≫ (pullback.snd f ((Scheme.fppfTopology.over S).yoneda.map b)).hom)) ∧
      ∀ (Z : Over S) (e : yoneda.obj Z ≅ O.obj.obj),
        IsSeparated
          (yoneda.preimage
            (e.hom ≫ j.hom ≫
              (pullback.snd f ((Scheme.fppfTopology.over S).yoneda.map b)).hom)).left ∧
        Scheme.Hom.IsLocallyQuasiFinite
          (yoneda.preimage
            (e.hom ≫ j.hom ≫
              (pullback.snd f ((Scheme.fppfTopology.over S).yoneda.map b)).hom)).left := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
