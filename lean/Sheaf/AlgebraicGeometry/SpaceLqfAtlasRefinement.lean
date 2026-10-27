/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q105
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Yoneda
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
import Sheaf.AlgebraicGeometry.IsLocallyQuasiFiniteEtaleSource

/-!
# Pulled-back atlases and common refinements for local quasi-finiteness

Source: Stacks Project, Spaces Morphisms, Tags 0ABM and 03MJ; Spaces, Tag 025V;
Descent, Tag 03X4 (blueprint: lem-a1-space-lqf-atlas-refinement).

Schemes over the base are objects of `Over S`, and `h_T` is `yoneda.obj T`.
The sheaf fibre products are expressed on their underlying presheaves; limits of
sheaves are computed on those presheaves. Projection equations specify the canonical
identifications, and an `IsPullback` square specifies the representing common refinement.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- Pullback of a surjective étale atlas, its scheme tests, and the common-refinement
criterion for local quasi-finiteness. Source: Stacks, Spaces Morphisms, Tags 0ABM and
03MJ; Spaces, Tag 025V; Descent, Tag 03X4
(blueprint: lem-a1-space-lqf-atlas-refinement).

Proof:
1. Regard `T` and `B` as algebraic spaces using `schemeSpace`
   [def-trf-scheme-algebraic-space]. Form the sheaf pullback by
   [lem-trf-space-fibre-products-etale-covers]. Yoneda full faithfulness
   [lem-galois-yoneda-fully-faithful] gives the scheme map `yoneda.preimage (a ≫ f)`.
   Form its scheme pullback with `b` [def-pc-fibre-product].
2. On sections send `(u, β)` to `(u, (a(u), β))`. The inverse forgets the redundant
   component `a(u)`. These formulas commute with restriction and both projections,
   giving the first canonical isomorphism and the induced map `aB`.
3. For any `D → X_B`, send `(d, (u, β))` to `(d, u)`; the inverse inserts the
   `B`-component of `d`. This gives the second canonical isomorphism. By the
   scheme-test definition [def-trf-algebraic-space], the latter pullback has an
   étale surjective scheme projection to `D`. Hence `aB` is representable,
   surjective and étale.
4. Test `aB` on `V` to get `W` and its surjective étale projection `p`.
   Interchanging factors tests `v` on `U_B`, so `q` is étale. The pullback equation
   makes the composites to `B` equal; Yoneda full faithfulness turns this into an
   equality of scheme maps [lem-galois-yoneda-fully-faithful].
5. If `U_B → B` is locally quasi-finite, precompose by the étale map `q` and then
   descend along the surjective étale map `p`, using both implications of
   [lem-a1-scheme-lqf-etale-source-locality]. This proves the assertions for `W`
   and `V`. No separatedness or quasi-compactness condition is used. -/
theorem space_lqf_atlas_refinement {S : Scheme.{u}} (T B U : Over S)
    (b : B ⟶ T) (X : AlgebraicSpace S) (f : X.obj.obj ⟶ yoneda.obj T)
    (a : yoneda.obj U ⟶ X.obj.obj) (ha : IsEtale a) (hs : IsSurjective a) :
    ∃ aB : yoneda.obj (Limits.pullback (yoneda.preimage (a ≫ f)) b) ⟶
        Limits.pullback f (yoneda.map b),
      (∃ e : yoneda.obj (Limits.pullback (yoneda.preimage (a ≫ f)) b) ≅
          Limits.pullback a (Limits.pullback.fst f (yoneda.map b)),
        e.hom ≫ Limits.pullback.fst a (Limits.pullback.fst f (yoneda.map b)) =
            yoneda.map (Limits.pullback.fst (yoneda.preimage (a ≫ f)) b) ∧
          e.hom ≫ Limits.pullback.snd a (Limits.pullback.fst f (yoneda.map b)) = aB) ∧
      aB ≫ Limits.pullback.snd f (yoneda.map b) =
        yoneda.map (Limits.pullback.snd (yoneda.preimage (a ≫ f)) b) ∧
      IsEtale aB ∧ IsSurjective aB ∧
      (∀ (D : Over S) (t : yoneda.obj D ⟶ Limits.pullback f (yoneda.map b)),
        ∃ e : Limits.pullback t aB ≅
            Limits.pullback (t ≫ Limits.pullback.fst f (yoneda.map b)) a,
          e.hom ≫ Limits.pullback.fst (t ≫ Limits.pullback.fst f (yoneda.map b)) a =
              Limits.pullback.fst t aB ∧
            e.hom ≫ Limits.pullback.snd (t ≫ Limits.pullback.fst f (yoneda.map b)) a =
              Limits.pullback.snd t aB ≫
                yoneda.map (Limits.pullback.fst (yoneda.preimage (a ≫ f)) b)) ∧
      ∀ (V : Over S) (v : yoneda.obj V ⟶ Limits.pullback f (yoneda.map b)),
        IsEtale v →
        ∃ (W : Over S) (p : W ⟶ V)
          (q : W ⟶ Limits.pullback (yoneda.preimage (a ≫ f)) b),
          IsPullback (yoneda.map p) (yoneda.map q) v aB ∧
          Etale p.left ∧ Surjective p.left ∧ Etale q.left ∧
          p ≫ yoneda.preimage (v ≫ Limits.pullback.snd f (yoneda.map b)) =
            q ≫ Limits.pullback.snd (yoneda.preimage (a ≫ f)) b ∧
          (Scheme.Hom.IsLocallyQuasiFinite
              (Limits.pullback.snd (yoneda.preimage (a ≫ f)) b).left →
            Scheme.Hom.IsLocallyQuasiFinite
                (q.left ≫ (Limits.pullback.snd (yoneda.preimage (a ≫ f)) b).left) ∧
              Scheme.Hom.IsLocallyQuasiFinite
                (yoneda.preimage (v ≫ Limits.pullback.snd f (yoneda.map b))).left) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
