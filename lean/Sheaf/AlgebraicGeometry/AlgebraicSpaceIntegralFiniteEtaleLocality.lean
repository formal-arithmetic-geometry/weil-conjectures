/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q23
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
import Sheaf.AlgebraicGeometry.FpqcFinerThanEtale
import Sheaf.AlgebraicGeometry.Morphisms.FpqcIntegralDescent
import WeilConjectures.AlgebraicGeometry.IsFiniteOfFpqcCover

/-!
# Integral and finite morphisms of algebraic spaces are étale local on the target

Source: Stacks Project, Morphisms of Spaces, Tag 03ZQ (`lemma-integral-local`),
equivalence of (1) and (3) (blueprint: lem-sfb-space-integral-finite-etale-locality).

The right side gives a scheme representing the pullback to the prescribed atlas, with
its projection. The pullback square is in presheaves, as in `IsRepresentableWith`.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- Integrality and representability can be checked on any surjective étale scheme atlas.
Source: Stacks Project, Morphisms of Spaces, Tag 03ZQ, (1) iff (3)
(blueprint: lem-sfb-space-integral-finite-etale-locality).

Proof:
1. Apply the scheme-test definition to `U` and `p` for the forward implication.
2. Conversely, the integral atlas pullback is affine by
   [def-weil-finite-integral-morphism]. The étale target criterion
   [lem-sfb-space-affine-locality] makes `f` representable and affine.
3. For any scheme `T → X`, its pullback `Z = Y ×_X T` is therefore a scheme.
   By [lem-trf-space-fibre-products-etale-covers], `V = T ×_X U` is a scheme
   surjective étale over `T`. Associativity identifies `Z ×_T V` with `W ×_U V`.
4. The latter projection is integral by [lem-sbc-integral-morphism-base-change].
5. The singleton étale covering `V → T` is fpqc by
   [lem-weil-pbc-fpqc-finer-than-etale]. Apply
   [lem-weil-pbc-fpqc-descend-integral] to conclude that `Z → T` is integral.
   This holds for every test scheme, without quasi-compactness assumptions on the atlas. -/
theorem isRepresentableWith_integral_iff_etaleAtlas {S : Scheme.{u}}
    (Y X : AlgebraicSpace S) (f : Y ⟶ X) (U : Over S)
    (p : yoneda.obj U ⟶ X.obj.obj) (he : IsEtale p) (hs : IsSurjective p) :
    IsRepresentableWith (fun _ _ r ↦ IsIntegralHom r.left) f.hom.hom ↔
      ∃ (W : Over S) (r : W ⟶ U) (q : yoneda.obj W ⟶ Y.obj.obj),
        IsPullback q (yoneda.map r) f.hom.hom p ∧ IsIntegralHom r.left := by
  sorry

/-- Finiteness and representability can be checked on any surjective étale scheme atlas.
Source: Stacks Project, Morphisms of Spaces, Tag 03ZQ, (1) iff (3)
(blueprint: lem-sfb-space-integral-finite-etale-locality).

Proof:
1. Apply the scheme-test definition to `U` and `p` for the forward implication.
2. Conversely, the finite atlas pullback is affine by
   [def-weil-finite-integral-morphism]. The étale target criterion
   [lem-sfb-space-affine-locality] makes `f` representable and affine.
3. For any scheme `T → X`, its pullback `Z = Y ×_X T` is a scheme, and
   [lem-trf-space-fibre-products-etale-covers] makes `V = T ×_X U` a scheme
   surjective étale over `T`. Associativity identifies `Z ×_T V` with `W ×_U V`.
4. The latter projection is finite by [lem-trf-finite-radicial-basechange].
5. Use [lem-weil-pbc-fpqc-finer-than-etale] on the singleton covering `V → T`,
   and then [lem-weil-pbc-fpqc-descend-finite] to descend finiteness to `Z → T`.
   Since `T` was arbitrary this is representability with finiteness. The covering
   lemma requires no quasi-compactness of the atlas, so no extra hypothesis is used. -/
theorem isRepresentableWith_finite_iff_etaleAtlas {S : Scheme.{u}}
    (Y X : AlgebraicSpace S) (f : Y ⟶ X) (U : Over S)
    (p : yoneda.obj U ⟶ X.obj.obj) (he : IsEtale p) (hs : IsSurjective p) :
    IsRepresentableWith (fun _ _ r ↦ IsFinite r.left) f.hom.hom ↔
      ∃ (W : Over S) (r : W ⟶ U) (q : yoneda.obj W ⟶ Y.obj.obj),
        IsPullback q (yoneda.map r) f.hom.hom p ∧ IsFinite r.left := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
