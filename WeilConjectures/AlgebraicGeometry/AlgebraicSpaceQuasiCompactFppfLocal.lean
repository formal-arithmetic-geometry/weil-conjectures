/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.SpaceQCSeparatedEtaleLocal
public import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceJointSurjectivity
public import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceAffineEtaleCover
import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceFlatLfpUniversallyOpen
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-! # Quasi-compact algebraic-space morphisms: base change and fppf descent

Source: Stacks Project, Spaces Descent, Tag 041L; Morphisms of Spaces, Tags 03HE,
03HF and 03KG; Topologies on Algebraic Spaces, Tag 0DFQ
(blueprint: lem-sfb-space-quasicompact-fppf-local).

The first conjunct identifies the existing affine-test atlas predicate with the definition
using all quasi-compact algebraic-space tests. Quasi-compactness of a space is expanded as
the existence of a surjective representable étale atlas from a quasi-compact scheme.
The other conjuncts state arbitrary base change and descent for the indicated fppf family.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- Quasi-compactness is given by quasi-compact space tests, preserved by arbitrary base
change, and local on the target for small jointly surjective flat lfp families.
`IsEtale` includes representability; `IsSurjective` tests surjectivity after scheme base
change. No separation, finite type, representability of `f`, or nonempty index is assumed.
Source: Stacks, Morphisms of Spaces, Tags 03HE, 03HF and 03KG; Spaces Descent, Tag 041L;
Topologies on Algebraic Spaces, Tag 0DFQ
(blueprint: lem-sfb-space-quasicompact-fppf-local).

Proof: Normalize the existing affine-test convention by Tag 03KG. Tests by all
quasi-compact spaces imply affine tests, since an affine scheme is quasi-compact and its
identity is a surjective étale atlas. Conversely first cover a quasi-compact test scheme
by finitely many affine opens and combine the quasi-compact atlases given by affine tests.
For a quasi-compact space test choose its quasi-compact scheme atlas, apply that scheme
criterion, and compose the resulting atlas with its surjective étale base change. This
is a quasi-compact scheme atlas of the desired fibre product. The empty test uses the
empty scheme and the empty finite covering.

1. For any base change `Y' → Y` and quasi-compact test `Z → Y'`, transitivity of
   fibre products identifies `(X ×_Y Y') ×_Y' Z` with `X ×_Y Z`. Transport its atlas.
   This uses [lem-trf-space-fibre-products-etale-covers] and proves the forward
   implication of descent as well.
2. Conversely fix a quasi-compact space `Z → Y`. Set `P = X ×_Y Z` and
   `P_i = Y_i ×_Y Z`. By [lem-a1-space-finite-affine-subatlas], the atlas of `Z`
   makes its point space quasi-compact. Joint surjectivity and
   [lem-a1-space-point-open-calculus] show the point images of the `P_i` cover `Z`.
   Choose a disjoint-affine étale atlas of each `P_i` by
   [lem-a1-space-affine-etale-cover]. Its component images are open and cover `P_i`.
3. By [lem-sfb-flat-lfp-space-universally-open], each `P_i → Z` is open, so all
   these affine-chart images are open in `Z`. Compactness selects finitely many,
   `V_r → Z`, each still factoring through its original cover member `Y_i`.
   No quasi-compactness of the covering maps is needed. For empty `Z` select none.
4. Each `V_r` is a quasi-compact scheme by [lem-weil-pbc-affine-scheme-qcqs].
   Local quasi-compactness gives a quasi-compact atlas of `X ×_Y V_r`, identified
   with the corresponding base change of `X ×_Y Y_i`. Thus its point space is
   quasi-compact by [lem-a1-space-finite-affine-subatlas].
5. By [lem-a1-space-point-open-calculus], the finitely many continuous maps
   `|X ×_Y V_r| → |P|` have images covering `|P|`: their images are inverse images
   of the chart images in `|Z|`. Pull an open cover back to each quasi-compact source
   and combine its finite subcovers. Thus `|P|` is quasi-compact, including the empty
   finite family. By [lem-sfb-qc-space-affine-etale-atlas], `P` has an affine étale
   surjective atlas, which is quasi-compact by [lem-weil-pbc-affine-scheme-qcqs].
   Since `Z → Y` was arbitrary, `f` is quasi-compact. -/
theorem quasiCompact_baseChange_and_fppfLocal
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    (IsQuasiCompactPresheafMap f.hom.hom ↔
      ∀ (Z : AlgebraicSpace S),
        (∃ (U : Over S) (a : yoneda.obj U ⟶ Z.obj.obj),
          CompactSpace U.left ∧ IsEtale a ∧ IsSurjective a) →
        ∀ g : Z ⟶ Y,
          ∃ (V : Over S) (b : yoneda.obj V ⟶ Limits.pullback f.hom.hom g.hom.hom),
            CompactSpace V.left ∧ IsEtale b ∧ IsSurjective b) ∧
    (IsQuasiCompactPresheafMap f.hom.hom →
      ∀ (Y' : AlgebraicSpace S) (g : Y' ⟶ Y),
        IsQuasiCompactPresheafMap (Limits.pullback.snd f.hom.hom g.hom.hom)) ∧
    (∀ (I : Type w) (Yᵢ : I → AlgebraicSpace S) (g : ∀ i : I, Yᵢ i ⟶ Y),
      (∀ i : I, MapIsFlat (g i)) →
      (∀ i : I, MapIsLocallyOfFinitePresentation (g i)) →
      IsJointlySurjective (fun i : I ↦ (g i).hom.hom) →
      (IsQuasiCompactPresheafMap f.hom.hom ↔
        ∀ i : I, IsQuasiCompactPresheafMap (Limits.pullback.snd f.hom.hom (g i).hom.hom))) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
