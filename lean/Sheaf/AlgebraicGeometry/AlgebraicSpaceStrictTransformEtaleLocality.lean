/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q154
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceStrictTransformPresentation
import Sheaf.AlgebraicGeometry.AlgebraicSpaceStrictTransformEtaleLocalization

/-! # Etale locality of the space strict transform

Source: Stacks Project, Divisors on Spaces, Tag 0863(1)-(2), lemma-strict-transform-local,
with the strict-transform convention of Tag 0862, definition-strict-transform
(blueprint: lem-sfb-space-strict-transform-etale-locality).

Cartesian squares express the canonical comparisons with both projections retained.
The centre on the chart is the image of the canonical tensor map. Blowups and strict
transforms use the existing presentations, including their full scheme structures.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- Strict transforms of algebraic spaces commute with etale charts of the base and source.
The charts need not form a cartesian square. The first pullback square identifies the
chart blowup with the base change of the original blowup. The next identifies the two
ambient fibre products; the last identifies the strict transforms over the source.
The inclusion equation and the equation over the blowup retain the closed-subspace
identification and its compatibility with the other projection.
Source: Stacks Project, Divisors on Spaces, Tag 0863(1)-(2), with Definition 0862
(blueprint: lem-sfb-space-strict-transform-etale-locality).

Proof:
1. By lem-trf-space-fibre-products-etale-covers, the sheaf fibre products are algebraic
   spaces. The canonical comparison U times_V (V times_T T') with
   (Y times_T T') times_Y U sends a compatible triple (u,v,t') to (u,t'); its inverse
   inserts the given image of u in V. These maps are inverse on every test scheme
   and preserve the projections. The original square need only commute.
2. Apply lem-sfb-space-strict-transform-etale-localization with X=Y, A=V and W=U.
   Its extended ideal is the image of the same canonical tensor map, hence is K_V.
   It gives the chart-blowup pullback square, the etale map between the ambient
   spaces, and the strict-transform pullback square. The structure-sheaf case of
   its module comparison preserves the quotient maps and identifies their torsion
   kernels. Thus this is an identification as closed subspaces of the ambient
   fibre product, with the stated inclusion equation.
3. Compose the inclusion equation with the ambient projections. The pullback
   squares give compatibility over U and Y, and the equation involving toBlowup
   gives compatibility over T'. No quasi-compactness, separation, reducedness or
   density is used; the stronger theorem's optional surjectivity is not invoked. -/
theorem strictTransform_etale_locality
    {S : Scheme.{u}} {Y T V U : AlgebraicSpace S}
    (g : Y ⟶ T) (a : V ⟶ T) (w : U ⟶ Y) (f : U ⟶ V)
    (comm : w ≫ g = f ≫ a)
    (hV : ∃ V₀ : Over S, Nonempty (V.obj.obj ≅ yoneda.obj V₀))
    (hU : ∃ U₀ : Over S, Nonempty (U.obj.obj ≅ yoneda.obj U₀))
    (ha : IsEtale a.hom.hom) (hw : IsEtale w.hom.hom)
    (K : QuasiCoherentIdeal T) (hK : (K.val : T.Modules).IsFiniteType)
    (B : BlowupPresentation K) (P : StrictTransformPresentation g K B) :
    ∃ (KV : QuasiCoherentIdeal V)
      (k : (moduleTensorPullback a).obj (K.val : T.Modules) ⟶ (KV.val : V.Modules)),
      Epi k ∧ k ≫ KV.val.arrow = idealTensorMap a K ∧
      ∃ (BV : BlowupPresentation KV) (PU : StrictTransformPresentation f KV BV)
        (v : BV.space ⟶ B.space) (h : PU.ambient ⟶ P.ambient),
        IsPullback BV.projection.hom v.hom a.hom B.projection.hom ∧
        IsEtale h.hom.hom ∧
        IsPullback h.hom PU.toSource.hom P.toSource.hom w.hom ∧
        h ≫ P.toBlowup = PU.toBlowup ≫ v ∧
        ∃ (j : PU.space ⟶ P.space),
          j ≫ P.inclusion = PU.inclusion ≫ h ∧
          IsPullback j.hom (PU.inclusion ≫ PU.toSource).hom
            (P.inclusion ≫ P.toSource).hom w.hom := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
