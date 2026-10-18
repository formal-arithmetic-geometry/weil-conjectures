/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P4
-/
module

public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.Limits

/-!
# Inverse image on sheaf slice categories

Source: Stacks Project, Sites, Tag 03CF, the middle diagram and the computation of
restriction via products (blueprint: lem-weil-pbc-slice-sheaf-inverse-image-equivalence).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- A continuous sheaf inverse image acts on localized sheaves by applying the
inverse image to the objects over a sheafified representable.

Source: Stacks Project, Sites, Tag 03CF, middle diagram; Tag 00Y1 and the product
calculation in the final paragraph of Tag 03CF.

Proof: Let A be the sheafification of the representable of V (with its values lifted
to the common universe). Use Tag 00Y1 to identify sheaves on the slice over V with
sheaves over A. The adjunction and Yoneda give L(A) isomorphic to the sheafification
of the representable of u(V): maps from either object to G identify naturally with
G(u(V)). Use this isomorphism to transport the analogous equivalence on C/u(V) to
an equivalence with sheaves over L(A). Under these equivalences the right adjoint
to Over.post L sends (G,q) to the pullback of R(q) along the adjunct A → R(L(A)).
The sectionwise fibre at a:T → V consists of s in G(u(T)) whose image is the
sheafification of u(a); this is exactly slice precomposition. The adjunction
bijections and uniqueness of left adjoints give the first comparison. For either
site, the inverse equivalence sends the product projection A × H → A to the sheaf
whose fibre at a is {(eta(a),s)}. Projection onto s is a bijection, commutes with
restrictions and morphisms, and gives the second and third comparisons. No finite
limit preservation of L is used in these identifications.
Proof: the theorem is the residual categorical step of Tag 03CF. The equivalences of Tag
00Y1 identify localized sheaves with sheaves over the sheafified representable. The
adjunction and Yoneda identify the image of that representable under the global inverse
image with the corresponding sheafified representable on the target. The induced right
adjoint on over-categories is computed by a pullback; its sections are the fibres described
in Tag 03CF, so the two inverse-image functors are isomorphic by uniqueness of left
adjoints. The product fibre formula in Tag 03EE gives the restriction comparison. The
finite-limit assertion follows because the global inverse image preserves finite limits,
`Over.post` preserves finite limits, and equivalences create and reflect limits.
(blueprint: stage3-slice-sheaf-inverse-image-equivalence). -/
theorem sliceSheafInverseImage_remainder
    {D : Type u} {C : Type v} [SmallCategory D] [SmallCategory C]
    (K : GrothendieckTopology D) (J : GrothendieckTopology C) (u : D ⥤ C)
    [u.IsContinuous K J]
    [(u.sheafPushforwardContinuous (Type (max u v)) K J).IsRightAdjoint]
    [PreservesFiniteLimits (u.sheafPullback (Type (max u v)) K J)]
    (V : D) [(Over.post (X := V) u).IsContinuous (K.over V) (J.over (u.obj V))]
    [((Over.post (X := V) u).sheafPushforwardContinuous (Type (max u v))
      (K.over V) (J.over (u.obj V))).IsRightAdjoint] :
    PreservesFiniteLimits ((Over.post (X := V) u).sheafPullback (Type (max u v))
      (K.over V) (J.over (u.obj V))) ∧
    Nonempty (K.overPullback (Type (max u v)) V ⋙
      (Over.post (X := V) u).sheafPullback (Type (max u v)) (K.over V) (J.over (u.obj V)) ≅
      u.sheafPullback (Type (max u v)) K J ⋙ J.overPullback (Type (max u v)) (u.obj V)) ∧
    Nonempty (u.sheafPushforwardContinuous (Type (max u v)) K J ⋙ K.overPullback
      (Type (max u v)) V ≅ J.overPullback (Type (max u v)) (u.obj V) ⋙
      (Over.post (X := V) u).sheafPushforwardContinuous (Type (max u v))
        (K.over V) (J.over (u.obj V))) := by sorry

end CategoryTheory
