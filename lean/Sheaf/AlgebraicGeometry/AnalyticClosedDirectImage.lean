/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NJ
-/
module

public import Sheaf.AlgebraicGeometry.SmoothAnalytificationCotangent
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Sheaf.AlgebraicGeometry.AnalyticClosedIdealLocalQuotient
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.StalkTensor
import WeilConjectures.Topology.InverseImageStalk
import WeilConjectures.AlgebraicGeometry.ClosedPushforwardStalks
import WeilConjectures.Topology.ClosedPushforwardAbelianStalks

/-! # Analytification commutes with closed direct image

Source: Serre, GAGA, no. 10, Proposition 11, printed p. 18, using no. 6,
Proposition 4 (blueprint: lem-sfb-analytic-closed-direct-image).
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u
open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry.SmoothAnalytic

/-- Closed direct image commutes with module analytification. The induced analytic map
is specified on complex points and on holomorphic functions. The equality `hpre` identifies
its iterated inverse-image opens, so also identifies the two composite direct images.
The first formula specifies the comparison on every local tensor: multiply the restricted
`1 ⊗ s` by `h`, and pull back `h` along the analytic closed embedding. The second formula
is the compatibility of the canonical units `s ↦ 1 ⊗ s` after applying `π_Y,*`.

Source: Serre, GAGA, no. 10, Proposition 11, printed p. 18; no. 9, Definition 2,
and no. 11 for the canonical unit (blueprint: lem-sfb-analytic-closed-direct-image).

Proof plan, following the node's five steps:
1. On inverse-image representatives send h tensor s to the restriction of h tensor s.
   The square of the point maps commutes because both paths take a complex point to
   its algebraic support. Pullback of holomorphic functions gives j. Its evaluation
   formula makes it canonical. Refinement restricts both entries, and multiplication
   by an algebraic function agrees on both sides. The inverse-image colimit and the
   tensor sheafification therefore produce a balanced, analytic-linear sheaf map.
   Use def-weil-pbc-topological-inverse-image, def-pc-topological-inverse-image-module,
   def-pur-sheaf-tensor-product and def-weil-pbc-sheafification. The embedding property
   follows from lem-sfb-smooth-analytification-cotangent.
2. Apply lem-pc-ringed-space-module-stalk-tensor over the inverse-image ring and
   lem-weil-pbc-topological-inverse-image-stalk. At y = j(x), put A = O_Y,π_Y(y),
   R = O_X,π_X(x), B = O_Yan,y, D = O_Xan,x and M = F_π_X(x). The two closed
   pushforward stalk lemmas identify the comparison with B tensor_A M mapping to
   D tensor_R M, b tensor m mapping to its restricted coefficient tensor m.
3. The algebraic closed immersion gives R = A/I. By
   lem-sfb-analytic-closed-ideal-local-quotient, D = B/IB through actual restriction.
   The inverse sends [b] tensor m to b tensor m. A change of lift contributes a sum
   b'a tensor m = b' tensor am = 0 for a in I. Lifting scalars to A proves balancing
   over A/I. Both composites fix pure tensors, proving invertibility on the image.
4. Off the analytic image the algebraic support is also off the algebraic image:
   otherwise the complex point factors through the closed subscheme. The algebraic
   closed-pushforward stalk vanishes, hence so does its analytic tensor extension.
   The topological closed-pushforward stalk also vanishes. Thus the map is invertible
   there as well (lem-weil-pbc-closed-pushforward-stalks,
   lem-sc-closed-pushforward-abelian-stalks and the tensor/inverse-image stalk lemmas).
5. Use lem-weil-pbc-sets-sheaf-iso-on-stalks on the underlying sheaves. The inverse is
   linear by cancellation through the bijective linear comparison. On an algebraic
   open, the comparison sends 1 tensor s to 1 tensor s; this is exactly i_*a_F.
   The iterated direct images have the same sections and restrictions by `hpre`.
   Empty source, identity immersion and zero module are included. -/
theorem exists_analyticClosedDirectImage {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of (ULift.{u} ℂ))) (g : Y ⟶ Spec (.of (ULift.{u} ℂ)))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] [Smooth f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g] [Smooth g]
    (D : Data f) (E : Data g) (i : Over.mk f ⟶ Over.mk g) [IsClosedImmersion i.left] :
    ∃ (j : D.space ⟶ E.space)
      (hpre : ∀ U : Y.Opens,
        (Opens.map D.pi.hom.base).obj (i.left ⁻¹ᵁ U) =
          (Opens.map j.hom.base).obj ((Opens.map E.pi.hom.base).obj U)),
      (∀ x : D.space, j.hom.base x = mapPoints D E i x) ∧
      (∀ (W : Opens E.space) (h : E.space.presheaf.obj (op W))
        (x : (Opens.map j.hom.base).obj W),
        D.functions.eval _ (j.hom.c.app (op W) h) x =
          E.functions.eval W h ⟨j.hom.base x.val, x.property⟩) ∧
      IsClosedHolomorphicEmbedding D.atlas E.atlas j.hom.base ∧
      ∀ F : X.Modules, RingedSpace.IsCoherent X.toRingedSpace F →
        ∃ e : analytify E ((Scheme.Modules.pushforward i.left).obj F) ≅
            (SheafOfModules.pushforward (F := Opens.map j.hom.base)
              (S := moduleRings E.space) (R := moduleRings D.space)
              ⟨Functor.whiskerRight j.hom.c (forget₂ CommRingCat RingCat)⟩).obj
                (analytify D F),
          (∀ (U : Y.Opens) (W : Opens E.space)
            (hW : W ≤ (Opens.map E.pi.hom.base).obj U)
            (hX : (Opens.map j.hom.base).obj W ≤
              (Opens.map D.pi.hom.base).obj (i.left ⁻¹ᵁ U))
            (h : E.space.presheaf.obj (op W)) (s : F.val.obj (op (i.left ⁻¹ᵁ U))),
            e.hom.val.app (op W)
              (h • (analytify E ((Scheme.Modules.pushforward i.left).obj F)).val.map
                (homOfLE hW).op
                (tensorSection E ((Scheme.Modules.pushforward i.left).obj F) U 1 s)) =
              j.hom.c.app (op W) h • (analytify D F).val.map (homOfLE hX).op
                (tensorSection D F (i.left ⁻¹ᵁ U) 1 s)) ∧
          (∀ (U : Y.Opens) (s : F.val.obj (op (i.left ⁻¹ᵁ U))),
            e.hom.val.app (op ((Opens.map E.pi.hom.base).obj U))
              (tensorSection E ((Scheme.Modules.pushforward i.left).obj F) U 1 s) =
                (analytify D F).val.map (eqToHom (hpre U).symm).op
                  (tensorSection D F (i.left ⁻¹ᵁ U) 1 s)) := by
  sorry

end AlgebraicGeometry.SmoothAnalytic
