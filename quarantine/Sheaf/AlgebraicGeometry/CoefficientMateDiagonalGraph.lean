/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q75
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Sheaf.Topology.ProfiniteCondensedRing
public import WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Defs

/-! # Diagonal and graph evaluation of coefficient mates

Source: blueprint main-20261015, sec-proetale-coefficients,
`sk-prop-sfb-cartesian-coefficients/lem-sfb-eta-comp.proof.md`, composition identity
and final fibre-product comparison (blueprint: lem-sfb-coefficient-mate-diagonal-graph).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

/-- Coefficient-mate composition evaluated along the diagonal and the graph. The
first conjunct is the section identity in `Λ_W(W/W)`; the second identifies the
base-changed diagonal with the graph under the very comparison used by `lowerStarComp`.
Here `u` and `w` are the structural maps of the test objects `V` and `W`, and `h.w`
is the equality `h.left ≫ V.hom = W.hom`. The restriction after `η_h` on the right
implements the canonical identification `V ×_V W ≅ W`.

Source: blueprint main-20261015, sec-proetale-coefficients,
`sk-prop-sfb-cartesian-coefficients/lem-sfb-eta-comp.proof.md`, composition identity
and final paragraph (blueprint: lem-sfb-coefficient-mate-diagonal-graph).

Proof plan:
1. Put P = V ×_B V (over V by its second projection), Q = P ×_V W and
   R = V ×_B W. The inverse component of `MorphismProperty.Over.pullbackComp`
   is e : Q ≅ R, sending (v1,v2,z) to (v1,z); its inverse inserts h(z).
   The pullback of the diagonal has domain D = V ×_V W, identified with W by
   its second projection. Its composite with e is gamma after this projection,
   since both maps have projections (h(z),z). This proves the second conjunct.
2. Apply `condensedPushforwardHom_comp` (`lem-sfb-eta-comp`) to h and u,
   evaluate at V and s, and use `def-sfb-finite-lower-star-comp` to express the
   comparison as restriction along e inverse. Thus η_w(s) = Λ_W(e inverse)(t),
   where t = η_{h,P}(η_{u,V}(s)).
3. Naturality of `condensedPushforwardHom Λ h.left` (`def-sfb-eta`) at the
   diagonal says restriction of t along its base change is η_{h,V} applied to
   diagonal restriction of η_{u,V}(s). Pushforward is restriction along base
   change (`def-sfb-finite-lower-star`), so this is the displayed right side.
4. Restrict step 2 along gamma. Contravariant functoriality and the geometric
   equality in step 1 identify the result with step 3. No monomorphism or
   constant-section assumption enters any of these steps. -/
theorem coefficientMate_diagonal_graph
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (B : Scheme.{u}) (V W : B.ProEt) (h : W ⟶ V) :
    (∀ s : (condensedRingObj Λ.X B).obj.obj (op V),
      (condensedRingObj Λ.X W.left).obj.map
          (MorphismProperty.Over.homMk
            (pullback.lift h.left (𝟙 W.left)
              (h.w.trans (Category.id_comp W.hom).symm))
            (pullback.lift_snd _ _ _) trivial :
              Scheme.ProEt.mk (𝟙 W.left) ⟶
                (MorphismProperty.Over.pullback @WeaklyEtale ⊤ W.hom).obj V).op
          ((condensedPushforwardHom Λ.X W.hom).hom.app (op V) s) =
        (condensedRingObj Λ.X W.left).obj.map
          (MorphismProperty.Over.homMk
            (pullback.lift h.left (𝟙 W.left)
              ((Category.comp_id h.left).trans (Category.id_comp h.left).symm))
            (pullback.lift_snd _ _ _) trivial :
              Scheme.ProEt.mk (𝟙 W.left) ⟶
                (MorphismProperty.Over.pullback @WeaklyEtale ⊤ h.left).obj
                  (Scheme.ProEt.mk (𝟙 V.left))).op
          ((condensedPushforwardHom Λ.X h.left).hom.app
            (op (Scheme.ProEt.mk (𝟙 V.left)))
            ((condensedRingObj Λ.X V.left).obj.map
              (MorphismProperty.Over.homMk (pullback.diagonal V.hom)
                (pullback.diagonal_snd V.hom) trivial :
                  Scheme.ProEt.mk (𝟙 V.left) ⟶
                    (MorphismProperty.Over.pullback @WeaklyEtale ⊤ V.hom).obj V).op
              ((condensedPushforwardHom Λ.X V.hom).hom.app (op V) s)))) ∧
    ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ h.left).map
        (MorphismProperty.Over.homMk (pullback.diagonal V.hom)
          (pullback.diagonal_snd V.hom) trivial :
            Scheme.ProEt.mk (𝟙 V.left) ⟶
              (MorphismProperty.Over.pullback @WeaklyEtale ⊤ V.hom).obj V)).left ≫
        ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤)
          h.left V.hom W.hom h.w.symm).inv.app V).left =
      pullback.snd (𝟙 V.left) h.left ≫
        pullback.lift h.left (𝟙 W.left)
          (h.w.trans (Category.id_comp W.hom).symm) := by
  sorry

end AlgebraicGeometry.ProEtale
