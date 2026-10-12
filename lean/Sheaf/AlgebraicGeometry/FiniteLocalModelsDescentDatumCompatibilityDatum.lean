/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteEtale
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver
/-! # Natural transport on a local representative -/

@[expose] public section
universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme
/-- Natural transport compatible with the local representation, before imposing cocycles.

Source: Stacks Project, Tags 03RV and 02W5.
(blueprint: def-weil-pbc-finite-local-model-compatible-transport)
The fields record transport of arbitrary scheme points, its naturality, and its
identification of equal sections on the small etale site. No data is chosen here. -/
structure FiniteLocalModelCompatibleTransport
    (T : Scheme.{u}) (E : Sheaf T.smallEtaleTopology (Type (u + 1)))
    (U : T.Etale) (Q : U.left.FiniteEtale)
    (e : (E.over U).obj ≅ (Etale.overToEtale U).op ⋙
      uliftYoneda.{u + 1}.obj Q.obj) where
  transport {W : Scheme.{u}} (a b : W ⟶ U.left) (h : a ≫ U.hom = b ≫ U.hom) :
    (Over.mk a ⟶ Over.mk Q.obj.hom) → (Over.mk b ⟶ Over.mk Q.obj.hom)
  naturality {W W' : Scheme.{u}} (g : W' ⟶ W) (a b : W ⟶ U.left)
    (h : a ≫ U.hom = b ≫ U.hom) (x : Over.mk a ⟶ Over.mk Q.obj.hom) :
    transport (g ≫ a) (g ≫ b) (by rw [Category.assoc, Category.assoc, h])
      ((Over.homMk g : Over.mk (g ≫ a) ⟶ Over.mk a) ≫ x) =
      (Over.homMk g : Over.mk (g ≫ b) ⟶ Over.mk b) ≫ transport a b h x
  compatibility :
      ∀ (W : T.Etale) (a b : W ⟶ U) (s : E.obj.obj (op W)),
        (transport a.left b.left
          ((MorphismProperty.Over.w a).trans (MorphismProperty.Over.w b).symm)
          (Over.homMk ((e.hom.app (op (Over.mk a))) s).down.left
            (MorphismProperty.Over.w ((e.hom.app (op (Over.mk a))) s).down))).left =
          ((e.hom.app (op (Over.mk b))) s).down.left

/-- Natural compatible transport exists on a local representative.

Source: Stacks Project, Tags 03RV and 02W5.
(blueprint: lem-weil-pbc-finite-local-model-compatible-transport-datum)
Proof: Set H = U times_T U. Both pullbacks of Q to H represent the same
restriction of E: the pullback universal property identifies their Yoneda
presheaves with the two restrictions of e. Yoneda full faithfulness on H gives
an isomorphism between them identifying the common section. Given arbitrary
scheme maps a,b with equal composite, pull back this comparison along (a,b)
and apply it to a Q-point. Pullback functoriality gives naturality. For an
etale W, the comparison identifies the section used to define the Q-point,
which gives compatibility. This construction uses only etale objects while
constructing the comparison, and then scheme base change for arbitrary W.
Empty objects are covered by the same universal properties. -/
theorem finiteLocalModels_descentDatum_compatibility_datum
    (T : Scheme.{u}) (E : Sheaf T.smallEtaleTopology (Type (u + 1)))
    (U : T.Etale) (Q : U.left.FiniteEtale)
    (e : (E.over U).obj ≅ (Etale.overToEtale U).op ⋙
      uliftYoneda.{u + 1}.obj Q.obj) :
    Nonempty (FiniteLocalModelCompatibleTransport T E U Q e) := by sorry
end AlgebraicGeometry.Scheme
