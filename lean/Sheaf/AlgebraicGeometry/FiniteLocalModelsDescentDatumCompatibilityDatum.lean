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

/--
Source: Stacks Project, Tags 03RV and 02W5.
(blueprint: finite-local-models-transport-exists)
The fiber-product Yoneda comparison of the two pullbacks of the finite etale
scheme defines transport for arbitrary scheme maps with equal composites.
Pulling this comparison back along the pair of maps gives the displayed map.
-/
theorem finiteLocalModels_transport_exists
    (T : Scheme.{u}) (E : Sheaf T.smallEtaleTopology (Type (u + 1)))
    (U : T.Etale) (Q : U.left.FiniteEtale)
    (e : (E.over U).obj ≅ (Etale.overToEtale U).op ⋙
      uliftYoneda.{u + 1}.obj Q.obj) :
    Nonempty (∀ {W : Scheme.{u}} (a b : W ⟶ U.left),
      a ≫ U.hom = b ≫ U.hom →
      (Over.mk a ⟶ Over.mk Q.obj.hom) →
      (Over.mk b ⟶ Over.mk Q.obj.hom)) := by sorry

/--
Source: Stacks Project, Tags 03RV and 02W5.
(blueprint: finite-local-models-transport-naturality)
The transport is induced by pullback of the comparison on the fiber product.
Functoriality of pullback, together with associativity of composition, proves
the displayed naturality equation.
-/
theorem finiteLocalModels_transport_naturality
    (T : Scheme.{u}) (E : Sheaf T.smallEtaleTopology (Type (u + 1)))
    (U : T.Etale) (Q : U.left.FiniteEtale)
    (e : (E.over U).obj ≅ (Etale.overToEtale U).op ⋙
      uliftYoneda.{u + 1}.obj Q.obj)
    (transport : ∀ {W : Scheme.{u}} (a b : W ⟶ U.left),
      a ≫ U.hom = b ≫ U.hom →
      (Over.mk a ⟶ Over.mk Q.obj.hom) →
      (Over.mk b ⟶ Over.mk Q.obj.hom)) :
    ∀ {W W' : Scheme.{u}} (g : W' ⟶ W) (a b : W ⟶ U.left)
      (h : a ≫ U.hom = b ≫ U.hom) (x : Over.mk a ⟶ Over.mk Q.obj.hom),
      transport (g ≫ a) (g ≫ b) (by rw [Category.assoc, Category.assoc, h])
        ((Over.homMk g : Over.mk (g ≫ a) ⟶ Over.mk a) ≫ x) =
      (Over.homMk g : Over.mk (g ≫ b) ⟶ Over.mk b) ≫ transport a b h x := by sorry

/--
Source: Stacks Project, Tags 03RV and 02W5.
(blueprint: finite-local-models-transport-compatibility)
For an etale source, the comparison identifies the two points obtained from a
common section under the representing isomorphism, yielding compatibility.
-/
theorem finiteLocalModels_transport_compatibility
    (T : Scheme.{u}) (E : Sheaf T.smallEtaleTopology (Type (u + 1)))
    (U : T.Etale) (Q : U.left.FiniteEtale)
    (e : (E.over U).obj ≅ (Etale.overToEtale U).op ⋙
      uliftYoneda.{u + 1}.obj Q.obj)
    (transport : ∀ {W : Scheme.{u}} (a b : W ⟶ U.left),
      a ≫ U.hom = b ≫ U.hom →
      (Over.mk a ⟶ Over.mk Q.obj.hom) →
      (Over.mk b ⟶ Over.mk Q.obj.hom)) :
    ∀ (W : T.Etale) (a b : W ⟶ U) (s : E.obj.obj (op W)),
      (transport a.left b.left
        ((MorphismProperty.Over.w a).trans (MorphismProperty.Over.w b).symm)
        (Over.homMk ((e.hom.app (op (Over.mk a))) s).down.left
          (MorphismProperty.Over.w ((e.hom.app (op (Over.mk a))) s).down))).left =
      ((e.hom.app (op (Over.mk b))) s).down.left := by sorry

theorem finiteLocalModels_descentDatum_compatibility_datum
    (T : Scheme.{u}) (E : Sheaf T.smallEtaleTopology (Type (u + 1)))
    (U : T.Etale) (Q : U.left.FiniteEtale)
    (e : (E.over U).obj ≅ (Etale.overToEtale U).op ⋙
      uliftYoneda.{u + 1}.obj Q.obj) :
    Nonempty (FiniteLocalModelCompatibleTransport T E U Q e) := by
  let transport : ∀ {W : Scheme.{u}} (a b : W ⟶ U.left),
      a ≫ U.hom = b ≫ U.hom →
      (Over.mk a ⟶ Over.mk Q.obj.hom) → (Over.mk b ⟶ Over.mk Q.obj.hom) :=
    (finiteLocalModels_transport_exists T E U Q e).some
  refine ⟨{
    transport := transport
    naturality := by
      intro W W' g a b h x
      exact finiteLocalModels_transport_naturality T E U Q e transport g a b h x
    compatibility := by
      intro W a b s
      exact finiteLocalModels_transport_compatibility T E U Q e transport W a b s
  }⟩
end AlgebraicGeometry.Scheme
