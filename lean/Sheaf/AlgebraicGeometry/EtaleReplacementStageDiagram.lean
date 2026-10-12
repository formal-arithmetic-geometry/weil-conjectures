/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q1
-/
module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Abelian.FunctorCategory

import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import Sheaf.CategoryTheory.SitePullbackAbelianExact
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-! # The stage diagram of an étale injective replacement

Source: Stacks Project, Tags 0EXZ and 04JC.
(blueprint: lem-weil-pbc-etale-replacement-stage-diagram).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

/-- Compatible injective and cokernel systems, assembled into a short exact diagram
on the cone point, before taking any filtered colimit.
Source: Stacks Project, Tag 0EXZ, its product-of-direct-images construction, and
Tag 04JC for exact inverse image.
(blueprint: lem-weil-pbc-etale-replacement-stage-diagram).

Proof: At every k use Injective.under (F k) and its canonical monomorphism.
At i form the product of their direct images over the arrows i to k. Transpose
coefficient transitions through the inverse-image/direct-image adjunction to
obtain the embedding. The identity component proves monicity. Exact inverse
image implies that direct image preserves injectives, and products of injectives
are injective. Reindexing the products defines the transition maps; adjunction
naturality and the inverse-image associativity and unit comparisons prove the
system laws and compatibility of the embeddings. Set FR i to the cokernel of
the embedding. Preservation of cokernels by inverse image defines its transitions;
cancel the epic cokernel projections to prove their identity and composition laws.
Pull both systems to the cone point, using the cone equation and upperStarComp
to define the functor arrows. The same unit and associativity equations prove
the functor laws. Transport the pulled-back embedding and quotient through eG,
eGI and eGR; compatibility makes them natural transformations α and β. Their
composite is zero by stagewise exactness. Each transported sequence is short
exact because inverse image is exact; kernels and cokernels in the functor
category are evaluated objectwise, so their short complex is short exact.
The inverse objectwise identifications define the displayed morphisms s; their
commutation equations are the definitions of α and β. Their first and third
components are eG.inv and eGR.inv. No colimit or exact limit sequence is asserted.
-/
theorem etale_replacement_stage_diagram
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D)
    (F : ∀ i : I, Sheaf (D.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : ∀ {i j : I} (f : i ⟶ j),
      (upperStar AddCommGrpCat.{u + 1} (D.map f.op)).obj (F i) ⟶ F j)
    (hidentity : ∀ i : I, φ (𝟙 i) =
      (eqToIso (congrArg (upperStar AddCommGrpCat.{u + 1}) (D.map_id (op i)))).hom.app
        (F i) ≫ (upperStarId AddCommGrpCat.{u + 1} (D.obj (op i))).hom.app (F i))
    (hcomposition : ∀ (i j k : I) (f : i ⟶ j) (g : j ⟶ k),
      φ (f ≫ g) =
        (upperStarComp AddCommGrpCat.{u + 1} (D.map g.op) (D.map f.op)
          (D.map (f ≫ g).op) (D.map_comp g.op f.op)).hom.app (F i) ≫
        (upperStar AddCommGrpCat.{u + 1} (D.map g.op)).map (φ f) ≫ φ g)
    (G : I ⥤ Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
    (eG : ∀ i : I, G.obj i ≅
      (upperStar AddCommGrpCat.{u + 1} (c.π.app (op i))).obj (F i))
    (hG : ∀ (i j : I) (f : i ⟶ j), G.map f =
      (eG i).hom ≫
        (upperStarComp AddCommGrpCat.{u + 1} (c.π.app (op j)) (D.map f.op)
          (c.π.app (op i)) (c.w f.op).symm).hom.app (F i) ≫
        (upperStar AddCommGrpCat.{u + 1} (c.π.app (op j))).map (φ f) ≫ (eG j).inv)
 :
    ∃ (FR : ∀ i : I, Sheaf (D.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (φR : ∀ {i j : I} (f : i ⟶ j),
      (upperStar AddCommGrpCat.{u + 1} (D.map f.op)).obj (FR i) ⟶ FR j)
    (hidentityR : ∀ i : I, φR (𝟙 i) =
      (eqToIso (congrArg (upperStar AddCommGrpCat.{u + 1}) (D.map_id (op i)))).hom.app
        (FR i) ≫ (upperStarId AddCommGrpCat.{u + 1} (D.obj (op i))).hom.app (FR i))
    (hcompositionR : ∀ (i j k : I) (f : i ⟶ j) (g : j ⟶ k),
      φR (f ≫ g) =
        (upperStarComp AddCommGrpCat.{u + 1} (D.map g.op) (D.map f.op)
          (D.map (f ≫ g).op) (D.map_comp g.op f.op)).hom.app (FR i) ≫
        (upperStar AddCommGrpCat.{u + 1} (D.map g.op)).map (φR f) ≫ φR g)
    (GR : I ⥤ Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
    (eGR : ∀ i : I, GR.obj i ≅
      (upperStar AddCommGrpCat.{u + 1} (c.π.app (op i))).obj (FR i))
    (hGR : ∀ (i j : I) (f : i ⟶ j), GR.map f =
      (eGR i).hom ≫
        (upperStarComp AddCommGrpCat.{u + 1} (c.π.app (op j)) (D.map f.op)
          (c.π.app (op i)) (c.w f.op).symm).hom.app (FR i) ≫
        (upperStar AddCommGrpCat.{u + 1} (c.π.app (op j))).map (φR f) ≫ (eGR j).inv)
    (FI : ∀ i : I, Sheaf (D.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (ψ : ∀ {i j : I} (f : i ⟶ j),
      (upperStar AddCommGrpCat.{u + 1} (D.map f.op)).obj (FI i) ⟶ FI j)
    (hidentityI : ∀ i : I, ψ (𝟙 i) =
      (eqToIso (congrArg (upperStar AddCommGrpCat.{u + 1}) (D.map_id (op i)))).hom.app
        (FI i) ≫ (upperStarId AddCommGrpCat.{u + 1} (D.obj (op i))).hom.app (FI i))
    (hcompositionI : ∀ (i j k : I) (f : i ⟶ j) (g : j ⟶ k),
      ψ (f ≫ g) =
        (upperStarComp AddCommGrpCat.{u + 1} (D.map g.op) (D.map f.op)
          (D.map (f ≫ g).op) (D.map_comp g.op f.op)).hom.app (FI i) ≫
        (upperStar AddCommGrpCat.{u + 1} (D.map g.op)).map (ψ f) ≫ ψ g)
    (GI : I ⥤ Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
    (eGI : ∀ i : I, GI.obj i ≅
      (upperStar AddCommGrpCat.{u + 1} (c.π.app (op i))).obj (FI i))
    (hGI : ∀ (i j : I) (f : i ⟶ j), GI.map f =
      (eGI i).hom ≫
        (upperStarComp AddCommGrpCat.{u + 1} (c.π.app (op j)) (D.map f.op)
          (c.π.app (op i)) (c.w f.op).symm).hom.app (FI i) ≫
        (upperStar AddCommGrpCat.{u + 1} (c.π.app (op j))).map (ψ f) ≫ (eGI j).inv)
    (ai : ∀ i : I, F i ⟶ FI i) (bi : ∀ i : I, FI i ⟶ FR i)
    (wi : ∀ i : I, ai i ≫ bi i = 0)
    (hi : ∀ i : I, (ShortComplex.mk (ai i) (bi i) (wi i)).ShortExact)
    (α : G ⟶ GI) (β : GI ⟶ GR) (w : α ≫ β = 0)
    (s : ∀ i : I,
      (ShortComplex.mk (ai i) (bi i) (wi i)).map
        (upperStar AddCommGrpCat.{u + 1} (c.π.app (op i))) ⟶
      (ShortComplex.mk (α.app i) (β.app i) (congrArg (fun f ↦ f.app i) w))),
      (∀ i : I, Injective (FI i)) ∧
      (ShortComplex.mk α β w).ShortExact ∧
      (∀ i : I, (s i).τ₁ = (eG i).inv) ∧
      (∀ i : I, (s i).τ₃ = (eGR i).inv) := by sorry

end AlgebraicGeometry.Etale
