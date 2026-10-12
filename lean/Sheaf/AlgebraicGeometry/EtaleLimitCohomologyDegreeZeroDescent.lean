/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import Sheaf.AlgebraicGeometry.AffineEtaleSiteColimit
import Sheaf.AlgebraicGeometry.EtaleCohomologyPullbackDegreeZero
import Sheaf.AlgebraicGeometry.EtaleQcqsCofinalFiniteCoverings
import Sheaf.AlgebraicGeometry.FullAffineEtaleTopos
import Sheaf.AlgebraicGeometry.LimitAffineTransition
import Sheaf.CategoryTheory.ColimitSiteSections
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek

/-! # Degree reduction for etale limit cohomology

Source: Stacks Project, Tags 09YQ, 09YP, 09YN and 0739.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- Degree-zero limit cohomology classes descend to a stage.

Source: Stacks Project, Etale Cohomology, Tag 09YQ, the degree-zero part of
Cohomology on Sites Tag 09YP, and Sites Tag 09YN.
(blueprint: lem-weil-pbc-etale-limit-cohomology-degree-zero-descent).

Proof: Identify H^0 with evaluation at the terminal etale object, naturally in
coefficients and inverse image, using H.equiv₀ and the adjunction-unit description
of cohomologyMap. Pass to a cofinal tail and use 0EYL and 04HR to identify the
limit affine etale site and its sheaves. Direct images on affine objects agree,
so uniqueness of left adjoints identifies inverse images compatibly with units.
The finite-cover section formula of 09YN computes sections of the colimit sheaf
as the filtered colimit of stage sections. For a general qcqs stage choose a
finite affine cover and finite affine refinements of its overlaps. Apply the
affine formula on the cover and refinements. Sections are the finite equalizer
of these restriction maps; filtered group colimits commute with finite limits.
Thus the same formula holds globally. A section has a finite-stage representative;
transport it back through eH and eB. The unit identification and hB give exactly
the displayed image equation. Zero coefficients and empty schemes have only
zero sections, represented at any stage; no negative cohomology degree occurs.
-/
theorem etale_limit_cohomology_degree_zero_descent
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)] [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    [∀ (i j : Iᵒᵖ) (f : i ⟶ j), IsAffineHom (D.map f)]
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
    (L : Cocone G) (hL : IsColimit L)
    (H : I ⥤ AddCommGrpCat.{u + 1})
    (eH : ∀ i : I, H.obj i ≅ AddCommGrpCat.of (Sheaf.H (F i) 0))
    (hH : ∀ (i j : I) (f : i ⟶ j), H.map f =
      (eH i).hom ≫ AddCommGrpCat.ofHom (cohomologyMap (D.map f.op) (F i) 0) ≫
        AddCommGrpCat.ofHom (Sheaf.H.map (φ f) 0) ≫ (eH j).inv)
    (B : Cocone H) (eB : B.pt ≅ AddCommGrpCat.of (Sheaf.H L.pt 0))
    (hB : ∀ i : I, B.ι.app i ≫ eB.hom =
      (eH i).hom ≫ AddCommGrpCat.ofHom (cohomologyMap (c.π.app (op i)) (F i) 0) ≫
        AddCommGrpCat.ofHom (Sheaf.H.map ((eG i).inv ≫ L.ι.app i) 0)) :
    ∀ y : B.pt, ∃ (i : I) (x : H.obj i), (B.ι.app i).hom x = y := by sorry

end AlgebraicGeometry.Etale
