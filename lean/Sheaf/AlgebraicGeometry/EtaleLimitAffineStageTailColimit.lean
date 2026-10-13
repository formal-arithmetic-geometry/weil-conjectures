/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D3
-/
module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import Sheaf.AlgebraicGeometry.EtaleLimitCohomologyAffineComparison

/-! # The comparison cocone on the affine tail

Source: Stacks Project, Tag 09YQ, cofinal-tail reduction.
(blueprint: lem-weil-pbc-etale-limit-affine-stage-tail-colimit).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

/-- The comparison cocone restricted above an affine stage is a colimit.

Source: Stacks Project, Tag 09YQ (theorem-colimit), the cofinal-tail reduction.
(blueprint: lem-weil-pbc-etale-limit-affine-stage-tail-colimit).

Proof: the upper tail of i0 is nonempty and directed. Its inclusion into I is
final, since every i has a common upper bound with i0. Its opposite is initial,
so whiskering the scheme cone preserves its limit. Whiskering the coefficient
cocone preserves its colimit. Each tail scheme has an affine morphism to the
affine scheme at i0, and is therefore affine. Restrict the coefficient sheaves,
transition maps, and the identifications eG and eH to this tail. The identity
and composition equations follow from functoriality of the inclusion; the
sheaf-transition, cohomology-transition and comparison-leg equations are the
original equations at the included indices. Apply affine cohomology comparison
(lem-weil-pbc-etale-limit-cohomology-affine-comparison) to these restricted data.
It identifies precisely the whiskered B as a colimit. No assertion about a
particular cohomology class or its eventual vanishing is made here.
For a singleton indexing system the restriction is the whole system. Degree
zero, zero sheaves and empty affine schemes are included in affine comparison;
no earlier scheme is assumed affine. -/
theorem etale_limit_affine_stage_tail_colimit
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
    (L : Cocone G) (hL : IsColimit L) (p : ℕ)
    (H : I ⥤ AddCommGrpCat.{u + 1})
    (eH : ∀ i : I, H.obj i ≅ AddCommGrpCat.of (Sheaf.H (F i) p))
    (hH : ∀ (i j : I) (f : i ⟶ j), H.map f =
      (eH i).hom ≫ AddCommGrpCat.ofHom (cohomologyMap (D.map f.op) (F i) p) ≫
        AddCommGrpCat.ofHom (Sheaf.H.map (φ f) p) ≫ (eH j).inv)
    (B : Cocone H) (eB : B.pt ≅ AddCommGrpCat.of (Sheaf.H L.pt p))
    (hB : ∀ i : I, B.ι.app i ≫ eB.hom =
      (eH i).hom ≫ AddCommGrpCat.ofHom (cohomologyMap (c.π.app (op i)) (F i) p) ≫
        AddCommGrpCat.ofHom (Sheaf.H.map ((eG i).inv ≫ L.ι.app i) p))
    (i₀ : I) [IsAffine (D.obj (op i₀))] :
    Nonempty (IsColimit (B.whisker
      (Subtype.mono_coe (· ∈ Set.Ici i₀)).functor)) := by sorry

end AlgebraicGeometry.Etale
