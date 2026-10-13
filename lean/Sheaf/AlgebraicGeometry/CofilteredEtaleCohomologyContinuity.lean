/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M4
-/
module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Sheaf.AlgebraicGeometry.EtaleCohomologyLimitOfSchemes
import Mathlib.CategoryTheory.Presentable.Directed

/-! # Ordinary etale continuity for cofiltered categories

Source: Stacks Project, Tags 09YQ and 0032.
(blueprint: lem-weil-pbc-cofiltered-etale-cohomology-continuity).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- Ordinary continuity extends from directed orders to small cofiltered categories.
Source: Stacks Project, Theorem 59.51.3 (Tag 09YQ) and Tag 0032.

Proof: Choose a small nonempty directed partial order A and a final R : A to I.op
using IsFiltered.exists_directed. The left opposite of R is initial, so whiskering
c gives a limiting cone. Compactness, quasi-separatedness, and affine transitions
are inherited. Reindex F and its transition maps along R. The identity law follows
from R.map_id, the composition law from R.map_comp and reversal by unop; equality
proof arguments agree by proof irrelevance. Reindex G, H, L, and B, together with
their object isomorphisms. Finality preserves the colimit of L, and the supplied
arrow and leg equations give those required for directed continuity. Apply
nonempty_isColimit_etale_cohomology_of_isLimit and transport the resulting colimit
of B.whisker R back by Functor.Final.isColimitWhiskerEquiv. Cofilteredness ensures
nonemptiness; degree zero and zero sheaves are included without extra hypotheses.
(blueprint: lem-weil-pbc-cofiltered-etale-cohomology-continuity). -/
theorem nonempty_isColimit_etale_cohomology_of_cofiltered_isLimit
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ i : I, CompactSpace (D.obj i)] [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    [∀ (i j : I) (f : i ⟶ j), IsAffineHom (D.map f)]
    (F : ∀ i : I, Sheaf (D.obj i).smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : ∀ {i j : I} (f : j ⟶ i),
      (upperStar AddCommGrpCat.{u + 1} (D.map f)).obj (F i) ⟶ F j)
    (hidentity : ∀ i : I, φ (𝟙 i) =
      (eqToIso (congrArg (upperStar AddCommGrpCat.{u + 1}) (D.map_id i))).hom.app
        (F i) ≫ (upperStarId AddCommGrpCat.{u + 1} (D.obj i)).hom.app (F i))
    (hcomposition : ∀ (i j k : I) (f : j ⟶ i) (g : k ⟶ j), φ (g ≫ f) =
      (upperStarComp AddCommGrpCat.{u + 1} (D.map g) (D.map f)
        (D.map (g ≫ f)) (D.map_comp g f)).hom.app (F i) ≫
      (upperStar AddCommGrpCat.{u + 1} (D.map g)).map (φ f) ≫ φ g)
    (G : Iᵒᵖ ⥤ Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
    (eG : ∀ i : I, G.obj (op i) ≅
      (upperStar AddCommGrpCat.{u + 1} (c.π.app i)).obj (F i))
    (hG : ∀ (i j : I) (f : j ⟶ i), G.map f.op = (eG i).hom ≫
      (upperStarComp AddCommGrpCat.{u + 1} (c.π.app j) (D.map f)
        (c.π.app i) (c.w f).symm).hom.app (F i) ≫
      (upperStar AddCommGrpCat.{u + 1} (c.π.app j)).map (φ f) ≫ (eG j).inv)
    (L : Cocone G) (hL : IsColimit L) (r : ℕ)
    (H : Iᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (eH : ∀ i : I, H.obj (op i) ≅ AddCommGrpCat.of (Sheaf.H (F i) r))
    (hH : ∀ (i j : I) (f : j ⟶ i), H.map f.op ≫ (eH j).hom =
      (eH i).hom ≫ AddCommGrpCat.ofHom (cohomologyMap (D.map f) (F i) r) ≫
        AddCommGrpCat.ofHom (Sheaf.H.map (φ f) r))
    (B : Cocone H) (eB : B.pt ≅ AddCommGrpCat.of (Sheaf.H L.pt r))
    (hB : ∀ i : I, B.ι.app (op i) ≫ eB.hom =
      (eH i).hom ≫ AddCommGrpCat.ofHom (cohomologyMap (c.π.app i) (F i) r) ≫
        AddCommGrpCat.ofHom (Sheaf.H.map ((eG i).inv ≫ L.ι.app (op i)) r)) :
    Nonempty (IsColimit B) := by sorry

end AlgebraicGeometry.Etale
