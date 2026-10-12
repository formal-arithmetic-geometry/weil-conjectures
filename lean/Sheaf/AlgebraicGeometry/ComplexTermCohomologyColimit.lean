/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Sheaf.AlgebraicGeometry.EtaleComplexFiltrationPageData
public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Sheaf.AlgebraicGeometry.EtaleCohomologyLimitOfSchemes
import Mathlib.CategoryTheory.Presentable.Directed
import Mathlib.Algebra.Homology.HomologicalComplexLimits

/-! # Cohomology colimits of evaluated complex terms

Source: Stacks Project, Tags 09YQ and 0032.
(blueprint: lem-weil-pbc-complex-term-cohomology-colimit).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- Ordinary sheaf cohomology preserves the cocone of evaluated complex terms.
Source: Stacks Project, Theorem 59.51.3 (Tag 09YQ).

Proof: Choose a small nonempty directed partial order A and a final functor
R : A to I.op using Mathlib IsFiltered.exists_directed (Stacks Tag 0032).
Its left opposite is initial, so c.whisker R.leftOp is limiting. The reindexed
schemes inherit compactness, quasi-separatedness and affine transition maps.
Finality preserves the colimit cocone L.whisker R. Evaluation at s preserves
complex colimits, so its evaluation is a colimit of the pulled-back term sheaves.
Take the stage sheaf at a to be (F ((R.obj a).unop)).X s and the transition for f
to be (phi ((R.map f).unop)).f s. Evaluating eG, hidentity, hcomposition and hG
at s supplies the pullback identifications and all three sheaf coherence laws.
Apply nonempty_isColimit_etale_cohomology_of_isLimit to these sheaves in degree r,
with the reindexed H and B. Expanding complexTermCohomologyMap gives cohomologyMap
followed by Sheaf.H.map. Cancel (eH j).hom in hH to obtain the required arrow
equality; hB is already the required cocone-leg equation. The ordinary continuity
theorem therefore makes B.whisker R a colimit cocone. Transport its universal
property through Functor.Final.isColimitWhiskerEquiv R B. No lower bound or
spectral-sequence data enter this argument.
Edge cases: I is nonempty by cofilteredness. Degree zero and zero term sheaves are
included in 09YQ; the argument does not require torsion.
(blueprint: lem-weil-pbc-complex-term-cohomology-colimit). -/
theorem nonempty_isColimit_complex_term_cohomology
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ i : I, CompactSpace (D.obj i)] [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    [∀ (i j : I) (f : i ⟶ j), IsAffineHom (D.map f)]
    (F : ∀ i : I, CochainComplex (Sheaf (D.obj i).smallEtaleTopology
      AddCommGrpCat.{u + 1}) ℤ)
    (φ : ∀ {i j : I} (f : j ⟶ i),
      ((upperStar AddCommGrpCat.{u + 1} (D.map f)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (F i) ⟶ F j)
    (hidentity : ∀ i : I, φ (𝟙 i) =
      (NatIso.mapHomologicalComplex
        (eqToIso (congrArg (upperStar AddCommGrpCat.{u + 1}) (D.map_id i)))
        (ComplexShape.up ℤ)).hom.app (F i) ≫
      (NatIso.mapHomologicalComplex (upperStarId AddCommGrpCat.{u + 1} (D.obj i))
        (ComplexShape.up ℤ)).hom.app (F i))
    (hcomposition : ∀ (i j k : I) (f : j ⟶ i) (g : k ⟶ j),
      φ (g ≫ f) =
        (NatIso.mapHomologicalComplex
          (upperStarComp AddCommGrpCat.{u + 1} (D.map g) (D.map f)
            (D.map (g ≫ f)) (D.map_comp g f))
          (ComplexShape.up ℤ)).hom.app (F i) ≫
        ((upperStar AddCommGrpCat.{u + 1} (D.map g)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (φ f) ≫ φ g)
    (G : Iᵒᵖ ⥤ CochainComplex (Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ)
    (eG : ∀ i : I, G.obj (op i) ≅
      ((upperStar AddCommGrpCat.{u + 1} (c.π.app i)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (F i))
    (hG : ∀ (i j : I) (f : j ⟶ i), G.map f.op =
      (eG i).hom ≫
        (NatIso.mapHomologicalComplex
          (upperStarComp AddCommGrpCat.{u + 1} (c.π.app j) (D.map f)
            (c.π.app i) (c.w f).symm) (ComplexShape.up ℤ)).hom.app (F i) ≫
        ((upperStar AddCommGrpCat.{u + 1} (c.π.app j)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (φ f) ≫ (eG j).inv)
    (L : Cocone G) (hL : IsColimit L) (r : ℕ) (s : ℤ)
    (H : Iᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (eH : ∀ i : I, H.obj (op i) ≅ AddCommGrpCat.of (Sheaf.H ((F i).X s) r))
    (hH : ∀ (i j : I) (f : j ⟶ i), H.map f.op ≫ (eH j).hom =
      (eH i).hom ≫ complexTermCohomologyMap (D.map f) (F i) (F j) (φ f) r s)
    (B : Cocone H) (eB : B.pt ≅ AddCommGrpCat.of (Sheaf.H (L.pt.X s) r))
    (hB : ∀ i : I, B.ι.app (op i) ≫ eB.hom =
      (eH i).hom ≫ complexTermCohomologyMap (c.π.app i) (F i) L.pt
        ((eG i).inv ≫ L.ι.app (op i)) r s) :
    Nonempty (IsColimit B) := by sorry

end AlgebraicGeometry.Etale
