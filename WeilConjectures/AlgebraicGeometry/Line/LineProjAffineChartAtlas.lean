/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Line.LineProjFractionChartData
import WeilConjectures.AlgebraicGeometry.Line.LineProjFractionCoefficientHom
import WeilConjectures.AlgebraicGeometry.Line.LineProjGenerationLocus
import WeilConjectures.AlgebraicGeometry.Line.LineProjFractionCompatibility

/-! # Compatible homogeneous-fraction charts

Source: Stacks Project, Tags 01NK and 01O9
(blueprint: lem-trf-line-proj-affine-chart-atlas).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

/-- Compatible homogeneous-fraction charts for an arbitrary graded map into tensor
powers of an invertible module, with positive-degree generation, unique local maps,
arbitrary-degree and arbitrary-base overlaps, and both kinds of open refinement.

Source: Stacks Project, Constructions, Tags 01NK (lemma-invertible-map-into-proj)
and 01O9 (lemma-invertible-map-into-relative-proj)
(blueprint: lem-trf-line-proj-affine-chart-atlas).

Proof: Construct the unique homogeneous fraction chart on each generator open by
lineProj_exists_chart and choose the resulting uniquely specified family. The local
generator criterion identifies each chart open with its basis-germ locus, and
a tensor-pullback stalk argument identifies their union with the positive-degree
surjectivity locus. The fraction uniqueness theorem gives the asserted equivalence on
every source refinement. Local frames compare the charts with Mathlib's morphism to
Proj, proving arbitrary-degree overlaps; fraction uniqueness under affine restriction
and the relative-Proj transitions give arbitrary-base overlaps and base refinement.
Finally the fraction equation in a local frame gives the scalar and basic-open formulas.
All component results include empty opens and exponent zero. -/
theorem exists_lineProj_affine_chart_atlas {W T : Scheme.{u}} (f : W ⟶ T)
    (A : RelativeProjAlgebra T) (L : W.Modules) [L.IsInvertible]
    (ψ : ∀ n : ℕ, (tensorPullback f).obj (A.piece n) ⟶ L.tensorPow n)
    (hunit : ∀ (V : T.Opens) (r : Γ(T, V)),
      lineProjImage f A L ψ V 0 (A.graded.unit.val.app (op V) (unitSectionsEquiv V r)) =
        unitSectionsEquiv (f ⁻¹ᵁ V) (f.app V r))
    (hmul : ∀ (V : T.Opens) (m n : ℕ) (a : Γ(A.piece m, V)) (b : Γ(A.piece n, V)),
      lineProjImage f A L ψ V (m + n) (A.graded.mul m n V a b) =
        (L.tensorPowAddIso m n).inv.app (f ⁻¹ᵁ V)
          (tmulSection (lineProjImage f A L ψ V m a) (lineProjImage f A L ψ V n b))) :
    ∃ q : ∀ (V : T.affineOpens) (d : ℕ) (_hd : 0 < d) (a : Γ(A.piece d, V.1)),
        LineProjChart f A L ψ V d a,
      (∀ (V : T.affineOpens) (d : ℕ) (_hd : 0 < d) (a : Γ(A.piece d, V.1)) (x : W),
        x ∈ lineProjGeneratorOpen f A L ψ V d a ↔
          ∃ hx : x ∈ f ⁻¹ᵁ V.1,
            Function.Bijective fun r : W.presheaf.stalk x ↦
              r • TopCat.Presheaf.germ (L.tensorPow d).val.presheaf (f ⁻¹ᵁ V.1) x hx
                (lineProjImage f A L ψ V.1 d a)) ∧
      ((⨆ (V : T.affineOpens) (d : ℕ) (_hd : 0 < d) (a : Γ(A.piece d, V.1)),
          lineProjGeneratorOpen f A L ψ V d a : W.Opens) : Set W) =
        {x | ∃ d : ℕ, 0 < d ∧ Function.Surjective
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (ψ d).mapPresheaf)} ∧
      (∀ (V : T.affineOpens) (d : ℕ) (hd : 0 < d) (a : Γ(A.piece d, V.1))
        (C : W.Opens) (hC : C ≤ lineProjGeneratorOpen f A L ψ V d a)
        (r : C.toScheme ⟶ Spec (.of (HomogeneousLocalization.Away (A.grade V)
          (lineProjElement A V d a).val))),
        LineProjFractionFormula f A L ψ V d a C (hC.trans inf_le_left) r ↔
          r = W.homOfLE hC ≫ q V d hd a) ∧
      (∀ (V V' : T.affineOpens) (d e : ℕ) (hd : 0 < d) (he : 0 < e)
        (a : Γ(A.piece d, V.1)) (b : Γ(A.piece e, V'.1)),
        W.homOfLE (inf_le_left :
            lineProjGeneratorOpen f A L ψ V d a ⊓ lineProjGeneratorOpen f A L ψ V' e b ≤
              lineProjGeneratorOpen f A L ψ V d a) ≫
            lineProjChartToRelative f A L ψ V d hd a (q V d hd a) =
          W.homOfLE inf_le_right ≫
            lineProjChartToRelative f A L ψ V' e he b (q V' e he b)) ∧
      (∀ (V : T.affineOpens) (d : ℕ) (hd : 0 < d) (a : Γ(A.piece d, V.1)),
        LineProjTrivializationFormula f A L ψ V d a (q V d hd a)) ∧
      LineProjBaseRefinement f A L ψ q := by
  classical
  choose q hq using lineProj_exists_chart f A L ψ hunit hmul
  have hform (V : T.affineOpens) (d : ℕ) (hd : 0 < d) (a : Γ(A.piece d, V.1)) :
      LineProjFractionFormula f A L ψ V d a
        (lineProjGeneratorOpen f A L ψ V d a) inf_le_left (q V d hd a) := by
    exact (hq V d hd a _ le_rfl _).mpr (by simp)
  obtain ⟨hover, hbase⟩ := lineProj_fraction_compatibility f A L ψ hunit hmul q hform
  exact ⟨q, fun V d _ a x ↦ lineProj_generator_stalk f A L ψ V d a x,
    lineProj_generation_locus f A L ψ, hq, hover,
    fun V d hd a ↦ lineProj_trivialization_formula f A L ψ V d a _ (hform V d hd a),
    hbase⟩

end AlgebraicGeometry.Scheme.Modules
