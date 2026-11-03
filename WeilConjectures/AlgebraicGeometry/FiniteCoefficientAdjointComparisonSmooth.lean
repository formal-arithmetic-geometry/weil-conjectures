/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteAffineRightScalarNormalForm
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionDirectImage
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalObjects
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionCtfFunctors
public import WeilConjectures.AlgebraicGeometry.ChartScalarReassociation
public import WeilConjectures.AlgebraicGeometry.CoefficientScalarRepresentatives.CoefficientScalarRepresentatives
public import WeilConjectures.AlgebraicGeometry.Ordered.OrderedAffineTraceNormalForm
public import WeilConjectures.AlgebraicGeometry.Etale.EtaleAmbientAdjointLocality
public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportComparisons
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantOpenSquareExchange
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
public import WeilConjectures.AlgebraicGeometry.Sf.SfCompactSupportRestrictionData
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Data
public import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonClassAdjunction
public import WeilConjectures.AlgebraicGeometry.Sf.SfFiniteExceptionalInverseImage
public import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceRightNormalForm
public import WeilConjectures.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars.Trace
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitude
import WeilConjectures.AlgebraicGeometry.FiniteCoefficientSmoothComparisonData
import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Smooth exceptional coefficient comparison over an arbitrary characteristic-p field

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-reduction/
sk-lem-sp-reduction-exceptional.md
(blueprint: lem-pur-finite-coefficient-adjoint-comparisons).

The statement follows the five general-field steps: construct the coefficient mate,
restrict it to finite smooth charts, identify the ordered Tate and affine counits, transport
through the canonical scalar/pullback comparisons, and conclude by open locality and
covering conservativity.  Every map in the chart clause is the published scalar-extension
and chart reassociation map; no normalized-tower or witness-compatibility interface is
used.
-/

public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale

open GeneralFieldChart

private theorem smoothMate_existsUnique
    {C D E F : Type*} [Category* C] [Category* D] [Category* E] [Category* F]
    {LA : C ⥤ D} {GA : D ⥤ C} {LB : E ⥤ F} {GB : F ⥤ E}
    (a : LA ⊣ GA) (b : LB ⊣ GB) (S : C ⥤ E) (T : D ⥤ F)
    (β : LA ⋙ T ≅ S ⋙ LB) :
    ∃! c : GA ⋙ S ⟶ T ⋙ GB,
      ∀ K, LB.map (c.app K) ≫ b.counit.app (T.obj K) =
        β.inv.app (GA.obj K) ≫ T.map (a.counit.app K) := by
  let c := (mateEquiv a b (TwoSquare.mk S LA LB T β.inv)).natTrans
  have hc (K : D) : LB.map (c.app K) ≫ b.counit.app (T.obj K) =
      β.inv.app (GA.obj K) ≫ T.map (a.counit.app K) :=
    mateEquiv_counit a b (TwoSquare.mk S LA LB T β.inv) K
  refine ⟨c, hc, ?_⟩
  intro c' hc'
  ext K
  apply (b.homEquiv _ _).symm.injective
  simpa only [Adjunction.homEquiv_counit] using (hc' K).trans (hc K).symm


/-- Smooth exceptional inverse image commutes with arbitrary finite coefficient extension.

Source: the latest exceptional-reduction proof, Existence, Locality and Charts;
coefficient coordinate-adjunction step of `det-sp-trace-basic`, Proof (2).
(blueprint: lem-pur-finite-coefficient-adjoint-comparisons).

Proof: the finite-data existence lemma supplies the restricted adjunctions.
Restrict the actual compact-support scalar isomorphism to the full subcategories
and apply the mates correspondence. Its counit formula proves normalization,
and the adjunction Hom bijection proves uniqueness. The geometric comparison
lemma supplies component invertibility and the chart equation, following these steps:
1. `lem-pur-general-field-compact-scalar-site-square` supplies the canonical b. Restrict
compact support and scalar extension to Dctf. Transpose the scalar-extended A-counit
composed with b inverse through the B-adjunction. Naturality and injectivity of the
Hom transposition prove naturality and uniqueness of c.
2. `lem-sp-smooth-admissible-coordinate-cover` gives finite etale coordinate charts.
Use `lem-pur-general-field-chart-adjunction-realization` for their finite-ctf domains
and counit-preserving identifications. `lem-pur-general-field-open-scalar-locality`
identifies each chart mate with the restriction of c through scalar/pullback.
3. `lem-pur-general-field-p1-proetale-counit` retains the Kummer and diagonal classes,
the ordered free splitting, projection trace and its scalar equation. Iterate using
`lem-pur-general-field-affine-proetale-counit`, including dimension zero and the fixed
compactification comparisons, to obtain the ordered affine counit equation.
4. `lem-pur-general-field-etale-proetale-counit` identifies etale summation and balancing.
Paste with the affine counit using `def-weil-pbc-composite-adjunction` and
`lem-weil-pbc-mate-pasting`. The compact-support/site square identifies its left map
with b; chart realization identifies its right map with the single actual
`chartScalarReassociationMap`, retaining the ordered Tate factors and even shift.
5. Cancel b and use uniqueness of transposition to get exactly the displayed chart
square. Open scalar locality and `lem-cbc-proetale-stalk-conservative` give invertibility
of c on X. The empty cover handles empty X.

The chart isomorphisms used by `FiniteCoefficientChartEquation` are constructed from
normalized counits; none is a free existential variable. The coordinate tower is the
specified affine d-space presentation, canonically identified by `affineTraceAffineSpaceIso`.
-/
theorem finiteCoefficientAdjointComparisonSmooth
    (ℓ pchar : ℕ) [Fact ℓ.Prime] (hp : 0 < pchar) (hℓ : pchar ≠ ℓ)
    (k : Type u) [Field k] [CharP k pchar]
    {X Z Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Z.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    (d : ℕ) [SmoothOfRelativeDimension d f]
    (j : X ⟶ Z) [IsOpenImmersion j] [j.IsOver (Spec (.of k))]
    (p : Z ⟶ Y) [IsProper p] [p.IsOver (Spec (.of k))] (hf : j ≫ p = f)
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (hA : ∃ n : ℕ, ∀ x : A, (ℓ ^ n) • x = 0)
    (hB : ∃ n : ℕ, ∀ x : B, (ℓ ^ n) • x = 0) (φ : A →+* B) :
    ∃ (hFA : ∀ M : chartCtfCategory X A,
        chartCtf Y A ((chartCompact A j p).obj M.obj))
      (hFB : ∀ M : chartCtfCategory X B,
        chartCtf Y B ((chartCompact B j p).obj M.obj))
      (hSX : ∀ M : chartCtfCategory X A,
        chartCtf X B ((chartScalar φ X).obj M.obj))
      (hSY : ∀ K : chartCtfCategory Y A,
        chartCtf Y B ((chartScalar φ Y).obj K.obj)),
      ∃ (GA : chartCtfCategory Y A ⥤ chartCtfCategory X A)
        (GB : chartCtfCategory Y B ⥤ chartCtfCategory X B)
        (adjA : chartCtfCompact A j p hFA ⊣ GA)
        (adjB : chartCtfCompact B j p hFB ⊣ GB),
        ∃ (RA : ChartAdjunctionRealization A j p hFA GA adjA)
          (RB : ChartAdjunctionRealization B j p hFB GB adjB),
        ∃ hb : ∀ K : chartCtfCategory Y A,
          IsIso ((chartCompactScalarComparison φ j p).app (GA.obj K).obj),
        ∃! c : GA ⋙ chartCtfScalar φ X hSX ⟶
          chartCtfScalar φ Y hSY ⋙ GB,
          (∀ K : chartCtfCategory Y A,
            (chartCompact B j p).map (c.app K).hom ≫
                (adjB.counit.app ((chartCtfScalar φ Y hSY).obj K)).hom =
              @inv _ _ _ _ ((chartCompactScalarComparison φ j p).app (GA.obj K).obj)
                  (hb K) ≫
                (chartScalar φ Y).map (adjA.counit.app K).hom) ∧
          (∀ K : chartCtfCategory Y A, IsIso (c.app K)) ∧
          (∀ (n : ℕ) (hn : 0 < ℓ ^ n) (hnA : ((ℓ ^ n : ℕ) : A) = 0)
              (hnB : ((ℓ ^ n : ℕ) : B) = 0)
              (MA : Etale.EtaleCompactSupportNormalization (ULift.{u + 1, u} A))
              (MB : Etale.EtaleCompactSupportNormalization (ULift.{u + 1, u} B))
              (tA : Etale.OrdinaryFiniteTwistTransport (ULift.{u + 1, u} A)
                (ℓ ^ n) (congrArg ULift.up hnA))
              (DA : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit ((ℓ ^ n : ℕ) : Γ(T, ⊤))),
                Etale.OrdinaryFiniteP1Datum (ULift.{u + 1, u} A) (ℓ ^ n)
                  (congrArg ULift.up hnA) tA T hT)
              (tB : Etale.OrdinaryFiniteTwistTransport (ULift.{u + 1, u} B)
                (ℓ ^ n) (congrArg ULift.up hnB))
              (DB : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit ((ℓ ^ n : ℕ) : Γ(T, ⊤))),
                Etale.OrdinaryFiniteP1Datum (ULift.{u + 1, u} B) (ℓ ^ n)
                  (congrArg ULift.up hnB) tB T hT)
              (hY : IsUnit ((ℓ ^ n : ℕ) : Γ(Y, ⊤)))
              (U : Scheme.{u}) [IsNoetherian U]
              (jU : U ⟶ X) [IsOpenImmersion jU]
              (e : U ⟶ affineTraceTower Y d) [AlgebraicGeometry.Etale e]
              [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
              (he : jU ≫ f = e ≫ affineTraceProjection Y d)
              (K : chartCtfCategory Y A),
            FiniteCoefficientChartEquation k φ j p hFA hFB hSX hSY GA GB adjA adjB
              RA RB MA MB c jU d e ((congrArg (fun q ↦ jU ≫ q) hf).trans he)
              (ℓ ^ n) hn hnA hnB tA DA tB DB hY K) := by
  classical
  obtain ⟨D⟩ := finiteCoefficientSmoothAdjunctionData_exists
    ℓ pchar hp hℓ k f d j p hf hA hB φ
  let beta : chartCtfCompact A j p D.hFA ⋙ chartCtfScalar φ Y D.hSY ≅
      chartCtfScalar φ X D.hSX ⋙ chartCtfCompact B j p D.hFB :=
    NatIso.ofComponents
      (fun M ↦ by
        have := D.hbAll M
        exact (chartCtf Y B).isoMk
          (asIso ((chartCompactScalarComparison φ j p).app M.obj)))
      (by
        intro M N g
        apply ObjectProperty.hom_ext
        exact (chartCompactScalarComparison φ j p).naturality g.hom)
  obtain ⟨c, hc, hu⟩ := smoothMate_existsUnique D.adjA D.adjB
    (chartCtfScalar φ X D.hSX) (chartCtfScalar φ Y D.hSY) beta
  have hc' : ∀ K : chartCtfCategory Y A,
      (chartCompact B j p).map (c.app K).hom ≫
          (D.adjB.counit.app ((chartCtfScalar φ Y D.hSY).obj K)).hom =
        @inv _ _ _ _ ((chartCompactScalarComparison φ j p).app (D.GA.obj K).obj)
            (D.hb K) ≫
          (chartScalar φ Y).map (D.adjA.counit.app K).hom := by
    intro K
    exact congrArg ((chartCtf Y B).ι.map) (hc K)
  have hprop := finiteCoefficientSmoothComparison_of_counit
    ℓ pchar hp hℓ k f d j p hf hA hB φ D c hc'
  refine ⟨D.hFA, D.hFB, D.hSX, D.hSY, D.GA, D.GB, D.adjA, D.adjB,
    D.RA, D.RB, D.hb, c, hprop, ?_⟩
  intro c' hc''
  apply hu c'
  intro K
  apply ObjectProperty.hom_ext
  exact hc''.1 K

end AlgebraicGeometry.ProEtale
