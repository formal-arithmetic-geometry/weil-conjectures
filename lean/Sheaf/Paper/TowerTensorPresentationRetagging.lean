/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P4
-/
module

public import Sheaf.Paper.TowerGeometricPurityData

/-! # Independence of the actual tower tensor transpose from its normalized model

Source: latest equivariance proof Step 1 and the tensor-transpose retagging argument.
(blueprint: lem-pur-tower-tensor-presentation-retagging).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local irreducible] AlgebraicGeometry.ProEtale.SpGeometricPurity.exchange
  AlgebraicGeometry.ProEtale.SpGeometricPurity.mate
  AlgebraicGeometry.ProEtale.SpGeometricPurity.pullRealization

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry.Scheme WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpGeometricPurity

/-- The inverse-projection/counit map and its Hom transpose are unchanged by a
counit-preserving change of right adjoint, for the two supplied normalized tensor
models. This does not assert the orientation comparison or a purity square.
Source: equivariance Step 1, tensor-transpose ground-field retagging.
(blueprint: lem-pur-tower-tensor-presentation-retagging).

Proof:
1. The tensor-retagging theorem with identity field automorphism and the same
factorization supplies the two equations for a normalized tensor model. Its right
adjoint comparison is adjgamma.rightAdjointUniq adj.
2. For the fixed closed adjunction, models.uncurry_model fixes the representative
comparison: transpose both candidates and compute their componentwise pure-tensor
evaluation. Injectivity of the Hom bijection makes the comparisons equal. On flat
K-flat representatives both symmetries are signed interchange and both unitors are
scalar multiplication. Cancel these representative comparisons and use full
faithfulness of restriction to representatives (cochain tensor model rigidity).
Thus the symmetry and coefficient unit constraints used by projectionCounit agree
for the actual a.tensorX,a.tensorY and the second presentation's tensor data.
3. Substitute these constraint identities into the tensor-retagging projectionCounit
equation. Membership and invertibility witnesses are proof irrelevant. This proves
the first equation below with the given tensor models.
4. Realize the two candidate tensorMate maps and take their adjunction transposes.
The first equation and counit preservation identify these transposes, so the Hom
bijection and the faithful realization identify the original maps. This gives the
second equation on whole towers, with no finite-evaluation faithfulness assertion.
The argument includes empty schemes, d=0 and arbitrary normalized model choices. -/
theorem tensor_presentation_retagging
    (S : PurityFiniteSetting.{u})
    (b : SpTowerShriek.Base S.coefficients.l S.extension)
    (o : SpTowerShriek.Operations S.coefficients.l S.extension b)
    (q : SpTowerCalculus.Coordinates S.coefficients.l S.extension b)
    {X Z Y : AlgebraicGeometry.Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
  (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y) [IsProper p]
  [QuasiCompact (j ≫ p)] [HasCompactification (j ≫ p)]
  (d : ℕ) (w : SpChartAdmissibility.Twists S.coefficients.l S.extension X)
  (hF : ∀ K : SpTowerCalculus.C S.coefficients.l S.extension b q X,
    spConstructibleTorTowers S.coefficients.l S.extension Y (q.abelian Y)
      ((SpTowerCalculus.F S.coefficients.l S.extension b o q (SpTowerGamma.factorization j p)).obj
        K.obj))
  (G : SpTowerCalculus.C S.coefficients.l S.extension b q Y ⥤ SpTowerCalculus.C S.coefficients.l
    S.extension b q X)
  (adj : SpTowerGluing.support S.coefficients.l S.extension b o q (SpTowerGamma.factorization j p)
    hF ⊣ G)
  (lv : SpTowerGluing.Levels S.coefficients.l S.extension b o q (SpTowerGamma.factorization j p) hF
    G adj)
  (a : SpTowerGamma.Purity S.coefficients.l S.extension b o q j p d w hF G adj lv)
  [AlgebraicGeometry.Scheme.Over X (Spec (.of S.field.k))]
  [AlgebraicGeometry.Scheme.Over Y (Spec (.of S.field.k))]
  [hSX : IsSeparated (X ↘ Spec (.of S.field.k))]
  [hTX : LocallyOfFiniteType (X ↘ Spec (.of S.field.k))] [hCX : QuasiCompact (X ↘ Spec (.of
    S.field.k))]
  [hSY : IsSeparated (Y ↘ Spec (.of S.field.k))]
  [hTY : LocallyOfFiniteType (Y ↘ Spec (.of S.field.k))] [hCY : QuasiCompact (Y ↘ Spec (.of
    S.field.k))]
  [hOver : (j ≫ p).IsOver (Spec (.of S.field.k))] [hsm : SmoothOfRelativeDimension d (j ≫ p)] :
    ∀ (Gγ : SpTowerCalculus.C S.coefficients.l S.extension b q Y ⥤ SpTowerCalculus.C
      S.coefficients.l S.extension b q X)
    (adjγ : SpTowerGluing.support S.coefficients.l S.extension b o q (SpTowerGamma.factorization j
      p) hF ⊣ Gγ)
    (lvγ : SpTowerGluing.Levels S.coefficients.l S.extension b o q (SpTowerGamma.factorization j p)
      hF Gγ adjγ)
    (aγ : SpTowerGamma.Purity S.coefficients.l S.extension b o q j p d w hF Gγ adjγ lvγ),
    ∀ K : SpTowerCalculus.C S.coefficients.l S.extension b q Y,
      (SpTowerShriek.F S.coefficients.l S.extension b o (SpTowerGamma.factorization j p)).map
          ((SpTowerShriek.tensor S.coefficients.l S.extension b X).map (Prod.mkHom (𝟙 _)
            ((SpTowerGamma.realization S.coefficients.l S.extension b q X).map
              ((adjγ.rightAdjointUniq adj).hom.app
                ⟨SpTowerGamma.originalUnit S.coefficients.l S.extension b q Y, a.unit_mem⟩)))) ≫
        SpTowerGamma.projectionCounit S.coefficients.l S.extension b o q (SpTowerGamma.factorization
          j p)
          a.tensorX a.tensorY hF G adj a.unit_mem K (a.projection_iso K) =
        SpTowerGamma.projectionCounit S.coefficients.l S.extension b o q (SpTowerGamma.factorization
          j p)
          aγ.tensorX aγ.tensorY hF Gγ adjγ aγ.unit_mem K (aγ.projection_iso K) ∧
      (SpTowerShriek.tensor S.coefficients.l S.extension b X).map (Prod.mkHom (𝟙 _)
          ((SpTowerGamma.realization S.coefficients.l S.extension b q X).map
            ((adjγ.rightAdjointUniq adj).hom.app
              ⟨SpTowerGamma.originalUnit S.coefficients.l S.extension b q Y, a.unit_mem⟩))) ≫
        SpTowerGamma.tensorMate S.coefficients.l S.extension b o q (SpTowerGamma.factorization j p)
          a.tensorX a.tensorY hF G adj a.unit_mem K (a.tensor_mem K)
            (a.projection_iso K) =
        SpTowerGamma.tensorMate S.coefficients.l S.extension b o q (SpTowerGamma.factorization j p)
          aγ.tensorX aγ.tensorY hF Gγ adjγ aγ.unit_mem K (aγ.tensor_mem K)
            (aγ.projection_iso K) ≫
          (SpTowerGamma.realization S.coefficients.l S.extension b q X).map
            ((adjγ.rightAdjointUniq adj).hom.app K) := by
  sorry

end AlgebraicGeometry.ProEtale.SpGeometricPurity
