/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P4
-/
module

public import Sheaf.Paper.TowerGeometricPurityData
import Sheaf.Paper.OrientationGroundFieldRetagging
import Sheaf.Paper.TowerTensorPresentationRetagging

/-! # Retagging normalized tower purity presentations

Source: latest blueprint equivariance of purity and trace, Steps 1 and 5.
(blueprint: lem-pur-tower-purity-presentation-retagging).
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
/-- The whole orientation and actual inverse-projection/counit transpose agree under
the counit-preserving comparison of two presentations of the same compactification.
Source: equivariance Step 1, retagging of the orientation and the tensor transpose.
(blueprint: lem-pur-tower-purity-presentation-retagging).

Proof:
1. Apply orientation_ground_field_retagging with the identity ground-field
automorphism, the two displayed structural maps, and the same factorization j,p.
Its quantified second presentation is arbitrary. Faithfulness of the inverse
realization removes that functor from its orientation equation.
2. Apply tensor_transpose_ground_field_retagging to the same compactification and
two right adjoints. Its counit-preserving comparison is adjgamma.rightAdjointUniq adj.
The apparent choice of normalized tensor presentation does not affect these maps:
on K-flat representatives every signed symmetry is the same signed interchange,
and every coefficient unitor is scalar multiplication. The fixed closed adjunction and
  models.uncurry_model fix its representative
comparison: transpose both candidates and use the same componentwise pure-tensor
evaluation, then injectivity of the Hom bijection. The representative equations
of TensorData therefore determine these constraints; cancel the localization comparisons.
Thus its projectionCounit equation applies to a.tensorX,a.tensorY and to the second
presentation's tensor data, with the proof-irrelevant membership and IsIso witnesses.
3. The same independence applies to tensorMate. Alternatively realize its two
adjunction transposes, use the equality from step 2, and use injectivity of the
representing Hom bijection. These give precisely the two quantified equalities in
Retagging. The argument includes arbitrary finite-level presentations, d=0 and empty
schemes, and takes place on whole towers before any finite evaluation. -/
theorem purity_presentation_retagging
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
    Retagging S.coefficients.l S.extension b o q j p d w hF G adj lv a := by
  unfold Retagging
  intro Gγ adjγ lvγ aγ
  constructor
  · apply (SpTowerCalculus.realization S.coefficients.l S.extension b X
      (q.abelian X)).inverse.map_injective
    have h := S.orientation_ground_field_retagging
      (AlgEquiv.refl : S.field.k ≃ₐ[S.field.k₀] S.field.k)
      (X ↘ Spec (.of S.field.k)) (Y ↘ Spec (.of S.field.k)) d (j ≫ p)
      ((AlgebraicGeometry.Scheme.Hom.isOver_iff (Spec (.of S.field.k))).mp inferInstance)
    dsimp only [WeilConjectures.PurityFiniteSetting.OrientationGroundFieldRetaggingConclusion]
      at h
    exact h.2 b o q Z j p rfl w hF Gγ G adjγ adj lvγ lv aγ a
  · exact tensor_presentation_retagging S b o q j p d w hF G adj lv a Gγ adjγ lvγ aγ

end AlgebraicGeometry.ProEtale.SpGeometricPurity
