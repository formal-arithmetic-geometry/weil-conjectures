/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P4
-/
module

public import Sheaf.Paper.TowerGeometricPurityData

/-! # The two semilinear tower purity factors

Source: latest blueprint equivariance of purity and trace, Steps 1 and 5.
(blueprint: lem-pur-tower-semilinear-purity-factors).
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
/-- The compact-support exchange is invertible; its exact counit mate intertwines
separately the whole orientation and the actual tensor transpose. The comparison u
is the unit exceptional exchange. Its displayed orientation equation determines it
uniquely, since pullback of the orientation is invertible.
Source: purity-bc-factors (1)--(2), specialized as in equivariance Step 1.
(blueprint: lem-pur-tower-semilinear-purity-factors).

Proof:
1. Give the source copies of X,Y the structural maps gX followed by aX and gY
followed by aY. The displayed Cartesian equation makes f linear for these maps and
gX,gY linear to the original copies. Isomorphisms preserve the finite-type and
separated hypotheses; the underlying smooth morphism and dimension are unchanged.
2. Apply tower exceptional base change. Its proper/open compact-support comparison,
followed by the canonical refinement from the pulled-back compactification to the
original one, is exchange. Its invertibility also follows by restricting
laws.exchange_iso and composing with the invertible refinement.
3. Transport the returned right adjoint to G using uniqueness of the representing
counit. Transpose the inverse compact-support comparison followed by pulled-back
counit. The two transposes agree by the counit-preserving comparison and injectivity
of adj.homEquiv, so the transported exceptional exchange is exactly mate below.
4. Apply tower_factors to the retagged linear square. Its orientation identity and
its tensor identity hold in the ordinary derived category of whole towers. Use hr
to identify the new same-compactification orientation and tensor transpose with a.
The finite root comparison agrees with the strict normalized root map t, since on
scalar/root generators both are coefficient restriction followed by root restriction.
Exact tensor and shifts give its ordered powers. This determines the twist comparison
without using Gamma to define it.
5. Let u be the unit component of the transported exceptional exchange, followed by
G of the specified coefficient-unit comparison. The orientation equation of step 4
is the first equation below. The tensor equation of that step is the second, after
combining the pullback square and u into the displayed product morphism. No assertion
about Gamma, naturality of its source comparison, normalization, or conjugation is
used in this lemma. All coefficient transitions and zero-fold units are retained. -/
theorem semilinear_purity_factors
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
  [hOver : (j ≫ p).IsOver (Spec (.of S.field.k))] [hsm : SmoothOfRelativeDimension d (j ≫ p)]
  (gX : X ⟶ X) (gY : Y ⟶ Y) [hGX : IsIso gX] [hGY : IsIso gY]
  (sq : IsPullback gX (j ≫ p) (j ≫ p) gY)
  (z : SpTowerCalculus.FiniteCoordinates S.coefficients.l S.extension)
  (h : SpTowerCalculus.Preservation S.coefficients.l S.extension S.field.k b o q)
  (cal : SpTowerCalculus.Calculus S.coefficients.l S.extension S.field.k b o q z h)
  (x : SpTowerShriek.OpenExchange S.coefficients.l S.extension b o)
  (laws : SpTowerShriek.Laws S.coefficients.l S.extension b o x)
  (hx : ∀ K : SpTowerCalculus.C S.coefficients.l S.extension b q X,
    spConstructibleTorTowers S.coefficients.l S.extension X (q.abelian X)
      ((SpTowerCalculus.etalePullback S.coefficients.l S.extension b o q gX).obj K.obj))
  (hy : ∀ K : SpTowerCalculus.C S.coefficients.l S.extension b q Y,
    spConstructibleTorTowers S.coefficients.l S.extension Y (q.abelian Y)
      ((SpTowerCalculus.etalePullback S.coefficients.l S.extension b o q gY).obj K.obj))
  (t : Roots S.coefficients.l S.extension b o gX w a.roots)
  (hr : Retagging S.coefficients.l S.extension b o q j p d w hF G adj lv a) :
    ∃ hb : IsIso (exchange S.coefficients.l S.extension b o q S.field.k (j ≫ p) gX gY sq
      (SpTowerGamma.factorization j p) z h cal x hx hy hF),
    ∃ u : (SpTowerShriek.pull S.coefficients.l S.extension b (o.geometry gX)).obj
        ((SpTowerGamma.exceptional S.coefficients.l S.extension b q G).obj
          ⟨SpTowerGamma.originalUnit S.coefficients.l S.extension b q Y, a.unit_mem⟩) ⟶
      (SpTowerGamma.exceptional S.coefficients.l S.extension b q G).obj
        ⟨SpTowerGamma.originalUnit S.coefficients.l S.extension b q Y, a.unit_mem⟩,
      (SpTowerShriek.pull S.coefficients.l S.extension b (o.geometry gX)).map a.orientation.hom ≫ u
        =
        (orderedRoots S.coefficients.l S.extension b o t d).hom ≫ a.orientation.hom ∧
      ∀ K : SpTowerCalculus.C S.coefficients.l S.extension b q Y,
        (SpTowerShriek.pull S.coefficients.l S.extension b (o.geometry gX)).map
            (SpTowerGamma.tensorMate S.coefficients.l S.extension b o q (SpTowerGamma.factorization
              j p)
              a.tensorX a.tensorY hF G adj a.unit_mem K
              (a.tensor_mem K) (a.projection_iso K)) ≫
          (pullRealization S.coefficients.l S.extension b o q gX hx (G.obj K)).inv ≫
          (SpTowerGamma.realization S.coefficients.l S.extension b q X).map
            ((mate S.coefficients.l S.extension b o q S.field.k (j ≫ p) gX gY sq
              (SpTowerGamma.factorization j p)
              z h cal x hx hy hF G adj hb).app K) =
        (o.geometry gX).tensorPullback.hom.app _ ≫
          (SpTowerShriek.tensor S.coefficients.l S.extension b X).map
            (Prod.mkHom
              (((SpTowerShriek.square S.coefficients.l S.extension b o gX (j ≫ p) (j ≫ p) gY
                sq.w).symm.app _ ≪≫
                (SpTowerShriek.pull S.coefficients.l S.extension b (o.geometry (j ≫ p))).mapIso
                  (pullRealization S.coefficients.l S.extension b o q gY hy K).symm).hom) u) ≫
          SpTowerGamma.tensorMate S.coefficients.l S.extension b o q (SpTowerGamma.factorization j
            p)
            a.tensorX a.tensorY hF G adj a.unit_mem ((P S.coefficients.l S.extension b o q gY
              hy).obj K)
            (a.tensor_mem _) (a.projection_iso _) := by
  sorry

end AlgebraicGeometry.ProEtale.SpGeometricPurity
