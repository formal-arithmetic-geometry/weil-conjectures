/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompositeProjectionCoefficients

/-! # Refinement comparisons and the tower projection

Source: Stacks Project, Tags 0F7J and 0B56, the proper-refinement projection square.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale.SpTowerProjectionRefinement
open CompositeProjectionCoefficients

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Transport a specified strict-coordinate compact-support comparison through the
fixed section realizations. All factors are given natural isomorphisms.
Source: the realization coordinate formula of the tower shriek calculus
(blueprint: lem-sp-tower-projection-refinement). -/
def supportComparison (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (q : SpTowerCalculus.Coordinates l E b) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c c' : Compactification f)
    (r : SpTowerCalculus.inclusion l E b q X ⋙ SpTowerCalculus.F l E b o q c ≅
      SpTowerCalculus.inclusion l E b q X ⋙ SpTowerCalculus.F l E b o q c')
    (K : SpTowerShriek.D l E X) (hK : towerCtf l E b q X K) :
    (SpTowerShriek.F l E b o c).obj K ≅ (SpTowerShriek.F l E b o c').obj K :=
  (SpTowerShriek.F l E b o c).mapIso
      ((SpTowerCalculus.realization l E b X (q.abelian X)).counitIso.app K).symm ≪≫
    ((SpCoordinateAdjunction.supportRealization l E b o q c).app
      ((SpTowerCalculus.realization l E b X (q.abelian X)).inverse.obj K)).symm ≪≫
    (SpTowerCalculus.realization l E b Y (q.abelian Y)).functor.mapIso
      (r.app ⟨(SpTowerCalculus.realization l E b X (q.abelian X)).inverse.obj K, hK⟩) ≪≫
    (SpCoordinateAdjunction.supportRealization l E b o q c').app
      ((SpTowerCalculus.realization l E b X (q.abelian X)).inverse.obj K) ≪≫
    (SpTowerShriek.F l E b o c').mapIso
      ((SpTowerCalculus.realization l E b X (q.abelian X)).counitIso.app K)

variable (D : WeilConjectures.FiniteFieldDatum.{u})
  (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
  (q : SpTowerCalculus.Coordinates l E b)
  (z : SpTowerCalculus.FiniteCoordinates l E)
  (pres : SpTowerCalculus.Preservation l E D.k b o q)
  (cal : SpTowerCalculus.Calculus l E D.k b o q z pres)
  {X Y : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))] [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))]
  [IsSeparated (Y ↘ Spec (.of D.k))] [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
  [QuasiCompact (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y)
  [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (c c' : Compactification f)

/-- The canonical compactification comparison commutes with the projection for one
map, before finite evaluation. This is the proper-refinement square, and makes no
assertion about a binary compact-support compositor.
Source: Stacks 0F7J, common refinements, and 0B56, projection-formula map
(blueprint: lem-sp-tower-projection-refinement).

Proof: for a proper refinement, use the arbitrary-ring-sequence clopen tensor square
and tensor-square mate transfer with the identity on the source. Proper projection
for the identity is the identity; proper projection composition and naturality give
the refinement square. Finite constructible origins and the finite etale/pro-etale
comparison show the evaluated refinement maps invertible. Conservativity detects
invertibility of the tower maps. Apply the square to a common refinement of c and c',
and cancel its two inverse comparisons. The refinement coherence of the recorded
calculus and the fixed realization counits identify the resulting comparison with
supportComparison. This calculation is in the ordinary tower category; evaluation
is used only to detect invertibility. Finally transport the codomain through the
specified isomorphism t by naturality. This permits a fixed pullback-composition
coordinate without a separate constructibility witness for the isomorphic object.
-/
theorem projection_refinement (_hl : l ≠ D.p)
    (M : SpTowerShriek.D l E X) (L : SpTowerShriek.D l E Y)
    (hM : towerCtf l E b q X M)
    (N : SpTowerShriek.D l E X) (hN : towerCtf l E b q X N)
    (t : (SpTowerShriek.tensor l E b X).obj
      (M, (SpTowerShriek.pull l E b (o.geometry f)).obj L) ≅ N) :
    (SpTowerShriek.tensor l E b Y).map
        (Prod.mkHom (supportComparison l E b o q c c'
          (cal.composition.refinement f c c') M hM).hom (𝟙 L)) ≫
      SpTowerShriek.projection l E b o c' M L ≫
      (SpTowerShriek.F l E b o c').map t.hom =
    SpTowerShriek.projection l E b o c M L ≫ (SpTowerShriek.F l E b o c).map t.hom ≫
      (supportComparison l E b o q c c' (cal.composition.refinement f c c') N hN).hom := by
  sorry

end AlgebraicGeometry.ProEtale.SpTowerProjectionRefinement
