/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerProjectionRefinement.TowerProjectionRefinementCoordinate

/-! # C-level proper/open mate square

The proper/open mate is stated on constructible coefficient objects.  The
support comparison is the conjugate of `cal.composition.refinement` by the
support-realization isomorphisms.
The equation uses the coefficient tensor, the C-level compact-support
functor and the supplied refinement components directly. (blueprint:
lem-sp-tower-projection-refinement-mate)
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
  (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (c c' : Compactification f)

/-- Refinement commutes with projection in the coefficient category.

Source: Stacks 0F7J, proper-refinement step, and 0B56, projection-formula map.
(blueprint: lem-sp-tower-projection-refinement-mate)

Expand the coefficient projection into the proper counit transpose and the open
projection mate. Apply proper/open mate pasting and the clopen tensor square,
then transfer the square across the tensor adjunction. The finite compact-site
and constructible-origin comparisons identify its refinement maps with the
finite evaluations of `cal.composition.refinement`; refinement coherence pastes
the comparisons in the coefficient category. No realization-conjugation or
transport along an arbitrary tensor-target isomorphism is part of this lemma.
-/
theorem proper_open_mate_C
    (_hl : l ≠ D.p) (K : SpTowerCalculus.C l E b q X)
    (L : SpTowerShriek.D l E Y)
    (hT : spConstructibleTorTowers l E X (q.abelian X)
      ((coefficientTensorPull l E b o q f L).obj K.obj)) :
    (coefficientTensor l E b q Y L).map
        ((cal.composition.refinement f c c').hom.app K) ≫
      coefficientProjection l E b o q c' K.obj L =
    coefficientProjection l E b o q c K.obj L ≫
      (cal.composition.refinement f c c').hom.app
        ⟨(coefficientTensorPull l E b o q f L).obj K.obj, hT⟩ := by
  sorry

end AlgebraicGeometry.ProEtale.SpTowerProjectionRefinement
