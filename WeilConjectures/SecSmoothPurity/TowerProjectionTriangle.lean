/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompositeProjectionCoefficients
public import WeilConjectures.Compactification.Triangle

/-! # Projection compatibility on an induced ell-power tower triangle

Source: Stacks Project, Tags 0F7J and 0B56, the compatible triangle calculation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale.SpTowerProjectionTriangle
open CompositeProjectionCoefficients

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (D : WeilConjectures.FiniteFieldDatum.{u})
  (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
  (q : SpTowerCalculus.Coordinates l E b)
  (z : SpTowerCalculus.FiniteCoordinates l E)
  (pres : SpTowerCalculus.Preservation l E D.k b o q)
  (cal : SpTowerCalculus.Calculus l E D.k b o q z pres)
  {X Y Z : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))] [Z.Over (Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))] [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))]
  [IsSeparated (Y ↘ Spec (.of D.k))] [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
  [QuasiCompact (Y ↘ Spec (.of D.k))]
  [IsSeparated (Z ↘ Spec (.of D.k))] [LocallyOfFiniteType (Z ↘ Spec (.of D.k))]
  [QuasiCompact (Z ↘ Spec (.of D.k))]
  (f : X ⟶ Y) (g : Y ⟶ Z)
  [f.IsOver (Spec (.of D.k))] [g.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]

/-- Projection compatibility on the specific cartesian triangle induced by `cg` and
`ce`. No arbitrary source or composite compactification is allowed in this lemma.
Source: Stacks 0F7J, compatible compactification triangle, and 0B56, counit projection
(blueprint: lem-sp-tower-projection-triangle).

Proof: write the cartesian square as `p b = i q`, and expand each projection into
its proper counit projection followed by its open tensor map. The arbitrary-ring-system
clopen tensor square and the tensor-square mate transfer intertwine the proper/open
mate with these two factors. Whisker that square by the outside proper image and the
inside open extension. Naturality moves the first open tensor factor across the mate.
The proper projection composition identity contracts the two proper projections.
Full faithfulness of open extension and identity-on-open normalization contract the
two open tensor factors. Proper and open composition and pullback associativity then
identify the resulting word with the displayed composite projection. Use the
proper/open normalization of the supplied calculus on this induced triangle to identify
its compositor with this word. All calculations precede finite evaluation.
-/
theorem projection_triangle (_hl : l ≠ D.p)
    (cg : Compactification g) (ce : Compactification (f ≫ cg.i))
    (M : SpTowerShriek.D l E X) (L : SpTowerShriek.D l E Z)
    (hM : towerCtf l E b q X M)
    (hML : towerCtf l E b q X ((SpTowerShriek.tensor l E b X).obj
      (M, (SpTowerShriek.pull l E b (o.geometry f)).obj
        ((SpTowerShriek.pull l E b (o.geometry g)).obj L)))) :
    SpTowerShriek.projection l E b o cg ((SpTowerShriek.F l E b o ce.restrict).obj M) L ≫
        (SpTowerShriek.F l E b o cg).map
          (SpTowerShriek.projection l E b o ce.restrict M
            ((SpTowerShriek.pull l E b (o.geometry g)).obj L)) ≫
        towerCompositor l E D b o q z pres cal f g ce.restrict cg (cg.comp ce) _ hML =
      (SpTowerShriek.tensor l E b Z).map
          (Prod.mkHom
            (towerCompositor l E D b o q z pres cal f g ce.restrict cg (cg.comp ce) M hM)
            (𝟙 L)) ≫
        SpTowerShriek.projection l E b o (cg.comp ce) M L ≫
        (SpTowerShriek.F l E b o (cg.comp ce)).map
          ((SpTowerShriek.tensor l E b X).map
            (Prod.mkHom (𝟙 M) ((o.comp f g).inv.app L))) := by
  sorry

end AlgebraicGeometry.ProEtale.SpTowerProjectionTriangle
