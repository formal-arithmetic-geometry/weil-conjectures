/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralDirectImageTower.IntegralDirectImageTowerData

/-! # Normalized limit coordinates for the two projection factors

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-sp-grp-ladic-summary/sec-towers-and-integral-coefficients/
sk-prop-sp-integral-adjunction/sk-prop-sp-integral-adjunction-direct-image.proof.md,
paragraph (3) (blueprint: lem-sp-integral-projection-tower-limit-coordinates).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.IntegralDirectImageTower

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The actual proper/open projection factors are total limits of their whole-system
mates in the normalized scalar and completion coordinates. This statement constructs
coordinates and proves equalities of specified maps; it asserts no invertibility of
the proper system projection.

Source: the current direct-image proof, paragraph (3), tensor reductions and descent
(blueprint: lem-sp-integral-projection-tower-limit-coordinates).

Proof: take flat-term K-flat representatives and form signed total tensors. The
quotient scalar/tensor comparison sends a tensor of sections to the tensor of their
quotient augmentations. The inverse-image/scalar comparison sends the pullback unit
section to that same augmentation. These are whole sequence-site chain maps; the
quotient transitions preserve products and units, so the maps descend together to
natural isomorphisms before any level evaluation. The representative normalizations
identify their proper counit and open unit mates with the specified system maps.
Use the supplied whole-tower compact-support comparison at M. Together with the
tensor and pullback comparisons it gives the three displayed coordinate isomorphisms.
The two integral endpoints are constructible by hypothesis. The middle object is
isomorphic to the input endpoint by the exact open unit-transpose tensor comparison.
Thus the normalized reduction/limit equivalence makes their actual units invertible.
Prove the proper and open scalar/projection squares separately on representatives.
Their composite is the square used in complete_projection_mate_descent. Apply the same
actual-unit naturality calculation to each factor to obtain the two displayed formulas. The uniform
finite-Tor constructibility assertions are exactly those of the current reduction
theorem; over a general field use the smooth-purity general-field descent inside the
proof, without imposing a hypothesis on k. No integral proper projection formula is
used and no morphism equality is inferred from finite derived evaluations. Zero
inputs, ramified extensions and empty schemes use the same normalized maps. -/
theorem integral_projection_tower_limit_coordinates
    (s : Presentation l E) (q : ReductionGeometry l E s)
    (hq : OpenReductionIsIso l E s q) (L : ∀ T : Scheme.{u}, Limit l E s T)
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
    (X Y : Scheme.{u}) [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] (c : Compactification f)
    (_v : CanonicalTowerComparison l E s q hq c)
    (M : Constructible l E X) (K : Constructible l E Y)
    (_hU : constantModelBoundedConstructible (spIntegralCondensed l E) Y
      ((shriek l E c).obj (((tensor l E X).obj M.obj).obj ((pull l E f).obj K.obj))))
    (_hV : constantModelBoundedConstructible (spIntegralCondensed l E) Y
      (((tensor l E Y).obj ((shriek l E c).obj M.obj)).obj K.obj)) :
    let C := (realization l E s X).functor.obj ((red l E s X).obj M.obj)
    let B := (realization l E s Y).functor.obj ((red l E s Y).obj K.obj)
    let R := red l E s Y ⋙ (realization l E s Y).functor
    let W := (realization l E s Y).inverse ⋙ lim l E s Y (L Y)
    let adj := (redLimitAdjunction l E s Y (L Y)).comp
      (realization l E s Y).toAdjunction
    let U := (shriek l E c).obj
      (((tensor l E X).obj M.obj).obj ((pull l E f).obj K.obj))
    let V := ((tensor l E Y).obj ((shriek l E c).obj M.obj)).obj K.obj
    let H := projectionMiddle l E c M.obj K.obj
    SpTowerProjection.constructibleTor l E s.base X (s.towers X) C ∧
    SpTowerProjection.constructibleTor l E s.base Y (s.towers Y) B ∧
    ∃ (eU : U ≅ W.obj (R.obj U)) (eV : V ≅ W.obj (R.obj V))
      (eH : H ≅ W.obj (R.obj H))
      (a : R.obj V ≅ (SpTowerProjection.source l E s.base s.operations c).obj (C, B))
      (b : R.obj H ≅ (SpTowerProjection.middle l E s.base s.operations c).obj (C, B))
      (z : R.obj U ≅ (SpTowerProjection.openSource l E s.base s.operations c).obj (C, B)),
      eU.hom = adj.unit.app U ∧ eV.hom = adj.unit.app V ∧ eH.hom = adj.unit.app H ∧
      properProjection l E c M.obj K.obj =
        eV.hom ≫ W.map (a.hom ≫ SpTowerProjection.properMap l E s.base s.operations c C B ≫
          b.inv) ≫ eH.inv ∧
      compactOpenProjection l E c M.obj K.obj =
        eU.hom ≫ W.map (z.hom ≫ SpTowerProjection.openMap l E s.base s.operations c C B ≫
          b.inv) ≫ eH.inv := by
  sorry

end AlgebraicGeometry.ProEtale.IntegralDirectImageTower
