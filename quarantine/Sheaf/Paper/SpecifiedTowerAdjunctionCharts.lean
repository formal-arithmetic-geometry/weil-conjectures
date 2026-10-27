/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J3
-/
module

public import Sheaf.Paper.TransportIntegralCounitData

/-! # Charts for a specified tower adjunction

Source: tower-gluing clauses (1)--(2), compactification and representing-pair uniqueness.
(blueprint: lem-pur-specified-tower-adjunction-charts). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
attribute [local irreducible] HasDerivedCategory.standard
  WeilConjectures.integralCompletedTensor WeilConjectures.integralDerivedPullback

-- Keep the canonical small-site sheafification instance ahead of generic alternatives.
attribute [local instance high]
  CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures

namespace AlgebraicGeometry.ProEtale.TransportIntegralCounit

variable (P : PurityFiniteSetting.{u}) (D : FieldShriekSystem.Models P)
  {X Z Y : Scheme.{u}}
  [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
  [IsSeparated (X ↘ Spec (.of P.field.k))]
  [IsSeparated (Y ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
  [QuasiCompact (X ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
  [QuasiCompact (Y ↘ Spec (.of P.field.k))]
  (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y) [IsProper p]
  [(j ≫ p).IsOver (Spec (.of P.field.k))] (d : ℕ)
  [QuasiSeparatedSpace Y]

/-- The chart counit data transfer to any specified representing tower adjunction
at the fixed compactification. No purity map or diagonal orientation is asserted here.
Source: latest blueprint, tower-geometric-gluing, Local pairs and uniqueness.
(blueprint: lem-pur-specified-tower-adjunction-charts).

Proof: apply tower_gluing to the canonical compactification. Keep its finite
coordinates, geometric calculus, normalized coordinate chart pairs, and open properties.
The compact-support compactification comparison in that calculus identifies its left
functor with the functor of the specified compactification, also after every open
restriction. Transport the gluing adjunction along this left comparison and use
right-adjoint uniqueness to identify its right functor with m.exceptional, preserving
counits. Apply open pullback to this comparison and compose it with each original chart
comparison. The new chart counit equation follows from naturality of the open-composition
comparison and of the open adjunction counit, followed by the counit-preserving equation
for the right-adjoint comparison. The compactification coherence equations make the
chart pair indexed by (c.precomp U.ι).copy he.symm the required pair; all coordinate
normalizations were retained. Zero-dimensional charts use the identity integration,
and the empty scheme uses the zero representing pair. -/
theorem specified_tower_adjunction_charts (E : FieldShriekSystem.Index P)
    (m : FieldExtensionTowers.IntegralModel P D E j p d)
    [IsNoetherian X] [IsNoetherian Y]
    [SmoothOfRelativeDimension d (j ≫ p)] :
    Nonempty (SpTowerGluing.Charts P.coefficients.l E.val (D.base E) (D.operations E)
      (D.coordinates E) P.field.k (X.asOver (Spec (.of P.field.k)))
      (Y.asOver (Spec (.of P.field.k)))
      ⟨‹IsSeparated (Y ↘ Spec (.of P.field.k))›,
        ‹LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))›,
        ‹QuasiCompact (Y ↘ Spec (.of P.field.k))›⟩
      ((j ≫ p).asOver (Spec (.of P.field.k))) d (SpTowerGamma.factorization j p)
      m.supportClosed m.exceptional m.adjunction) := by sorry

end AlgebraicGeometry.ProEtale.TransportIntegralCounit
