/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassDiagonal

/-! # Supported coefficient extension in prescribed diagonal geometry -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.SpTowerClasses
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Ordinary supported reduction, followed by scalar extension, identifies with
exact direct image for the supplied diagonal geometry and its coefficient unit.

Source: latest blueprint classes proof (3), steps 11--12 of
`lem-sp-prescribed-projective-class-package`.
(blueprint: lem-sp-tower-class-supported-scalar-push-comparison).

Proof: the ordinary reduction adjunction unit is the cokernel of the variable
prime-power endomorphism of the supported integer tower. Exact closed direct
image preserves these cokernels, so their quotient is the supported residue
coefficient tower with its actual quotient transitions. An integral basis for
the coefficient extension reduces to one compatible finite basis at every
level. In this basis scalar extension and supported direct image are the same
finite sum, and the canonical tensor/direct-image map sends each tensor to its
identical coefficient section. This proves invertibility of the universal
scalar counit on this supported module and of the ordinary comparison.
Transpose the constant-coefficient restriction through the supplied geometric
adjunction, using p. Its normalization gives precisely the same residue map
on each chart. The ordinary transition equation makes these maps a system
map, not independent level maps. Exact closed pushforward localizes to its
canonical total right derived functor. The representative transpose identities
for reduction, scalar extension and geometry carry the reduced supported unit
to the specified geometric unit on whole systems, giving the final equation.
The empty scheme and the n=0 level obey these same universal properties. -/
theorem exists_supportedScalarPushComparison
    {b : SpTowerShriek.Base l E} (S : Scheme.{u}) [IsNoetherian S]
    (c : Chern l E (diagonalSurface S)) (hc : c.Normalized l E)
    (g : SpTowerShriek.Geometry l E b (diagonalImmersion S))
    (p : CoefficientPullback l E b (diagonalImmersion S) g)
    (a : c.reduction.derived.obj
        ((DerivedCategory.singleFunctor (Ab (diagonalSurface S)) 0).obj
          ((constant (diagonalSurface S)).obj (diagonalIntegralSource S))) ≅
      (DerivedCategory.singleFunctor (Systems (diagonalSurface S)
        (Rrings l (diagonalSurface S))) 0).obj
        (c.reduction.ordinary.obj
          ((constant (diagonalSurface S)).obj (diagonalIntegralSource S))))
    (ha : c.reduction.model.sourceNormalization a
      (c.reduction.model.adjunction.unit.app
        ((constant (diagonalSurface S)).obj (diagonalIntegralSource S)))) :
    ∃ s : c.scalar.T.obj
        ((DerivedCategory.singleFunctor (Systems (diagonalSurface S)
          (Rrings l (diagonalSurface S))) 0).obj
          (c.reduction.ordinary.obj
            ((constant (diagonalSurface S)).obj (diagonalIntegralSource S)))) ≅
        (SpTowerShriek.push l E b g).obj
          (unit (ProjectiveLine S) (Arings l E (ProjectiveLine S))),
      diagonalExtendedUnit l E c ≫ (c.scalar.T.map a.hom ≫ s.hom) = unitArrow l E p := by
  sorry

end AlgebraicGeometry.ProEtale.SpTowerClasses
