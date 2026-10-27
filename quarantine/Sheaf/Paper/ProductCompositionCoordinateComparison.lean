/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B6
-/
module

public import Sheaf.Paper.ProductExchangeCoordinateDefinitions

/-! # Composition comparison in product compactifications

Source: Stacks 0F7J and the compatible-tower construction of compact-support composition
(blueprint: lem-pur-product-composition-coordinate-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.ProductExchangeCoordinates

/-- Transport the canonical tower formula to the explicit product compactifications.
Source: Stacks 0F7J, compatible tower; product-coordinate node Step 8
(blueprint: lem-pur-product-composition-coordinate-comparison).

Proof: use the tower with h=pullback.snd f g, d=cg and upper compactification
whose open is (cf.baseChange g).i followed by i cf cg and whose proper part is
pullback.snd cf.g cg.g. Its restriction along cg.i is canonically isomorphic
to cf.baseChange g by the Cartesian square square cf cg. The unique
projection-preserving isomorphism identifies the tower comparisons with the
canonical candidate comparisons in alpha. On a bounded-below etale input apply
proEtaleCompositionTowerNormalization (or its equality-only tower formula).
The open-adjunction normalization identifies towerGamma with properOpenMate:
restriction is rho, and the remaining factor is inverse open unit. Canonical
composition of exact open adjunctions identifies the final open compositor with
properOpenShriekComp. Direct-image composition is finiteDirectImageComposition
by its defining right-derived comparison. These identifications give the equality
on pullback of the etale antecedent. For a general etale-origin object, choose its
retained antecedent and isomorphism, apply naturality of both composites, and
cancel the isomorphism. The predicate is propositional, so this argument does
not choose new data in the definitions. -/
theorem productCompositionCoordinateComparison
    {B X Z : Scheme.{u}} {f : X ⟶ B} {g : Z ⟶ B}
    [IsNoetherian B] [IsNoetherian X] [IsNoetherian Z]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (cf : Compactification f) (cg : Compactification g)
    (A : Type u) [CommRing A] [Finite A]
    (Q : ProperOpenDerived (ULift.{u + 1} A) (pullback f g))
    (hQ : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} A))
      (pullback f g) Q) :
    alpha cf cg A Q hQ = compositionRoute cf cg A Q := by sorry

end AlgebraicGeometry.ProEtale.ProductExchangeCoordinates
