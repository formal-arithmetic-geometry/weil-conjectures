/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B5
-/
module

public import Sheaf.SixFunctors.ListedCoefficientMaps
public import Sheaf.Paper.LocalizingAdmissibleCoefficients
public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.Paper.ConstantModelTorAmplitude

/-! # Admissibility and scalar preservation for the listed coefficient presentations

Source: blueprint latest, scalar-six coefficient list and
`det-prop-scalar-six-direct-image.proof.md`, Preservation.
(blueprint: lem-sfb-listed-coefficient-ctf).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory
  HasDerivedCategory.ofHasKInjectiveResolutions HasDerivedCategory.standard
  scalarSixChange


/-- The endpoints of a listed map are admissible, and its actual scalar-change
functor preserves bounded constructible objects of finite Tor amplitude.

Source: blueprint latest, scalar-six coefficient list (1)--(4),
`det-prop-scalar-six-ctf` (3), and direct-image proof, Preservation.
(blueprint: lem-sfb-listed-coefficient-ctf).

Proof: Induct on ListedCoefficientMap. For finite endpoints choose finite rings
in Type 0 isomorphic to the given rings, equip them with the discrete topology,
and use constant-to-continuous finite coefficient comparison. The pointwise
normalization of the map identifies it with postcomposition by its ring map.
For integral-to-finite maps use the continuous ring map in the definition;
for integral and field maps use their specified equality with postcomposition.
These identifications give the elementary maps in IsListedScalarCoefficientMap,
up to the displayed ring-object isomorphisms. Apply scalarSixCtf (3), transporting
finite constant presentations, boundedness and Tor tests along the exact scalar
equivalences. The endpoints satisfy the corresponding disjuncts of
IsLocalizingAdmissibleCoefficient. The algebraic-closure identity preserves the
subcategory by the scalar unit isomorphism; its endpoint is the last disjunct.
For a composite retain the outer endpoint assertions from the induction hypotheses,
apply scalar preservation twice and transport along scalarSixTower. This also
covers the zero finite ring: its module category is zero and the same comparisons
and finite presentations apply. No flatness of a finite ring map is used. -/
theorem listedCoefficientCtf (ell : ℕ) [Fact ell.Prime]
    {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ') (ha : ListedCoefficientMap ell a) :
    IsLocalizingAdmissibleCoefficient ell Λ.X ∧
    IsLocalizingAdmissibleCoefficient ell Λ'.X ∧
    (∀ (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
      (X : Over (Spec (.of k)))
      [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
      (K : DerivedCategory (ModuleRingedComparison.internalModules Λ.X X.left)),
      (constantModelBoundedConstructible Λ.X X.left K ∧
        DerivedCategory.finiteTorAmplitude _ K) →
      constantModelBoundedConstructible Λ'.X X.left ((scalarSixChange a X.left).obj K) ∧
        DerivedCategory.finiteTorAmplitude _ ((scalarSixChange a X.left).obj K)) := by sorry

end AlgebraicGeometry.ProEtale.CondensedRing
