/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R9
-/
module

public import Sheaf.Paper.InternalScalarPullbackNormalization

/-! # Flat scalar units under the normalized tensor and section comparisons

Source: Stacks 03EK, 015F and 0FND; the scalar-unit step of the rational
proper-base-change coefficient square.
(blueprint: lem-sfb-flat-scalar-unit-normalization).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace AlgebraicGeometry.ProEtale.QuotientChange

attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.rightDerivedFunctor CategoryTheory.Functor.mapDerivedCategory
  AlgebraicGeometry.ProEtale.upperStarFromPoint
  DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed

variable {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
  (a : R ⟶ S) [IsMonHom a]
  [∀ T : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a T))]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules R T)]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules S T)]

/-- The scalar unit tensors with the specified coefficient map, and section
reconstruction preserves that same adjunction unit.

Source: Stacks 03EK, 015F and 0FND; step 2 of
lem-sfb-flat-coefficient-square-normalization.
(blueprint: lem-sfb-flat-scalar-unit-normalization).

Proof: the ordinary extension unit inserts the ring unit before the balanced
coequalizer. The prescribed ordinary tensor comparison sends s tensor m to
m tensor s, hence sends the unit to tensoring with q. Apply the termwise exact
scalar adjunction and its universal computation equation. The tensor localization
map with the flat coefficient in degree zero is invertible, so TensorNormalized
identifies the resulting derived equation with the stated tensor-unit equation.
For the section comparison, use internal scalar pullback normalization with the
identity scheme map. Its tensor presentation equals e: their ordinary maps agree
by the prescribed underlying balanced maps; their derived maps agree after
cancellation of the invertible flat-coefficient tensor localization map.
The section scalar comparison is normalized by its local generators and the
universal derived computation maps. The ordinary comparison preserves units on
generators. Derive this equality on flat-term K-flat models, using the normalized
Hom transposes of internal_section_scalar_adjunction. Resolve arbitrary complexes
and cancel the localized quasi-isomorphisms to obtain the displayed unit identity.
For identity coefficients, zero target ring and empty schemes these are the same
unit and balancing equations; no nonzero coefficient or boundedness is used. -/
theorem flat_scalar_unit_normalization (T : Scheme.{u})
    (e : TensorNormalization a T) (he : TensorNormalized a T e)
    (q : Mod.regular (condensedRingObj R T) ⟶ B₀ a T)
    (hq : q.hom = coefficientMap a T) :
    (∀ M : DerivedCategory (Modules R T),
      (scalarAdj a T).unit.app M ≫ e.derived.hom.app M =
        (ρ_ M).inv ≫ M ◁ DerivedCategory.Q.map
          ((CochainComplex.singleFunctor (Modules R T) 0).map q)) ∧
    ∃ s : SectionScalarComparison a T,
      SectionScalarNormalized a T s ∧ SectionTensorNormalized a T s e ∧
      ∀ M : DerivedCategory (Modules R T),
        (ModuleRingedComparison.derivedEquivalence R T).functor.map
            ((scalarAdj a T).unit.app M) ≫
          (sectionScalarRestriction a T s).hom.app ((D a T).obj M) ≫
          (SheafOfModules.scalarDerivedRestriction.{u + 1, u, u + 1, u + 1}
            (CategoryTheory.InternalAbelianSheafModule.sectionScalarMap.{u + 1, u + 1, u}
              (Scheme.ProEt.topology T) (coefficientMap a T))).map
                (s.derived.hom.app M) =
        s.pair.adjunction.unit.app
          ((ModuleRingedComparison.derivedEquivalence R T).functor.obj M) := by
  sorry

end AlgebraicGeometry.ProEtale.QuotientChange
