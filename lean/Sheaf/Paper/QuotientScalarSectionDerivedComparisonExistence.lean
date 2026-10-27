/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.QuotientSectionTensorData

/-! Derived counit normalization for a fixed sectionwise scalar model. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj ChangeOfRings

namespace AlgebraicGeometry.ProEtale.QuotientSectionTensor

open QuotientChange IntegralQuotient ModuleRingedComparison

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  (a : Λ ⟶ Λ') [IsMonHom a]

variable [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ T)]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ' T)]

/-- A fixed sectionwise model admits a derived comparison normalized by its counit.
Source: Stacks 06YY and 07A6; this is the derived half of the fixed-model
comparison construction.
(blueprint: lem-sfb-quotient-scalar-section-derived-comparison-existence).

Proof: compare the fixed model with the total left-derived functor of its
ordinary extension. Uniqueness of counit-compatible left-derived functors gives
the isomorphism, and its defining counit square is the displayed equation after
transport through the section localization comparisons. -/
theorem scalar_section_derived_comparison_exists (T : Scheme.{u})
    (model : SectionModel a T)
    (ordinary : QuotientChange.extension a T ⋙
        (equivalence Λ' T).functor ≅
      (equivalence Λ T).functor ⋙ model.E) :
    ∃ derived : D a T ⋙ derivedFunctor Λ' T ≅
        derivedFunctor Λ T ⋙ model.T,
      ∀ P : CochainComplex (Modules Λ T) ℤ,
        derived.hom.app (DerivedCategory.Q.obj P) ≫
            model.T.map (sectionLocalizationComparison Λ T P).hom ≫
            model.ε.app
              (((equivalence Λ T).functor.mapHomologicalComplex (.up ℤ)).obj P) =
          (derivedFunctor Λ' T).map (compute a T P) ≫
            (sectionLocalizationComparison Λ' T
              (((QuotientChange.extension a T).mapHomologicalComplex
                (.up ℤ)).obj P)).hom ≫
            DerivedCategory.Q.map
              ((Functor.mapHomologicalComplexCompIso ordinary (.up ℤ)).hom.app P) ≫
            DerivedCategory.Q.map
              ((Functor.mapHomologicalComplexCompIso
                (Iso.refl ((equivalence Λ T).functor ⋙ model.E)) (.up ℤ)).inv.app P) := by
  sorry

end AlgebraicGeometry.ProEtale.QuotientSectionTensor
