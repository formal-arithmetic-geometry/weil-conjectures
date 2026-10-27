/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.QuotientSectionTensorData

/-! A normalized natural transformation for sectionwise scalar extension. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

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

/-- The sectionwise scalar extension admits a natural transformation normalized on generators.
Source: Stacks 03EK and 06YY; this is the map part of the fixed-model comparison.
(blueprint: lem-sfb-quotient-scalar-section-ordinary-normalized-map).

Proof: construct the sheafified change-of-rings map on each module and use its universal
scalar-extension property. The displayed equation is the image of `1 tensor m` under that
map, and naturality follows from functoriality of tensoring and sheafification. -/
theorem scalar_section_ordinary_normalized_map (T : Scheme.{u})
    (model : SectionModel a T) :
    ∃ ordinary : QuotientChange.extension a T ⋙
        (equivalence Λ' T).functor ⟶
      (equivalence Λ T).functor ⋙ model.E,
      ∀ (M : Modules Λ T) (W : T.ProEtᵒᵖ) (m : M.X.obj.obj W),
        (((ordinary.app M) ≫ eqToHom (model.obj_eq _)).val.app W)
            (((Mod.extendUnit (ProEtale.coefficientMap a T) M).hom.hom.app W) m) =
          (toSheafify (Scheme.ProEt.topology T)
            (SheafOfModules.changeOfRingsPresheaf (sectionQuotient a T)
              ((equivalence Λ T).functor.obj M)).presheaf).app W
                ((1 : (ring Λ' T).obj.obj W)
                  ⊗ₜ[(ring Λ T).obj.obj W,
                    ((sectionQuotient a T).hom.app W).hom] m) := by
  sorry

end AlgebraicGeometry.ProEtale.QuotientSectionTensor
