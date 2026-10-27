/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C3
-/
module

public import Sheaf.Paper.EtaleRingedDerivedIdentificationData

/-! # Canonical constraints of normalized etale tensor models -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] WeilConjectures.SemilinearSections.hasDerived

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.ConstantScalarRestriction CategoryTheory.ConstantModuleDerivedProjection
open CategoryTheory.Functor
namespace AlgebraicGeometry.Etale.RingedProjectionIdentification

set_option Elab.async false

/-- The inverse localization tensorator determines the canonical derived associator and
Koszul symmetry on every normalized corner model.
Source: Stacks Project, Cohomology on Sites, Tags 06YU and 07A4
(blueprint: lem-pur-etale-ringed-normalized-constraints).
Proof: on flat-term K-flat representatives the model comparison is the inverse of
localization's lax tensorator, by ModelNormalized. Total tensors of two such complexes
again have flat terms and are K-flat. Invert the lax associativity equation to obtain
the representative associator equation. The representative equation for the canonical
derived braiding similarly gives the symmetry equation, with the total Koszul swap.
Naturality of the derived associator and braiding supplies the remaining fields of
TensorConstraints. Choosing these very constraints gives the displayed equalities.
The argument applies unchanged to zero coefficients, zero complexes and shifts of
all integer degrees, so the Koszul signs are retained. -/
theorem etale_ringed_normalized_constraints (T : Scheme.{u})
    (Λ : Type (u + 1)) [CommRing Λ]
    [HasDerivedCategory.{u + 1} (Modules (topology T) Λ)]
    (a : SheafOfModules.RingedTensorModel (corner T Λ)) (ha : ModelNormalized T Λ a) :
    ∃ t : SheafOfModules.ProjectionCoherence.TensorConstraints (corner T Λ) a,
      (∀ E F G : DerivedCategory (Modules (topology T) Λ),
        t.associator E F G = α_ E F G) ∧
      (∀ E F : DerivedCategory (Modules (topology T) Λ),
        t.symmetry E F = DerivedMonoidal.braiding'
          (DerivedCategory.Qh (C := Modules (topology T) Λ))
          (HomotopyCategory.quasiIso (Modules (topology T) Λ) (.up ℤ)) E F) := by
  sorry

end AlgebraicGeometry.Etale.RingedProjectionIdentification
