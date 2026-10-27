/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R6
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleCoefficientSliceComparisonData

/-! # Closed slice comparison with transported coefficients

Source: Hemo--Richarz--Scholbach, Lemma 4.5; Stacks 03CE, 07A4, 08J9, 08JB.
(blueprint: lem-zl-proetale-coefficient-slice-closed-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u u₁ v₁ u₂ v₂
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
namespace AlgebraicGeometry.Scheme

/-- Slice restriction has an invertible closed mate for its normalized exact tensor
comparison. The mate is defined by evaluation, so invertibility gives the internal
Hom comparison with its required normalization.

Source: Stacks, sites-cohomology.tex, Tags 08JB (lemma-restriction-RHom-to-U)
and 08J9 (lemma-internal-hom), and Section 0A8X (section-hom-complexes)
(blueprint: lem-zl-proetale-slice-closed-mates).

Proof: use ProEt.sliceEquiv to identify restriction with the literal slice functor.
The normalized total tensor map becomes the pure-tensor comparison on that slice.
A K-injective target remains K-injective after restriction. On each further slice,
local Hom maps and their restriction maps identify with the same linear maps;
products and the differential d_I f - (-1)^n f d_L are unchanged. The existing
unbounded slice internal-Hom theorem therefore gives a natural isomorphism. Its
evaluation compatibility identifies this isomorphism with the displayed closed mate:
uncurry both maps, then apply the injectivity of the closed adjunction bijection.
This argument uses no finite presentation, boundedness or constancy, including
for empty sites and zero rings. -/
theorem proEtaleSlice_closed_maps_isIso {X : Scheme.{u}} (U : X.ProEt)
    (O : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (B : Sheaf (ProEt.topology U.left) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage U.hom CommRingCat.{u + 1}).obj O ≅ B)
    (delta : ProEtaleObjectRestrictionComparison U CommRingCat.{u + 1})
    (S : CoefficientClosedStructure (proEtaleCoefficientHom X O))
    (SR : CoefficientClosedStructure (proEtaleCoefficientHom U.left (proEtaleSliceRing U O)))
    (SB : CoefficientClosedStructure (proEtaleCoefficientHom U.left B))
    (T : CoefficientTensorModels.{u + 1, u + 1, u} (ProEt.topology X) O S)
    (TR : CoefficientTensorModels.{u + 1, u + 1, u} (ProEt.topology U.left)
      (proEtaleSliceRing U O) SR)
    (TB : CoefficientTensorModels.{u + 1, u + 1, u} (ProEt.topology U.left) B SB)
    (d : ProEtaleCoefficientSliceComparison.TensorData U O B c delta S SR SB T TR TB)
    (hd : ProEtaleCoefficientSliceComparison.TensorNormalized
      U O B c delta S SR SB T TR TB d) :
    ∀ L M : DerivedCategory (proEtaleRingModules X O),
      IsIso (coefficientClosedPullbackMap S SR
        (proEtaleSliceModuleRestriction U O).mapDerivedCategory
          d.restrictionTensor.rho L M) := by
  sorry

end AlgebraicGeometry.Scheme
