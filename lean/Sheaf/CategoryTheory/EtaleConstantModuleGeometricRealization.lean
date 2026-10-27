/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y2
-/
module

public import Sheaf.CategoryTheory.ConstantModuleGeometricComparisonData
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal

/-! # Ordinary geometric data for the small etale module inverse image

Source: Stacks Project, Modules on Sites, Tags 03D6, 03D7 and 03EL.
(blueprint: lem-sfb-etale-constant-module-geometric-realization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096
attribute [-instance] WeilConjectures.SemilinearSections.hasDerived
universe z
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.ConstantModuleDerivedProjection

/-- Realize the etale set inverse image and the published module adjunction as ordinary
constant-ring geometric data.
Source: Stacks Tags 03D6, 03D7 and 03EL; the etale specialization of Tag 00YV (6).
(blueprint: lem-sfb-etale-constant-module-geometric-realization).

Proof: apply etaleInverseImageModulesExact to the constant commutative ring sheaves.
Its ring inverse image, constant-section isomorphism and transported action supply the
algebraic inverse image and scalar isomorphism. Extension of scalars along this ring
isomorphism is the actual changeOfRings construction; its tensor map sends a tensor
of two scalar-extension units to the unit of their tensor. The inverse-image action
and the abelian Hom equation identify its adjunction with the ringed module adjunction.
For fixed modules take the published upperStar, lowerStar and their adjunction.
The continuous direct image is unchanged on underlying sections. Its Hom bijection
preserves addition and scalar endomorphisms, which proves the generalized-section
linear equation. Choose its underlying comparison to be the identity on sections.
The canonical etale inverse-image monoidal structure, with its Hom-normalized
underlying comparison, gives FixedTensorData: the sheafified tensor comparison is
the map on generalized pure tensors, so its pure equation follows from the ordinary
tensor universal property. Its monoidal field is the published structure itself.
The set, ring and additive Hom equations give ringHom. Bundle the
same set adjunction, direct image and structural constant-ring map into ringed, so
its six comparison fields are identities. All construction equalities are then the
defining equations, including equality of the fixed adjunction itself. This works
for the zero ring, the empty scheme and the identity morphism without modification. -/
theorem etale_constant_module_geometric_realization
    {X Y : AlgebraicGeometry.Scheme.{z}} (f : X ⟶ Y)
    (B : Type (z + 1)) [CommRing B] :
    ∃ d : GeometricData Y.smallEtaleTopology X.smallEtaleTopology B,
      d.inverse = AlgebraicGeometry.Scheme.etaleSetPullback f ∧
      d.direct = AlgebraicGeometry.Etale.lowerStar (Type (z + 1)) f ∧
      ∃ (hL : d.pullA = AlgebraicGeometry.Etale.upperStar (ModuleCat.{z + 1} B) f)
        (hR : d.pushA = AlgebraicGeometry.Etale.lowerStar (ModuleCat.{z + 1} B) f),
        HEq d.fixedAdj
          (AlgebraicGeometry.Etale.upperStarLowerStarAdjunction (ModuleCat.{z + 1} B) f) ∧
        ∃ t : FixedTensorData d,
          HEq t.monoidal
            (inferInstance :
              (AlgebraicGeometry.Etale.upperStar (ModuleCat.{z + 1} B) f).Monoidal) := by
  sorry

end CategoryTheory.ConstantModuleDerivedProjection
