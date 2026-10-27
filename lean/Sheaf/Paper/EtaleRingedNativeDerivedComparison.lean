/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C3
-/
module

public import Sheaf.Paper.EtaleRingedDerivedIdentificationData

/-! # The normalized native derived comparison on lifted étale sites -/

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
namespace AlgebraicGeometry.Etale.RingedProjectionIdentification

/-- Localization of the ordinary scalar comparison identifies the specified
unbounded étale adjunction and tensor pullback comparison.
Source: Stacks Project, sites-cohomology.tex, Tags 07A4 and 07A6
(blueprint: lem-pur-etale-ringed-native-derived-comparison).
Proof: exact scalar restriction and the site equivalence preserve and reflect
quasi-isomorphisms, so the ordinary inverse-image comparison localizes. Uniqueness
of the universal left-derived extension gives the specified left normalization.
Compute both direct images on a K-injective resolution. An exact equivalence
preserves K-injectives, since its inverse is exact; the ordinary direct-image
comparison therefore gives the right normalization with the right-derived unit.
On a complex and a K-injective target, the Hom bijection is localization, the
ordinary Hom adjunction and localization back. The ordinary comparison identifies
those bijections; their values on identities give the unit and counit equations.
The ordinary scalar-extension tensor map carries 1 tensor (m tensor n) to the
tensor of the two inserted sections. Transfer its coherent tensor structure through
the exact equivalence and localize its signed total. Both tensor routes agree on
all flat-term K-flat pairs, bidegree by bidegree, and resolving tensor descent gives
the tensor square on all unbounded inputs. Finally the projection square follows
by transposing this tensor square followed by counit tensor identity. No projection
map is assumed invertible and no boundedness or coefficient finiteness is used. -/
theorem etale_ringed_native_derived_comparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    (Λ : Type (u + 1)) [CommRing Λ]
    [HasDerivedCategory.{u + 1} (Modules (topology Y) Λ)]
    [HasDerivedCategory.{u + 1} (Modules (topology X) Λ)]
    (d : GeometricData (topology Y) (topology X) Λ) (x : ExactData d)
    (o : OrdinaryIdentification d)
    (hL : d.pullA = transportedInverse f (ModuleCat.{u + 1} Λ))
    (hR : d.pushA = transportedDirect f (ModuleCat.{u + 1} Λ))
    (mY : NativeOrdinaryTensorData Y Λ) (mX : NativeOrdinaryTensorData X Λ)
    (cY : NativeTensorData Y Λ mY.braided) (cX : NativeTensorData X Λ mX.braided)
    (hAdj : HEq d.fixedAdj
      ((nativeEquivalence Y Λ).symm.toAdjunction.comp
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).comp
          (nativeEquivalence X Λ).toAdjunction)))
    (a : SheafOfModules.RingedTensorModel (corner Y Λ))
    (b : SheafOfModules.RingedTensorModel (corner X Λ))
    (ha : ModelNormalized Y Λ a) (hb : ModelNormalized X Λ b) :
    ∃ e : NativeIdentification f Λ d x o hL hR mY mX cY cX,
      (∀ M N : DerivedCategory (Modules (topology Y) Λ),
        @Functor.OplaxMonoidal.δ _ _ _ _ _ _ d.pullR.mapDerivedCategory
          e.tensor.val.1.toOplaxMonoidal M N =
          ((edge Λ d x).tensorComparison a b).hom.app (M, N)) ∧
      PublishedProjectionSquare f Λ d x o hL hR mY mX cY cX e a b := by
  sorry

end AlgebraicGeometry.Etale.RingedProjectionIdentification
