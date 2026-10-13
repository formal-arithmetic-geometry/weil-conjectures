/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S4
-/
module

public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Mathlib.AlgebraicGeometry.AffineScheme
import Sheaf.AlgebraicGeometry.AffinePerfectMapLift
import Sheaf.AlgebraicGeometry.AffinePerfectSupportExtension
import Sheaf.AlgebraicGeometry.DerivedOpenGluing
import Sheaf.AlgebraicGeometry.SupportedMapInitialAmbientLift
import Sheaf.AlgebraicGeometry.DerivedOpenLocalization
import Sheaf.AlgebraicGeometry.DerivedOpenRestrictionQCoh

/-! # One affine attachment for supported stabilized maps

Source: Stacks Project, Tag 09IM.
(blueprint: lem-sc-supported-map-affine-attachment).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

set_option backward.isDefEq.respectTransparency false in
/-- Attaching a single affine open extends the source plus its shift.
The input source need only be perfect and supported on the old open; its behaviour
elsewhere in X is immaterial.
Source: Stacks Project, Tag 09IM, the case X = U union V in its proof.
(blueprint: lem-sc-supported-map-affine-attachment).

Proof: Restrict R and β to W. Its pointwise local perfect models make this
restriction perfect, and its cohomology stalks vanish on W minus T. On W replace
R by R plus R[1] and β by the first projection followed by β. The intersection
W intersect V is quasi-compact by quasi-separatedness, as is V minus T.
On the affine V apply supported perfect extension to R restricted to the
intersection. This yields Q supported on T intersect V and an identification with
(R plus R[1]) on the intersection. Compose the identification with the projection
and restricted β. Affine perfect map lifting replaces Q by a perfect tensor
augmentation, unchanged on the intersection and still supported on T intersect V,
and lifts the composite to E restricted to V. Derived open gluing gives a source
and map on W union V. At points of W or V its local models are strictly perfect,
and its stalks vanish away from T. Extend this source and map by zero from W union V
to X, using the exact derived adjunction. This does not affect those local properties.
On U restrict the gluing identification and apply the biproduct and shift
restriction comparisons. The resulting isomorphism identifies the restricted
map with the first projection followed by β restricted to U.
All comparisons are induced by Modules.overEquiv and iterated overFunctorMap.
No support or perfectness outside W union V is required. Empty or redundant V
still works, and the zero source uses the same construction. -/
theorem exists_supported_map_affine_attachment
    (X : Scheme.{u}) [QuasiSeparatedSpace X]
    (U W V : X.Opens) (hUW : U ≤ W) (hW : IsCompact (W : Set X))
    (hV : IsAffineOpen V) (T : Set X) (hT : IsClosed T) (hTc : IsCompact Tᶜ)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ V : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    [∀ V : U.toScheme.Opens,
      HasDerivedCategory.{w}
        (SheafOfModules.{u} ((moduleRings U.toScheme.toRingedSpace).over V))]
    (E : schemeDerivedQCohCategory X)
    (R : schemeDerivedCategory X) (β : R ⟶ E.obj)
    (hR : (∀ x : X, x ∈ W → ∃ O : X.Opens, x ∈ O ∧
        ∃ K : CochainComplex
            (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over O)) ℤ,
          IsStrictlyPerfect X O K ∧
          Nonempty ((SheafOfModules.overFunctor.{u}
            (moduleRings X.toRingedSpace) O).mapDerivedCategory.obj R ≅
              DerivedCategory.Q.obj K)))
    (hRT : (∀ (i : ℤ) (x : X), x ∈ W → x ∉ T →
        Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).obj R).val.presheaf x))))
    :
    ∃ (R' : schemeDerivedCategory X) (β' : R' ⟶ E.obj),
      (∀ x : X, x ∈ (W ⊔ V) → ∃ O : X.Opens, x ∈ O ∧
        ∃ K : CochainComplex
            (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over O)) ℤ,
          IsStrictlyPerfect X O K ∧
          Nonempty ((SheafOfModules.overFunctor.{u}
            (moduleRings X.toRingedSpace) O).mapDerivedCategory.obj R' ≅
              DerivedCategory.Q.obj K)) ∧
      (∀ (i : ℤ) (x : X), x ∈ (W ⊔ V) → x ∉ T →
        Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).obj R').val.presheaf x))) ∧
      ∃ e : ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U) ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
            (Modules.overEquiv U)).mapDerivedCategory.obj R' ≅
          ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U) ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
            (Modules.overEquiv U)).mapDerivedCategory.obj R ⊞
            (((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U) ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
            (Modules.overEquiv U)).mapDerivedCategory.obj R)⟦(1 : ℤ)⟧,
        ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U) ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
            (Modules.overEquiv U)).mapDerivedCategory.map β' =
          e.hom ≫ biprod.fst ≫ ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U) ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
            (Modules.overEquiv U)).mapDerivedCategory.map β := by sorry

end AlgebraicGeometry.Scheme
