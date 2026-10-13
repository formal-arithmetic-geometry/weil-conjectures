/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U3
-/
module

public import Sheaf.AlgebraicGeometry.DerivedOpenRestrictionMaps
public import Sheaf.AlgebraicGeometry.DerivedTensorStructure
public import Sheaf.AlgebraicGeometry.DerivedPullback

/-! # Supported-open comparisons before the projection formula

Source: Stacks Project, Tags 08EV, 08DF, 08DX and 08DW.
(blueprint: lem-pc-supported-open-tensor-direct-image-comparisons).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry

/-- Restrict supported direct images, including a derived tensor input, to an open.
Source: Stacks Project, Tag 08EV, support reduction; Tag 08DF, supported-open unit;
Tags 08DX and 08DW, compatibility of tensor and pullback with restriction.
(blueprint: lem-pc-supported-open-tensor-direct-image-comparisons).

Proof: put V = X minus T. The supported-open adjunction unit E -> Rj_*(E|_U)
restricts to an isomorphism on U and to a map between zero objects on V, hence
is invertible by detection on this cover. Apply Rf_* and the derived composition
comparison to obtain the first isomorphism. Exact restriction to V annihilates E;
its compatibility with K-flat derived tensor annihilates E tensor Lf^*K as well.
Thus that tensor input also has all cohomology stalks zero outside T. Apply the
same supported-open unit and composition comparison to it. Finally, exact open
restriction commutes with derived tensor, and restriction of Lf^*K agrees with
L(fj)^*K: on K-flat resolutions both are the termwise tensor pullback restricted
to U. Apply R(fj)_* to these two identifications for the second isomorphism.
For independent localization universes, use the standard localizations on U
and V in these calculations and the unique localization equivalences to transport
the comparisons to the supplied localizations. These equivalences preserve
homology and the K-flat tensor models. No quasi-coherence, boundedness, properness,
or projection formula is used. Empty opens and zero E give zero comparisons. -/
theorem supportedOpen_tensor_directImage_comparisons
    {X S : Scheme.{u}} (f : X ⟶ S) (U : X.Opens)
    (T : Set X) (hT : IsClosed T) (hTU : T ⊆ (U : Set X))
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    (E : schemeDerivedCategory X)
    (hE : ∀ (n : ℤ) (x : X), x ∉ T →
      Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj E).val.presheaf x)))
    (K : schemeDerivedCategory S) :
    Nonempty ((schemeDerivedDirectImage f).obj E ≅
      (schemeDerivedDirectImage (U.ι ≫ f)).obj
        ((schemeOpenRestriction X U).mapDerivedCategory.obj E)) ∧
    Nonempty ((schemeDerivedDirectImage f).obj (E ⊗ (derivedPullback f).obj K) ≅
      (schemeDerivedDirectImage (U.ι ≫ f)).obj
        (((schemeOpenRestriction X U).mapDerivedCategory.obj E) ⊗
          (derivedPullback (U.ι ≫ f)).obj K)) := by sorry

end AlgebraicGeometry
