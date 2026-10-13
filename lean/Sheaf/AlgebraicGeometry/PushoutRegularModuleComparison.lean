/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q4
-/
module

public import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-! # The regular module of a ring-sheaf pushout

Source: Stacks Project, Morphisms, Tag 01SB, scalar-extension construction.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
variable {U X : Scheme.{u}} (f : U ⟶ X)

/-- The regular module of the pushout algebra is the tensor pullback of the direct
image of the regular structure module, compatibly with the pullback unit.
Source: Stacks Project, Morphisms, Tag 01SB, construction of h; Modules, Tag 008A.
(blueprint: stage3-pushout-regular-module-comparison).

Proof: Write A = f_*O_U and restrict its regular module along O_X → A. This is
literally the module pushforward of O_U. Apply affine_module_tensor_baseChange
(which does not assume affineness) to the regular A-module. Inverse image of the
regular A-module is the regular inverse-image algebra module: the inverse-image
unit commutes with addition and multiplication; uniqueness of extensions of
these operations identifies the scalar action. Extension of this module along
IA → B is the regular B-module. On the tensor presheaf the two maps are
z tensor a ↦ z*t(a) and z ↦ z tensor 1. Balancing and the unit laws show they
are inverse and B-linear, and naturality gives inverse maps after sheafification.
Restrict scalars along b and compose this isomorphism with the cancellation
isomorphism. Its unit formula sends the module pullback unit of d to
1*t(η(d)) = δ(d). No affine hypothesis is needed for this sheaf-level comparison.
The zero algebra and empty open cause no exception: the same formulas and
balanced tensor identities apply. -/
theorem exists_pushout_regularModule_comparison
    (B : U.toTopCat.Sheaf CommRingCat.{u}) (b : U.sheaf ⟶ B)
    (t : TopCat.Sheaf.inverseImageRing f.base
      ((TopCat.Sheaf.pushforward CommRingCat.{u} f.base).obj U.sheaf) ⟶ B)
    (hpushout : IsPushout (tensorPullbackRingMap f)
      ((TopCat.Sheaf.inverseImageConstruction f.base CommRingCat.{u}).map
        (show X.sheaf ⟶
          (TopCat.Sheaf.pushforward CommRingCat.{u} f.base).obj U.sheaf from ⟨f.c⟩)) b t) :
    ∃ e : (tensorPullback f).obj
        ((pushforward f).obj (SheafOfModules.unit U.ringCatSheaf)) ≅
      (SheafOfModules.restrictScalars
        ((sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).map b)).obj
          (SheafOfModules.unit
            ((sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).obj B)),
      ∀ (V : X.Opens) (d : Γ(U, f ⁻¹ᵁ V)),
        e.hom.val.app (op (f ⁻¹ᵁ V))
          (((Classical.choose (exists_tensorPullbackAdjunction f)).unit.app
            ((pushforward f).obj (SheafOfModules.unit U.ringCatSheaf))).val.app (op V) d) =
          (t.hom.app (op (f ⁻¹ᵁ V))).hom
            (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
              (Opens.map f.base) CommRingCat.{u} (Opens.grothendieckTopology X)
              (Opens.grothendieckTopology U)).unit.app
                ((TopCat.Sheaf.pushforward CommRingCat.{u} f.base).obj U.sheaf)).hom.app
                  (op V) d) := by
  sorry

end
end AlgebraicGeometry.Scheme.Modules
