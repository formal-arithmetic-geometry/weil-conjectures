/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.MixedHomTensorPullbackIso
public import Sheaf.AlgebraicGeometry.GlobalHomAdjunctionIso

/-! # Base change preserves the direct-image tensor pairing
Source: Stacks Project, cohomology.tex Tag 08I3 and Remark 08HY;
duality.tex Tag 0AA8, final comparison diagrams.
(blueprint: lem-sc-mixed-tensor-pairing-base-change-identity).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
noncomputable section
namespace AlgebraicGeometry
variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]

/-- Identity-pairing coherence for the canonical base-change mate.
Source: Stacks Project, cohomology.tex, Remark 08HY and Lemma 079U;
duality.tex, Tag 0AA8, final comparison diagrams.
(blueprint: lem-sc-mixed-tensor-pairing-base-change-identity).

Proof: transpose under the upper pullback/direct-image adjunction and expand the
base-change mates. Counit naturality and triangle identities reduce the equality
to compatibility of the pullback-composition comparisons with normalized tensorators.
On K-flat representatives, termwise composition comparisons and tensorators carry
pure tensors to the same pulled-back sections. The normalization equations and
invertible K-flat derived counits transport the equality to the derived category.
K-flat resolutions and naturality extend it to arbitrary A and B. No base-change
map is cancelled or assumed invertible. -/
theorem mixedTensorPairing_baseChange_identity
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y)
    (A B : schemeDerivedCategory X) :
    (schemeDerivedBaseChangeMap f (pullback.snd f g) g (pullback.fst f g)
        pullback.condition A ⊗ₘ
      schemeDerivedBaseChangeMap f (pullback.snd f g) g (pullback.fst f g)
        pullback.condition B) ≫
      ((schemeHomPullbackAdjunction (pullback.snd f g)).homEquiv _ _
        ((mixedHomTensorPullbackIso (pullback.snd f g)).hom.app
          ((schemeDerivedDirectImage (pullback.snd f g)).obj
              ((derivedPullback (pullback.fst f g)).obj A),
           (schemeDerivedDirectImage (pullback.snd f g)).obj
              ((derivedPullback (pullback.fst f g)).obj B)) ≫
          ((schemeHomPullbackAdjunction (pullback.snd f g)).counit.app
              ((derivedPullback (pullback.fst f g)).obj A) ⊗ₘ
           (schemeHomPullbackAdjunction (pullback.snd f g)).counit.app
              ((derivedPullback (pullback.fst f g)).obj B)))) ≫
      (schemeDerivedDirectImage (pullback.snd f g)).map
        ((mixedHomTensorPullbackIso (pullback.fst f g)).inv.app (A, B)) =
    (mixedHomTensorPullbackIso g).inv.app
        ((schemeDerivedDirectImage f).obj A, (schemeDerivedDirectImage f).obj B) ≫
      (derivedPullback g).map
        (((schemeHomPullbackAdjunction f).homEquiv _ _
      ((mixedHomTensorPullbackIso f).hom.app
        ((schemeDerivedDirectImage f).obj A, (schemeDerivedDirectImage f).obj B) ≫
        ((schemeHomPullbackAdjunction f).counit.app A ⊗ₘ
          (schemeHomPullbackAdjunction f).counit.app B)))) ≫
      schemeDerivedBaseChangeMap f (pullback.snd f g) g (pullback.fst f g)
        pullback.condition (A ⊗ B) := by sorry


end AlgebraicGeometry
