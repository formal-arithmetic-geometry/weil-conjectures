/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.GlobalHomAdjunctionIso
import WeilConjectures.AlgebraicGeometry.MixedTensorPairingBaseChangeTransport
import WeilConjectures.AlgebraicGeometry.MixedTensorPairingBaseChangeNaturality

/-! # Base change preserves the direct-image tensor pairing

## References

* Stacks Project, Tags 08I3, 08HY and 0AA8.
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

/-- The direct-image tensor pairing, constructed by transposing the tensor of counits
(Stacks, Tags 079U and 08HY). -/
def mixedDirectImageTensorPairing {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A B : schemeDerivedCategory X) :
    (schemeDerivedDirectImage f).obj A ⊗ (schemeDerivedDirectImage f).obj B ⟶
      (schemeDerivedDirectImage f).obj (A ⊗ B) :=
  (schemeHomPullbackAdjunction f).homEquiv _ _
    ((mixedHomTensorPullbackIso f).hom.app
      ((schemeDerivedDirectImage f).obj A, (schemeDerivedDirectImage f).obj B) ≫
      ((schemeHomPullbackAdjunction f).counit.app A ⊗ₘ
        (schemeHomPullbackAdjunction f).counit.app B))

/-- Base change transports an arbitrary tensor pairing. This is independent of internal
Hom: `a` is any morphism from a tensor product, with no closed structure involved
(Stacks, Tags 08I3, 08HY and 0AA8). -/
theorem mixedTensorPairing_baseChange
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y)
    (A B C : schemeDerivedCategory X) (a : A ⊗ B ⟶ C) :
    (schemeDerivedBaseChangeMap f (pullback.snd f g) g (pullback.fst f g)
        pullback.condition A ⊗ₘ
      schemeDerivedBaseChangeMap f (pullback.snd f g) g (pullback.fst f g)
        pullback.condition B) ≫
      mixedDirectImageTensorPairing (pullback.snd f g)
        ((derivedPullback (pullback.fst f g)).obj A)
        ((derivedPullback (pullback.fst f g)).obj B) ≫
      (schemeDerivedDirectImage (pullback.snd f g)).map
        ((mixedHomTensorPullbackIso (pullback.fst f g)).inv.app (A, B) ≫
          (derivedPullback (pullback.fst f g)).map a) =
    (mixedHomTensorPullbackIso g).inv.app
        ((schemeDerivedDirectImage f).obj A, (schemeDerivedDirectImage f).obj B) ≫
      (derivedPullback g).map
        (mixedDirectImageTensorPairing f A B ≫ (schemeDerivedDirectImage f).map a) ≫
      schemeDerivedBaseChangeMap f (pullback.snd f g) g (pullback.fst f g)
        pullback.condition C := by
  have h :
    (schemeDerivedBaseChangeMap f (pullback.snd f g) g (pullback.fst f g)
        pullback.condition A ⊗ₘ
      schemeDerivedBaseChangeMap f (pullback.snd f g) g (pullback.fst f g)
        pullback.condition B) ≫
      mixedDirectImageTensorPairing (pullback.snd f g)
        ((derivedPullback (pullback.fst f g)).obj A)
        ((derivedPullback (pullback.fst f g)).obj B) ≫
      (schemeDerivedDirectImage (pullback.snd f g)).map
        ((mixedHomTensorPullbackIso (pullback.fst f g)).inv.app (A, B)) =
    (mixedHomTensorPullbackIso g).inv.app
        ((schemeDerivedDirectImage f).obj A, (schemeDerivedDirectImage f).obj B) ≫
      (derivedPullback g).map
        (mixedDirectImageTensorPairing f A B) ≫
      schemeDerivedBaseChangeMap f (pullback.snd f g) g (pullback.fst f g)
        pullback.condition (A ⊗ B) := by
    exact mixedTensorPairing_baseChange_identity f g A B
  have ha := congrArg
    (fun z ↦ z ≫ (schemeDerivedDirectImage (pullback.snd f g)).map
      ((derivedPullback (pullback.fst f g)).map a)) h
  simpa only [Functor.map_comp, Category.assoc,
    mixedTensorPairing_baseChange_naturality] using ha


end AlgebraicGeometry
