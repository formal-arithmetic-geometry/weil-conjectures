/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.LocallyClosedStratification
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import WeilConjectures.AlgebraicGeometry.ProEtaleGeometricStalk
public import WeilConjectures.AlgebraicGeometry.ProEtaleOperations

/-!
# Restricting a constant ring sheaf to its constant scalars

Source: Stacks Project, Tags 093I and 03CY.
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Sheafification of the constant ring unit remains locally bijective after
forgetting commutativity. Source: the constant-sheaf construction in Bhatt--Scholze
7.3.1(1) (blueprint: def-weil-proetale-locally-constant-sheaf).
Proof: the unit is locally bijective on underlying sets; forgetting commutativity
leaves those sets and every restriction map unchanged. -/
theorem proEtaleConstantRingUnit_locallyBijective (Y : Scheme.{u}) (A : Type u)
    [CommRing A] :
    Presheaf.IsLocallyInjective (ProEt.topology Y)
      (Functor.whiskerRight (CategoryTheory.toSheafify (ProEt.topology Y)
        ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} A))))
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})) ∧
    Presheaf.IsLocallySurjective (ProEt.topology Y)
      (Functor.whiskerRight (CategoryTheory.toSheafify (ProEt.topology Y)
        ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} A))))
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})) := by
  constructor
  · apply (Presheaf.isLocallyInjective_forget_iff _ _).mp
    change Presheaf.IsLocallyInjective (ProEt.topology Y)
      (Functor.whiskerRight (CategoryTheory.toSheafify (ProEt.topology Y)
        ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} A))))
        (CategoryTheory.forget CommRingCat.{u + 1}))
    infer_instance
  · apply (Presheaf.isLocallySurjective_iff_whisker_forget _ _).mpr
    change Presheaf.IsLocallySurjective (ProEt.topology Y)
      (Functor.whiskerRight (CategoryTheory.toSheafify (ProEt.topology Y)
        ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} A))))
        (CategoryTheory.forget CommRingCat.{u + 1}))
    infer_instance

variable (T : Scheme.{u}) (B : Type u) [CommRing B]

/-- The canonical constant-section map, forgetting commutativity. -/
noncomputable def proEtaleModuleScalarUnit :
    (Functor.const T.ProEtᵒᵖ).obj (RingCat.of (ULift.{u + 1, u} B)) ⟶
      ((sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          (proEtaleConstantRing T B)).obj :=
  Functor.whiskerRight (toSheafify (ProEt.topology T)
    ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} B))))
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})

private noncomputable instance scalarUnit_injective :
    Presheaf.IsLocallyInjective (ProEt.topology T) (proEtaleModuleScalarUnit T B) :=
  (proEtaleConstantRingUnit_locallyBijective T B).1

private noncomputable instance scalarUnit_surjective :
    Presheaf.IsLocallySurjective (ProEt.topology T) (proEtaleModuleScalarUnit T B) :=
  (proEtaleConstantRingUnit_locallyBijective T B).2

end AlgebraicGeometry.Scheme
