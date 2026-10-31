/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleHomOfPreserves
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleIhom
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleDevissageSupplement
public import WeilConjectures.AlgebraicGeometry.FiniteTypeDirectImageSingleBound
public import WeilConjectures.AlgebraicGeometry.FiniteTypeDirectImageSingleConstructible
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar

/-! # The tensor–Hom adjunction restricted by preservation

Source: blueprint, sec-six-functors-basics, def-sfb-dc-tensor-hom-adjunction
(blueprint: def-sfb-dc-tensor-hom-adjunction).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Restrict the ambient left-factor tensor–Hom adjunction along the full inclusions,
assuming precisely preservation by tensor and internal Hom. Its counit is the restricted
ambient evaluation. Source: blueprint def-sfb-dc-tensor-hom-adjunction
(blueprint: def-sfb-dc-tensor-hom-adjunction). -/
def boundedConstructibleTensorHomAdjunctionOfPreserves
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated X.hom]
    (hT : ∀ A B : BoundedConstructible (condensedRingObj Λ X.left),
      boundedConstructible (condensedRingObj Λ X.left)
        (((derivedTensor Λ X.left).obj A.obj).obj B.obj))
    (hH : ∀ A B : BoundedConstructible (condensedRingObj Λ X.left),
      boundedConstructible (condensedRingObj Λ X.left)
        (((derivedHom Λ X.left).obj (op A.obj)).obj B.obj))
    (K : BoundedConstructible (condensedRingObj Λ X.left)) :
    (boundedConstructible (condensedRingObj Λ X.left)).lift
      ((boundedConstructible _).ι ⋙ (derivedTensor Λ X.left).obj K.obj) (hT K) ⊣
      (boundedConstructibleHomOfPreserves ℓ X Λ hH).obj (op K) :=
  Adjunction.restrictFullyFaithful (derivedTensorHomAdjunction Λ K.obj)
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    (ObjectProperty.liftCompιIso _ _ _).symm
    (boundedConstructibleHomOfPreservesCompatibility ℓ X Λ hH K).symm

end AlgebraicGeometry.ProEtale.CondensedRing
