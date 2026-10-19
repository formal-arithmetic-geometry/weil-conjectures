/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.MixedHomTensorPullbackIso
public import Sheaf.Algebra.Homology.DerivedInternalHom
public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
public import Sheaf.AlgebraicGeometry.CanonicalDerivedTensorHom
public import Sheaf.AlgebraicGeometry.GlobalHomAdjunctionIso
import all Sheaf.AlgebraicGeometry.GlobalHomAdjunctionIso

/-! # Evaluation-mate direct-image Hom comparison
Source: Stacks Project, Tags 08I3 and 0B6I.
(blueprint: lem-sc-mixed-hom-direct-image-comparison).
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

/-- Existence of the evaluation-mate direct-image internal Hom comparison.
Fixed-data form of the landed `exists_derivedDirectImage_internalHom_comparison`,
using the pinned tensor-Hom family.
All adjunction and tensor data here are fixed, shared with the pullback comparison.
Source: Stacks, Tags 08I3 and 0B6I (blueprint: lem-sc-mixed-hom-direct-image-comparison).
Proof: for every test object A transpose a map into Rf_* internal Hom by the
pullback adjunction and tensor-Hom bijection. Pull back A tensor Rf_*L, apply the
counit at L, then evaluation. Transpose back. This is natural in A, so Yoneda
gives the specified map, and naturality in both Hom entries gives the transformation. -/
theorem exists_mixedHomDirectImageComparison {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃ c : derivedInternalHom (Opens.grothendieckTopology X) X.sheaf ⋙
        schemeDerivedDirectImage f ⟶
      (schemeDerivedDirectImage f).op.prod (schemeDerivedDirectImage f) ⋙
        derivedInternalHom (Opens.grothendieckTopology Y) Y.sheaf,
      ∀ (L M : schemeDerivedCategory X) (A : schemeDerivedCategory Y)
        (α : A ⟶ (schemeDerivedDirectImage f).obj
          ((derivedInternalHom (Opens.grothendieckTopology X) X.sheaf).obj (op L, M))),
        (schemeDerivedTensorHomEquiv Y) A
          ((schemeDerivedDirectImage f).obj L) ((schemeDerivedDirectImage f).obj M)
            (α ≫ c.app (op L, M)) =
          (schemeHomPullbackAdjunction f).homEquiv (A ⊗ (schemeDerivedDirectImage f).obj L) M
            ((mixedHomTensorPullbackIso f).hom.app (A, (schemeDerivedDirectImage f).obj L) ≫
              (𝟙 ((derivedPullback f).obj A) ⊗ₘ
                (schemeHomPullbackAdjunction f).counit.app L) ≫
              (schemeDerivedTensorHomEquiv X)
                ((derivedPullback f).obj A) L M
                  (((schemeHomPullbackAdjunction f).homEquiv A
                    ((derivedInternalHom (Opens.grothendieckTopology X) X.sheaf).obj
                      (op L, M))).symm α)) := by
  exact @internalHomMate_exists (schemeDerivedCategory X) (schemeDerivedCategory Y)
    inferInstance inferInstance (schemeDerivedTensorMonoidal X) (schemeDerivedTensorMonoidal Y)
    (derivedInternalHom (Opens.grothendieckTopology X) X.sheaf)
    (derivedInternalHom (Opens.grothendieckTopology Y) Y.sheaf)
    (derivedPullback f) (schemeDerivedDirectImage f)
    (schemeHomPullbackAdjunction f) (mixedHomTensorPullbackIso f)
    (schemeDerivedTensorHomEquiv X) (schemeDerivedTensorHomEquiv Y)
    (schemeHomTensorHom_naturality X) (schemeHomTensorHom_naturality Y)

end AlgebraicGeometry
