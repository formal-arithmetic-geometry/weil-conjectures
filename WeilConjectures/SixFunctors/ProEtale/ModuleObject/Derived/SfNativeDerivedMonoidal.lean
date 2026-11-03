/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom

/-! # The canonical derived monoidal structure with its coefficient proof supplied

Source: the native internal-module tensor construction, used by thm-sf-biduality-class.
(blueprint: def-sf-native-derived-monoidal).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The canonical commutativity proof in the symmetric sheaf presentation.
Source: isCommMonObj_condensedRingObj (blueprint: def-sf-native-derived-monoidal).
Proof: the symmetric braiding is the existing sheaf braiding; unfold its aliases
and apply the existing commutativity theorem for monoidal pullback from the point. -/
theorem sfNativeCoefficientComm
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) :
    letI : BraidedCategory (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) :=
      (inferInstance :
        SymmetricCategory (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})).toBraidedCategory
    IsCommMonObj (condensedRingObj Λ X) := by
  with_unfolding_all
    exact AlgebraicGeometry.ProEtale.isCommMonObj_condensedRingObj Λ X

/-- The existing derived tensor structure on internal modules over the actual
pulled-back coefficient ring, with its canonical commutativity proof supplied.
Source: Mod.derivedMonoidalCategory (blueprint: def-sf-native-derived-monoidal).
The construction is the existing K-flat derived tensor; it introduces no new
choice, tensor functor or unit. Supply the symmetric sheaf braiding and its
commutativity proof, then apply the already constructed module-derived structure. -/
@[instance_reducible]
def sfNativeDerivedMonoidal
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) :
    MonoidalCategory (DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) := by
  letI : BraidedCategory (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) :=
    (inferInstance :
      SymmetricCategory (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})).toBraidedCategory
  haveI : IsCommMonObj (condensedRingObj Λ X) := sfNativeCoefficientComm Λ X
  with_unfolding_all
    exact CategoryTheory.Mod.derivedMonoidalCategory

/-- The fourfold graded tensor condition follows from preservation of the small
coproducts defining total tensor products.
Source: Mathlib GradedObject.HasTensor₄ObjExt and the native closed module category
(blueprint: def-sf-native-derived-monoidal).
Proof: introduce the two grading indices. Tensoring on the left is a left adjoint,
so preserves the coproduct indexed by triples with the prescribed total degree. -/
theorem sfNativeTensorFour
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    (A B C D : GradedObject ℤ
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    GradedObject.HasTensor₄ObjExt A B C D := by
  let : BraidedCategory (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) :=
    (inferInstance :
      SymmetricCategory (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})).toBraidedCategory
  have : IsCommMonObj (condensedRingObj Λ X) := sfNativeCoefficientComm Λ X
  have : MonoidalClosed
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) := by
    with_unfolding_all
      exact CategoryTheory.Mod.monoidalClosed
  have hcolim (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) :
      CategoryTheory.Limits.PreservesColimitsOfSize.{0, 0}
        (MonoidalCategory.tensorLeft M) := by
    infer_instance
  intro i j
  with_unfolding_all
    exact (hcolim (A i)).preservesColimitsOfShape.preservesColimit

/-- Tensoring preserves the degreewise coproducts used in the graded associator.
Source: the native closed symmetric module category
(blueprint: def-sf-native-derived-monoidal).
Proof: supply the canonical coefficient commutativity proof, use closedness to
obtain preservation of small colimits by tensoring, and take its coproduct component. -/
theorem sfNativeGoodTensor12
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    (A B C : GradedObject ℤ
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    GradedObject.HasGoodTensor₁₂Tensor A B C := by
  let : BraidedCategory (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) :=
    (inferInstance :
      SymmetricCategory (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})).toBraidedCategory
  have : IsCommMonObj (condensedRingObj Λ X) := sfNativeCoefficientComm Λ X
  have : MonoidalClosed
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) := by
    with_unfolding_all
      exact CategoryTheory.Mod.monoidalClosed
  have hcolim (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) :
      CategoryTheory.Limits.PreservesColimitsOfSize.{0, 0}
        (MonoidalCategory.tensorRight M) := by
    infer_instance
  intro i j
  with_unfolding_all
    exact (hcolim (C j)).preservesColimitsOfShape.preservesColimit

/-- Tensoring preserves the degreewise coproducts used in the graded associator.
Source: the native closed symmetric module category
(blueprint: def-sf-native-derived-monoidal).
Proof: supply the canonical coefficient commutativity proof, use closedness to
obtain preservation of small colimits by tensoring, and take its coproduct component. -/
theorem sfNativeGoodTensor23
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    (A B C : GradedObject ℤ
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    GradedObject.HasGoodTensorTensor₂₃ A B C := by
  let : BraidedCategory (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) :=
    (inferInstance :
      SymmetricCategory (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})).toBraidedCategory
  have : IsCommMonObj (condensedRingObj Λ X) := sfNativeCoefficientComm Λ X
  have : MonoidalClosed
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) := by
    with_unfolding_all
      exact CategoryTheory.Mod.monoidalClosed
  have hcolim (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) :
      CategoryTheory.Limits.PreservesColimitsOfSize.{0, 0}
        (MonoidalCategory.tensorLeft M) := by
    infer_instance
  intro i j
  with_unfolding_all
    exact (hcolim (A i)).preservesColimitsOfShape.preservesColimit

/-- The native relative tensor preserves sequential colimits in each argument.
Source: the native closed symmetric module category
(blueprint: def-sf-native-derived-monoidal).
Proof: use the canonical coefficient proof and closed structure. Tensoring is a
left adjoint, hence preserves small colimits, in particular those indexed by ℤ. -/
theorem sfNativeTensorLeftInt
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    CategoryTheory.Limits.PreservesColimitsOfShape ℤ
      (MonoidalCategory.tensorLeft M) := by
  let : BraidedCategory (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) :=
    (inferInstance :
      SymmetricCategory (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})).toBraidedCategory
  have : IsCommMonObj (condensedRingObj Λ X) := sfNativeCoefficientComm Λ X
  have : MonoidalClosed
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) := by
    with_unfolding_all
      exact CategoryTheory.Mod.monoidalClosed
  have hcolim (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) :
      CategoryTheory.Limits.PreservesColimitsOfSize.{0, 0}
        (MonoidalCategory.tensorLeft M) := by
    infer_instance
  with_unfolding_all
    exact (hcolim M).preservesColimitsOfShape

/-- The native relative tensor preserves sequential colimits in each argument.
Source: the native closed symmetric module category
(blueprint: def-sf-native-derived-monoidal).
Proof: use the canonical coefficient proof and closed structure. Tensoring is a
left adjoint, hence preserves small colimits, in particular those indexed by ℤ. -/
theorem sfNativeTensorRightInt
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    CategoryTheory.Limits.PreservesColimitsOfShape ℤ
      (MonoidalCategory.tensorRight M) := by
  let : BraidedCategory (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) :=
    (inferInstance :
      SymmetricCategory (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})).toBraidedCategory
  have : IsCommMonObj (condensedRingObj Λ X) := sfNativeCoefficientComm Λ X
  have : MonoidalClosed
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) := by
    with_unfolding_all
      exact CategoryTheory.Mod.monoidalClosed
  have hcolim (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) :
      CategoryTheory.Limits.PreservesColimitsOfSize.{0, 0}
        (MonoidalCategory.tensorRight M) := by
    infer_instance
  with_unfolding_all
    exact (hcolim M).preservesColimitsOfShape

/-- Native internal modules admit the existing functorial flat resolutions.
Source: Mod.hasFunctorialFlatResolution
(blueprint: def-sf-native-derived-monoidal).
Proof: supply coefficient commutativity in the symmetric sheaf presentation and
apply the existing free-module construction of functorial flat resolutions. -/
theorem sfNativeFlatResolution
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) :
    Abelian.HasFunctorialFlatResolution
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) := by
  let : BraidedCategory (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) :=
    (inferInstance :
      SymmetricCategory (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})).toBraidedCategory
  have : IsCommMonObj (condensedRingObj Λ X) := sfNativeCoefficientComm Λ X
  with_unfolding_all
    exact CategoryTheory.Mod.hasFunctorialFlatResolution

/-- The existing native relative tensor on internal modules is closed.
Source: Mod.monoidalClosed (blueprint: def-sf-native-derived-monoidal).
The construction is the existing right adjoint to relative left tensoring.
Supply coefficient commutativity in the symmetric sheaf presentation, and use
that already constructed closed structure without changing its tensor or Hom. -/
@[instance_reducible]
def sfNativeModuleClosed
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) :
    MonoidalClosed
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) := by
  letI : BraidedCategory (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) :=
    (inferInstance :
      SymmetricCategory (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})).toBraidedCategory
  haveI : IsCommMonObj (condensedRingObj Λ X) := sfNativeCoefficientComm Λ X
  with_unfolding_all
    exact CategoryTheory.Mod.monoidalClosed


/-- The existing braided module-object tensor presentation.
Source: Mod.braidedCategory (blueprint: def-sf-native-derived-monoidal).
Proof: use the canonical symmetric sheaf presentation and the existing module
braiding, with the coefficient commutativity proof supplied explicitly. -/
@[instance_reducible]
def sfNativeModuleBraided
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) :
    BraidedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) := by
  letI : BraidedCategory (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) :=
    (inferInstance :
      SymmetricCategory (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})).toBraidedCategory
  haveI : IsCommMonObj (condensedRingObj Λ X) := sfNativeCoefficientComm Λ X
  with_unfolding_all
    exact CategoryTheory.Mod.braidedCategory


attribute [local instance 50000] sfNativeDerivedMonoidal sfNativeCoefficientComm
  sfNativeTensorFour sfNativeGoodTensor12 sfNativeGoodTensor23
  sfNativeTensorLeftInt sfNativeTensorRightInt sfNativeFlatResolution
  sfNativeModuleClosed sfNativeModuleBraided

/-- Actual scalar extension preserves quasi-isomorphisms between K-flat objects.
Source: Mod.preservesKFlatQuasiIso
(blueprint: def-sf-native-derived-monoidal).
Proof: supply the two native coefficient commutativity proofs and apply the
existing scalar-extension theorem. It computes extension by the relative tensor
with the target regular module and uses K-flatness to preserve acyclic cones. -/
theorem sfNativeScalarsKFlat
    (Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ'] (X : Scheme.{u})
    (φ : condensedRingObj Λ X ⟶ condensedRingObj Λ' X) [IsMonHom φ] :
    (Mod.extendScalars φ).PreservesKFlatQuasiIso := by
  let : BraidedCategory (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) :=
    (inferInstance :
      SymmetricCategory (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})).toBraidedCategory
  have : IsCommMonObj (condensedRingObj Λ X) := sfNativeCoefficientComm Λ X
  have : IsCommMonObj (condensedRingObj Λ' X) := sfNativeCoefficientComm Λ' X
  with_unfolding_all
    exact CategoryTheory.Mod.preservesKFlatQuasiIso φ

attribute [local instance 50000] sfNativeScalarsKFlat

/-- The actual left derived extension along a pulled-back coefficient-ring map.
Source: Mod.extendScalars and Functor.leftDerivedFunctor
(blueprint: def-sf-native-derived-monoidal).
This is the existing K-flat construction, named once so exported comparison types
reuse its data. The morphism, source ring and target ring are retained verbatim;
no scalar-change or comparison isomorphism is selected. -/
def sfNativeDerivedScalars
    (Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ'] (X : Scheme.{u})
    (φ : condensedRingObj Λ X ⟶ condensedRingObj Λ' X) [IsMonHom φ] :
    DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) ⥤
      DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ' X)) :=
  (Mod.extendScalars φ).leftDerivedFunctor

end AlgebraicGeometry.ProEtale.CondensedRing
