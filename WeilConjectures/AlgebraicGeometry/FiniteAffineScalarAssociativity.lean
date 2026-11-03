/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientMaps
import all WeilConjectures.AlgebraicGeometry.Etale.EtaleNormalizedScalarSymmetry
import all WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothCoefficientArrows
import all WeilConjectures.CategoryTheory.Exact.ExactDegreeZeroAdjoint
import all WeilConjectures.SixFunctors.Etale.Derived.Shift
import all WeilConjectures.AlgebraicGeometry.Etale.Open.EtaleOpenScalarRestrictionTensor

/-! # Associativity of the normalized scalar tensor comparison

Source: Charts, ordered tensor reassociation in retained Step 4
(blueprint: lem-sp-finite-affine-scalar-associativity).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale
attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.mapDerivedCategory Functor.leftDerivedFunctor Functor.rightDerivedFunctor upperStar

private theorem core_assoc {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D] (F : C ⥤ D) (c : F.CoreMonoidal)
    (K L M : C) :
    (c.μIso (K ⊗ L) M).inv ≫ ((c.μIso K L).inv ▷ F.obj M) ≫
        (α_ (F.obj K) (F.obj L) (F.obj M)).hom =
      F.map (α_ K L M).hom ≫ (c.μIso K (L ⊗ M)).inv ≫
        (F.obj K ◁ (c.μIso L M).inv) := by
  let : F.Monoidal := c.toMonoidal
  exact Functor.OplaxMonoidal.associativity F K L M

/-- The actual normalized scalar tensorator preserves the ordered tensor associator.
Source: Charts, ordered Tate tensor reassociation in retained Step 4
(blueprint: lem-sp-finite-affine-scalar-associativity).

Proof: uniqueness of left adjoints identifies the canonical scalar extension with
the derived ordinary scalar extension and identifies their cochain counits.
Transport its monoidal structure across this natural isomorphism. Uniqueness of
the flat K-flat normalization identifies the transported inverse tensorator with
the inverse of etaleHomTensorComparison, hence with ExceptionalCoefficients.tensorIso.
The oplax associativity law of the transported monoidal structure is exactly the
displayed equality. This involves only reassociation and never permutes factors;
it holds for arbitrary derived inputs and arbitrary coefficient homomorphisms. -/
theorem finiteAffineScalar_associativity
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B) (Z : Scheme.{u})
    (K L M : DerivedCategoryModule A Z) :
    (ExceptionalCoefficients.tensorIso φ Z).hom.app (K ⊗ L, M) ≫
        ((ExceptionalCoefficients.tensorIso φ Z).hom.app (K, L) ▷
          (scalarExtension φ Z).obj M) ≫
        (α_ ((scalarExtension φ Z).obj K) ((scalarExtension φ Z).obj L)
          ((scalarExtension φ Z).obj M)).hom =
      (scalarExtension φ Z).map (α_ K L M).hom ≫
        (ExceptionalCoefficients.tensorIso φ Z).hom.app (K, L ⊗ M) ≫
        ((scalarExtension φ Z).obj K ◁
          (ExceptionalCoefficients.tensorIso φ Z).hom.app (L, M)) := by
  let E := ProEtale.etaleSheafExtendScalars φ Z
  let U := Sheaf.restrictScalars Z.smallEtaleTopology φ
  let adj : E ⊣ U := ProEtale.etaleSheafExtendScalarsAdjunction φ Z
  let : E.IsLeftAdjoint := adj.isLeftAdjoint
  let : E.PreservesFlat := extension_preservesFlat φ Z
  let : E.PreservesKFlatQuasiIso := extension_preservesKFlatQuasiIso φ Z
  let : E.OplaxMonoidal := adj.leftAdjointOplaxMonoidal
  let : E.Monoidal := CategoryTheory.composeAndSheafifyMonoidal Z.smallEtaleTopology
    (ModuleCat.extendRestrictScalarsAdj.{u + 1} φ)
  obtain ⟨e, hr⟩ := ExceptionalCoefficients.scalarDerivedComparison A B φ Z
  let := E.leftDerivedFunctorMonoidal
  let c := Functor.Monoidal.coreMonoidalTransport e.symm
  have ht := Functor.core_tensor_normalized E (scalarExtension φ Z) e
    (scalarExtensionRepresentative φ Z) hr (etaleHomTensorComparison Z φ)
    (etaleHomTensorComparison_existsUnique Z φ).choose_spec.1
  have hδ (P Q : DerivedCategoryModule A Z) :
      (c.μIso P Q).inv = (ExceptionalCoefficients.tensorIso φ Z).hom.app (P, Q) :=
    (ht P Q).trans (scalar_tensor_eq φ Z P Q).symm
  simpa only [hδ] using core_assoc (scalarExtension φ Z) c K L M

end AlgebraicGeometry.Etale
