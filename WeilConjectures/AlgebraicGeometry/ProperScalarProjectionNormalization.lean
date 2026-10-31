/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SupportScalarProjectionCoordinates
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekProjection
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat

/-! # Components of support scalar normalization -/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- Restriction of the direct-image scalar mate is the constant-coefficient projection.
Source: Stacks 07A4, 07A6, 07A7
(blueprint: lem-exc-proper-scalar-projection-normalization).

Proof: compare the supplied left adjoints with normalized K-flat scalar extension.
On flat K-flat representatives its restriction is tensor with the constant A-module
underlying B, using the balanced tensor map and symmetry. The constant-coefficient
realization preserves this normalization. The sectionwise restriction/direct-image
comparison has geometric transpose the counit tensored with B. The scalar/pullback
and tensor/pullback comparisons agree on pure tensors, so injectivity of the
geometric Hom equivalence identifies the arrows. Transport the source and target
by these balancing isomorphisms. Resolving B as well as the first input proves
this for nonflat coefficients and unbounded complexes. -/
theorem properScalarMate_projection_arrowIso
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {Z Y : Scheme.{u}} (g : Z ⟶ Y)
    (LZ : proEtaleDerivedCategory Z A ⥤ proEtaleDerivedCategory Z B)
    (LY : proEtaleDerivedCategory Y A ⥤ proEtaleDerivedCategory Y B)
    (aZ : LZ ⊣ (proEtaleCoefficientRestrictScalars Z φ).mapDerivedCategory)
    (aY : LY ⊣ (proEtaleCoefficientRestrictScalars Y φ).mapDerivedCategory)
    (P : DerivedCategory
      (Sheaf (ProEt.topology Z) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))) :
    Nonempty (properScalarMateArrow φ g LZ LY aZ aY P ≅ (Arrow.mk
          (((ProEtale.rightDerivedLowerStarProjectionMap
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) g).app
              P).app
            ((constantSheaf (ProEt.topology Y)
              (ModuleCat.{u + 1} (ULift.{u + 1, u} A))).mapDerivedCategory.obj
              ((DerivedCategory.singleFunctor _ 0).obj
                ((ModuleCat.restrictScalars.{u + 1} φ.ulift).obj
                  (ModuleCat.of (ULift.{u + 1, u} B) (ULift.{u + 1, u} B)))))))) := by
  sorry

end WeilConjectures
