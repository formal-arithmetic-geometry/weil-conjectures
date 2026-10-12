/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Authors: SHEAF group U3
-/
module

public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
public import Sheaf.AlgebraicGeometry.DirectImageAlgebraDerivedCategory
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import Sheaf.AlgebraicGeometry.AffineSinglePushforwardUnitIso
import Sheaf.AlgebraicGeometry.DerivedCategory

/-! # Canonical single-complex transport of a derived scalar counit

Source: Stacks Project, Tags 0AVW and 0AX3
(blueprint: lem-sc-finite-exact-hom-single-counit-transport). -/

@[expose] public section

universe u wX wY wA

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

set_option maxHeartbeats 800000 in
-- Elaborating the canonical factorization unfolds the two ring-sheaf presentations.
/-- Lift an algebra-valued derived isomorphism between single complexes, keeping
track of the scalar adjunction counit through the canonical pushforward factorization.
Source: Stacks Project, Tag 0AVW, canonical factorization; Tag 0AX3, counit comparison
(blueprint: lem-sc-finite-exact-hom-single-counit-transport).

Proof: Let F be g_* and T scalar restriction. Form the canonical comparison from
(F M)[0] to RF(M[0]) using the inverse termwise single comparison and the right-derived
unit. Under exact T and the specified canonical gamma this becomes the analogous
f_* comparison. The latter is invertible for quasi-coherent M by affine vanishing.
Exact scalar restriction reflects isomorphisms on derived categories: it commutes with
cohomology, reflects isomorphisms of modules (the underlying abelian sheaf is unchanged),
and cohomology detects derived isomorphisms. Thus the g_* comparison is invertible.
Compose it with e and the exact-H single comparison. Full faithfulness of the single
functor lifts this composite isomorphism to j. Map j by exact T and apply the derived
adjunction counit. The derived counit factorization on L[0] identifies the last two
factors with the single of adjH.counit at L. Naturality of the exact-T single comparison
and the canonical gamma factorization replace the first factors with the f_* comparison
followed by gamma inverse. This is exactly the equation stated. All comparisons are
canonical; arbitrary rescalings of gamma are excluded by hγ. The zero module and empty
schemes satisfy the same factorization and full-faithfulness identities. -/
theorem finite_exactHom_single_counit_transport
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [HasDerivedCategory.{wA} (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace f)))]
    [IsAffineHom f]
    (M : X.Modules) (hM : M.IsQuasicoherent) (L : Y.Modules)
    [PreservesFiniteLimits (SheafOfModules.restrictScalars
      (R := moduleRings Y.toRingedSpace)
      (R' := moduleRings (directImageAlgebraSpace f)) f.toRingCatSheafHom)]
    [PreservesFiniteColimits (SheafOfModules.restrictScalars
      (R := moduleRings Y.toRingedSpace)
      (R' := moduleRings (directImageAlgebraSpace f)) f.toRingCatSheafHom)]
    (H : SheafOfModules.{u} (moduleRings Y.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings (directImageAlgebraSpace f)))
    [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (adjH : SheafOfModules.restrictScalars
        (R := moduleRings Y.toRingedSpace)
        (R' := moduleRings (directImageAlgebraSpace f)) f.toRingCatSheafHom ⊣ H)
    (γ : RingedSpace.derivedModuleDirectImage (toDirectImageAlgebraSpace f) ⋙
      (SheafOfModules.restrictScalars
        (R := moduleRings Y.toRingedSpace)
        (R' := moduleRings (directImageAlgebraSpace f)) f.toRingCatSheafHom).mapDerivedCategory ≅
        schemeDerivedDirectImage f)
    (hγ : γ =
      (Functor.rightDerivedFunctorCompMapDerivedCategoryIso
        (RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace f))
        (SheafOfModules.restrictScalars
        (R := moduleRings Y.toRingedSpace)
        (R' := moduleRings (directImageAlgebraSpace f)) f.toRingCatSheafHom)).symm ≪≫
      Functor.rightDerivedFunctorNatIso
        (show RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace f) ⋙
          SheafOfModules.restrictScalars
        (R := moduleRings Y.toRingedSpace)
        (R' := moduleRings (directImageAlgebraSpace f)) f.toRingCatSheafHom ≅
          RingedSpace.moduleDirectImage f.toLRSHom.toShHom from Iso.refl _))
    (e : (RingedSpace.derivedModuleDirectImage (toDirectImageAlgebraSpace f)).obj
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj M) ≅
      H.rightDerivedFunctor.obj ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj L)) :
    ∃ j : (RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace f)).obj M ≅ H.obj L,
      (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).map
          ((SheafOfModules.restrictScalars
        (R := moduleRings Y.toRingedSpace)
        (R' := moduleRings (directImageAlgebraSpace f)) f.toRingCatSheafHom).map j.hom ≫
            adjH.counit.app L) =
      DerivedCategory.Q.map
        ((HomologicalComplex.singleMapHomologicalComplex
          (RingedSpace.moduleDirectImage f.toLRSHom.toShHom) (ComplexShape.up ℤ) 0).inv.app M) ≫
        (RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerivedFunctorUnit.app
          ((HomotopyCategory.quotient _ _).obj ((CochainComplex.singleFunctor
            (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj M)) ≫
        γ.inv.app ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj M) ≫
        (SheafOfModules.restrictScalars
        (R := moduleRings Y.toRingedSpace)
        (R' := moduleRings (directImageAlgebraSpace f)) f.toRingCatSheafHom).mapDerivedCategory.map
          e.hom ≫
        adjH.mapDerivedCategoryRightDerivedAdjunction.counit.app
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj L) := by sorry

end AlgebraicGeometry
