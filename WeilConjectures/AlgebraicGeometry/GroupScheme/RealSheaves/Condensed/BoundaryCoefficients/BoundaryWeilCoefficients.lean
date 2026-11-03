/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.RealSheaves.Setup.RealSheavesSetup
public import WeilConjectures.WeilSheaf.RealSheaves.Setup.RealWeilSheaves
public import WeilConjectures.SmoothPurity.CondensedWeilModules
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousLocallyFreePullbackSupplement
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeCondensedModule.NativeCondensedModuleLocalFrobenius
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement

/-! # The coefficient data needed for the boundary formula

These are the concrete Frobenius and ordinary module fixed pairs of the real-sheaf
convention, without the separate Tate-twist and strict-complex comparison theorems.
Source: latest blueprint, sk-d-real-weil, Convention;
(blueprint: def-real-boundary-coefficients-core).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace RealSheaves.Condensed.BoundaryCoefficients

/-- Geometric Frobenius on an arbitrary model, given by inverse finite-field Frobenius.
The inverse identities are the existing galoisMap_inverse theorem.
Source: real-sheaf Convention (blueprint: def-real-boundary-coefficients-core). -/
def modelFrobenius (D : WeilConjectures.FiniteFieldDatum.{u})
    (T₀ : Over (Spec (.of D.k₀))) :
    Aut (pullback T₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))) :=
  letI := Fintype.ofFinite D.k₀
  { hom := D.galoisMap T₀.hom
      (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k)
    inv := D.galoisMap T₀.hom
      (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k).symm
    hom_inv_id := (D.galoisMap_inverse T₀.hom _).1
    inv_hom_id := (D.galoisMap_inverse T₀.hom _).2 }

/-- The same geometric Frobenius, specialized to the chapter setup.
Source: real-sheaf Convention (blueprint: def-real-boundary-coefficients-core). -/
@[irreducible] def frobenius (D : Setup.{u, v}) (X₀ : Over (Spec (.of D.k₀))) :
    Aut (D.geometricCurve X₀.left) :=
  modelFrobenius D.weilFieldDatum X₀

/-- Ordinary Weil modules are actual module sheaves with an invertible pullback map.
Source: real-sheaf Convention (blueprint: def-real-boundary-coefficients-core). -/
abbrev WeilModule
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}} (g : X ≅ X) :=
  WeilConjectures.condensedWeilModules Λ g.hom

/-- Lissity is local finite freeness of the actual underlying module sheaf.
Source: real-sheaf Convention (blueprint: def-real-boundary-coefficients-core). -/
abbrev LisseWeil
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}} (g : X ≅ X) :=
  ObjectProperty.FullSubcategory
    (fun M : WeilModule Λ g ↦ CondensedRing.LocallyFree (condensedRingObj Λ X) M.carrier)

end RealSheaves.Condensed.BoundaryCoefficients
