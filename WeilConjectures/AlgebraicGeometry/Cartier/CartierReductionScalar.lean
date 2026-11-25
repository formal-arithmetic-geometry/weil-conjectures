/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Geo.GeoCartierCanonicalClass
import WeilConjectures.AlgebraicGeometry.Cartier.CartierNormalizedScalarUnits
import WeilConjectures.AlgebraicGeometry.Cartier.CartierBoundaryScalarSquare

/-! # Naturality of the normalized Cartier reduction
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
private theorem scalar_square_of_source_isos
    {C E : Type*} [Category* C] [Category* E] [Abelian C] [Abelian E]
    [HasExt C] [HasExt E] (U : E ⥤ C) [U.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    {X P Y : C} {X' P' Y' : E} (a : X ≅ P) (b : X' ≅ P')
    (η : P ⟶ U.obj P') (θ : Y ⟶ U.obj Y')
    (k : Ext X Y 2) (k' : Ext X' Y' 2)
    (h : (Ext.mk₀ (a.hom ≫ η ≫ U.map b.inv)).comp
      (k'.mapExactFunctor U) (zero_add 2) = k.comp (Ext.mk₀ θ) (add_zero 2)) :
    (Ext.mk₀ η).comp
      (((Ext.mk₀ b.inv).comp k' (zero_add 2)).mapExactFunctor U) (zero_add 2) =
    ((Ext.mk₀ a.inv).comp k (zero_add 2)).comp (Ext.mk₀ θ) (add_zero 2) := by
  have hcancel := congrArg
    (fun c ↦ (Ext.mk₀ a.inv).comp c (zero_add 2)) h
  simp only [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    Ext.mk₀_comp_mk₀_assoc, Ext.comp_assoc_of_third_deg_zero]
  simpa only [Ext.mk₀_comp_mk₀_assoc, Iso.inv_hom_id_assoc] using hcancel

namespace AlgebraicGeometry.ProEtale

/-- Reduction of the integral pole boundary commutes with an arbitrary finite
coefficient homomorphism, including a nonflat one. -/
theorem geoCartierCanonicalClass_scalar (A B : Type (u + 1)) [CommRing A] [CommRing B]
    [Finite A] [Finite B] (n : ℕ) (hn : 0 < n) (hA : (n : A) = 0)
    (hB : (n : B) = 0) (φ : A →+* B) {D Z : Scheme.{u}} (i : D ⟶ Z)
    [IsClosedImmersion i] (hI : i.ker.IsInvertible) (hZ : IsUnit (n : Γ(Z, ⊤))) :
    GeoCartierScalarCompatibility φ n hA hB i
      (geoCartierCanonicalClass A n hn hA i hI hZ)
      (geoCartierCanonicalClass B n hn hB i hI hZ) := by
  obtain ⟨η, θ, hη, hθ, hηunit, hθunit⟩ :=
    geoCartier_normalized_scalar_units A B n hn hA hB φ i hZ
  have hsq := geoCartier_boundary_scalar_square A B n hn hA hB φ i hI hZ
    (Etale.geoCartierEtaleClass A n hn hA i hI hZ)
    (Etale.geoCartierEtaleClass B n hn hB i hI hZ)
    (Etale.geoCartierEtaleClass_spec A n hn hA i hI hZ).1
    (Etale.geoCartierEtaleClass_spec B n hn hB i hI hZ).1 η θ ⟨hη, hθ⟩
  unfold GeoCartierScalarCompatibility
  refine ⟨η, θ, hη, hθ, hηunit, hθunit, ?_⟩
  exact scalar_square_of_source_isos
    (Sheaf.restrictScalars (Scheme.ProEt.topology Z) φ)
    (asIso (geoCartierSourceComparison A i)) (asIso (geoCartierSourceComparison B i))
    ((lowerStar (ModuleCat.{u + 1} A) i).map η) θ _ _ hsq

end AlgebraicGeometry.ProEtale
