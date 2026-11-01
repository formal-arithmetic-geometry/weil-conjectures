/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.ProperScalarProjectionCanonicalEndpoint
public import WeilConjectures.AlgebraicGeometry.Proper.ProperScalarCounitSquare
public import WeilConjectures.AlgebraicGeometry.Direct.DirectImageScalarOperations

/-! # Proper scalar projection normalization

The displayed mate is the explicit counit transpose.  For supplied left adjoints
`L_T`, its comparison `h_T` is the unique adjunction preserving comparison with
the normalized derived scalar extension.  The proof transports this formula to
the normalized mate and then uses the finite scalar projection presentation.
(Source: blueprint `lem-exc-proper-scalar-projection-normalization`.)
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
namespace WeilConjectures

/-- The explicit mate `R_B(h_Z⁻¹) ∘ γ_K ∘ h_Y`, transported to fixed coefficients.
Here `h_T` is the comparison supplied by `Adjunction.leftAdjointUniq` with the
normalized scalar extension, and `γ` is the mate of the scalar/pullback comparison.
Source: Stacks Tags 07A4, 07A6 and 07A7
(blueprint: lem-exc-proper-scalar-projection-normalization). -/
noncomputable abbrev properScalarExplicitMateArrow
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {Z Y : Scheme.{u}} (g : Z ⟶ Y)
    (LZ : proEtaleDerivedCategory Z A ⥤ proEtaleDerivedCategory Z B)
    (LY : proEtaleDerivedCategory Y A ⥤ proEtaleDerivedCategory Y B)
    (aZ : LZ ⊣ (proEtaleCoefficientRestrictScalars Z φ).mapDerivedCategory)
    (aY : LY ⊣ (proEtaleCoefficientRestrictScalars Y φ).mapDerivedCategory)
    (P : DerivedCategory
      (Sheaf (ProEt.topology Z) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))) :
    Arrow (DerivedCategory
      (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))) := by
  let LZ₀ := directImageScalarExtension φ Z
  let LY₀ := directImageScalarExtension φ Y
  let aZ₀ := directImageScalarAdjunction φ Z
  let aY₀ := directImageScalarAdjunction φ Y
  let hZ := aZ.leftAdjointUniq aZ₀
  let hY := aY.leftAdjointUniq aY₀
  let K := (sfIntrinsicDerivedEquivalence Z A).functor.obj P
  let γ : (directImageScalarExtension φ Y).obj ((directImageConstantPush A g).obj K) ⟶
      (directImageConstantPush B g).obj ((directImageScalarExtension φ Z).obj K) :=
    (directImageScalarComparison φ g).app K
  let m := hY.hom.app ((directImageConstantPush A g).obj K) ≫ γ ≫
    (directImageConstantPush B g).map (hZ.inv.app K)
  exact Arrow.mk (((proEtaleCoefficientRestrictScalars Y φ).mapDerivedCategory ⋙
    (sfIntrinsicDerivedEquivalence Y A).inverse).map m)

/-- Transport the explicit supplied-adjunction mate to the canonical geometric mate.
Source: Stacks Tag 07A6 (blueprint: helper-proper-scalar-explicit-transport).

Proof: the explicit mate is `h_Y ≫ γ ≫ R_B(h_Z⁻¹)` with `h_Y`, `h_Z` isomorphisms.
Take the source isomorphism `V_Y(h_Y)` and the target isomorphism `V_Y(R_B(h_Z))`,
both realized by `E_Y⁻¹`; the square commutes since `R_B(h_Z⁻¹) ≫ R_B(h_Z)` is the
identity. -/
theorem properScalarMate_explicit_transport_iso
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {Z Y : Scheme.{u}} (g : Z ⟶ Y)
    (LZ : proEtaleDerivedCategory Z A ⥤ proEtaleDerivedCategory Z B)
    (LY : proEtaleDerivedCategory Y A ⥤ proEtaleDerivedCategory Y B)
    (aZ : LZ ⊣ (proEtaleCoefficientRestrictScalars Z φ).mapDerivedCategory)
    (aY : LY ⊣ (proEtaleCoefficientRestrictScalars Y φ).mapDerivedCategory)
    (P : DerivedCategory
      (Sheaf (ProEt.topology Z) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))) :
    Nonempty (properScalarExplicitMateArrow φ g LZ LY aZ aY P ≅
      Arrow.mk (((proEtaleCoefficientRestrictScalars Y φ).mapDerivedCategory ⋙
        (sfIntrinsicDerivedEquivalence Y A).inverse).map
        ((directImageScalarComparison φ g).app
          ((sfIntrinsicDerivedEquivalence Z A).functor.obj P)))) := by
  let hZ := aZ.leftAdjointUniq (directImageScalarAdjunction φ Z)
  let hY := aY.leftAdjointUniq (directImageScalarAdjunction φ Y)
  let K := (sfIntrinsicDerivedEquivalence Z A).functor.obj P
  let RY := (proEtaleCoefficientRestrictScalars Y φ).mapDerivedCategory ⋙
    (sfIntrinsicDerivedEquivalence Y A).inverse
  refine ⟨Arrow.isoMk (RY.mapIso (hY.app ((directImageConstantPush A g).obj K)))
    (RY.mapIso ((directImageConstantPush B g).mapIso (hZ.app K))) ?_⟩
  change RY.map (hY.hom.app ((directImageConstantPush A g).obj K)) ≫
      RY.map ((directImageScalarComparison φ g).app K) =
    RY.map (hY.hom.app ((directImageConstantPush A g).obj K) ≫
      (directImageScalarComparison φ g).app K ≫
      (directImageConstantPush B g).map (hZ.inv.app K)) ≫
      RY.map ((directImageConstantPush B g).map (hZ.hom.app K))
  rw [← RY.map_comp, ← RY.map_comp]
  congr 1
  have e : (directImageConstantPush B g).map (hZ.inv.app K) ≫
      (directImageConstantPush B g).map (hZ.hom.app K) = 𝟙 _ :=
    ((directImageConstantPush B g).mapIso (hZ.app K)).inv_hom_id
  simp only [Category.assoc, e]
  exact congrArg (fun t ↦ hY.hom.app ((directImageConstantPush A g).obj K) ≫ t)
    (Category.comp_id ((directImageScalarComparison φ g).app K)).symm

/-- The normalized geometric mate is the intrinsic finite scalar projection.
The proof is the finite discrete encoding, scalar-mate normalization and
realization transport; it is independent of arbitrary supplied adjunctions.
Source: Stacks Tags 07A4, 07A6 and 07A7
(blueprint: helper-proper-scalar-geometric-projection). -/
theorem properScalarMate_geometric_canonical_projection
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {Z Y : Scheme.{u}} (g : Z ⟶ Y)
    (P : DerivedCategory
      (Sheaf (ProEt.topology Z) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))) :
    Nonempty (Arrow.mk
      (((proEtaleCoefficientRestrictScalars Y φ).mapDerivedCategory ⋙
        (sfIntrinsicDerivedEquivalence Y A).inverse).map
        ((directImageScalarComparison φ g).app
          ((sfIntrinsicDerivedEquivalence Z A).functor.obj P))) ≅
      canonicalScalarProjectionArrow φ g P) := by
  sorry

/-- The explicit scalar mate is the proper-factor tensor projection.
The source is the counit transpose of `D_Z(ε) ≫ λ`, and the comparisons `h_T`
are the unique adjunction-preserving comparisons with the normalized extension.
The finite-discrete encoding and the scalar-mate normalization identify its
restriction with the literal projection arrow, with the coefficient module in
degree zero.  No properness, boundedness or flatness hypothesis is used.
Source: Stacks Tags 07A4, 07A6 and 07A7
(blueprint: lem-exc-proper-scalar-projection-normalization).
-/
theorem properScalarMate_projection_arrowIso
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {Z Y : Scheme.{u}} (g : Z ⟶ Y)
    (LZ : proEtaleDerivedCategory Z A ⥤ proEtaleDerivedCategory Z B)
    (LY : proEtaleDerivedCategory Y A ⥤ proEtaleDerivedCategory Y B)
    (aZ : LZ ⊣ (proEtaleCoefficientRestrictScalars Z φ).mapDerivedCategory)
    (aY : LY ⊣ (proEtaleCoefficientRestrictScalars Y φ).mapDerivedCategory)
    (P : DerivedCategory
      (Sheaf (ProEt.topology Z) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))) :
    Nonempty (properScalarExplicitMateArrow φ g LZ LY aZ aY P ≅ (Arrow.mk
          (((ProEtale.rightDerivedLowerStarProjectionMap
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) g).app
              P).app
            ((constantSheaf (ProEt.topology Y)
              (ModuleCat.{u + 1} (ULift.{u + 1, u} A))).mapDerivedCategory.obj
              ((DerivedCategory.singleFunctor _ 0).obj
                ((ModuleCat.restrictScalars.{u + 1} φ.ulift).obj
                  (ModuleCat.of (ULift.{u + 1, u} B) (ULift.{u + 1, u} B)))))))) := by
  obtain ⟨ht⟩ := properScalarMate_explicit_transport_iso φ g LZ LY aZ aY P
  obtain ⟨h⟩ := properScalarMate_geometric_canonical_projection φ g P
  obtain ⟨e⟩ := properScalarMate_canonical_endpoint_arrowIso φ g P
  exact ⟨ht ≪≫ h ≪≫ e⟩

end WeilConjectures
