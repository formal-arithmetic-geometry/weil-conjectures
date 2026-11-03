/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Support.SupportScalarProjectionCoordinates
import WeilConjectures.SmoothPurity.Support.SupportScalarMateCanonicalOpen
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Unique

/-! # Components of support scalar normalization -/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- Removing the invertible open scalar factor identifies the support scalar mate
with the direct-image scalar mate on the open extension, for a middle scalar
adjunction supplied by the canonical extension construction.
Source: Stacks 03DI, 0GL6 and 07A6
(blueprint: lem-exc-support-scalar-open-transport).

Proof: take as witnesses the canonical derived scalar extension on the middle
scheme, `ProEtale.scalarExtension φ c.Z`, with its unit-normalized adjunction
`proEtaleRingDerivedExtensionAdjunction` along the constant lifted ring map.
First replace the supplied source adjunction `aX` by the canonical one `a0` on `X`:
by `mateEquiv_leftAdjointUniq` (with `aY.leftAdjointUniq aY = Iso.refl`) the mate
under `(aX, aY)` is the mate under `(a0, aY)` followed by the compact-support image of
the uniqueness comparison `a0.leftAdjointUniq aX`; so the two realized arrows are
isomorphic with the identity at the source and the realized image of that comparison
at the target (`Arrow.isoMk`). Then compose with the canonical open-factor removal
`supportScalarMate_canonical_open` (blueprint: new-support-scalar-mate-canonical-open),
which identifies the canonical realized mate with the proper scalar mate on the fixed
open extension. Only units, counits and naturality are used: no flatness,
boundedness or direct-image invertibility. -/
theorem supportScalarMate_open_arrowIso
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (LX : proEtaleDerivedCategory X A ⥤ proEtaleDerivedCategory X B)
    (LY : proEtaleDerivedCategory Y A ⥤ proEtaleDerivedCategory Y B)
    (aX : LX ⊣ (proEtaleCoefficientRestrictScalars X φ).mapDerivedCategory)
    (aY : LY ⊣ (proEtaleCoefficientRestrictScalars Y φ).mapDerivedCategory)
    (K : DerivedCategory
      (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))) :
    ∃ (LZ : proEtaleDerivedCategory c.Z A ⥤ proEtaleDerivedCategory c.Z B)
      (aZ : LZ ⊣ (proEtaleCoefficientRestrictScalars c.Z φ).mapDerivedCategory),
    Nonempty ((Arrow.mk
        (((proEtaleCoefficientRestrictScalars Y φ).mapDerivedCategory ⋙
            (sfIntrinsicDerivedEquivalence Y A).inverse).map
          (((mateEquiv aX aY).symm
            (TwoSquare.mk _ _ _ _ (sfCompactSupportRestriction c φ).hom)).natTrans.app
              ((sfIntrinsicDerivedEquivalence X A).functor.obj K)))) ≅
      properScalarMateArrow φ c.g LZ LY aZ aY
        ((ProEtale.openImmersionLowerShriek
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c.i).mapDerivedCategory.obj K)) := by
  let LZ := AlgebraicGeometry.ProEtale.scalarExtension φ c.Z
  let aZ := AlgebraicGeometry.Scheme.proEtaleRingDerivedExtensionAdjunction
    (AlgebraicGeometry.Scheme.proEtaleConstantRingMap (T := c.Z) φ)
  refine ⟨LZ, aZ, ?_⟩
  have h₁ : Nonempty (Arrow.mk
      (((proEtaleCoefficientRestrictScalars Y φ).mapDerivedCategory ⋙
        (sfIntrinsicDerivedEquivalence Y A).inverse).map
        (((mateEquiv aX aY).symm
          (TwoSquare.mk _ _ _ _ (sfCompactSupportRestriction c φ).hom)).natTrans.app
          ((sfIntrinsicDerivedEquivalence X A).functor.obj K))) ≅ Arrow.mk
      (((proEtaleCoefficientRestrictScalars Y φ).mapDerivedCategory ⋙
        (sfIntrinsicDerivedEquivalence Y A).inverse).map
        (((mateEquiv
          (Scheme.proEtaleRingDerivedExtensionAdjunction
            (proEtaleConstantRingMap (T := X) φ))
          aY).symm
          (TwoSquare.mk _ _ _ _ (sfCompactSupportRestriction c φ).hom)).natTrans.app
          ((sfIntrinsicDerivedEquivalence X A).functor.obj K)))) := by
    let a0 := proEtaleRingDerivedExtensionAdjunction
      (proEtaleConstantRingMap (T := X) φ)
    let r := TwoSquare.mk _ _ _ _ (sfCompactSupportRestriction c φ).hom
    let w := (mateEquiv aX aY).symm r
    have h := mateEquiv_leftAdjointUniq a0 aX aY aY w
    have hself : aY.leftAdjointUniq aY = Iso.refl _ :=
      Iso.ext (Adjunction.leftAdjointUniq_refl aY)
    rw [hself] at h
    have hh := h.trans ((mateEquiv aX aY).apply_symm_apply r)
    have hh' := (mateEquiv a0 aY).injective
      (hh.trans ((mateEquiv a0 aY).apply_symm_apply r).symm)
    have h' := congrArg (fun z ↦ z.natTrans.app
      ((sfIntrinsicDerivedEquivalence X A).functor.obj K)) hh'
    let F := (proEtaleCoefficientRestrictScalars Y φ).mapDerivedCategory ⋙
      (sfIntrinsicDerivedEquivalence Y A).inverse
    let H := sfAmbientCompactSupportCandidate B c
    let e := H.mapIso ((a0.leftAdjointUniq aX).symm.app
      ((sfIntrinsicDerivedEquivalence X A).functor.obj K))
    refine ⟨Arrow.isoMk (Iso.refl _) (F.mapIso e) ?_⟩
    have h'' := h'
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, NatTrans.id_app,
      Functor.whiskerRight_app, Iso.refl_hom] at h''
    have hm := congrArg F.map h''
    simp only [Functor.map_comp] at hm
    let Q := LY.obj ((sfAmbientCompactSupportCandidate A c).obj
      ((sfIntrinsicDerivedEquivalence X A).functor.obj K))
    have hid : F.map (𝟙 Q) = 𝟙 (F.obj Q) := F.map_id Q
    rw [hid] at hm
    have hm' := (Category.id_comp (F.map (w.natTrans.app
      ((sfIntrinsicDerivedEquivalence X A).functor.obj K)) ≫
      F.map (H.map ((a0.leftAdjointUniq aX).inv.app
        ((sfIntrinsicDerivedEquivalence X A).functor.obj K))))).symm.trans hm
    simpa only [Arrow.mk_hom, F, e, H, w, r, a0, NatTrans.comp_app,
      Functor.whiskerLeft_app, NatTrans.id_app, Functor.map_id,
      Functor.whiskerRight_app, Functor.mapIso_hom, Iso.app_hom,
      Iso.symm_hom, Iso.refl_hom, Category.id_comp, Functor.map_comp]
      using hm'.symm
  obtain ⟨h₁⟩ := h₁
  obtain ⟨h₂⟩ := supportScalarMate_canonical_open φ c LY aY K
  exact ⟨h₁ ≪≫ (by simpa [LZ, aZ] using h₂)⟩

end WeilConjectures
