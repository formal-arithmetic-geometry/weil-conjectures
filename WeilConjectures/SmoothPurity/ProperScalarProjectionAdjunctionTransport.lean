/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Support.SupportScalarProjectionCoordinates
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Unique

/-! # Transport of proper scalar mates between left-adjoint choices -/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- Proper scalar mates are unchanged up to an arrow isomorphism when the left adjoints
are replaced by other left adjoints of the same restriction functors.
Source: Stacks Tag 07A6 (blueprint: helper-proper-scalar-adjunction-transport).

Proof: use `Adjunction.leftAdjointUniq` at both schemes.  The mate uniqueness identity
transports the restriction square across these two canonical left-adjoint isomorphisms;
`Arrow.isoMk` packages the resulting source and target isomorphisms.  Naturality and the
triangle identities show that the resulting square commutes at every input.
-/
theorem properScalarMate_arrowIso_of_adjunctions
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {Z Y : Scheme.{u}} (g : Z ⟶ Y)
    (LZ LZ' : proEtaleDerivedCategory Z A ⥤ proEtaleDerivedCategory Z B)
    (LY LY' : proEtaleDerivedCategory Y A ⥤ proEtaleDerivedCategory Y B)
    (aZ : LZ ⊣ (proEtaleCoefficientRestrictScalars Z φ).mapDerivedCategory)
    (aZ' : LZ' ⊣ (proEtaleCoefficientRestrictScalars Z φ).mapDerivedCategory)
    (aY : LY ⊣ (proEtaleCoefficientRestrictScalars Y φ).mapDerivedCategory)
    (aY' : LY' ⊣ (proEtaleCoefficientRestrictScalars Y φ).mapDerivedCategory)
    (P : DerivedCategory
      (Sheaf (ProEt.topology Z) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))) :
    Nonempty (properScalarMateArrow φ g LZ LY aZ aY P ≅
      properScalarMateArrow φ g LZ' LY' aZ' aY' P) := by
  let q := sfDerivedImageRestriction g φ
  let sZ := aZ.leftAdjointUniq aZ'
  let sY := aY.leftAdjointUniq aY'
  let v := TwoSquare.mk _ _ _ _ q.hom
  let w := (mateEquiv aZ' aY').symm v
  have hw := mateEquiv_leftAdjointUniq aZ aZ' aY aY' w
  dsimp [w, v] at hw
  let RY := (proEtaleCoefficientRestrictScalars Y φ).mapDerivedCategory
      ⋙ (sfIntrinsicDerivedEquivalence Y A).inverse
  let F := proEtaleConstantDerivedDirectImage g A
  let G := proEtaleConstantDerivedDirectImage g B
  let EZ := (sfIntrinsicDerivedEquivalence Z A).functor
  let eS := RY.mapIso (sY.app (F.obj (EZ.obj P)))
  let eT := RY.mapIso (G.mapIso (sZ.app (EZ.obj P)))
  have htransport :
      TwoSquare.mk _ _ _ _
          (F.whiskerLeft sY.hom ≫ w.natTrans ≫ Functor.whiskerRight sZ.inv G) =
        (mateEquiv aZ aY).symm v := by
    apply (mateEquiv aZ aY).injective
    rw [Equiv.apply_symm_apply]
    rw [← Equiv.apply_symm_apply (mateEquiv aZ' aY') v]
    simpa only [F, G, sY, sZ, w] using hw
  have hcomp := congrArg (fun t ↦ t.natTrans.app (EZ.obj P)) htransport
  have hcomp' :
      sY.hom.app (F.obj (EZ.obj P)) ≫
          w.natTrans.app (EZ.obj P) ≫ G.map (sZ.inv.app (EZ.obj P)) =
        ((mateEquiv aZ aY).symm v).natTrans.app (EZ.obj P) := by
    change sY.hom.app (F.obj (EZ.obj P)) ≫
        w.natTrans.app (EZ.obj P) ≫ G.map (sZ.inv.app (EZ.obj P)) =
      ((mateEquiv aZ aY).symm v).natTrans.app (EZ.obj P) at hcomp
    exact hcomp
  refine ⟨Arrow.isoMk eS eT ?_⟩
  change RY.map (sY.hom.app (F.obj (EZ.obj P))) ≫
      RY.map (w.natTrans.app (EZ.obj P)) =
    RY.map (((mateEquiv aZ aY).symm v).natTrans.app (EZ.obj P)) ≫
      RY.map (G.map (sZ.hom.app (EZ.obj P)))
  calc
    _ = RY.map (sY.hom.app (F.obj (EZ.obj P)) ≫
        w.natTrans.app (EZ.obj P) ≫ G.map (sZ.inv.app (EZ.obj P))) ≫
        RY.map (G.map (sZ.hom.app (EZ.obj P))) := by
      rw [← RY.map_comp, ← RY.map_comp]
      apply congrArg RY.map
      simp only [Category.assoc]
      rw [← G.map_comp, Iso.inv_hom_id_app, G.map_id]
      rw [← Category.assoc]
      exact (Category.comp_id
        (sY.hom.app (F.obj (EZ.obj P)) ≫ w.natTrans.app (EZ.obj P))).symm
    _ = RY.map (((mateEquiv aZ aY).symm v).natTrans.app (EZ.obj P)) ≫
        RY.map (G.map (sZ.hom.app (EZ.obj P))) := by rw [hcomp']
    _ = _ := by
      rfl

end WeilConjectures
