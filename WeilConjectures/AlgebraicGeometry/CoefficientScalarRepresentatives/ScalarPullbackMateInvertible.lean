/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoefficientScalarRepresentatives.CoefficientScalarRepresentatives
public import WeilConjectures.CategoryTheory.Etale.EtaleUnboundedRestrictionComparison
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.RestrictScalars
import WeilConjectures.Algebra.Homology.SixFunctors.OrdinaryDerivedChangeOfRings
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.AlgebraicGeometry.EtaleRestrictScalarsAdjunctionIdentities
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat

/-! # Invertibility of the canonical inverse scalar/pullback mate

Source: scalar-six pullback proof (1), Stacks 06YY, 07A4 and 0G7E;
orientation base-change factors proof (1)
(blueprint: lem-sfb-proetale-scalar-pullback-mate-invertible).

The restriction squares below are obtained termwise from the ordinary canonical
squares and transported through the exact geometric derived comparisons.
The scalar adjunctions are fixed by CoefficientScalarRepresentatives.adjunction.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.CoefficientScalarRepresentatives

private theorem pro_ordinary_iso
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (a : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsIso (((mateEquiv (ordinaryAdjunction (Scheme.ProEt.topology Y) a)
      (ordinaryAdjunction (Scheme.ProEt.topology X) a)).symm
      (TwoSquare.mk _ _ _ _ (upperStarRestrictScalarsIso a f).hom)).natTrans) := by
  apply isIso_left_mate_of_iterated
    (ordinaryAdjunction (Scheme.ProEt.topology Y) a)
    (ordinaryAdjunction (Scheme.ProEt.topology X) a)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f)
  have h := mate_of_conjugate
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
    (Sheaf.restrictCoextendScalarsAdj (Scheme.ProEt.topology X) a)
    (Sheaf.restrictCoextendScalarsAdj (Scheme.ProEt.topology Y) a)
    (Iso.refl _) (show lowerStar (ModuleCat.{u + 1} B) f ⋙
      Sheaf.restrictScalars (Scheme.ProEt.topology Y) a ⟶
      Sheaf.restrictScalars (Scheme.ProEt.topology X) a ⋙
        lowerStar (ModuleCat.{u + 1} A) f from 𝟙 _) (by
      ext F V x
      simp only [mateEquiv_apply, NatTrans.comp_app, Functor.comp_obj,
        Functor.rightUnitor_inv_app, Functor.leftUnitor_hom_app,
        Functor.associator_hom_app, Functor.associator_inv_app,
        Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.id_app,
        Category.id_comp]
      exact congrArg (fun k ↦ k.hom x)
        ((ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1} a).right_triangle_components
          _))
  change (mateEquiv _ _ (TwoSquare.mk _ _ _ _
    (upperStarRestrictScalarsIso a f).hom)).natTrans = _ at h
  rw [h]
  infer_instance

private theorem pro_computed_iso
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (a : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsIso (((mateEquiv
      (scalarDerivedAdjunctionData (Scheme.ProEt.topology Y) a).adjunction
      (scalarDerivedAdjunctionData (Scheme.ProEt.topology X) a).adjunction).symm
      (TwoSquare.mk _ _ _ _
        (Functor.mapDerivedCategorySquareIso
          (upperStarRestrictScalarsIso a f)).hom)).natTrans) := by
  have := pro_flat A f
  have : IsIso (((mateEquiv
      (ordinaryAdjunction (Scheme.ProEt.topology Y) a)
      (ordinaryAdjunction (Scheme.ProEt.topology X) a)).symm
      (TwoSquare.mk _ _ _ _ (upperStarRestrictScalarsIso a f).symm.inv)).natTrans) := by
    simpa only [Iso.symm_inv] using pro_ordinary_iso a f
  have h := derived_mate_isIso_of_flat
    (A := Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A))
    (B := Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} B))
    (C := Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))
    (D := Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} B))
    (ordinaryAdjunction (Scheme.ProEt.topology Y) a)
    (ordinaryAdjunction (Scheme.ProEt.topology X) a)
    (scalarDerivedAdjunctionData (Scheme.ProEt.topology Y) a)
    (scalarDerivedAdjunctionData (Scheme.ProEt.topology X) a)
    (upperStar (ModuleCat.{u + 1} A) f)
    (upperStar (ModuleCat.{u + 1} B) f)
    (upperStarRestrictScalarsIso a f).symm
  have hs : (Functor.mapDerivedCategoryNatIso
      (upperStarRestrictScalarsIso a f).symm).inv =
      (Functor.mapDerivedCategoryNatIso (upperStarRestrictScalarsIso a f)).hom := by
    simpa only [Iso.symm_symm_eq] using
      (Functor.mapDerivedCategoryNatIso_symm (upperStarRestrictScalarsIso a f).symm).symm
  simpa only [Functor.mapDerivedCategorySquareIso,
    Functor.mapDerivedCategoryNatIso_symm, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv, hs, Category.assoc] using h

/-- The pro-etale inverse scalar mate is invertible for arbitrary coefficient maps.
Source: Stacks 07A4 and 0G7E
(blueprint: lem-sfb-proetale-scalar-pullback-mate-invertible).
Proof: the ordinary left mate is invertible by iterated mates and pointwise
restriction/coextension. Representably flat base change preserves the local relation
criterion for flat sheaves. The resulting flat K-flat resolutions compute the
left derived scalar mate. Finally transport the mate across uniqueness of scalar
left adjoints and the canonical exact geometric comparison. -/
theorem proEtaleScalarPullbackMate_isIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (a : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsIso (((mateEquiv
      (adjunction (Scheme.ProEt.topology Y) a)
      (adjunction (Scheme.ProEt.topology X) a)).symm
      (TwoSquare.mk _ _ _ _
        (ProEtale.leftDerivedUpperStarRestrictScalarsIso a f).hom)).natTrans) := by
  have := pro_computed_iso a f
  have := isIso_left_mate_change_adjunction
    (adjunction (Scheme.ProEt.topology Y) a)
    (adjunction (Scheme.ProEt.topology X) a)
    (scalarDerivedAdjunctionData (Scheme.ProEt.topology Y) a).adjunction
    (scalarDerivedAdjunctionData (Scheme.ProEt.topology X) a).adjunction
    (Functor.mapDerivedCategorySquareIso (upperStarRestrictScalarsIso a f)).hom
  exact transport_left_mate
    (adjunction (Scheme.ProEt.topology Y) a)
    (adjunction (Scheme.ProEt.topology X) a)
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f)
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) f)
    (Functor.mapDerivedCategorySquareIso (upperStarRestrictScalarsIso a f)).hom

/-- The etale inverse scalar mate is invertible for arbitrary coefficient maps.
Source: Stacks 07A4 and 0G7E
(blueprint: lem-sfb-proetale-scalar-pullback-mate-invertible).
Proof: apply the ordinary restriction/direct-image mate identity, then the flat
resolution comparison. Etale pullback preserves flatness stalkwise. Uniqueness of
left adjoints and the exact geometric comparison transport invertibility to the
specified scalar adjunction. -/
theorem etaleScalarPullbackMate_isIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (a : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsIso (((mateEquiv
      (adjunction Y.smallEtaleTopology a)
      (adjunction X.smallEtaleTopology a)).symm
      (TwoSquare.mk _ _ _ _ (Etale.scalarRestrictionPullbackIso a f).hom)).natTrans) := by
  have := et_computed_iso a f
  have := isIso_left_mate_change_adjunction
    (adjunction Y.smallEtaleTopology a)
    (adjunction X.smallEtaleTopology a)
    (scalarDerivedAdjunctionData Y.smallEtaleTopology a).adjunction
    (scalarDerivedAdjunctionData X.smallEtaleTopology a).adjunction
    (Functor.mapDerivedCategorySquareIso (Etale.upperStarRestrictScalarsIsoSheaf a f)).hom
  exact transport_left_mate
    (adjunction Y.smallEtaleTopology a)
    (adjunction X.smallEtaleTopology a)
    (Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f)
    (Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) f)
    (Functor.mapDerivedCategorySquareIso (Etale.upperStarRestrictScalarsIsoSheaf a f)).hom

private theorem et_computed_iso
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (a : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsIso (((mateEquiv
      (scalarDerivedAdjunctionData Y.smallEtaleTopology a).adjunction
      (scalarDerivedAdjunctionData X.smallEtaleTopology a).adjunction).symm
      (TwoSquare.mk _ _ _ _
        (Functor.mapDerivedCategorySquareIso
          (Etale.upperStarRestrictScalarsIsoSheaf a f)).hom)).natTrans) := by
  have hOrd : IsIso (((mateEquiv
      (ordinaryAdjunction Y.smallEtaleTopology a)
      (ordinaryAdjunction X.smallEtaleTopology a)).symm
      (TwoSquare.mk _ _ _ _ (Etale.upperStarRestrictScalarsIsoSheaf a f).hom)).natTrans) := by
    apply isIso_left_mate_of_iterated (ordinaryAdjunction Y.smallEtaleTopology a)
      (ordinaryAdjunction X.smallEtaleTopology a)
      (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
      (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f)
    rw [Etale.underived_mate]
    infer_instance
  have : IsIso (((mateEquiv
      (ordinaryAdjunction Y.smallEtaleTopology a)
      (ordinaryAdjunction X.smallEtaleTopology a)).symm
      (TwoSquare.mk _ _ _ _ (Etale.upperStarRestrictScalarsIsoSheaf a f).symm.inv)).natTrans) := by
    simpa only [Iso.symm_inv] using hOrd
  have h := derived_mate_isIso_of_flat
    (A := Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))
    (B := Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} B))
    (C := Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
    (D := Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))
    (ordinaryAdjunction Y.smallEtaleTopology a)
    (ordinaryAdjunction X.smallEtaleTopology a)
    (scalarDerivedAdjunctionData Y.smallEtaleTopology a)
    (scalarDerivedAdjunctionData X.smallEtaleTopology a)
    (Etale.upperStar (ModuleCat.{u + 1} A) f)
    (Etale.upperStar (ModuleCat.{u + 1} B) f)
    (Etale.upperStarRestrictScalarsIsoSheaf a f).symm
  have hs : (Functor.mapDerivedCategoryNatIso
      (Etale.upperStarRestrictScalarsIsoSheaf a f).symm).inv =
      (Functor.mapDerivedCategoryNatIso (Etale.upperStarRestrictScalarsIsoSheaf a f)).hom := by
    simpa only [Iso.symm_symm_eq] using
      (Functor.mapDerivedCategoryNatIso_symm (Etale.upperStarRestrictScalarsIsoSheaf a f).symm).symm
  simpa only [Functor.mapDerivedCategorySquareIso,
    Functor.mapDerivedCategoryNatIso_symm, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv, hs, Category.assoc] using h

end AlgebraicGeometry.CoefficientScalarRepresentatives
