/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportCoefficientChange
import WeilConjectures.CategoryTheory.Adjunction.SquareCompatibleMate
import all WeilConjectures.AlgebraicGeometry.Comparison.ComparisonOpenTensorCoherence
import all WeilConjectures.AlgebraicGeometry.Etale.ProEtale.EtaleProEtaleScalarPullbackCube

/-! # Restriction and the exact open-extension site boundary

Source: Stacks 03DI, 09AF and 099R.
(blueprint: lem-sf-open-restriction-site-square).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

private theorem mate_whisker_top
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {G G' : C ⥤ E} {H : D ⥤ F}
    {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (w : TwoSquare G' L₁ L₂ H) (t : G ⟶ G') :
    mateEquiv a₁ a₂ (w.whiskerTop t) = (mateEquiv a₁ a₂ w).whiskerRight t := by
  simpa [TwoSquare.whiskerBottom, TwoSquare.whiskerLeft] using
    mateEquiv_whiskerTop_whiskerBottom a₁ a₂ w t (𝟙 H)

private theorem inverse_mate_cube
    {CA DA CB DB EA FA EB FB : Type*}
    [Category CA] [Category DA] [Category CB] [Category DB]
    [Category EA] [Category FA] [Category EB] [Category FB]
    {LA : CA ⥤ DA} {RA : DA ⥤ CA} {LB : CB ⥤ DB} {RB : DB ⥤ CB}
    {LA' : EA ⥤ FA} {RA' : FA ⥤ EA} {LB' : EB ⥤ FB} {RB' : FB ⥤ EB}
    (aA : LA ⊣ RA) (aB : LB ⊣ RB) (bA : LA' ⊣ RA') (bB : LB' ⊣ RB')
    {U : CB ⥤ CA} {V : DB ⥤ DA} {U' : EB ⥤ EA} {V' : FB ⥤ FA}
    {GA : CA ⥤ EA} {HA : DA ⥤ FA} {GB : CB ⥤ EB} {HB : DB ⥤ FB}
    (aa : TwoSquare GA LA LA' HA) (ab : TwoSquare GB LB LB' HB)
    (k : TwoSquare U LB LA V) (i : TwoSquare U' LB' LA' V')
    (t : U ⋙ GA ⟶ GB ⋙ U') (s : V ⋙ HA ⟶ HB ⋙ V')
    (h : ∀ M : DB,
      t.app (RB.obj M) ≫ U'.map ((mateEquiv aB bB ab).app M) ≫
          (mateEquiv bB bA i).app (HB.obj M) =
        GA.map ((mateEquiv aB aA k).app M) ≫
          (mateEquiv aA bA aa).app (V.obj M) ≫ RA'.map (s.app M))
    (N : CB) :
    LA'.map (t.app N) ≫ i.app (GB.obj N) ≫ V'.map (ab.app N) =
      aa.app (U.obj N) ≫ HA.map (k.app N) ≫ s.app (LB.obj N) := by
  have hc : (ab.hComp i).whiskerTop t = (k.hComp aa).whiskerBottom s := by
    apply (mateEquiv aB bA).injective
    rw [mate_whisker_top, mateEquiv_whiskerBottom,
      mateEquiv_vcomp aB bB bA, mateEquiv_vcomp aB aA bA]
    ext M
    simpa only [TwoSquare.vComp, TwoSquare.whiskerRight, TwoSquare.whiskerLeft,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Category.id_comp, Category.comp_id, Category.assoc] using h M
  simpa only [TwoSquare.hComp, TwoSquare.whiskerTop, TwoSquare.whiskerBottom,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Category.assoc] using
    congrArg (fun w ↦ w.natTrans.app N) hc

private theorem support_pullback_eq
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (j : X ⟶ Y) :
    supportSiteComparisonCoefficientPullbackIso (ModuleCat.{u + 1} A) j =
      (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} A) j).symm := by
  rfl

private theorem exact_open_site_mate
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] :
    (mapDerivedCategoryOpenImmersionLowerShriekComparisonUpperStarIso
      (ModuleCat.{u + 1} A) j).inv =
      ((mateEquiv
        (Etale.derivedOpenImmersionLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} A) j)
        (derivedOpenImmersionLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} A) j)).symm
          (TwoSquare.mk _ _ _ _ (Functor.mapDerivedCategorySquareIso
            (F₁ := Etale.upperStar (ModuleCat.{u + 1} A) j)
            (F₂ := comparisonUpperStar (ModuleCat.{u + 1} A) X)
            (G₁ := comparisonUpperStar (ModuleCat.{u + 1} A) Y)
            (G₂ := upperStar (ModuleCat.{u + 1} A) j)
            (supportSiteComparisonCoefficientPullbackIso (ModuleCat.{u + 1} A) j)).hom)
      ).natTrans := by
  apply NatTrans.ext
  funext K
  apply ((derivedOpenImmersionLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} A) j).homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit]
  erw [← unit_mateEquiv_symm]
  exact comparison_derived_extension_mate A j K

private theorem etale_open_exact_mate
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    [IsIso (Etale.coefficientRestrictionOpenMap φ j)] :
    (Functor.mapDerivedCategorySquareIso
      (asIso (Etale.coefficientRestrictionOpenMap φ j))).hom =
      ((mateEquiv
        (Etale.openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B)
          j).mapDerivedCategoryAdjunction
        (Etale.openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A)
          j).mapDerivedCategoryAdjunction).symm
        (TwoSquare.mk _ _ _ _ (Functor.mapDerivedCategorySquareIso
          (asIso (Etale.upperStarRestrictScalars φ j).natTrans).symm).hom)).natTrans := by
  apply NatTrans.ext
  funext K
  apply (((Etale.openImmersionLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} A) j).mapDerivedCategoryAdjunction).homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit]
  erw [← unit_mateEquiv_symm]
  apply Adjunction.mapDerivedCategoryAdjunction_mate
  intro M
  exact (unit_mateEquiv_symm
    (Etale.openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j)
    (Etale.openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j)
    (TwoSquare.mk _ _ _ _
      (asIso (Etale.upperStarRestrictScalars φ j).natTrans).inv) M).symm

private theorem etale_restriction_iso_eq
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {X Y : Scheme.{u}} (p : X ⟶ Y) :
    Etale.upperStarRestrictScalarsIso φ p = Etale.upperStarRestrictScalarsIsoSheaf φ p := by
  let a := (Sheaf.restrictCoextendScalarsAdj Y.smallEtaleTopology φ).comp
    (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p)
  let b := (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) p).comp
    (Sheaf.restrictCoextendScalarsAdj X.smallEtaleTopology φ)
  apply Iso.ext
  apply (conjugateEquiv b a).injective
  rw [Etale.conjugateEquiv_upperStarRestrictScalarsIso_hom]
  exact (congrArg Iso.inv ((conjugateIsoEquiv a b).apply_symm_apply (Iso.refl _))).symm

private theorem square_symm
    {C D E V : Type*} [Category C] [Category D] [Category E] [Category V]
    [Abelian C] [Abelian D] [Abelian E] [Abelian V]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory E] [HasDerivedCategory V]
    {F : C ⥤ D} {G : D ⥤ V} {H : C ⥤ E} {J : E ⥤ V}
    [F.Additive] [G.Additive] [H.Additive] [J.Additive]
    [Limits.PreservesFiniteLimits F] [Limits.PreservesFiniteColimits F]
    [Limits.PreservesFiniteLimits G] [Limits.PreservesFiniteColimits G]
    [Limits.PreservesFiniteLimits H] [Limits.PreservesFiniteColimits H]
    [Limits.PreservesFiniteLimits J] [Limits.PreservesFiniteColimits J]
    (e : F ⋙ G ≅ H ⋙ J) :
    Functor.mapDerivedCategorySquareIso e.symm =
      (Functor.mapDerivedCategorySquareIso e).symm := by
  ext M
  simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv, Functor.mapDerivedCategoryNatIso_symm,
    NatTrans.comp_app, Category.assoc]

private theorem reverse_hexagon
    {C : Type*} [Category C] {V₀ V₁ V₂ V₃ V₄ V₅ : C}
    (a : V₀ ≅ V₁) (b : V₁ ≅ V₂) (c : V₂ ≅ V₃)
    (d : V₀ ≅ V₄) (e : V₄ ≅ V₅) (f : V₅ ≅ V₃)
    (h : a.hom ≫ b.hom ≫ c.hom = d.hom ≫ e.hom ≫ f.hom) :
    f.hom ≫ c.inv ≫ b.inv = e.inv ≫ d.inv ≫ a.hom := by
  apply (cancel_epi (d.hom ≫ e.hom)).mp
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← reassoc_of% h]
  simp only [Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]

private theorem inverse_exact_restriction_cube
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y : Scheme.{u}} (j : X ⟶ Y)
    (M : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} B))) :
    (pbcDerivedComparisonRestrict X φ).inv.app
        ((Etale.upperStar (ModuleCat.{u + 1} B) j).mapDerivedCategory.obj M) ≫
      (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ).map
        ((Functor.mapDerivedCategorySquareIso
          (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} B) j)).inv.app M) ≫
      (Functor.mapDerivedCategorySquareIso (upperStarRestrictScalarsIso φ j)).inv.app
        ((comparisonUpperStar (ModuleCat.{u + 1} B) Y).mapDerivedCategory.obj M) =
    (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.map
        ((Functor.mapDerivedCategorySquareIso
          (Etale.upperStarRestrictScalarsIsoSheaf φ j)).inv.app M) ≫
      (Functor.mapDerivedCategorySquareIso
        (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} A) j)).inv.app
        ((Sheaf.derivedRestrictScalars Y.smallEtaleTopology φ).obj M) ≫
      (upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategory.map
        ((pbcDerivedComparisonRestrict Y φ).inv.app M) := by
  exact reverse_hexagon
    ((upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategory.mapIso
      ((pbcDerivedComparisonRestrict Y φ).symm.app M))
    ((Functor.mapDerivedCategorySquareIso (upperStarRestrictScalarsIso φ j)).app
      ((comparisonUpperStar (ModuleCat.{u + 1} B) Y).mapDerivedCategory.obj M))
    ((Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ).mapIso
      ((Functor.mapDerivedCategorySquareIso
        (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} B) j)).app M))
    ((Functor.mapDerivedCategorySquareIso
      (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} A) j)).app
      ((Sheaf.derivedRestrictScalars Y.smallEtaleTopology φ).obj M))
    ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.mapIso
      ((Functor.mapDerivedCategorySquareIso (Etale.upperStarRestrictScalarsIsoSheaf φ j)).app M))
    ((pbcDerivedComparisonRestrict X φ).symm.app
      ((Etale.upperStar (ModuleCat.{u + 1} B) j).mapDerivedCategory.obj M))
    (exact_restriction_cube φ j M)

private theorem ambient_open_cube
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    [IsIso (Etale.coefficientRestrictionOpenMap φ j)]
    (M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))) :
    (openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.map
        ((pbcDerivedComparisonRestrict X φ).inv.app M) ≫
      (fixedScalarRestrictionOpenMap φ j).app
        ((comparisonUpperStar (ModuleCat.{u + 1} B) X).mapDerivedCategory.obj M) ≫
      (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Y) φ).map
        ((mapDerivedCategoryOpenImmersionLowerShriekComparisonUpperStarIso
          (ModuleCat.{u + 1} B) j).inv.app M) =
    (mapDerivedCategoryOpenImmersionLowerShriekComparisonUpperStarIso
        (ModuleCat.{u + 1} A) j).inv.app
        ((Sheaf.derivedRestrictScalars X.smallEtaleTopology φ).obj M) ≫
      (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.map
        ((Functor.mapDerivedCategorySquareIso
          (asIso (Etale.coefficientRestrictionOpenMap φ j))).hom.app M) ≫
      (pbcDerivedComparisonRestrict Y φ).inv.app
        ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} B) j).mapDerivedCategory.obj M) := by
  let aA := (Etale.openImmersionLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} A) j).mapDerivedCategoryAdjunction
  let aB := (Etale.openImmersionLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} B) j).mapDerivedCategoryAdjunction
  let bA := (openImmersionLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} A) j).mapDerivedCategoryAdjunction
  let bB := (openImmersionLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} B) j).mapDerivedCategoryAdjunction
  let sA := Functor.mapDerivedCategorySquareIso
    (F₁ := Etale.upperStar (ModuleCat.{u + 1} A) j)
    (F₂ := comparisonUpperStar (ModuleCat.{u + 1} A) X)
    (G₁ := comparisonUpperStar (ModuleCat.{u + 1} A) Y)
    (G₂ := upperStar (ModuleCat.{u + 1} A) j)
    (supportSiteComparisonCoefficientPullbackIso (ModuleCat.{u + 1} A) j)
  let sB := Functor.mapDerivedCategorySquareIso
    (F₁ := Etale.upperStar (ModuleCat.{u + 1} B) j)
    (F₂ := comparisonUpperStar (ModuleCat.{u + 1} B) X)
    (G₁ := comparisonUpperStar (ModuleCat.{u + 1} B) Y)
    (G₂ := upperStar (ModuleCat.{u + 1} B) j)
    (supportSiteComparisonCoefficientPullbackIso (ModuleCat.{u + 1} B) j)
  let qE := Functor.mapDerivedCategorySquareIso (Etale.upperStarRestrictScalarsIso φ j).symm
  let qP := Functor.mapDerivedCategorySquareIso (upperStarRestrictScalarsIso φ j)
  have h := inverse_mate_cube aA aB bA bB
    ((mateEquiv aA bA).symm (TwoSquare.mk _ _ _ _ sA.hom))
    ((mateEquiv aB bB).symm (TwoSquare.mk _ _ _ _ sB.hom))
    ((mateEquiv aB aA).symm (TwoSquare.mk _ _ _ _ qE.hom))
    ((mateEquiv bB bA).symm (TwoSquare.mk _ _ _ _ qP.inv))
    (pbcDerivedComparisonRestrict X φ).inv (pbcDerivedComparisonRestrict Y φ).inv
    (fun N ↦ by
      simp only [Equiv.apply_symm_apply]
      simpa only [sA, sB, qE, qP, support_pullback_eq,
        etale_restriction_iso_eq, square_symm, Iso.symm_hom] using
        inverse_exact_restriction_cube φ j N) M
  rw [exact_open_site_mate, exact_open_site_mate, etale_open_exact_mate]
  simpa only [aA, aB, bA, bB, sA, sB, qE, qP,
    Etale.derivedOpenImmersionLowerShriekUpperStarAdjunction,
    derivedOpenImmersionLowerShriekUpperStarAdjunction,
    Etale.upperStarRestrictScalarsIso,
    ← fixedScalarRestrictionOpenMap_eq_exact_mate] using h

private theorem plus_comp_inv
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    [Limits.PreservesFiniteLimits F] [Limits.PreservesFiniteColimits F]
    [Limits.PreservesFiniteLimits G] [Limits.PreservesFiniteColimits G]
    (L : DerivedCategory.Plus C) :
    DerivedCategory.Plus.ι.map ((Functor.mapDerivedCategoryPlusCompIso F G).inv.app L) =
      (Functor.mapDerivedCategoryCompIso F G).inv.app L.obj := by
  have he : DerivedCategory.Plus.ι.mapIso
      ((Functor.mapDerivedCategoryPlusCompIso F G).app L) =
      (Functor.mapDerivedCategoryCompIso F G).app L.obj :=
    Iso.ext (Functor.ι_map_mapDerivedCategoryPlusCompIso_hom_app F G L)
  exact congrArg Iso.inv he

private theorem etale_open_plus_normalization
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    [IsIso (Etale.coefficientRestrictionOpenMap φ j)]
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))) :
    (((Etale.coefficientRestrictionOpenPlus φ j).hom.app L).hom) =
      (Functor.mapDerivedCategorySquareIso
        (asIso (Etale.coefficientRestrictionOpenMap φ j))).hom.app L.obj := by
  change DerivedCategory.Plus.ι.map
    ((Etale.coefficientRestrictionOpenPlus φ j).hom.app L) = _
  simp only [Etale.coefficientRestrictionOpenPlus, Functor.mapDerivedCategorySquareIso,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.map_comp]
  rw [plus_comp_inv, Functor.ι_map_mapDerivedCategoryPlusNatIso_hom_app,
    Functor.ι_map_mapDerivedCategoryPlusCompIso_hom_app]
  rfl

/-- The exact open site boundary with its output in the bounded etale category.
Source: Stacks 03DI, 09AF and 099R
(blueprint: lem-sf-open-restriction-site-square). -/
def openRestrictionSiteBoundary (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] :
    (DerivedCategory.Plus.ι ⋙
      (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory) ⋙
        (openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory ≅
    (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategoryPlus ⋙
      (DerivedCategory.Plus.ι ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory) :=
  Functor.isoWhiskerLeft DerivedCategory.Plus.ι
      ((Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
        Functor.mapDerivedCategoryNatIso
          (openImmersionLowerShriekComparisonUpperStarIso (ModuleCat.{u + 1} A) j).symm ≪≫
        Functor.mapDerivedCategoryCompIso _ _) ≪≫
    Functor.isoWhiskerRight
      ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategoryPlusCompatibility
        ).symm _

private theorem open_boundary_normalization
    (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (openRestrictionSiteBoundary A j).hom.app L =
      (mapDerivedCategoryOpenImmersionLowerShriekComparisonUpperStarIso
        (ModuleCat.{u + 1} A) j).inv.app L.obj := by
  simp only [openRestrictionSiteBoundary,
    mapDerivedCategoryOpenImmersionLowerShriekComparisonUpperStarIso,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.comp_app,
    Functor.mapDerivedCategoryPlusCompatibility, Iso.refl_inv, NatTrans.id_app,
    Functor.mapDerivedCategoryNatIso_symm, Category.assoc]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]
  rfl

/-- Scalar restriction respects the specified exact open-extension site boundary.
Source: Stacks 03DI, 09AF and 099R
(blueprint: lem-sf-open-restriction-site-square).

Proof: comparison restriction and restriction to an open are literal restrictions
of sections. They commute with scalar coextension, so their sectionwise cube is
commutative. Conjugate its comparison/scalar faces using the
restriction/coextension adjunction and take the inverse open mates. The open
extension site comparison and both open coefficient restriction maps are exactly
these unit-normalized mates. Thus mate pasting gives the ordinary open-extension
cube. All its functors are exact, so termwise descent gives the unbounded derived
cube. Insert the exact D-plus inclusion comparisons on the etale open functors;
compatibility of exact derived squares with these inclusions gives the equation.
On an empty open the maps are the unique maps between zero objects; identity
opens give the same unit equation, so neither case requires an exception. -/
theorem openRestriction_site_square
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))) :
    (openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.map
        ((pbcDerivedComparisonRestrict X φ).inv.app L.obj) ≫
      (fixedScalarRestrictionOpen φ j).hom.app
        ((comparisonUpperStar (ModuleCat.{u + 1} B) X).mapDerivedCategory.obj L.obj) ≫
      (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Y) φ).map
        ((openRestrictionSiteBoundary B j).hom.app L) =
    (openRestrictionSiteBoundary A j).hom.app
        ((Sheaf.restrictScalars X.smallEtaleTopology φ).mapDerivedCategoryPlus.obj L) ≫
      (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.map
        (((Etale.coefficientRestrictionOpenPlus φ j).hom.app L).hom) ≫
      (pbcDerivedComparisonRestrict Y φ).inv.app
        ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} B) j).mapDerivedCategoryPlus.obj
          L).obj := by
  let := Etale.coefficientRestrictionOpenMap_isIso φ j
  rw [open_boundary_normalization, open_boundary_normalization,
    etale_open_plus_normalization]
  simpa only [fixedScalarRestrictionOpen, asIso_hom,
    Functor.mapDerivedCategoryPlus, ObjectProperty.lift_obj_obj,
    Functor.comp_obj, ObjectProperty.ι_obj] using ambient_open_cube φ j L.obj

end AlgebraicGeometry.ProEtale
