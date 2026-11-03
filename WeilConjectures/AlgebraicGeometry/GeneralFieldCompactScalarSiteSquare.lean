/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionDirectImage
public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactScalarCoherence
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModuleIntrinsicComparison
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.ProEtale.Fixed.ProEtaleFixedModuleConstructible
public import WeilConjectures.AlgebraicGeometry.GeneralFieldDctf
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalObjects
public import WeilConjectures.AlgebraicGeometry.Finite.Compact.FiniteCompactSiteCoherence
public import WeilConjectures.AlgebraicGeometry.FiniteCompactScalar.FiniteCompactSupportScalarTransportData
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence
public import WeilConjectures.AlgebraicGeometry.CoefficientCompatibility.EtaleProEtaleCoefficientCompatibility
public import WeilConjectures.AlgebraicGeometry.CoefficientCompatibility.EtaleProEtaleCoefficientTransport
public import WeilConjectures.AlgebraicGeometry.CoefficientCompatibility.EtaleProEtaleCompactScalarSquare
public import WeilConjectures.AlgebraicGeometry.CoefficientCompatibility.RecordedOpenScalarNormalization
public import WeilConjectures.AlgebraicGeometry.CoefficientCompatibility.RecordedRestrictionNormalization
public import WeilConjectures.AlgebraicGeometry.Etale.Open.EtaleOpenScalarExchange
public import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingConstructibleDerivedOrigin
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantOpenSquareExchange
public import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenCoefficientMate
public import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenCoefficientRefinement
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement
public import WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange

/-!
# General-field compact-support scalar/site square

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-sp-grp-ladic-summary/sec-change-of-finite-coefficients/
sk-lem-sp-reduction/sk-lem-sp-reduction-exceptional.md, Existence and Locality and Charts
(blueprint: lem-pur-general-field-compact-scalar-site-square).

The statement uses the canonical intrinsic scalar map and the canonical etale-origin
comparison.  Its proof is postponed.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

private theorem scalarSite_unbounded_interchange
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (sq : IsPullback k r p i) (E : DerivedCategoryModule A U)
    :
    (scalarExtension φ Z).map ((properOpenCoefficientInterchange A sq).hom.app E) ≫
        finiteCoefficientDirectImageMap φ p (D((k)_!open[ModuleCat.{u + 1} A]).obj E) ≫
        R((p)_*[ModuleCat.{u + 1} B]).map ((openScalarExtension φ k).hom.app E) =
      properOpenCoefficientComposite φ sq E := by
  let := (properOpenCoefficientInterchange_normalization B sq
    ((scalarExtension φ U).obj E)).2
  have h := coefficient_interchange_of_restriction
    (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) k)
    (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) i)
    (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) k)
    (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) i)
    R((r)_*[ModuleCat.{u + 1} A]) R((p)_*[ModuleCat.{u + 1} A])
    R((r)_*[ModuleCat.{u + 1} B]) R((p)_*[ModuleCat.{u + 1} B])
    (scalarExtension φ U) (scalarExtension φ V) (scalarExtension φ W) (scalarExtension φ Z)
    (exactScalarReverse φ k) (exactScalarReverse φ i)
    (exactCoefficientMap φ r) (exactCoefficientMap φ p)
    (openScalarExtension φ k) (openScalarExtension φ i)
    (exactDerivedBaseChangeMap (ModuleCat.{u + 1} A) sq.toCommSq)
    (exactDerivedBaseChangeMap (ModuleCat.{u + 1} B) sq.toCommSq)
    (exactCoefficient_exchange φ sq.toCommSq)
    (openScalarExtension_unit φ i) (openScalarExtension_unit φ k) E
    ((properOpenCoefficientInterchange A sq).hom.app E)
    ((properOpenCoefficientInterchange B sq).hom.app ((scalarExtension φ U).obj E))
    (properOpenCoefficientInterchange_normalization A sq E).1
    (properOpenCoefficientInterchange_normalization B sq ((scalarExtension φ U).obj E)).1
  simpa only [exactCoefficientMap_app, properOpenCoefficientComposite] using h

private theorem scalarSite_unbounded_open_interchange
    [Finite A] [Finite B] (φ : A →+* B)
    {U V W Z : Scheme.{u}}
    [IsNoetherian U] [IsNoetherian V] [IsNoetherian W] [IsNoetherian Z]
    {k : U ⟶ V} {r : U ⟶ W} {p : V ⟶ Z} {i : W ⟶ Z}
    [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
    (sq : IsPullback k r p i) (E : DerivedCategoryModule A U)
    :
    (scalarExtension φ Z).map
        ((openImmersionLowerShriekLowerStarExchange
          (ModuleCat.{u + 1} A) sq.flip).app E) ≫
      (scalarMate φ p).app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} A) k).mapDerivedCategory.obj E) ≫
      (rightDerivedLowerStar (ModuleCat.{u + 1} B) p).map
        ((openScalarExtension φ k).hom.app E) =
    (openScalarExtension φ i).hom.app
        ((rightDerivedLowerStar (ModuleCat.{u + 1} A) r).obj E) ≫
      (openImmersionLowerShriek (ModuleCat.{u + 1} B) i).mapDerivedCategory.map
        ((scalarMate φ r).app E) ≫
      (openImmersionLowerShriekLowerStarExchange
        (ModuleCat.{u + 1} B) sq.flip).app ((scalarExtension φ U).obj E) := by
  simpa only [properOpenCoefficientComposite, properOpenCoefficientInterchange_source,
    finiteCoefficientDirectImage_scalarMate, rightDerivedLowerStar] using
    scalarSite_unbounded_interchange φ sq E

private theorem scalarSite_unbounded_tower
    [Finite A] [Finite B] (φ : A →+* B)
    {X Y Z : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) (d : Compactification g)
    (e : Compactification (f ≫ d.i)) (M : DerivedCategoryModule A X)
 :
    (scalarExtension φ Z).map
        ((rightDerivedLowerShriekOfCompactificationCompIso A d e).hom.app M) ≫
      (compactScalarMap φ (d.comp e)).app M =
    (compactScalarMap φ d).app
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
          e.restrict).obj M) ≫
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) d).map
        ((compactScalarMap φ e.restrict).app M) ≫
      (rightDerivedLowerShriekOfCompactificationCompIso B d e).hom.app
        ((scalarExtension φ X).obj M) := by
  have : IsLocallyNoetherian d.Z := LocallyOfFiniteType.isLocallyNoetherian d.g
  have : CompactSpace d.Z := QuasiCompact.compactSpace_of_compactSpace d.g
  have : IsNoetherian d.Z := ⟨⟩
  have : IsLocallyNoetherian e.Z := LocallyOfFiniteType.isLocallyNoetherian e.g
  have : CompactSpace e.Z := QuasiCompact.compactSpace_of_compactSpace e.g
  have : IsNoetherian e.Z := ⟨⟩
  have : IsLocallyNoetherian e.restrict.Z :=
    LocallyOfFiniteType.isLocallyNoetherian e.restrict.g
  have : CompactSpace e.restrict.Z := QuasiCompact.compactSpace_of_compactSpace e.restrict.g
  have : IsNoetherian e.restrict.Z := ⟨⟩
  have hi := scalarSite_unbounded_open_interchange φ e.isPullback_restrict.flip
    ((openImmersionLowerShriek (ModuleCat.{u + 1} A)
      e.restrict.i).mapDerivedCategory.obj M)
  have ho := scalarOpen_composition_eq φ e.restrict.i (pullback.fst e.g d.i)
    e.i e.restrict_i_fst M
  have hp := scalarMate_directImage_composition_eq φ e.g d.g (e.g ≫ d.g) rfl
    ((openImmersionLowerShriek (ModuleCat.{u + 1} A)
      (pullback.fst e.g d.i)).mapDerivedCategory.obj
        ((openImmersionLowerShriek (ModuleCat.{u + 1} A)
          e.restrict.i).mapDerivedCategory.obj M))
  rw [right_derived_star_comp_eq, right_derived_star_comp_eq] at hp
  let aR := fun (R : Type (u + 1)) [CommRing R] ↦
    ((mapDerivedCategoryOpenImmersionLowerShriekComp
      (ModuleCat.{u + 1} R) e.restrict.i (pullback.fst e.g d.i)).symm ≪≫
      mapDerivedCategoryOpenImmersionLowerShriekCongr
        (ModuleCat.{u + 1} R) e.restrict_i_fst).hom
  have h := tower_scalar_pasting
    (scalarExtension φ X) (scalarExtension φ e.restrict.Z) (scalarExtension φ e.Z)
    (scalarExtension φ Y) (scalarExtension φ d.Z) (scalarExtension φ Z)
    (openImmersionLowerShriek (ModuleCat.{u + 1} A) e.restrict.i).mapDerivedCategory
    (openImmersionLowerShriek (ModuleCat.{u + 1} A)
      (pullback.fst e.g d.i)).mapDerivedCategory
    (openImmersionLowerShriek (ModuleCat.{u + 1} A) e.i).mapDerivedCategory
    (openImmersionLowerShriek (ModuleCat.{u + 1} A) d.i).mapDerivedCategory
    (rightDerivedLowerStar (ModuleCat.{u + 1} A) e.restrict.g)
    (rightDerivedLowerStar (ModuleCat.{u + 1} A) e.g)
    (rightDerivedLowerStar (ModuleCat.{u + 1} A) d.g)
    (rightDerivedLowerStar (ModuleCat.{u + 1} A) (e.g ≫ d.g))
    (openImmersionLowerShriek (ModuleCat.{u + 1} B) e.restrict.i).mapDerivedCategory
    (openImmersionLowerShriek (ModuleCat.{u + 1} B)
      (pullback.fst e.g d.i)).mapDerivedCategory
    (openImmersionLowerShriek (ModuleCat.{u + 1} B) e.i).mapDerivedCategory
    (openImmersionLowerShriek (ModuleCat.{u + 1} B) d.i).mapDerivedCategory
    (rightDerivedLowerStar (ModuleCat.{u + 1} B) e.restrict.g)
    (rightDerivedLowerStar (ModuleCat.{u + 1} B) e.g)
    (rightDerivedLowerStar (ModuleCat.{u + 1} B) d.g)
    (rightDerivedLowerStar (ModuleCat.{u + 1} B) (e.g ≫ d.g))
    (openScalarExtension φ e.restrict.i).hom
    (openScalarExtension φ (pullback.fst e.g d.i)).hom
    (openScalarExtension φ e.i).hom (openScalarExtension φ d.i).hom
    (scalarMate φ e.restrict.g) (scalarMate φ e.g)
    (scalarMate φ d.g) (scalarMate φ (e.g ≫ d.g))
    (aR A) (aR B)
    (openImmersionLowerShriekLowerStarExchange
      (ModuleCat.{u + 1} A) e.isPullback_restrict)
    (openImmersionLowerShriekLowerStarExchange
      (ModuleCat.{u + 1} B) e.isPullback_restrict)
    (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) e.g d.g).hom
    (rightDerivedLowerStarComp (ModuleCat.{u + 1} B) e.g d.g).hom M ho hp hi
  simpa only [rightDerivedLowerShriekOfCompactificationCompIso, Iso.trans_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Functor.map_comp, Category.assoc, asIso_hom,
    compactScalarMap, ExceptionalCoefficients.compactSupportMap,
    rightDerivedLowerShriekOfCompactification, Functor.comp_obj, Functor.comp_map,
    compactScalarOpen_eq, Compactification.comp, Compactification.copy,
    Compactification.postcomp, rightDerivedLowerStar, aR] using h

private theorem adjoint_inverse_square
    {C D E C' D' E' : Type*}
    [Category C] [Category D] [Category E]
    [Category C'] [Category D'] [Category E']
    {L : E ⥤ D} {R : D ⥤ E} {L' : E' ⥤ D'} {R' : D' ⥤ E'}
    (a : L ⊣ R) (a' : L' ⊣ R')
    (QX : C ⥤ C') (QC : D ⥤ D') (QD : E ⥤ E')
    (JC : C ⥤ D) (JD : C ⥤ E) (JC' : C' ⥤ D') (JD' : C' ⥤ E')
    (χ : R ⋙ QD ⟶ QC ⋙ R')
    (l : QD ⋙ L' ≅ L ⋙ QC)
    (bc : JC ≅ JD ⋙ L) (bc' : JC' ≅ JD' ⋙ L')
    (oc : JC ⋙ QC ≅ QX ⋙ JC') (od : JD ⋙ QD ≅ QX ⋙ JD')
    (hu : ∀ N, QD.map (a.unit.app N) ≫ χ.app (L.obj N) =
      a'.unit.app (QD.obj N) ≫ R'.map (l.hom.app N))
    (K : C)
    (hb : l.hom.app (JD.obj K) ≫ QC.map (bc.inv.app K) ≫ oc.hom.app K =
      L'.map (od.hom.app K) ≫ bc'.inv.app (QX.obj K)) :
    QD.map (a.unit.app (JD.obj K) ≫ R.map (bc.inv.app K)) ≫
        χ.app (JC.obj K) ≫ R'.map (oc.hom.app K) =
      od.hom.app K ≫ a'.unit.app (JD'.obj (QX.obj K)) ≫
        R'.map (bc'.inv.app (QX.obj K)) := by
  have hn := χ.naturality (bc.inv.app K)
  dsimp only [Functor.comp_map] at hn
  simp only [Functor.map_comp, CategoryTheory.Category.assoc]
  rw [reassoc_of% hn, reassoc_of% (hu (JD.obj K))]
  simp only [← R'.map_comp_assoc]
  rw [← R'.map_comp, CategoryTheory.Category.assoc, hb]
  simp only [Functor.map_comp]
  exact (a'.unit.naturality_assoc (od.hom.app K) _).symm

private theorem bc_scalar
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d)
    (hp : IsPullback c.i (𝟙 X) r.hom d.i) (M : DerivedCategoryModule A X) :
    (properOpenCoefficientPullbackIso φ r.hom).hom.app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} A) d.i).mapDerivedCategory.obj M) ≫
      (scalarExtension φ c.Z).map
        ((refinementLowerShriekBaseChangeDerivedIso (ModuleCat.{u + 1} A) r hp).inv.app M) ≫
      (openScalarExtension φ c.i).hom.app M =
    (upperStar (ModuleCat.{u + 1} B) r.hom).mapDerivedCategory.map
        ((openScalarExtension φ d.i).hom.app M) ≫
      (refinementLowerShriekBaseChangeDerivedIso (ModuleCat.{u + 1} B) r hp).inv.app
        ((scalarExtension φ X).obj M) := by
  let JA := (openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory
  let JB := (openImmersionLowerShriek (ModuleCat.{u + 1} B) c.i).mapDerivedCategory
  let UD := (upperStar (ModuleCat.{u + 1} A) d.i).mapDerivedCategory
  let UD' := (upperStar (ModuleCat.{u + 1} B) d.i).mapDerivedCategory
  let R := (upperStar (ModuleCat.{u + 1} B) r.hom).mapDerivedCategory
  let Q := scalarExtension φ c.Z
  let S := scalarExtension φ X
  let kA := Functor.mapDerivedCategoryTriangleIso
    (upperStarCompIso (ModuleCat.{u + 1} A) c.i r.hom d.i r.i_hom)
  let kB := Functor.mapDerivedCategoryTriangleIso
    (upperStarCompIso (ModuleCat.{u + 1} B) c.i r.hom d.i r.i_hom)
  let bA := refinementLowerShriekBaseChangeDerivedIso (ModuleCat.{u + 1} A) r hp
  let bB := refinementLowerShriekBaseChangeDerivedIso (ModuleCat.{u + 1} B) r hp
  have hc (N : DerivedCategoryModule A d.Z) :
      S.map (kA.hom.app N) ≫
          (properOpenCoefficientPullbackIso φ c.i).inv.app
            ((upperStar (ModuleCat.{u + 1} A) r.hom).mapDerivedCategory.obj N) ≫
          (upperStar (ModuleCat.{u + 1} B) c.i).mapDerivedCategory.map
            ((properOpenCoefficientPullbackIso φ r.hom).inv.app N) =
        (properOpenCoefficientPullbackIso φ d.i).inv.app N ≫
          kB.hom.app ((scalarExtension φ d.Z).obj N) := by
    apply (cancel_epi ((properOpenCoefficientPullbackIso φ d.i).hom.app N)).mp
    have hh := coefficientPullback_comp φ r.hom c.i d.i r.i_hom N
    have hh' :
        kB.hom.app ((scalarExtension φ d.Z).obj N) ≫
          (upperStar (ModuleCat.{u + 1} B) c.i).mapDerivedCategory.map
            ((properOpenCoefficientPullbackIso φ r.hom).hom.app N) ≫
          (properOpenCoefficientPullbackIso φ c.i).hom.app
            ((upperStar (ModuleCat.{u + 1} A) r.hom).mapDerivedCategory.obj N) =
        (properOpenCoefficientPullbackIso φ d.i).hom.app N ≫ S.map (kA.hom.app N) := by
      simpa only [kA, kB, Functor.mapDerivedCategoryTriangleIso, upperStarCompIso_eq]
        using hh
    rw [← reassoc_of% hh']
    simp only [Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app, ← Functor.map_comp]
    erw [CategoryTheory.Functor.map_id, CategoryTheory.Category.comp_id]
  have h := mate_cube
    (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) d.i)
    (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) c.i)
    (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) d.i)
    (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) c.i)
    (openScalarExtension φ d.i) (openScalarExtension φ c.i)
    (Functor.leftUnitor JA ≪≫ bA) (Functor.leftUnitor JB ≪≫ bB)
    (properOpenCoefficientPullbackIso φ d.i) (properOpenCoefficientPullbackIso φ c.i)
    (Functor.rightUnitor S ≪≫ (Functor.leftUnitor S).symm)
    (properOpenCoefficientPullbackIso φ r.hom)
    (Functor.rightUnitor UD ≪≫ kA) (Functor.rightUnitor UD' ≪≫ kB)
    (scalarOpen_unit φ d.i) (scalarOpen_unit φ c.i)
    (by
      intro K
      dsimp only [JA, UD, kA, bA, Iso.trans_hom, NatTrans.comp_app,
        Functor.leftUnitor_hom_app, Functor.rightUnitor_hom_app, Functor.id_obj]
      erw [CategoryTheory.Category.id_comp, CategoryTheory.Category.id_comp]
      exact unit_map_refinementLowerShriekBaseChangeDerivedIso
        (ModuleCat.{u + 1} A) r hp K)
    (by
      intro K
      dsimp only [JB, UD', kB, bB, Iso.trans_hom, NatTrans.comp_app,
        Functor.leftUnitor_hom_app, Functor.rightUnitor_hom_app, Functor.id_obj]
      erw [CategoryTheory.Category.id_comp, CategoryTheory.Category.id_comp]
      exact unit_map_refinementLowerShriekBaseChangeDerivedIso
        (ModuleCat.{u + 1} B) r hp K)
    (by
      intro N
      dsimp only [S, UD, UD', Iso.trans_hom, Iso.trans_inv, NatTrans.comp_app,
        Functor.leftUnitor_inv_app, Functor.leftUnitor_hom_app,
        Functor.rightUnitor_hom_app, Functor.rightUnitor_inv_app,
        Iso.symm_inv, Functor.id_map, Functor.id_obj]
      erw [CategoryTheory.Category.id_comp, CategoryTheory.Category.id_comp,
        CategoryTheory.Category.id_comp, CategoryTheory.Category.id_comp]
      exact hc N) M
  let l := bB.app (S.obj M) ≪≫ R.mapIso ((openScalarExtension φ d.i).symm.app M)
  let t := (openScalarExtension φ c.i).symm.app M ≪≫
    Q.mapIso (bA.app M) ≪≫ (properOpenCoefficientPullbackIso φ r.hom).symm.app _
  have he : l.hom = t.hom := by
    dsimp only [JA, JB, UD, UD', S, Q, R, Iso.trans_hom, Iso.trans_inv,
      Iso.symm_hom, Iso.symm_inv, Functor.leftUnitor_hom_app,
      Functor.rightUnitor_inv_app, NatTrans.comp_app, Functor.id_obj] at h
    erw [CategoryTheory.Category.id_comp, CategoryTheory.Functor.map_id,
      CategoryTheory.Category.id_comp, CategoryTheory.Category.id_comp,
      CategoryTheory.Category.id_comp] at h
    simpa only [l, t, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
      Iso.app_hom, Iso.app_inv, S, Q, R, CategoryTheory.Category.assoc] using h
  simpa only [l, t, Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv,
    Iso.app_inv, Iso.app_hom, bA, bB, Q, R, S, CategoryTheory.Category.assoc] using
    (congrArg Iso.inv (Iso.ext he)).symm

private theorem inner_scalar
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d)
    (hp : IsPullback c.i (𝟙 X) r.hom d.i) (M : DerivedCategoryModule A X) :
    let a := mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) r.hom
    let b := mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) r.hom
    let JA := (openImmersionLowerShriek (ModuleCat.{u + 1} A) d.i).mapDerivedCategory
    let JB := (openImmersionLowerShriek (ModuleCat.{u + 1} B) d.i).mapDerivedCategory
    (scalarExtension φ d.Z).map
        (a.unit.app (JA.obj M) ≫
          (rightDerivedLowerStar (ModuleCat.{u + 1} A) r.hom).map
            ((refinementLowerShriekBaseChangeDerivedIso (ModuleCat.{u + 1} A) r hp).inv.app M)) ≫
      (scalarMate φ r.hom).app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory.obj M) ≫
      (rightDerivedLowerStar (ModuleCat.{u + 1} B) r.hom).map
        ((openScalarExtension φ c.i).hom.app M) =
    (openScalarExtension φ d.i).hom.app M ≫ b.unit.app
        (JB.obj ((scalarExtension φ X).obj M)) ≫
      (rightDerivedLowerStar (ModuleCat.{u + 1} B) r.hom).map
        ((refinementLowerShriekBaseChangeDerivedIso (ModuleCat.{u + 1} B) r hp).inv.app
          ((scalarExtension φ X).obj M)) := by
  dsimp only
  apply adjoint_inverse_square
    (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) r.hom)
    (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) r.hom)
    (scalarExtension φ X) (scalarExtension φ c.Z) (scalarExtension φ d.Z)
    (openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory
    (openImmersionLowerShriek (ModuleCat.{u + 1} A) d.i).mapDerivedCategory
    (openImmersionLowerShriek (ModuleCat.{u + 1} B) c.i).mapDerivedCategory
    (openImmersionLowerShriek (ModuleCat.{u + 1} B) d.i).mapDerivedCategory
    (scalarMate φ r.hom) (properOpenCoefficientPullbackIso φ r.hom)
    (refinementLowerShriekBaseChangeDerivedIso (ModuleCat.{u + 1} A) r hp)
    (refinementLowerShriekBaseChangeDerivedIso (ModuleCat.{u + 1} B) r hp)
    (openScalarExtension φ c.i) (openScalarExtension φ d.i) ?_ M (bc_scalar φ r hp M)
  intro N
  symm
  apply ProEtale.CoefficientCompatibility.scalar_unit_of_counit
  intro V
  simpa only [mapDerivedUpperStarLowerStarAdjunction_eq] using coefficientMate_counit φ r.hom V

private theorem scalarSite_unbounded_refinement
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian Y] {f : X ⟶ Y} {c d : Compactification f}
    (r : c.Refinement d) (hp : IsPullback c.i (𝟙 X) r.hom d.i)
    (M : DerivedCategoryModule A X) :
    (scalarExtension φ Y).map
        ((rightDerivedLowerShriekOfCompactificationComparison (ModuleCat.{u + 1} A)
          r hp).app M) ≫ (compactScalarMap φ c).app M =
      (compactScalarMap φ d).app M ≫
        (rightDerivedLowerShriekOfCompactificationComparison (ModuleCat.{u + 1} B)
          r hp).app ((scalarExtension φ X).obj M) := by
  have : IsLocallyNoetherian c.Z := LocallyOfFiniteType.isLocallyNoetherian c.g
  have : CompactSpace c.Z := QuasiCompact.compactSpace_of_compactSpace c.g
  have : IsNoetherian c.Z := ⟨⟩
  have : IsLocallyNoetherian d.Z := LocallyOfFiniteType.isLocallyNoetherian d.g
  have : CompactSpace d.Z := QuasiCompact.compactSpace_of_compactSpace d.g
  have : IsNoetherian d.Z := ⟨⟩
  let αA := (mapDerivedUpperStarLowerStarAdjunction
    (ModuleCat.{u + 1} A) r.hom).unit.app
      ((openImmersionLowerShriek (ModuleCat.{u + 1} A) d.i).mapDerivedCategory.obj M) ≫
    (rightDerivedLowerStar (ModuleCat.{u + 1} A) r.hom).map
      ((refinementLowerShriekBaseChangeDerivedIso (ModuleCat.{u + 1} A) r hp).inv.app M)
  let αB := (mapDerivedUpperStarLowerStarAdjunction
    (ModuleCat.{u + 1} B) r.hom).unit.app
      ((openImmersionLowerShriek (ModuleCat.{u + 1} B) d.i).mapDerivedCategory.obj
        ((scalarExtension φ X).obj M)) ≫
    (rightDerivedLowerStar (ModuleCat.{u + 1} B) r.hom).map
      ((refinementLowerShriekBaseChangeDerivedIso (ModuleCat.{u + 1} B) r hp).inv.app
        ((scalarExtension φ X).obj M))
  let kA := Functor.rightDerivedFunctorCompIso' (lowerStar (ModuleCat.{u + 1} A) r.hom)
    (lowerStar (ModuleCat.{u + 1} A) d.g) (refinementLowerStarComp (ModuleCat.{u + 1} A) r)
  let kB := Functor.rightDerivedFunctorCompIso' (lowerStar (ModuleCat.{u + 1} B) r.hom)
    (lowerStar (ModuleCat.{u + 1} B) d.g) (refinementLowerStarComp (ModuleCat.{u + 1} B) r)
  have heA : (rightDerivedLowerShriekOfCompactificationComparison
      (ModuleCat.{u + 1} A) r hp).app M =
      (rightDerivedLowerStar (ModuleCat.{u + 1} A) d.g).map αA ≫
        kA.hom.app
          ((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory.obj M) := by
    simp only [rightDerivedLowerShriekOfCompactificationComparison, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.comp_map,
      ← Functor.map_comp_assoc]
    rfl
  have heB : (rightDerivedLowerShriekOfCompactificationComparison
      (ModuleCat.{u + 1} B) r hp).app ((scalarExtension φ X).obj M) =
      (rightDerivedLowerStar (ModuleCat.{u + 1} B) d.g).map αB ≫
        kB.hom.app
          ((openImmersionLowerShriek (ModuleCat.{u + 1} B) c.i).mapDerivedCategory.obj
            ((scalarExtension φ X).obj M)) := by
    simp only [rightDerivedLowerShriekOfCompactificationComparison, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.comp_map,
      ← Functor.map_comp_assoc]
    rfl
  have ho := inner_scalar φ r hp M
  have hc (N : DerivedCategoryModule A c.Z) :
      (scalarExtension φ Y).map (kA.hom.app N) ≫ (scalarMate φ c.g).app N =
        (scalarMate φ d.g).app ((rightDerivedLowerStar (ModuleCat.{u + 1} A) r.hom).obj N) ≫
          (rightDerivedLowerStar (ModuleCat.{u + 1} B) d.g).map ((scalarMate φ r.hom).app N) ≫
          kB.hom.app ((scalarExtension φ c.Z).obj N) := by
    dsimp only [kA, kB]
    rw [refinementLowerStarComp_eq, refinementLowerStarComp_eq]
    exact scalarMate_directImage_composition_eq φ r.hom d.g c.g r.hom_g.symm N
  dsimp only [rightDerivedLowerStar] at *
  rw [heA, heB]
  dsimp only [compactScalarMap, ExceptionalCoefficients.compactSupportMap,
    rightDerivedLowerShriekOfCompactification, Functor.comp_obj]
  simp only [Functor.map_comp, CategoryTheory.Category.assoc]
  rw [reassoc_of% hc]
  have hn := (scalarMate φ d.g).naturality αA
  dsimp only [Functor.comp_map, rightDerivedLowerStar] at hn
  erw [reassoc_of% hn]
  have hk := kB.hom.naturality ((ExceptionalCoefficients.openIso φ c.i).hom.app M)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hk
  erw [← hk]
  simp only [← Functor.map_comp_assoc]
  rw [compactScalarOpen_eq, compactScalarOpen_eq]
  dsimp only [αA, αB]
  simpa only [CategoryTheory.Functor.comp_map, CategoryTheory.Functor.map_comp,
    CategoryTheory.Functor.id_obj, CategoryTheory.Category.assoc, rightDerivedLowerStar] using
    congrArg (fun z ↦ (scalarMate φ d.g).app _ ≫
      (rightDerivedLowerStar (ModuleCat.{u + 1} B) d.g).map z ≫ kB.hom.app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} B) c.i).mapDerivedCategory.obj
          ((scalarExtension φ X).obj M))) ho

private theorem generalFieldDctf_iso
    {T : Scheme.{u}} {R : Type u} [CommRing R] [Finite R]
    {K N : proEtaleDerivedCategory T R} (e : K ≅ N) (h : generalFieldDctf T R K) :
    generalFieldDctf T R N := by
  refine ⟨h.1.subset (fun i hi hz ↦ hi
    (hz.of_iso ((DerivedCategory.homologyFunctor _ i).mapIso e).symm)),
    fun i ↦ intrinsicConstructible_of_iso T R
      ((DerivedCategory.homologyFunctor _ i).mapIso e) (h.2.1 i), ?_⟩
  obtain ⟨a, b, ht⟩ := h.2.2
  refine ⟨a, b, ht.1, ?_⟩
  intro P Q hP f hf hQ V i hi
  obtain ⟨q⟩ := hP
  exact ht.2 P Q ⟨q ≪≫ e.symm⟩ f hf hQ V i hi

/-- Canonical compact-support comparison for an etale-origin input.

Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/`
`sk-lem-sp-reduction/sk-lem-sp-reduction-exceptional.md`, Charts.
(blueprint: `lem-pur-general-field-compact-scalar-site-square`).

The comparison is assembled from the published site comparison,
the fixed constant-ring compact-support comparison, and the ordinary
compactification comparison.  Keeping it as a definition prevents an
arbitrary natural isomorphism from entering the statement. -/
noncomputable def canonicalCompactSupportSiteIso
    (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (L : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))) :
    (finiteCoefficientIntrinsicDerivedComparison Y A).obj
        ((Etale.rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c).obj L.obj) ≅
    (reductionCompactSupport A c.i c.g).obj
        ((finiteCoefficientIntrinsicDerivedComparison X A).obj L.obj) := by
  exact (Scheme.FiniteCompactScalar.intrinsicSiteFunctorIso A Y).app _ ≪≫
    ((sfIntrinsicDerivedEquivalence Y A).functor.mapIso
      ((compactSupportSiteComparison (ULift.{u + 1, u} A) c).app L).symm ≪≫
      (CoefficientCompatibility.supportPresentation A c).symm.app
        ((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
          X).mapDerivedCategory.obj L.obj)) ≪≫
    (reductionCompactSupport A c.i c.g).mapIso
      ((Scheme.FiniteCompactScalar.intrinsicSiteFunctorIso A X).app L.obj).symm

/-- Canonical scalar/site comparison on an etale-origin object.

Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/`
`sec-smooth-purity/sec-sp-grp-ladic-summary/sec-change-of-finite-coefficients/`
`sk-lem-sp-reduction/sk-lem-sp-reduction-exceptional.md`, Charts.
(blueprint: `lem-pur-general-field-compact-scalar-site-square`).
-/
noncomputable def canonicalSiteScalarIso
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (T : Scheme.{u}) :=
  Scheme.FiniteCompactScalar.siteScalarIso φ T

/-- Intrinsic compact-support compositor obtained by transporting the chosen
etale compositor through the finite coefficient site comparisons.  The etale
compositor is `coherenceEtaleCompositor` for exactly the three supplied
compactifications (chosen compositor conjugated by the canonical compactification
changes), so no further triangle datum is needed.
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-sp-grp-ladic-summary/sec-change-of-finite-coefficients/
sk-lem-sp-reduction/sk-lem-sp-reduction-direct-image.md, Step 4.
(blueprint: `lem-pur-general-field-compact-scalar-site-square`). -/
noncomputable def canonicalIntrinsicCompactSupportCompositor
    (A : Type u) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
    {f : X ⟶ Y} {g : Y ⟶ Z}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (cf : Compactification f) (cg : Compactification g)
    (cfg : Compactification (f ≫ g))
    (E : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))) :
    (reductionCompactSupport A cg.i cg.g).obj
        ((reductionCompactSupport A cf.i cf.g).obj
          ((finiteCoefficientIntrinsicDerivedComparison X A).obj E.obj)) ≅
      (reductionCompactSupport A cfg.i cfg.g).obj
        ((finiteCoefficientIntrinsicDerivedComparison X A).obj E.obj) := by
  let Ecf := (Etale.rightDerivedLowerShriekOfCompactificationPlus
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) cf).obj E
  let qcf := (Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) cf).app E
  let qcg := (Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) cg).app Ecf
  let qcfg := (Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) cfg).app E
  exact (Functor.mapIso (reductionCompactSupport A cg.i cg.g)
      (canonicalCompactSupportSiteIso A cf E).symm) ≪≫
    (Functor.mapIso (reductionCompactSupport A cg.i cg.g)
      ((finiteCoefficientIntrinsicDerivedComparison Y A).mapIso qcf.symm)) ≪≫
    (canonicalCompactSupportSiteIso A cg Ecf).symm ≪≫
    (finiteCoefficientIntrinsicDerivedComparison Z A).mapIso qcg.symm ≪≫
    (finiteCoefficientIntrinsicDerivedComparison Z A).mapIso
      (DerivedCategory.Plus.ι.mapIso
        ((coherenceEtaleCompositor (ULift.{u + 1, u} A) cf cg cfg).app E)) ≪≫
    (finiteCoefficientIntrinsicDerivedComparison Z A).mapIso qcfg ≪≫
    canonicalCompactSupportSiteIso A cfg E

/-- Intrinsic compact-support refinement comparison obtained by transporting
the canonical bounded-plus refinement isomorphism through the site comparisons.
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-sp-grp-ladic-summary/sec-change-of-finite-coefficients/
sk-lem-sp-reduction/sk-lem-sp-reduction-direct-image.md, Step 4.
(blueprint: `lem-pur-general-field-compact-scalar-site-square`). -/
noncomputable def canonicalIntrinsicCompactSupportRefinement
    (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    {cf cd : Compactification f} (r : cf.Refinement cd)
    (E : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))) :
    (reductionCompactSupport A cd.i cd.g).obj
        ((finiteCoefficientIntrinsicDerivedComparison X A).obj E.obj) ≅
      (reductionCompactSupport A cf.i cf.g).obj
        ((finiteCoefficientIntrinsicDerivedComparison X A).obj E.obj) := by
  let qcd := (Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) cd).app E
  let qcf := (Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) cf).app E
  exact (canonicalCompactSupportSiteIso A cd E).symm ≪≫
    (finiteCoefficientIntrinsicDerivedComparison Y A).mapIso qcd.symm ≪≫
    (finiteCoefficientIntrinsicDerivedComparison Y A).mapIso
      (DerivedCategory.Plus.ι.mapIso
        ((Etale.rightDerivedLowerShriekOfCompactificationPlusRefinementIso
          (ULift.{u + 1, u} A) r).app E)) ≪≫
    (finiteCoefficientIntrinsicDerivedComparison Y A).mapIso qcf ≪≫
    canonicalCompactSupportSiteIso A cf E

private theorem pushCongr_eq {C D : Type*} [Category C] [Category D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {F : C ⥤ D} [F.IsContinuous J K]
    {R : Sheaf K RingCat} {S : Sheaf J RingCat}
    {φ ψ : S ⟶ (F.sheafPushforwardContinuous RingCat J K).obj R}
    (e : φ = ψ) :
    SheafOfModules.pushforwardCongr e = eqToIso (congrArg SheafOfModules.pushforward e) := by
  subst ψ
  rfl

private theorem derived_eqIso
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [Abelian.HasKInjectiveResolutions C]
    {F G : C ⥤ D} [F.Additive] [G.Additive] (h : F = G) :
    Functor.rightDerivedFunctorNatIso (eqToIso h) =
      eqToIso (by cases h; rfl) := by
  subst G
  apply Iso.ext
  simp only [eqToIso_refl, Iso.refl_hom, Functor.rightDerivedFunctorNatIso,
    Functor.rightDerivedFunctorNatTrans, NatTrans.mapHomotopyCategory_id,
    Functor.whiskerRight_id', Functor.rightDerivedNatTrans_id]

private theorem model_eq (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (g : X ⟶ Y) :
    openSquare_directImageModel A g = eqToIso (by
      unfold proEtaleConstantRingPushforward proEtaleRingModuleDirectImage
        proEtaleConstantModuleDirectImage
      rw [openSquare_coefficientMap A g]) := by
  unfold openSquare_directImageModel
  rw [pushCongr_eq]

private theorem left_eqIso {C D E : Type*} [Category C] [Category D] [Category E]
    (H : C ⥤ D) {F G : D ⥤ E} (h : F = G) :
    isoWhiskerLeft H (eqToIso h) = eqToIso (congrArg (fun P => H ⋙ P) h) := by
  subst G
  rfl

private theorem directPresentation_eq (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (g : X ⟶ Y) :
    CoefficientCompatibility.directImagePresentation A g =
      eqToIso (by rw [reductionConstantPush_eq]) ≪≫
        sfIntrinsicDerivedDirectImageComparison g A := by
  unfold CoefficientCompatibility.directImagePresentation
  rw [CoefficientCompatibility.directImageModel_eq, model_eq, derived_eqIso, left_eqIso]

private theorem support_change
    {C₀ C₁ C₂ C₃ C₄ C₅ : Type*}
    [Category C₀] [Category C₁] [Category C₂] [Category C₃]
    [Category C₄] [Category C₅]
    (EX : C₀ ⥤ C₁) (J : C₁ ⥤ C₂) (JF : C₀ ⥤ C₄)
    (EZ : C₄ ⥤ C₂) (PF : C₄ ⥤ C₅) (EY : C₅ ⥤ C₃)
    (o : EX ⋙ J ≅ JF ⋙ EZ) {Q Q' : C₂ ⥤ C₃} (e : Q = Q')
    (p : EZ ⋙ Q' ≅ PF ⋙ EY) :
    (Functor.associator EX J Q).symm ≪≫ isoWhiskerRight o Q ≪≫
      Functor.associator JF EZ Q ≪≫
      isoWhiskerLeft JF (eqToIso (congrArg (fun H => EZ ⋙ H) e) ≪≫ p) ≪≫
      (Functor.associator JF PF EY).symm =
    eqToIso (congrArg (fun H => EX ⋙ J ⋙ H) e) ≪≫
      (Functor.associator EX J Q').symm ≪≫ isoWhiskerRight o Q' ≪≫
      Functor.associator JF EZ Q' ≪≫ isoWhiskerLeft JF p ≪≫
      (Functor.associator JF PF EY).symm := by
  subst Q'
  simp only [eqToIso_refl, Iso.refl_trans]

private theorem supportPresentation_eq (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    CoefficientCompatibility.supportPresentation A c =
      eqToIso (by
        dsimp only [reductionCompactSupport, sfIntrinsicCompactSupport]
        rw [reductionConstantPush_eq]) ≪≫ FiniteCompactScalar.compactRealizationIso A c := by
  unfold CoefficientCompatibility.supportPresentation
  rw [directPresentation_eq]
  unfold FiniteCompactScalar.compactRealizationIso
  exact support_change _ _ _ _ _ _ _ (reductionConstantPush_eq A c.g) _

private def presentedSiteIso
    (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (L : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))) :=
  (sfIntrinsicDerivedEquivalence Y A).functor.mapIso
    ((compactSupportSiteComparison (ULift.{u + 1, u} A) c).app L).symm ≪≫
      (supportPresentation A c).symm.app
        ((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X).mapDerivedCategory.obj
          L.obj)

private def presentedScalarIso
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (X : Scheme.{u})
    (L : DerivedCategory
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))) :=
  (scalarPresentation φ X).app
      ((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X).mapDerivedCategory.obj L) ≪≫
    (sfIntrinsicDerivedEquivalence X B).functor.mapIso
      ((pbcComparisonReduction X (uliftRingHom φ)).app L)

private theorem realized_recorded
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : DerivedCategory (Sheaf (ProEt.topology X)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))) :
    (sfIntrinsicDerivedEquivalence Y B).functor.map
        ((transportedRecordedReductionDirectImageComparison φ c
          (reductionDirectImageComparison φ c.i c.g)).app K) =
      (scalarPresentation φ Y).inv.app
          ((rightDerivedLowerShriekOfCompactification
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c).obj K) ≫
        (scalarExtensionFunctor φ Y).map ((supportPresentation A c).inv.app K) ≫
        (reductionDirectImageComparison φ c.i c.g).app
          ((sfIntrinsicDerivedEquivalence X A).functor.obj K) ≫
        (reductionCompactSupport B c.i c.g).map ((scalarPresentation φ X).hom.app K) ≫
        (supportPresentation B c).hom.app ((liftedScalarExtension φ X).obj K) := by
  let FF := (Functor.FullyFaithful.ofFullyFaithful
    (sfIntrinsicDerivedEquivalence Y B).functor).whiskeringRight
    (DerivedCategory (Sheaf (ProEt.topology X)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A))))
  let m := Functor.whiskerLeft (rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c) (scalarPresentation φ Y).inv ≫
      Functor.whiskerRight (supportPresentation A c).inv (scalarExtensionFunctor φ Y) ≫
      Functor.whiskerLeft (sfIntrinsicDerivedEquivalence X A).functor
        (reductionDirectImageComparison φ c.i c.g) ≫
      Functor.whiskerRight (scalarPresentation φ X).hom (reductionCompactSupport B c.i c.g) ≫
      Functor.whiskerLeft (liftedScalarExtension φ X) (supportPresentation B c).hom
  have hm := congr_app (FF.map_preimage
    (X := rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c ⋙ liftedScalarExtension φ Y)
    (Y := liftedScalarExtension φ X ⋙ rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) c) m) K
  simpa only [FF, m, transportedRecordedReductionDirectImageComparison,
    whiskeringRight_obj_map, NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
    Functor.comp_obj] using hm

private theorem presented_square
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (L : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A))))
    (hLB : DerivedCategory.TStructure.t.plus ((Etale.scalarExtension φ.ulift X).obj L.obj)) :
    (scalarExtensionFunctor φ Y).map (presentedSiteIso A c L).hom ≫
        (reductionDirectImageComparison φ c.i c.g).app
          ((sfIntrinsicDerivedEquivalence X A).functor.obj
            ((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
              X).mapDerivedCategory.obj L.obj)) ≫
        (reductionCompactSupport B c.i c.g).map (presentedScalarIso φ X L.obj).hom =
      (presentedScalarIso φ Y
        ((Etale.rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c).obj L.obj)).hom ≫
        (sfIntrinsicDerivedEquivalence Y B).functor.map
          ((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) Y).mapDerivedCategory.map
            ((Etale.compactScalarMap φ.ulift c).app L.obj)) ≫
        (presentedSiteIso B c ⟨_, hLB⟩).hom := by
  let NA := (comparisonUpperStar
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X).mapDerivedCategory
  let EB := (sfIntrinsicDerivedEquivalence Y B).functor
  let T := scalarExtensionFunctor φ Y
  let F := reductionCompactSupport B c.i c.g
  let b := (reductionDirectImageComparison φ c.i c.g).app
    ((sfIntrinsicDerivedEquivalence X A).functor.obj (NA.obj L.obj))
  let bf := (transportedRecordedReductionDirectImageComparison φ c
    (reductionDirectImageComparison φ c.i c.g)).app (NA.obj L.obj)
  have hb : T.map ((supportPresentation A c).inv.app (NA.obj L.obj)) ≫ b ≫
      F.map ((scalarPresentation φ X).hom.app (NA.obj L.obj)) =
      (scalarPresentation φ Y).hom.app
          ((rightDerivedLowerShriekOfCompactification
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c).obj (NA.obj L.obj)) ≫
        EB.map bf ≫ (supportPresentation B c).inv.app
          ((liftedScalarExtension φ X).obj (NA.obj L.obj)) := by
    rw [realized_recorded]
    simp only [b, F, T, Category.assoc, Iso.hom_inv_id_app_assoc,
      Iso.hom_inv_id_app, Category.comp_id]
    erw [Category.comp_id]
  have hs := congrArg EB.map (transportedCompactScalar_site_square φ c L hLB)
  simp only [Functor.map_comp, Category.assoc] at hs
  have hσ := (scalarPresentation φ Y).hom.naturality
    ((compactSupportSiteComparison (ULift.{u + 1, u} A) c).inv.app L)
  have hP := (supportPresentation B c).inv.naturality
    ((pbcComparisonReduction X (uliftRingHom φ)).hom.app L.obj)
  dsimp only [Functor.comp_map, Functor.comp_obj, DerivedCategory.Plus.ι,
    ObjectProperty.ι_obj] at hσ hP
  dsimp only [NA, EB, bf] at hb ⊢
  simp only [presentedSiteIso, presentedScalarIso, Iso.trans_hom, Iso.symm_hom,
    Iso.app_hom, Iso.app_inv, Functor.mapIso_hom, Functor.mapIso_inv, Functor.map_comp,
    Category.assoc]
  erw [reassoc_of% hb, reassoc_of% hσ, ← hP, reassoc_of% hs]
  rfl

private theorem site_change
    {C D : Type*} [Category C] [Category D]
    {F G : C ⥤ D} (e : F = G) {U V : C} {W Z : D}
    (a : U ≅ V) (b : W ≅ Z) (p : G.obj V ≅ Z) :
    (b ≪≫ p.symm ≪≫ G.mapIso a.symm) ≪≫
        eqToIso (congrArg (fun H : C ⥤ D => H.obj U) e).symm =
      b ≪≫ (eqToIso (congrArg (fun H : C ⥤ D => H.obj V) e) ≪≫ p).symm ≪≫
        F.mapIso a.symm := by
  subst G
  simp only [eqToIso_refl, Iso.refl_trans, Iso.trans_refl]

private theorem symm_iso_app {C D : Type*} [Category C] [Category D]
    {F G : C ⥤ D} (e : F ≅ G) (K : C) : e.symm.app K = (e.app K).symm := rfl

private theorem eq_iso_app
    {C D : Type*} [Category C] [Category D]
    {F G : C ⥤ D} (e : F = G) (K : C) :
    (eqToIso e).app K = eqToIso (congrArg (fun H : C ⥤ D => H.obj K) e) := by
  subst G
  rfl

private theorem canonical_site_factor
    (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (L : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))) :
    canonicalCompactSupportSiteIso A c L =
      (intrinsicSiteFunctorIso A Y).app _ ≪≫ presentedSiteIso A c L ≪≫
        (reductionCompactSupport A c.i c.g).mapIso
          ((intrinsicSiteFunctorIso A X).app L.obj).symm := by
  rfl

private theorem canonical_scalar_factor
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (X : Scheme.{u})
    (L : DerivedCategory
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))) :
    (canonicalSiteScalarIso φ X).app L =
      (scalarExtensionFunctor φ X).mapIso ((intrinsicSiteFunctorIso A X).app L) ≪≫
        presentedScalarIso φ X L ≪≫ ((intrinsicSiteFunctorIso B X).app _).symm := by
  unfold canonicalSiteScalarIso presentedScalarIso siteScalarIso
  rw [scalarPresentation_eq]
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.app_hom, Iso.app_inv, Iso.symm_hom,
    Functor.mapIso_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Category.comp_id, Category.assoc]
  rfl

private theorem intrinsic_square
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (L : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A))))
    (hLB : DerivedCategory.TStructure.t.plus ((Etale.scalarExtension φ.ulift X).obj L.obj)) :
    (scalarExtensionFunctor φ Y).map (canonicalCompactSupportSiteIso A c L).hom ≫
        (reductionDirectImageComparison φ c.i c.g).app
          ((finiteCoefficientIntrinsicDerivedComparison X A).obj L.obj) ≫
        (reductionCompactSupport B c.i c.g).map
          ((canonicalSiteScalarIso φ X).hom.app L.obj) =
      (canonicalSiteScalarIso φ Y).hom.app
        ((Etale.rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c).obj L.obj) ≫
        (finiteCoefficientIntrinsicDerivedComparison Y B).map
          ((Etale.compactScalarMap φ.ulift c).app L.obj) ≫
        (canonicalCompactSupportSiteIso B c ⟨_, hLB⟩).hom := by
  have hs := presented_square φ c L hLB
  have hb := (reductionDirectImageComparison φ c.i c.g).naturality
    ((intrinsicSiteFunctorIso A X).inv.app L.obj)
  have ha := (intrinsicSiteFunctorIso B Y).inv.naturality
    ((Etale.compactScalarMap φ.ulift c).app L.obj)
  change (scalarExtensionFunctor φ Y).map
      ((reductionCompactSupport A c.i c.g).map
        ((intrinsicSiteFunctorIso A X).inv.app L.obj)) ≫
      (reductionDirectImageComparison φ c.i c.g).app _ =
    (reductionDirectImageComparison φ c.i c.g).app _ ≫
      (reductionCompactSupport B c.i c.g).map
        ((scalarExtensionFunctor φ X).map ((intrinsicSiteFunctorIso A X).inv.app L.obj)) at hb
  dsimp only [Functor.comp_map] at ha
  have hcancel : (reductionCompactSupport B c.i c.g).map
        ((scalarExtensionFunctor φ X).map ((intrinsicSiteFunctorIso A X).inv.app L.obj)) ≫
      (reductionCompactSupport B c.i c.g).map
        ((scalarExtensionFunctor φ X).map ((intrinsicSiteFunctorIso A X).hom.app L.obj)) =
      𝟙 _ := by
    rw [← Functor.map_comp, ← Functor.map_comp, Iso.inv_hom_id_app,
      CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  have hX := congrArg Iso.hom (canonical_scalar_factor φ X L.obj)
  have hY := congrArg Iso.hom (canonical_scalar_factor φ Y
    ((Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c).obj L.obj))
  simp only [Iso.app_hom] at hX hY
  rw [hX, hY]
  simp only [canonical_site_factor,
    Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv, Functor.mapIso_hom,
    Functor.mapIso_inv, Functor.map_comp, Category.assoc]
  erw [reassoc_of% hb]
  erw [reassoc_of% hcancel]
  erw [reassoc_of% hs, ← reassoc_of% ha]
  dsimp only [ObjectProperty.ι_obj, Etale.rightDerivedLowerShriekOfCompactification,
    Functor.comp_obj]
  simp only [Iso.inv_hom_id_app_assoc]

private theorem intrinsic_formula
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (L : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A))))
    (hLB : DerivedCategory.TStructure.t.plus ((Etale.scalarExtension φ.ulift X).obj L.obj)) :
    (reductionDirectImageComparison φ c.i c.g).app
        ((finiteCoefficientIntrinsicDerivedComparison X A).obj L.obj) =
      (scalarExtensionFunctor φ Y).map (canonicalCompactSupportSiteIso A c L).inv ≫
        (canonicalSiteScalarIso φ Y).hom.app
          ((Etale.rightDerivedLowerShriekOfCompactification
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c).obj L.obj) ≫
        (finiteCoefficientIntrinsicDerivedComparison Y B).map
          ((Etale.compactScalarMap φ.ulift c).app L.obj) ≫
        (canonicalCompactSupportSiteIso B c ⟨_, hLB⟩).hom ≫
        (reductionCompactSupport B c.i c.g).map
          ((canonicalSiteScalarIso φ X).inv.app L.obj) := by
  have hs := intrinsic_square φ c L hLB
  have hh := congrArg (fun z =>
    (scalarExtensionFunctor φ Y).map (canonicalCompactSupportSiteIso A c L).inv ≫ z ≫
    (reductionCompactSupport B c.i c.g).map
      ((canonicalSiteScalarIso φ X).inv.app L.obj)) hs
  simp only [Category.assoc] at hh
  erw [← (scalarExtensionFunctor φ Y).map_comp_assoc, Iso.inv_hom_id,
    (scalarExtensionFunctor φ Y).map_id, Category.id_comp,
    ← (reductionCompactSupport B c.i c.g).map_comp, Iso.hom_inv_id_app,
    (reductionCompactSupport B c.i c.g).map_id, Category.comp_id] at hh
  exact hh

private theorem canonical_site_naturality
    (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    {L K : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))}
    (a : L ⟶ K) :
    (finiteCoefficientIntrinsicDerivedComparison Y A).map
        ((Etale.rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c).map a.hom) ≫
        (canonicalCompactSupportSiteIso A c K).hom =
      (canonicalCompactSupportSiteIso A c L).hom ≫
        (reductionCompactSupport A c.i c.g).map
          ((finiteCoefficientIntrinsicDerivedComparison X A).map a.hom) := by
  have hY := (intrinsicSiteFunctorIso A Y).hom.naturality
    ((Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c).map a.hom)
  have hC := congrArg (sfIntrinsicDerivedEquivalence Y A).functor.map
    ((compactSupportSiteComparison (ULift.{u + 1, u} A) c).inv.naturality a)
  have hP := (supportPresentation A c).inv.naturality
    ((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X).mapDerivedCategory.map
      a.hom)
  have hX := (intrinsicSiteFunctorIso A X).inv.naturality a.hom
  dsimp only [Functor.comp_map, Functor.comp_obj, ObjectProperty.ι_obj,
    ObjectProperty.ι_map] at hY hC hP hX
  simp only [Functor.map_comp] at hC
  change (sfIntrinsicDerivedEquivalence Y A).functor.map _ ≫
      (supportPresentation A c).inv.app _ =
    (supportPresentation A c).inv.app _ ≫
      (reductionCompactSupport A c.i c.g).map
        ((sfIntrinsicDerivedEquivalence X A).functor.map
          ((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X).mapDerivedCategory.map
            a.hom)) at hP
  simp only [canonical_site_factor, presentedSiteIso, Iso.trans_hom,
    Iso.app_hom, Iso.app_inv, Iso.symm_hom, Functor.mapIso_hom,
    Functor.mapIso_inv, Category.assoc]
  erw [reassoc_of% hY, reassoc_of% hC, reassoc_of% hP]
  have hx := congrArg (reductionCompactSupport A c.i c.g).map hX
  simp only [Functor.map_comp] at hx
  erw [hx]
  rfl

private theorem change_compositor_hom
    {C D E : Type*} [Category C] [Category D] [Category E]
    (F F' : C ⥤ D) (G G' : D ⥤ E) (H H' : C ⥤ E)
    (a : F ≅ F') (b : G ≅ G') (c : F' ⋙ G' ≅ H) (d : H ≅ H') :
    (coherenceCompositorOfChanges F F' G G' H H' a b c d).hom =
      NatTrans.hcomp a.hom b.hom ≫ c.hom ≫ d.hom := by
  ext L
  simp only [coherenceCompositorOfChanges, coherenceIsoFour, coherenceFourMap,
    NatIso.ofComponents_hom_app, Functor.mapIso_hom, Iso.app_hom,
    NatTrans.comp_app, NatTrans.hcomp_app, Category.assoc]
  exact b.hom.naturality_assoc (a.hom.app L) _

private theorem compositor_plus
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
    {f : X ⟶ Y} {g : Y ⟶ Z}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (cf : Compactification f) (cg : Compactification g)
    (cfg : Compactification (f ≫ g))
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    DerivedCategory.Plus.ι.map ((coherenceEtaleCompositor A cf cg cfg).hom.app K) ≫
        (Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
          (ModuleCat.{u + 1} A) cfg).hom.app K =
      (Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
          (ModuleCat.{u + 1} A) cg).hom.app
        ((Etale.rightDerivedLowerShriekOfCompactificationPlus
          (ModuleCat.{u + 1} A) cf).obj K) ≫
      (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cg).map
        ((Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
          (ModuleCat.{u + 1} A) cf).hom.app K) ≫
      (CoefficientCompatibility.etaleCompositor A cf cg cfg).hom.app K.obj := by
  let := cf.hasCompactification
  let := cg.hasCompactification
  let := cfg.hasCompactification
  let f₀ := HasCompactification.compactification f
  let g₀ := HasCompactification.compactification g
  let h₀ := HasCompactification.compactification (f ≫ g)
  apply Etale.restriction_compositor_paste
    (Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
      (ModuleCat.{u + 1} A) cf).hom
    (Etale.rightDerivedLowerShriekPlusCompatibility (ModuleCat.{u + 1} A) f).hom
    (Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
      (ModuleCat.{u + 1} A) cg).hom
    (Etale.rightDerivedLowerShriekPlusCompatibility (ModuleCat.{u + 1} A) g).hom
    (Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
      (ModuleCat.{u + 1} A) cfg).hom
    (Etale.rightDerivedLowerShriekPlusCompatibility (ModuleCat.{u + 1} A) (f ≫ g)).hom
    (Etale.rightDerivedLowerShriekIso A cf).hom
    (Etale.rightDerivedLowerShriekIso A cg).hom
    (Etale.unboundedEtaleLowerShriekCompIso A f g).hom
    (Etale.rightDerivedLowerShriekIso A cfg).inv
    (coherenceEtaleChangeIso A cf f₀).hom
    (coherenceEtaleChangeIso A cg g₀).hom
    (Etale.rightDerivedLowerShriekPlusCompIso A f g).hom
    (coherenceEtaleChangeIso A h₀ cfg).hom
    (Etale.unboundedEtaleCompactSupport_comparison_plus A f cf f₀)
    (Etale.unboundedEtaleCompactSupport_comparison_plus A g cg g₀)
    (Etale.unboundedEtaleCompactSupport_composition_plus A f g)
    ?_ (CoefficientCompatibility.etaleCompositor A cf cg cfg).hom
    (coherenceEtaleCompositor A cf cg cfg).hom ?_ ?_ K
  · intro L
    have ht := Etale.unboundedEtaleCompactSupport_comparison_plus A (f ≫ g) h₀ cfg L
    simpa only [coherenceEtaleChangeIso, Etale.rightDerivedLowerShriekIso,
      ← Etale.unbounded_pairwise_iso_symm A (f ≫ g) cfg h₀,
      Iso.symm_hom, h₀, Etale.rightDerivedLowerShriekPlusCompatibility] using ht
  · ext L
    simp only [CoefficientCompatibility.etaleCompositor, Iso.trans_hom,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Iso.symm_hom,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      NatTrans.hcomp_app, Category.assoc]
    exact (Etale.rightDerivedLowerShriekIso A cg).hom.naturality_assoc
      ((Etale.rightDerivedLowerShriekIso A cf).hom.app L) _
  · change (coherenceCompositorOfChanges _ _ _ _ _ _ _ _ _ _).hom = _
    exact change_compositor_hom _ _ _ _ _ _ _ _ _ _

private theorem canonical_compositor_factor
    (A : Type u) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
    {f : X ⟶ Y} {g : Y ⟶ Z}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (cf : Compactification f) (cg : Compactification g)
    (cfg : Compactification (f ≫ g))
    (E : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A))))
    (hFL : DerivedCategory.TStructure.t.plus
      ((Etale.rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) cf).obj E.obj)) :
    canonicalIntrinsicCompactSupportCompositor A cf cg cfg E =
      (reductionCompactSupport A cg.i cg.g).mapIso
        (canonicalCompactSupportSiteIso A cf E).symm ≪≫
      (canonicalCompactSupportSiteIso A cg ⟨_, hFL⟩).symm ≪≫
      (finiteCoefficientIntrinsicDerivedComparison Z A).mapIso
        ((etaleCompositor (ULift.{u + 1, u} A) cf cg cfg).app E.obj) ≪≫
      canonicalCompactSupportSiteIso A cfg E := by
  let N := finiteCoefficientIntrinsicDerivedComparison Z A
  let F := Etale.rightDerivedLowerShriekOfCompactification
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) cg
  let G := reductionCompactSupport A cg.i cg.g
  let Ecf := (Etale.rightDerivedLowerShriekOfCompactificationPlus
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) cf).obj E
  let qcf := (Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) cf).app E
  let qcg := (Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) cg).app Ecf
  let qcfg := (Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) cfg).app E
  have hc : N.map qcg.inv ≫
        N.map (DerivedCategory.Plus.ι.map
          ((coherenceEtaleCompositor (ULift.{u + 1, u} A) cf cg cfg).hom.app E)) ≫
        N.map qcfg.hom =
      N.map (F.map qcf.hom) ≫
        N.map ((etaleCompositor (ULift.{u + 1, u} A) cf cg cfg).hom.app E.obj) := by
    apply (cancel_epi (N.map qcg.hom)).1
    simp only [← N.map_comp_assoc, Iso.hom_inv_id_assoc]
    simpa only [N, F, qcf, qcg, qcfg, Ecf, Iso.app_hom,
      ← Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc] using
      congrArg N.map (compositor_plus (ULift.{u + 1, u} A) cf cg cfg E)
  have hn := canonical_site_naturality A cg
    (ObjectProperty.homMk qcf.hom : Ecf ⟶ ⟨_, hFL⟩)
  have hq : G.map ((finiteCoefficientIntrinsicDerivedComparison Y A).map qcf.inv) ≫
        (canonicalCompactSupportSiteIso A cg Ecf).inv ≫ N.map (F.map qcf.hom) =
      (canonicalCompactSupportSiteIso A cg ⟨_, hFL⟩).inv := by
    apply (cancel_mono (canonicalCompactSupportSiteIso A cg ⟨_, hFL⟩).hom).1
    simp only [Category.assoc, Iso.inv_hom_id]
    erw [hn]
    simp only [Iso.inv_hom_id_assoc, ObjectProperty.homMk_hom, G,
      ← Functor.map_comp, Iso.inv_hom_id]
    erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  apply Iso.ext
  dsimp only [canonicalIntrinsicCompactSupportCompositor]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.mapIso_inv,
    Iso.app_hom, Iso.app_inv, Category.assoc]
  erw [reassoc_of% hc, reassoc_of% hq]
  rfl

private theorem canonical_refinement_factor
    (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    {cf cd : Compactification f} (r : cf.Refinement cd)
    (E : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))) :
    canonicalIntrinsicCompactSupportRefinement A f r E =
      (canonicalCompactSupportSiteIso A cd E).symm ≪≫
      (finiteCoefficientIntrinsicDerivedComparison Y A).mapIso
        ((Etale.rightDerivedLowerShriekOfCompactificationIso
          (ULift.{u + 1, u} A) cd cf).app E.obj) ≪≫
      canonicalCompactSupportSiteIso A cf E := by
  have hh := Etale.unboundedEtaleCompactSupport_comparison_plus
    (ULift.{u + 1, u} A) f cd cf E
  rw [← Etale.rightDerivedLowerShriekOfCompactificationPlusIso_symm,
    ← Etale.rightDerivedLowerShriekOfCompactificationPlusRefinementIso_eq
      (ULift.{u + 1, u} A) r] at hh
  let N := finiteCoefficientIntrinsicDerivedComparison Y A
  apply Iso.ext
  simp only [canonicalIntrinsicCompactSupportRefinement, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Functor.mapIso_inv, Iso.app_hom, Iso.app_inv, Category.assoc]
  simp only [← Functor.map_comp_assoc]
  erw [hh]
  simp only [Iso.inv_hom_id_app_assoc]
  rfl

private theorem intrinsic_refinement
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B)
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
        (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
        {cf cd : Compactification f} (r : cf.Refinement cd)
        (E : DerivedCategory.Plus
          (Sheaf X.smallEtaleTopology
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A))))
        (hE : DerivedCategory.TStructure.t.plus
          ((Etale.scalarExtension
            (RingHom.ulift.{u + 1, u + 1, u, u} φ) X).obj E.obj)) :
        (scalarExtensionFunctor φ Y).map
            (canonicalIntrinsicCompactSupportRefinement A f r E).hom ≫
          (reductionDirectImageComparison φ cf.i cf.g).app
            ((finiteCoefficientIntrinsicDerivedComparison X A).obj E.obj) ≫
          (reductionCompactSupport B cf.i cf.g).map
            ((canonicalSiteScalarIso φ X).hom.app E.obj) =
        (reductionDirectImageComparison φ cd.i cd.g).app
            ((finiteCoefficientIntrinsicDerivedComparison X A).obj E.obj) ≫
          (reductionCompactSupport B cd.i cd.g).map
            ((canonicalSiteScalarIso φ X).hom.app E.obj) ≫
          (canonicalIntrinsicCompactSupportRefinement B f r
            ⟨(Etale.scalarExtension
                (RingHom.ulift.{u + 1, u + 1, u, u} φ) X).obj E.obj, hE⟩).hom := by
  let T := scalarExtensionFunctor φ Y
  let N := finiteCoefficientIntrinsicDerivedComparison Y B
  let EB : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} B))) := ⟨_, hE⟩
  have he := Etale.compactScalar_compactification_comparison φ.ulift cd cf E hE
  have hn := (canonicalSiteScalarIso φ Y).hom.naturality
    ((Etale.rightDerivedLowerShriekOfCompactificationIso
      (ULift.{u + 1, u} A) cd cf).hom.app E.obj)
  dsimp only [Functor.comp_map] at hn
  have ht := coefficientRefinementTransport
    (T.mapIso (canonicalCompactSupportSiteIso A cd E))
    (T.mapIso (canonicalCompactSupportSiteIso A cf E))
    (canonicalCompactSupportSiteIso B cd EB).symm
    (canonicalCompactSupportSiteIso B cf EB).symm
    (intrinsic_square φ cd E hE) (intrinsic_square φ cf E hE) hn
    (by simpa only [Functor.map_comp] using congrArg N.map he)
  simp only [canonical_refinement_factor, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Functor.mapIso_inv, Iso.app_hom, Iso.app_inv,
    Functor.map_comp, Category.assoc] at ht ⊢
  exact ht

private theorem intrinsic_composition
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B)
    {X Y S : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] [IsNoetherian S]
        {f : X ⟶ Y} {g : Y ⟶ S} [IsSeparated f] [LocallyOfFiniteType f]
        [QuasiCompact f] [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
        (cf : Compactification f) (cg : Compactification g)
        (cfg : Compactification (f ≫ g))
        (E : DerivedCategory.Plus
          (Sheaf X.smallEtaleTopology
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A))))
        (hE : DerivedCategory.TStructure.t.plus
          ((Etale.scalarExtension
            (RingHom.ulift.{u + 1, u + 1, u, u} φ) X).obj E.obj)) :
        (scalarExtensionFunctor φ S).map
            (canonicalIntrinsicCompactSupportCompositor A cf cg cfg E).inv ≫
          (reductionDirectImageComparison φ cg.i cg.g).app
            ((reductionCompactSupport A cf.i cf.g).obj
              ((finiteCoefficientIntrinsicDerivedComparison X A).obj E.obj)) ≫
          (reductionCompactSupport B cg.i cg.g).map
            ((reductionDirectImageComparison φ cf.i cf.g).app
              ((finiteCoefficientIntrinsicDerivedComparison X A).obj E.obj)) ≫
          (reductionCompactSupport B cg.i cg.g).map
            ((reductionCompactSupport B cf.i cf.g).map
              ((canonicalSiteScalarIso φ X).hom.app E.obj)) ≫
          (canonicalIntrinsicCompactSupportCompositor B cf cg cfg
            ⟨(Etale.scalarExtension
                (RingHom.ulift.{u + 1, u + 1, u, u} φ) X).obj E.obj, hE⟩).hom =
        (reductionDirectImageComparison φ cfg.i cfg.g).app
          ((finiteCoefficientIntrinsicDerivedComparison X A).obj E.obj) ≫
          (reductionCompactSupport B cfg.i cfg.g).map
            ((canonicalSiteScalarIso φ X).hom.app E.obj) := by
  let RA := ULift.{u + 1, u} A
  let RB := ULift.{u + 1, u} B
  let F := Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} RA) cf
  let FB := Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} RB) cf
  let H := Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} RB) cg
  let G := reductionCompactSupport B cg.i cg.g
  let T := scalarExtensionFunctor φ S
  let N := finiteCoefficientIntrinsicDerivedComparison S B
  have hFL := Etale.compactification_preserves_plus RA cf E
  have hFAB := Etale.scalar_compactification_preserves_plus φ.ulift cf E hE
  have hFBL := Etale.compactification_preserves_plus RB cf ⟨_, hE⟩
  let FL : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} RA)) :=
    ⟨_, hFL⟩
  let FLB : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} RB)) :=
    ⟨_, hFAB⟩
  let FBL : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} RB)) :=
    ⟨_, hFBL⟩
  let EB : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} RB)) :=
    ⟨_, hE⟩
  let BA := (reductionCompactSupport A cg.i cg.g).mapIso
      (canonicalCompactSupportSiteIso A cf E).symm ≪≫
    (canonicalCompactSupportSiteIso A cg FL).symm
  let BB := G.mapIso (canonicalCompactSupportSiteIso B cf EB).symm ≪≫
    (canonicalCompactSupportSiteIso B cg FBL).symm
  have hc := intrinsic_square φ cf E hE
  have hd := intrinsic_square φ cg FL hFAB
  have he := intrinsic_square φ cfg E hE
  have hc' := coefficientSquareForward
    ((scalarExtensionFunctor φ Y).mapIso (canonicalCompactSupportSiteIso A cf E))
    (canonicalCompactSupportSiteIso B cf EB).symm hc
  have hd' := coefficientSquareForward
    (T.mapIso (canonicalCompactSupportSiteIso A cg FL))
    (canonicalCompactSupportSiteIso B cg FLB).symm hd
  have hn₀ := canonical_site_naturality B cg
    (ObjectProperty.homMk ((Etale.compactScalarMap φ.ulift cf).app E.obj) : FLB ⟶ FBL)
  have hn := congrArg (fun z => (canonicalCompactSupportSiteIso B cg FLB).inv ≫ z ≫
    (canonicalCompactSupportSiteIso B cg FBL).inv) hn₀
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id, Category.comp_id] at hn
  have hv := coefficientVerticalForward
    (scalarExtensionFunctor φ Y) T (reductionCompactSupport A cg.i cg.g) G
    (reductionDirectImageComparison φ cg.i cg.g)
    (canonicalCompactSupportSiteIso A cf E).symm
    (canonicalCompactSupportSiteIso A cg FL).symm
    (canonicalCompactSupportSiteIso B cf EB).symm
    (canonicalCompactSupportSiteIso B cg FLB).symm
    (canonicalCompactSupportSiteIso B cg FBL).symm
    ((canonicalSiteScalarIso φ Y).hom.app FL.obj)
    ((finiteCoefficientIntrinsicDerivedComparison Y B).map
      ((Etale.compactScalarMap φ.ulift cf).app E.obj))
    ((reductionDirectImageComparison φ cf.i cf.g).app
        ((finiteCoefficientIntrinsicDerivedComparison X A).obj E.obj) ≫
      (reductionCompactSupport B cf.i cf.g).map
        ((canonicalSiteScalarIso φ X).hom.app E.obj))
    ((canonicalSiteScalarIso φ S).hom.app
        ((Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} RA) cg).obj
          FL.obj) ≫ N.map ((Etale.compactScalarMap φ.ulift cg).app FL.obj))
    (N.map (H.map ((Etale.compactScalarMap φ.ulift cf).app E.obj)))
    (by simpa only [Functor.mapIso_inv, Iso.symm_inv, Iso.symm_hom,
      Category.assoc, FL, RA] using hc')
    (by simpa only [Functor.mapIso_inv, Iso.symm_inv, Iso.symm_hom,
      Category.assoc, FL, RA, G, N] using hd') hn.symm
  have hEt := etaleCoefficientComposition φ.ulift f g cf cg cfg E hE hFL hFAB
  simp only [etaleCoefficientMap_eq_compactScalarMap] at hEt
  have hNEt := congrArg N.map hEt
  simp only [Functor.map_comp] at hNEt
  have hδ := (canonicalSiteScalarIso φ S).hom.naturality
    ((etaleCompositor RA cf cg cfg).hom.app E.obj)
  dsimp only [Functor.comp_map] at hδ
  have hv' : T.map BA.hom ≫
      (canonicalSiteScalarIso φ S).hom.app
        ((Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} RA) cg).obj
          FL.obj) ≫
      N.map ((Etale.compactScalarMap φ.ulift cg).app FL.obj) ≫
      N.map (H.map ((Etale.compactScalarMap φ.ulift cf).app E.obj)) =
    (reductionDirectImageComparison φ cg.i cg.g).app
        ((reductionCompactSupport A cf.i cf.g).obj
          ((finiteCoefficientIntrinsicDerivedComparison X A).obj E.obj)) ≫
      G.map ((reductionDirectImageComparison φ cf.i cf.g).app
        ((finiteCoefficientIntrinsicDerivedComparison X A).obj E.obj)) ≫
      G.map ((reductionCompactSupport B cf.i cf.g).map
        ((canonicalSiteScalarIso φ X).hom.app E.obj)) ≫ BB.hom := by
    simpa only [BA, BB, Iso.trans_hom, Functor.mapIso_hom, Functor.mapIso_inv,
      Iso.symm_hom, Iso.app_hom, Iso.app_inv, Functor.map_comp, Category.assoc,
      G, H, T, N, FL, FBL, EB, ObjectProperty.homMk_hom] using hv
  have hcomp :
      T.map (canonicalIntrinsicCompactSupportCompositor A cf cg cfg E).hom ≫
        (reductionDirectImageComparison φ cfg.i cfg.g).app
          ((finiteCoefficientIntrinsicDerivedComparison X A).obj E.obj) ≫
        (reductionCompactSupport B cfg.i cfg.g).map
          ((canonicalSiteScalarIso φ X).hom.app E.obj) =
      (reductionDirectImageComparison φ cg.i cg.g).app
          ((reductionCompactSupport A cf.i cf.g).obj
            ((finiteCoefficientIntrinsicDerivedComparison X A).obj E.obj)) ≫
        G.map ((reductionDirectImageComparison φ cf.i cf.g).app
          ((finiteCoefficientIntrinsicDerivedComparison X A).obj E.obj)) ≫
        G.map ((reductionCompactSupport B cf.i cf.g).map
          ((canonicalSiteScalarIso φ X).hom.app E.obj)) ≫
        (canonicalIntrinsicCompactSupportCompositor B cf cg cfg EB).hom := by
    rw [canonical_compositor_factor A cf cg cfg E hFL,
      canonical_compositor_factor B cf cg cfg EB hFBL]
    simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.mapIso_inv,
      Iso.app_hom, Iso.app_inv, Functor.map_comp, Category.assoc]
    erw [he, reassoc_of% hδ, reassoc_of% hNEt]
    simp only [BA, BB, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
      Functor.mapIso_inv, Iso.app_hom, Iso.app_inv, Functor.map_comp, Category.assoc] at hv'
    erw [reassoc_of% hv']
    rfl
  have hh := congrArg (fun z =>
    T.map (canonicalIntrinsicCompactSupportCompositor A cf cg cfg E).inv ≫ z) hcomp
  simpa only [Category.assoc, ← T.map_comp_assoc, Iso.inv_hom_id, T.map_id,
    Category.id_comp] using hh.symm

/-- General-field compact-support scalar/site square.

Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-sp-grp-ladic-summary/sec-change-of-finite-coefficients/
sk-lem-sp-reduction/sk-lem-sp-reduction-exceptional.md`, Existence and Locality:
`b`, open balancing and composition; Charts: identification with finite-site computation
(blueprint: `lem-pur-general-field-compact-scalar-site-square`).

Proof steps: (1) construct the intrinsic constant-ring comparison from the etale
proper mate and the exact open tensor comparison; (2) prove the proper square by
the finite-coefficient projection formula; (3) prove the open square by the
unit-normalized balancing map; (4) paste the proper and open squares to obtain
the displayed formula; (5) transport it through every etale-origin presentation;
(6) use the canonical etale compact-support compositor, its intrinsic site transport,
and the finite-site coherence calculation to identify the composite b-map with
`F_{v,B}(b_u) ≫ b_v(F_{u,A})`; the coefficient-mate and tensor/site squares
transport this identity through `φ`.  Use the canonical etale lower-shriek
composition isomorphism to identify the corresponding beta composite. (7) use the
canonical proper-refinement comparison, the pro-etale refinement coefficient mate,
and their intrinsic site transport for the b square; use the canonical lower-shriek
refinement comparison for the beta scalar square.  The naturality clause transports
the displayed formula through `η` by naturality of the scalar map and of both
reduction functors.
The proof is postponed. -/
theorem generalFieldCompactScalarSiteSquare
    (ell pchar : ℕ) [Fact ell.Prime] (hp : 0 < pchar) (hell : pchar ≠ ell)
    (k : Type u) [Field k] [CharP k pchar]
    {Z W : Scheme.{u}}
    [Z.Over (Spec (.of k))] [W.Over (Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))]
    [QuasiCompact (Z ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))]
    [LocallyOfFiniteType (W ↘ Spec (.of k))]
    [QuasiCompact (W ↘ Spec (.of k))]
    [IsSeparated (W ↘ Spec (.of k))]
    (h : Z ⟶ W) [h.IsOver (Spec (.of k))]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    (c : Compactification h)
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (hA : ∃ n : ℕ, ∀ x : A, (ell ^ n) • x = 0)
    (hB : ∃ n : ℕ, ∀ x : B, (ell ^ n) • x = 0)
    (φ : A →+* B)
    (M : proEtaleDerivedCategory Z A)
    (hM : generalFieldDctf Z A M)
    (L : DerivedCategory.Plus
      (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A))))
    (hL : Etale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) Z L.obj)
    (hLB : DerivedCategory.TStructure.t.plus
      ((Etale.scalarExtension
        (RingHom.ulift.{u + 1, u + 1, u, u} φ) Z).obj L.obj))
    (η : (finiteCoefficientIntrinsicDerivedComparison Z A).obj L.obj ≅ M) :
    IsIso ((reductionDirectImageComparison φ c.i c.g).app M) ∧
      generalFieldDctf W B
        ((scalarExtensionFunctor φ W).obj
          ((reductionCompactSupport A c.i c.g).obj M)) ∧
      generalFieldDctf W B
        ((reductionCompactSupport B c.i c.g).obj
          ((scalarExtensionFunctor φ Z).obj M)) ∧
      IsIso ((Etale.compactScalarMap
        (RingHom.ulift.{u + 1, u + 1, u, u} φ) c).app L.obj) ∧
      generalFieldDctf Z A
        ((finiteCoefficientIntrinsicDerivedComparison Z A).obj L.obj) ∧
      generalFieldDctf W B
        ((finiteCoefficientIntrinsicDerivedComparison W B).obj
          ((Etale.rightDerivedLowerShriekOfCompactification
              (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) c).obj
            ((Etale.scalarExtension
              (RingHom.ulift.{u + 1, u + 1, u, u} φ) Z).obj L.obj))) ∧
      ((reductionDirectImageComparison φ c.i c.g).app
          ((finiteCoefficientIntrinsicDerivedComparison Z A).obj L.obj)) =
        (scalarExtensionFunctor φ W).map
          (canonicalCompactSupportSiteIso A c L).inv ≫
          (canonicalSiteScalarIso φ W).hom.app ((Etale.rightDerivedLowerShriekOfCompactification
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c).obj L.obj) ≫
          (finiteCoefficientIntrinsicDerivedComparison W B).map
            ((Etale.compactScalarMap
              (RingHom.ulift.{u + 1, u + 1, u, u} φ) c).app L.obj) ≫
          (canonicalCompactSupportSiteIso B c
            ⟨(Etale.scalarExtension
                (RingHom.ulift.{u + 1, u + 1, u, u} φ) Z).obj L.obj, hLB⟩).hom ≫
          (reductionCompactSupport B c.i c.g).map
            ((canonicalSiteScalarIso φ Z).inv.app L.obj) ∧
      ((scalarExtensionFunctor φ W).map
          ((reductionCompactSupport A c.i c.g).map η.hom) ≫
        (reductionDirectImageComparison φ c.i c.g).app M) =
        (reductionDirectImageComparison φ c.i c.g).app
            ((finiteCoefficientIntrinsicDerivedComparison Z A).obj L.obj) ≫
          (reductionCompactSupport B c.i c.g).map
            ((scalarExtensionFunctor φ Z).map η.hom) ∧
      (∀ {C : Type u} [CommRing C] [Finite C]
        (hC : ∃ n : ℕ, ∀ x : C, (ell ^ n) • x = 0)
        (ψ : B →+* C),
        (scalarExtensionFunctor_composition φ ψ W).hom.app
            ((reductionCompactSupport A c.i c.g).obj M) ≫
          (reductionDirectImageComparison (ψ.comp φ) c.i c.g).app M =
        (scalarExtensionFunctor ψ W).map
            ((reductionDirectImageComparison φ c.i c.g).app M) ≫
          (reductionDirectImageComparison ψ c.i c.g).app
            ((scalarExtensionFunctor φ Z).obj M) ≫
          (reductionCompactSupport C c.i c.g).map
            ((scalarExtensionFunctor_composition φ ψ Z).hom.app M)) ∧
      (∀ {X Y S : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] [IsNoetherian S]
        {f : X ⟶ Y} {g : Y ⟶ S} [IsSeparated f] [LocallyOfFiniteType f]
        [QuasiCompact f] [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
        (cf : Compactification f) (cg : Compactification g)
        (cfg : Compactification (f ≫ g))
        (E : DerivedCategory.Plus
          (Sheaf X.smallEtaleTopology
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A))))
        (hE : DerivedCategory.TStructure.t.plus
          ((Etale.scalarExtension
            (RingHom.ulift.{u + 1, u + 1, u, u} φ) X).obj E.obj)),
        (scalarExtensionFunctor φ S).map
            (canonicalIntrinsicCompactSupportCompositor A cf cg cfg E).inv ≫
          (reductionDirectImageComparison φ cg.i cg.g).app
            ((reductionCompactSupport A cf.i cf.g).obj
              ((finiteCoefficientIntrinsicDerivedComparison X A).obj E.obj)) ≫
          (reductionCompactSupport B cg.i cg.g).map
            ((reductionDirectImageComparison φ cf.i cf.g).app
              ((finiteCoefficientIntrinsicDerivedComparison X A).obj E.obj)) ≫
          (reductionCompactSupport B cg.i cg.g).map
            ((reductionCompactSupport B cf.i cf.g).map
              ((canonicalSiteScalarIso φ X).hom.app E.obj)) ≫
          (canonicalIntrinsicCompactSupportCompositor B cf cg cfg
            ⟨(Etale.scalarExtension
                (RingHom.ulift.{u + 1, u + 1, u, u} φ) X).obj E.obj, hE⟩).hom =
        (reductionDirectImageComparison φ cfg.i cfg.g).app
          ((finiteCoefficientIntrinsicDerivedComparison X A).obj E.obj) ≫
          (reductionCompactSupport B cfg.i cfg.g).map
            ((canonicalSiteScalarIso φ X).hom.app E.obj)) ∧
      (∀ {X Y Z : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
        {f : X ⟶ Y} {g : Y ⟶ Z}
        [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
        [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
        (d : Compactification g) (e : Compactification (f ≫ d.i))
        (E : DerivedCategory
          (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))),
        (Etale.scalarExtension (RingHom.ulift.{u + 1, u + 1, u, u} φ) Z).map
            ((Etale.rightDerivedLowerShriekOfCompactificationCompIso
              (ULift.{u + 1, u} A) d e).hom.app E) ≫
          (Etale.compactScalarMap
            (RingHom.ulift.{u + 1, u + 1, u, u} φ) (d.comp e)).app E =
        (Etale.compactScalarMap
            (RingHom.ulift.{u + 1, u + 1, u, u} φ) d).app
            ((Etale.rightDerivedLowerShriekOfCompactification
              (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) e.restrict).obj E) ≫
          (Etale.rightDerivedLowerShriekOfCompactification
            (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) d).map
            ((Etale.compactScalarMap
              (RingHom.ulift.{u + 1, u + 1, u, u} φ) e.restrict).app E) ≫
          (Etale.rightDerivedLowerShriekOfCompactificationCompIso
            (ULift.{u + 1, u} B) d e).hom.app
            ((Etale.scalarExtension
              (RingHom.ulift.{u + 1, u + 1, u, u} φ) X).obj E)) ∧
      (∀ {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
        (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
        {cf cd : Compactification f} (r : cf.Refinement cd)
        (E : DerivedCategory.Plus
          (Sheaf X.smallEtaleTopology
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A))))
        (hE : DerivedCategory.TStructure.t.plus
          ((Etale.scalarExtension
            (RingHom.ulift.{u + 1, u + 1, u, u} φ) X).obj E.obj)),
        (scalarExtensionFunctor φ Y).map
            (canonicalIntrinsicCompactSupportRefinement A f r E).hom ≫
          (reductionDirectImageComparison φ cf.i cf.g).app
            ((finiteCoefficientIntrinsicDerivedComparison X A).obj E.obj) ≫
          (reductionCompactSupport B cf.i cf.g).map
            ((canonicalSiteScalarIso φ X).hom.app E.obj) =
        (reductionDirectImageComparison φ cd.i cd.g).app
            ((finiteCoefficientIntrinsicDerivedComparison X A).obj E.obj) ≫
          (reductionCompactSupport B cd.i cd.g).map
            ((canonicalSiteScalarIso φ X).hom.app E.obj) ≫
          (canonicalIntrinsicCompactSupportRefinement B f r
            ⟨(Etale.scalarExtension
                (RingHom.ulift.{u + 1, u + 1, u, u} φ) X).obj E.obj, hE⟩).hom) ∧
      (∀ {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
        (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
        {cf cd : Compactification f} (r : cf.Refinement cd)
        (hcart : IsPullback cf.i (𝟙 X) r.hom cd.i)
        (E : DerivedCategory
          (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))),
        (Etale.scalarExtension (RingHom.ulift.{u + 1, u + 1, u, u} φ) Y).map
            ((Etale.rightDerivedLowerShriekOfCompactificationComparison
              (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) r hcart).app E) ≫
          (Etale.compactScalarMap
            (RingHom.ulift.{u + 1, u + 1, u, u} φ) cf).app E =
        (Etale.compactScalarMap
            (RingHom.ulift.{u + 1, u + 1, u, u} φ) cd).app E ≫
          (Etale.rightDerivedLowerShriekOfCompactificationComparison
            (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) r hcart).app
            ((Etale.scalarExtension
              (RingHom.ulift.{u + 1, u + 1, u, u} φ) X).obj E)) := by
  sorry

end AlgebraicGeometry.ProEtale
