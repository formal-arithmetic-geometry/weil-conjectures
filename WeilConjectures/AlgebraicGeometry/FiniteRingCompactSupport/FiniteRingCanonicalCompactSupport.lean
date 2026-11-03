/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekIndependence
public import WeilConjectures.SixFunctors.LowerShriek.Formalism.Compactification
import all WeilConjectures.AlgebraicGeometry.Compact.CompactSupportExchangeTransport
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison

/-! # Canonical finite-ring compact-support comparisons

Source: latest blueprint, thm-cbc-finite-level-proetale; Stacks 0F7I and 09AF.
(blueprint: thm-cbc-finite-level-proetale).

All categories are ordinary uncompleted categories of fixed-ring module sheaves.
The comparison is the transported common-refinement comparison, with its specified
proper/open site-comparison factors. The origin witness is only a computational model.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.FiniteRingCompactSupport

variable (A : Type (u + 1)) [CommRing A] [Finite A]

/-- The ambient ordinary derived category of constant-A module sheaves.
Source: latest blueprint, constant finite coefficients
(blueprint: thm-cbc-finite-level-proetale). -/
abbrev Category (X : Scheme.{u}) :=
  _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))

/-- The compactification representative, using exact open extension followed by Rp_*.
Source: latest blueprint, compactification formula
(blueprint: thm-cbc-finite-level-proetale). -/
abbrev support {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :=
  rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c

/-- The exact comparison functor on ordinary unbounded derived categories.
Source: latest blueprint, site comparison (blueprint: thm-cbc-finite-level-proetale). -/
abbrev comparison (X : Scheme.{u}) :=
  (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory

/-- The actual comparison evaluated on a retained bounded-below etale model.
The middle map is the published origin comparison
`rightDerivedLowerShriekOfCompactificationOriginIso`: the etale common-refinement
comparison conjugated by the proper/open site comparisons, rather than a chosen
isomorphism of the endpoints. Source: latest blueprint, independence of compactification
(blueprint: thm-cbc-finite-level-proetale). -/
def changeAt {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    (c d : Compactification f)
    (L : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (K : Category A X) (w : (comparison A X).obj L.obj ≅ K) :
    (support A c).obj K ≅ (support A d).obj K :=
  (support A c).mapIso w.symm ≪≫
    (rightDerivedLowerShriekOfCompactificationOriginIso A c d).app L ≪≫
    (support A d).mapIso w

/-- Compute the same normalized comparison from an origin certificate.
The certificate determines a model together with its identification with K. Full
faithfulness of comparison makes the above expression independent of this presentation;
it is never an arbitrary isomorphism between the support objects.
Source: latest blueprint, witness-independent transported comparison
(blueprint: thm-cbc-finite-level-proetale). -/
def change {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    (c d : Compactification f) (K : Category A X)
    (hK : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X K) :
    (support A c).obj K ≅ (support A d).obj K :=
  changeAt A c d ⟨hK.choose, hK.choose_spec.1⟩ K
    (Classical.choice hK.choose_spec.2)

/-- The exchange with its target compactification changed by the specified comparison.
Source: latest blueprint, the transported proper/open exchange
(blueprint: thm-cbc-finite-level-proetale). -/
def exchange {X' X Y' Y : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    [QuasiCompact f'] (sq : IsPullback g' f' f g)
    (c : Compactification f) (d : Compactification f')
    (K : Category A X)
    (hP : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X'
      ((upperStar (ModuleCat.{u + 1} A) g').leftDerivedFunctor.obj K)) :
    (upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.obj ((support A c).obj K) ⟶
      (support A d).obj
        ((upperStar (ModuleCat.{u + 1} A) g').leftDerivedFunctor.obj K) :=
  (rightDerivedLowerShriekOfCompactificationBaseChangeMap
    (ModuleCat.{u + 1} A) sq c).app K ≫
    (change A (c.ofIsPullback sq) d _ hP).hom

private theorem changeAt_naturality {X Y : Scheme.{u}} {f : X ⟶ Y}
    [QuasiCompact f] (c d : Compactification f)
    (L M : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (K N : Category A X) (w : (comparison A X).obj L.obj ≅ K)
    (z : (comparison A X).obj M.obj ≅ N) (v : K ⟶ N) :
    (support A c).map v ≫ (changeAt A c d M N z).hom =
      (changeAt A c d L K w).hom ≫ (support A d).map v := by
  obtain ⟨t, ht⟩ := (bijective_comparisonUpperStar_mapDerivedCategory_map
    L.obj M.obj M.property).surjective (w.hom ≫ v ≫ z.inv)
  have hn := (rightDerivedLowerShriekOfCompactificationOriginIso A c d).hom.naturality
    (ObjectProperty.homMk t)
  change (support A c).map ((comparison A X).map t) ≫ _ =
    _ ≫ (support A d).map ((comparison A X).map t) at hn
  have h := congrArg (fun q ↦ (support A c).map w.inv ≫ q ≫
    (support A d).map z.hom) hn
  simp only [ht, Functor.map_comp, Category.assoc] at h
  simpa only [changeAt, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    Category.assoc, ← Functor.map_comp_assoc, ← Functor.map_comp,
    Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id, Iso.hom_inv_id,
    CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id, Iso.app_hom] using h

private theorem change_eq_changeAt {X Y : Scheme.{u}} {f : X ⟶ Y}
    [QuasiCompact f] (c d : Compactification f) (K : Category A X)
    (hK : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X K)
    (L : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (w : (comparison A X).obj L.obj ≅ K) :
    change A c d K hK = changeAt A c d L K w := by
  apply Iso.ext
  have h := changeAt_naturality A c d
    ⟨hK.choose, hK.choose_spec.1⟩ L K K
    (Classical.choice hK.choose_spec.2) w (𝟙 K)
  simpa [change] using h.symm

private theorem change_trans {X Y : Scheme.{u}} {f : X ⟶ Y}
    [QuasiCompact f] (c d e : Compactification f) (K : Category A X)
    (hK : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X K) :
    change A c d K hK ≪≫ change A d e K hK = change A c e K hK := by
  have h := congrArg (fun t ↦ t.app
    (⟨hK.choose, hK.choose_spec.1⟩ :
      _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))))
    (rightDerivedLowerShriekOfCompactificationOriginIso_trans A c d e)
  apply Iso.ext
  have hh := congrArg Iso.hom h
  simpa [change, changeAt, Category.assoc, ← Functor.map_comp_assoc] using
    congrArg (fun q ↦ (support A c).map (Classical.choice hK.choose_spec.2).inv ≫ q ≫
      (support A e).map (Classical.choice hK.choose_spec.2).hom) hh

private theorem change_refl {X Y : Scheme.{u}} {f : X ⟶ Y}
    [QuasiCompact f] (c : Compactification f) (K : Category A X)
    (hK : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X K) :
    change A c c K hK = Iso.refl _ := by
  have h := change_trans A c c c K hK
  apply Iso.ext
  have hh := congrArg Iso.hom h
  exact (cancel_epi (change A c c K hK).hom).1 (by simpa using hh)

private abbrev etaleComparison (X : Scheme.{u}) :=
  _root_.DerivedCategory.Plus.ι ⋙ comparison A X

private abbrev etaleSupport {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :=
  Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A) c

private def modelComparison {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    etaleComparison A X ⋙ support A c ≅ etaleSupport A c ⋙ etaleComparison A Y :=
  rightDerivedLowerShriekOfCompactificationComparisonIso (ModuleCat.{u + 1} A) c ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility _ c).symm _ ≪≫
    Functor.associator _ _ _

private theorem modelComparison_origin {X Y : Scheme.{u}} {f : X ⟶ Y}
    [QuasiCompact f] (c d : Compactification f)
    (L : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (modelComparison A c).hom.app L ≫ (etaleComparison A Y).map
        ((Etale.rightDerivedLowerShriekOfCompactificationPlusIso A c d).hom.app L) =
      (rightDerivedLowerShriekOfCompactificationOriginIso A c d).hom.app L ≫
        (modelComparison A d).hom.app L := by
  simp only [modelComparison, rightDerivedLowerShriekOfCompactificationOriginIso,
    Etale.rightDerivedLowerShriekOfCompactificationPlusιIso,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.comp_map, Category.id_comp, Category.assoc, Iso.inv_hom_id_app_assoc,
    comparison, Functor.map_comp]
  simp only [← Functor.map_comp, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.comp_id]

private theorem modelComparison_inv {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f)
    (L : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (modelComparison A c).inv.app L =
      (rightDerivedLowerStarComparisonIso' c.g (ModuleCat.{u + 1} A)).hom.app
          ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i)
            |>.mapDerivedCategoryPlus.obj L) ≫
        (lowerStar (ModuleCat.{u + 1} A) c.g).rightDerivedFunctor.map
          ((fixSiteOpenComparison A c.i).hom.app L.obj) := by
  with_unfolding_all
    have hsym : Functor.mapDerivedCategoryNatIso
        (openImmersionLowerShriekComparisonUpperStarIso (ModuleCat.{u + 1} A) c.i).symm =
        (Functor.mapDerivedCategoryNatIso
          (openImmersionLowerShriekComparisonUpperStarIso (ModuleCat.{u + 1} A) c.i)).symm := by
      apply Iso.ext
      exact Functor.mapDerivedCategoryNatIso_symm _
    simp only [modelComparison, rightDerivedLowerShriekOfCompactificationComparisonIso,
      Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility,
      rightDerivedLowerStarComparisonIso, rightDerivedLowerStarComparisonIso',
      rightDerivedLowerStarComparisonPlusIso, fixSiteOpenComparison,
      Functor.mapDerivedCategoryPlusCompatibility,
      Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
      NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv,
      Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Iso.refl_hom, Iso.refl_inv,
      NatTrans.id_app, Functor.comp_map, CategoryTheory.Functor.map_id, Category.id_comp,
      Category.comp_id,
      Category.assoc, hsym]
    dsimp only [Functor.comp_obj, ObjectProperty.ι_obj, Functor.mapDerivedCategoryPlus,
      ObjectProperty.lift]
    simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
    simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app]
    erw [CategoryTheory.Functor.map_id, Category.id_comp]

private theorem transport_origin {X Y : Scheme.{u}} {f : X ⟶ Y}
    [QuasiCompact f] (c d : Compactification f)
    (L : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (compactExchangeTransportComparison A c).hom.app L ≫
        (rightDerivedLowerShriekOfCompactificationOriginIso A c d).hom.app L =
      (etaleComparison A Y).map
          ((Etale.rightDerivedLowerShriekOfCompactificationPlusIso A c d).hom.app L) ≫
        (compactExchangeTransportComparison A d).hom.app L := by
  have hc := (modelComparison_inv A c L).trans (compactComparison_hom A c L).symm
  have hd := (modelComparison_inv A d L).trans (compactComparison_hom A d L).symm
  rw [← hc, ← hd]
  have hh := congrArg (fun q ↦ (modelComparison A c).inv.app L ≫ q ≫
    (modelComparison A d).inv.app L) (modelComparison_origin A c d L)
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Iso.hom_inv_id_app] at hh
  erw [Category.comp_id] at hh
  exact hh.symm

private theorem source_transport_change {X Y Y' : Scheme.{u}}
    {f : X ⟶ Y} [QuasiCompact f] (g : Y' ⟶ Y) (c b : Compactification f)
    (L : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (etaleComparison A Y').map
        ((Etale.upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategoryPlus.map
          ((Etale.rightDerivedLowerShriekOfCompactificationPlusIso A c b).hom.app L)) ≫
      (compactExchangeTransportSource A g b).hom.app L =
    (compactExchangeTransportSource A g c).hom.app L ≫
      (upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.map
        ((rightDerivedLowerShriekOfCompactificationOriginIso A c b).hom.app L) := by
  with_unfolding_all
    have hn := (leftDerivedUpperStarComparisonIso g A).hom.naturality
      ((Etale.rightDerivedLowerShriekOfCompactificationPlusIso A c b).hom.app L)
    simp only [Functor.comp_map] at hn
    simp only [compactExchangeTransportSource, Iso.trans_hom, Iso.symm_hom,
      NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp, Category.assoc,
      etaleComparison, comparison, Functor.comp_map]
    erw [reassoc_of% hn, ← Functor.map_comp, ← transport_origin A c b L, Functor.map_comp]
    rfl

private theorem target_transport_change {X' X Y' Y : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    [QuasiCompact f'] (sq : IsPullback g' f' f g) (c b : Compactification f)
    (L : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (etaleComparison A Y').map
        ((Etale.rightDerivedLowerShriekOfCompactificationPlusIso A
          (c.ofIsPullback sq) (b.ofIsPullback sq)).hom.app
            ((Etale.upperStar (ModuleCat.{u + 1} A) g').mapDerivedCategoryPlus.obj L)) ≫
      (compactExchangeTransportTarget A sq b).hom.app L =
    (compactExchangeTransportTarget A sq c).hom.app L ≫
      (changeAt A (c.ofIsPullback sq) (b.ofIsPullback sq)
        ((Etale.upperStar (ModuleCat.{u + 1} A) g').mapDerivedCategoryPlus.obj L)
        ((upperStar (ModuleCat.{u + 1} A) g').leftDerivedFunctor.obj
          ((comparison A X).obj L.obj))
        ((leftDerivedUpperStarComparisonIso g' A).app L)).hom := by
  with_unfolding_all
    simp only [compactExchangeTransportTarget, changeAt,
      Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app_hom, Iso.app_inv,
      NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp, Category.assoc]
    dsimp only [Functor.comp_obj, ObjectProperty.ι_obj]
    simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app, Category.id_comp]
    erw [CategoryTheory.Functor.map_id, Category.id_comp]
    have htr := transport_origin A (c.ofIsPullback sq) (b.ofIsPullback sq)
      ((Etale.upperStar (ModuleCat.{u + 1} A) g').mapDerivedCategoryPlus.obj L)
    rw [reassoc_of% htr]
    rfl

private theorem square_of_transport {C D : Type*} [CategoryTheory.Category C]
    [CategoryTheory.Category D] (F : C ⥤ D) {a b c d : C} {p q r s : D}
    (S : F.obj a ≅ p) {T : F.obj b ⟶ q} {U : F.obj c ⟶ r} {V : F.obj d ⟶ s}
    {ab : a ⟶ b} {cd : c ⟶ d} {ac : a ⟶ c} {bd : b ⟶ d}
    {pq : p ⟶ q} {rs : r ⟶ s} {pr : p ⟶ r} {qs : q ⟶ s}
    (he : ab ≫ bd = ac ≫ cd)
    (hc : F.map ac ≫ U = S.hom ≫ pr) (hb : F.map bd ≫ V = T ≫ qs)
    (hs : F.map ab ≫ T = S.hom ≫ pq) (ht : F.map cd ≫ V = U ≫ rs) :
    pq ≫ qs = pr ≫ rs := by
  apply (cancel_epi S.hom).1
  calc
    S.hom ≫ (pq ≫ qs) = F.map ab ≫ (T ≫ qs) := by
      rw [← Category.assoc, ← hs, Category.assoc]
    _ = F.map ab ≫ (F.map bd ≫ V) := by rw [hb]
    _ = F.map ac ≫ (F.map cd ≫ V) := by
      rw [← Functor.map_comp_assoc, he, Functor.map_comp, Category.assoc]
    _ = (F.map ac ≫ U) ≫ rs := by rw [ht, Category.assoc]
    _ = S.hom ≫ (pr ≫ rs) := by rw [hc, Category.assoc]

private theorem etale_change_square {X' X Y' Y : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    [QuasiCompact f] [QuasiCompact f'] (sq : IsPullback g' f' f g)
    (c b : Compactification f) :
    Functor.whiskerRight
        (Etale.rightDerivedLowerShriekOfCompactificationPlusIso A c b).hom
        (Etale.upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategoryPlus ≫
      Etale.rightDerivedLowerShriekOfCompactificationPlusBaseChangeMap A sq b =
    Etale.rightDerivedLowerShriekOfCompactificationPlusBaseChangeMap A sq c ≫
      Functor.whiskerLeft (Etale.upperStar (ModuleCat.{u + 1} A) g').mapDerivedCategoryPlus
        (Etale.rightDerivedLowerShriekOfCompactificationPlusIso A
          (c.ofIsPullback sq) (b.ofIsPullback sq)).hom := by
  have h := (Etale.derivedPlusFormalism (ModuleCat.{u + 1} A))
    |>.shriekBaseChangeOfIsPullback_shriekIso sq c b
  erw [Etale.derivedPlusFormalism_shriekIso,
    Etale.derivedPlusFormalism_shriekIso] at h
  exact h

private theorem raw_model_square {X' X Y' Y : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] [QuasiCompact f']
    (sq : IsPullback g' f' f g) (c b : Compactification f)
    (L : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.map
        ((rightDerivedLowerShriekOfCompactificationOriginIso A c b).hom.app L) ≫
      (rightDerivedLowerShriekOfCompactificationBaseChangeMap
        (ModuleCat.{u + 1} A) sq b).app ((comparison A X).obj L.obj) =
    (rightDerivedLowerShriekOfCompactificationBaseChangeMap
        (ModuleCat.{u + 1} A) sq c).app ((comparison A X).obj L.obj) ≫
      (changeAt A (c.ofIsPullback sq) (b.ofIsPullback sq)
        ((Etale.upperStar (ModuleCat.{u + 1} A) g').mapDerivedCategoryPlus.obj L)
        ((upperStar (ModuleCat.{u + 1} A) g').leftDerivedFunctor.obj
          ((comparison A X).obj L.obj))
        ((leftDerivedUpperStarComparisonIso g' A).app L)).hom := by
  with_unfolding_all
    have hc := congrArg (fun t ↦ t.app L) (compactSupport_exchange_transport A sq c).1
    have hb := congrArg (fun t ↦ t.app L) (compactSupport_exchange_transport A sq b).1
    have he := congrArg (fun t ↦ t.app L) (etale_change_square A sq c b)
    dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at he
    dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.comp_map] at hc hb
    exact square_of_transport (etaleComparison A Y')
      ((compactExchangeTransportSource A g c).app L) he hc hb
      (source_transport_change A g c b L) (target_transport_change A sq c b L)

private theorem raw_change_square {X' X Y' Y : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] [QuasiCompact f']
    (sq : IsPullback g' f' f g) (c b : Compactification f) (K : Category A X)
    (hK : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X K)
    (hP : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X'
      ((upperStar (ModuleCat.{u + 1} A) g').leftDerivedFunctor.obj K)) :
    (upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.map
        (change A c b K hK).hom ≫
      (rightDerivedLowerShriekOfCompactificationBaseChangeMap
        (ModuleCat.{u + 1} A) sq b).app K =
    (rightDerivedLowerShriekOfCompactificationBaseChangeMap
        (ModuleCat.{u + 1} A) sq c).app K ≫
      (change A (c.ofIsPullback sq) (b.ofIsPullback sq) _ hP).hom := by
  with_unfolding_all
    let L : _root_.DerivedCategory.Plus
        (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) := ⟨hK.choose, hK.choose_spec.1⟩
    let w : (comparison A X).obj L.obj ≅ K := Classical.choice hK.choose_spec.2
    let M := (Etale.upperStar (ModuleCat.{u + 1} A) g').mapDerivedCategoryPlus.obj L
    let w₀ := (leftDerivedUpperStarComparisonIso g' A).app L
    let wP := w₀ ≪≫ (upperStar (ModuleCat.{u + 1} A) g').leftDerivedFunctor.mapIso w
    rw [change_eq_changeAt A c b K hK L w,
      change_eq_changeAt A (c.ofIsPullback sq) (b.ofIsPullback sq) _ hP M wP]
    have hs := changeAt_naturality A c b L L _ K (Iso.refl _) w w.hom
    have hs' : (support A c).map w.hom ≫ (changeAt A c b L K w).hom =
        (rightDerivedLowerShriekOfCompactificationOriginIso A c b).hom.app L ≫
          (support A b).map w.hom := by
      simpa [changeAt] using hs
    have ht := changeAt_naturality A (c.ofIsPullback sq) (b.ofIsPullback sq)
      M M _ _ w₀ wP ((upperStar (ModuleCat.{u + 1} A) g').leftDerivedFunctor.map w.hom)
    have hc := (rightDerivedLowerShriekOfCompactificationBaseChangeMap
      (ModuleCat.{u + 1} A) sq c).naturality w.hom
    have hb := (rightDerivedLowerShriekOfCompactificationBaseChangeMap
      (ModuleCat.{u + 1} A) sq b).naturality w.hom
    dsimp only [Functor.comp_map] at hc hb
    have hm := congrArg (fun q ↦ (upperStar (ModuleCat.{u + 1} A) g)
      |>.leftDerivedFunctor.map q) hs'
    simp only [Functor.map_comp] at hm
    exact square_of_transport (Functor.id (Category A Y'))
      ((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.mapIso
        ((support A c).mapIso w)) (raw_model_square A sq c b L)
      hc.symm hb.symm hm.symm ht.symm

/-- Finite-ring base change and the complete normalization of its representative changes.
Source: latest blueprint thm-cbc-finite-level-proetale, transported exchange and both
independence clauses (blueprint: thm-cbc-finite-level-proetale).

Proof: the first clause is the published
`isIso_rightDerivedLowerShriekOfCompactificationBaseChangeMap_app`. Compute on a bounded-below
etale witness. Finite torsion etale proper base change
makes the proper unit-square-counit mate invertible. Exact extension by zero commutes
with the comparison and with base change. Pasting these gives exactly the raw exchange
in exchange. Proper/open comparison identifies its factors with the transported etale
factors. Full faithfulness of the bounded-below comparison identifies any two witnesses
by their unique compatible isomorphism. Naturality cancels this isomorphism in changeAt,
proving its witness independence. The identity and cocycle rules for etale shriekIso,
conjugated by the displayed site comparisons, give the corresponding rules for change.
Naturality of the site comparison gives naturality for every derived morphism. Applying
these rules to source and target compactifications gives the final exchange square.
No restriction on residue characteristics or constructibility is used. -/
theorem canonical_finite_ring_base_change :
    (∀ {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
      {f : X ⟶ Y} {g : Y' ⟶ Y} [IsSeparated f] [LocallyOfFiniteType f]
      [QuasiCompact f] (sq : IsPullback g' f' f g) (c : Compactification f)
      (K : Category A X)
      (hK : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X K),
      IsIso ((rightDerivedLowerShriekOfCompactificationBaseChangeMap
        (ModuleCat.{u + 1} A) sq c).app K)) ∧
    (∀ {X Y : Scheme.{u}} {f : X ⟶ Y} [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
      (c d : Compactification f) (K : Category A X)
      (hK : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X K)
      (L : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
      (w : (comparison A X).obj L.obj ≅ K),
      change A c d K hK = changeAt A c d L K w) ∧
    (∀ {X Y : Scheme.{u}} {f : X ⟶ Y} [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
      (c d e : Compactification f) (K : Category A X)
      (hK : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X K),
      change A c c K hK = Iso.refl _ ∧
      change A c d K hK ≪≫ change A d e K hK = change A c e K hK) ∧
    (∀ {X Y : Scheme.{u}} {f : X ⟶ Y} [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
      (c d : Compactification f) (K L : Category A X)
      (hK : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X K)
      (hL : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X L) (v : K ⟶ L),
      (support A c).map v ≫ (change A c d L hL).hom =
        (change A c d K hK).hom ≫ (support A d).map v) ∧
    (∀ {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
      {f : X ⟶ Y} {g : Y' ⟶ Y} [IsSeparated f] [LocallyOfFiniteType f]
      [QuasiCompact f'] [QuasiCompact f]
      (sq : IsPullback g' f' f g) (c b : Compactification f)
      (d e : Compactification f') (K : Category A X)
      (hK : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X K)
      (hP : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X'
        ((upperStar (ModuleCat.{u + 1} A) g').leftDerivedFunctor.obj K)),
      IsIso (exchange A sq c d K hP) ∧
      (upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.map
          (change A c b K hK).hom ≫ exchange A sq b e K hP =
        exchange A sq c d K hP ≫ (change A d e _ hP).hom) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro X' X Y' Y g' f' f g _ _ _ sq c K hK
    exact isIso_rightDerivedLowerShriekOfCompactificationBaseChangeMap_app A sq c K hK
  · intro X Y f _ _ _ c d K hK L w
    exact change_eq_changeAt A c d K hK L w
  · intro X Y f _ _ _ c d e K hK
    exact ⟨change_refl A c K hK, change_trans A c d e K hK⟩
  · intro X Y f _ _ _ c d K L hK hL v
    exact changeAt_naturality A c d
      ⟨hK.choose, hK.choose_spec.1⟩ ⟨hL.choose, hL.choose_spec.1⟩ K L
      (Classical.choice hK.choose_spec.2) (Classical.choice hL.choose_spec.2) v
  · intro X' X Y' Y g' f' f g _ _ _ _ sq c b d e K hK hP
    have := isIso_rightDerivedLowerShriekOfCompactificationBaseChangeMap_app A sq c K hK
    refine ⟨by dsimp only [exchange]; infer_instance, ?_⟩
    have hh := raw_change_square A sq c b K hK hP
    have hb := congrArg Iso.hom
      (change_trans A (c.ofIsPullback sq) (b.ofIsPullback sq) e _ hP)
    have hd := congrArg Iso.hom (change_trans A (c.ofIsPullback sq) d e _ hP)
    simp only [Iso.trans_hom] at hb hd
    dsimp only [exchange]
    rw [← Category.assoc, hh]
    simp only [Category.assoc]
    rw [hb, hd]

end AlgebraicGeometry.ProEtale.FiniteRingCompactSupport
