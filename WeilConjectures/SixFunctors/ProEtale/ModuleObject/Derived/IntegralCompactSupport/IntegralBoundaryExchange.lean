/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralCompactSupport.IntegralCompactSupportDefs
public import WeilConjectures.Compactification.RefinementOfIsPullback
public import WeilConjectures.CategoryTheory.Adjunction.ExchangeConjugate
public import WeilConjectures.SixFunctors.LowerShriek.Formalism.BaseChange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ExchangeMono

/-! # Total-derived exchange and a normalized boundary refinement -/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [local instance 3000]
  AlgebraicGeometry.ProEtale.CondensedRing.projectionDerivedMonoidal
attribute [local instance 4000]
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleAbelian
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleMonoidal
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleHasDerived
attribute [local instance 5000]
  AlgebraicGeometry.ProEtale.CondensedRing.projectionSheafMonoidal
  AlgebraicGeometry.ProEtale.CondensedRing.projectionCoefficientMonObj
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleCategory
set_option synthInstance.maxSize 2048

universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing.IntegralCompactSupport
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

@[instance_reducible] private def totalCategory (X : Scheme.{u}) :
    Category (Ambient Λ X) := inferInstance

private abbrev native_refinement_iso {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d) (K : Ambient Λ X) :=
  (extend Λ d.i).obj K ≅ (push Λ r.hom).obj ((extend Λ c.i).obj K)

private abbrev native_normalization {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d) (K : Ambient Λ X)
    (e : native_refinement_iso Λ r K) : Prop :=
  (openAdjunction Λ d.i).homEquiv _ _ e.hom ≫
    refinementRestriction Λ r K = (openAdjunction Λ c.i).unit.app K

private abbrev native_open_isIso {X Y X' Y' : Scheme.{u}}
    {f : X ⟶ Y} {v : Y' ⟶ Y} {f' : X' ⟶ Y'} {u' : X' ⟶ X}
    (c : Compactification f) (sq : IsPullback u' f' f v) : Prop :=
  IsIso (openExchange Λ (c.isPullback_i_ofIsPullback sq).toCommSq)

private theorem normalized_arrow
    {A C D : Type*} [Category A] [Category C] [Category D]
    {Jd : A ⥤ D} {Pd : D ⥤ A} {Jc : A ⥤ C} {Pc : C ⥤ A}
    {L : D ⥤ C} {R : C ⥤ D} (ad : Jd ⊣ Pd) (ac : Jc ⊣ Pc) (ar : L ⊣ R)
    (q : Pd ≅ L ⋙ Pc) (β : Jc ⟶ Jd ⋙ L) [IsIso β]
    (hβ : ∀ K, ad.unit.app K ≫ q.hom.app (Jd.obj K) =
      ac.unit.app K ≫ Pc.map (β.app K))
    [IsIso ad.unit] [IsIso ac.unit]
    (K : A) (e : Jd.obj K ≅ R.obj (Jc.obj K))
    (he : ad.homEquiv _ _ e.hom ≫
        (q.hom.app (R.obj (Jc.obj K)) ≫ Pc.map (ar.counit.app (Jc.obj K))) =
      ac.unit.app K) :
    e.hom = ar.homEquiv _ _ (inv (β.app K)) := by
  let z := ar.homEquiv _ _ (inv (β.app K))
  have hz : ad.homEquiv _ _ z ≫
      (q.hom.app (R.obj (Jc.obj K)) ≫ Pc.map (ar.counit.app (Jc.obj K))) =
        ac.unit.app K := by
    rw [ad.homEquiv_unit]
    have hn := q.hom.naturality z
    dsimp only [Functor.comp_map] at hn
    have ht : L.map z ≫ ar.counit.app (Jc.obj K) = inv (β.app K) :=
      (ar.homEquiv _ _).symm_apply_apply _
    simp only [Category.assoc]
    rw [reassoc_of% hn, ← Pc.map_comp, ht, reassoc_of% (hβ K),
      ← Pc.map_comp, IsIso.hom_inv_id, Pc.map_id, Category.comp_id]
  have hziso : IsIso (ad.homEquiv _ _ e.hom) := by
    rw [ad.homEquiv_unit]
    infer_instance
  have hcomp : IsIso (ad.homEquiv _ _ e.hom ≫
      (q.hom.app (R.obj (Jc.obj K)) ≫ Pc.map (ar.counit.app (Jc.obj K)))) := by
    rw [he]
    infer_instance
  have := IsIso.of_isIso_comp_left (ad.homEquiv _ _ e.hom)
    (q.hom.app (R.obj (Jc.obj K)) ≫ Pc.map (ar.counit.app (Jc.obj K)))
  apply (ad.homEquiv _ _).injective
  apply (cancel_mono (q.hom.app (R.obj (Jc.obj K)) ≫
    Pc.map (ar.counit.app (Jc.obj K)))).mp
  exact he.trans hz.symm

private theorem left_transport_mate
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {J : A ⥤ B} {P : B ⥤ A} {J' : C ⥤ D} {P' : D ⥤ C}
    {U : A ⥤ C} {V : B ⥤ D} (a : J ⊣ P) (b : J' ⊣ P')
    (q : P ⋙ U ≅ V ⋙ P') :
    (Functor.leftUnitor _).inv ≫ Functor.whiskerRight a.unit _ ≫
        (Functor.squareTransport J J' q).hom ≫
        Functor.whiskerLeft _ b.counit ≫ (Functor.rightUnitor _).hom =
      ((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ q.hom)).natTrans := by
  ext K
  simp only [mateEquiv, Equiv.coe_fn_symm_mk, NatTrans.comp_app,
    Functor.squareTransport_hom_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.leftUnitor_inv_app,
    Functor.rightUnitor_hom_app, Functor.comp_obj, Functor.comp_map,
    TwoSquare.natTrans, TwoSquare.mk, Category.id_comp]
  simp

private theorem right_transport_mate
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L : A ⥤ B} {R : B ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
    {U : A ⥤ C} {V : B ⥤ D} (a : L ⊣ R) (b : L' ⊣ R')
    (q : U ⋙ L' ≅ L ⋙ V) :
    (Functor.rightUnitor _).inv ≫ Functor.whiskerLeft _ b.unit ≫
        (Functor.squareTransport R R' q).hom ≫
        Functor.whiskerRight a.counit _ ≫ (Functor.leftUnitor _).hom =
      (mateEquiv a b (TwoSquare.mk _ _ _ _ q.hom)).natTrans := by
  ext K
  simp only [mateEquiv, Equiv.coe_fn_mk, NatTrans.comp_app,
    Functor.squareTransport_hom_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.leftUnitor_hom_app,
    Functor.rightUnitor_inv_app, Functor.comp_obj, Functor.comp_map,
    TwoSquare.natTrans, TwoSquare.mk, Category.id_comp]

private abbrev totalFormalism : CompactSupportFormalism := {
  obj X := Ambient Λ X
  category X := totalCategory Λ X
  pb f := pull Λ f
  pbId X := leftDerivedUpperStarId Λ X
  pbComp f g := leftDerivedUpperStarComp Λ f g
  pbComp_assoc f g h K := leftDerivedUpperStarComp_assoc_app Λ f g h K
  pbId_comp f K := leftDerivedUpperStarComp_id_left_app Λ f K
  pbComp_id f K := leftDerivedUpperStarComp_id_right_app Λ f K
  pf f := push Λ f
  adj f := derivedUpperStarLowerStarAdjunction Λ f
  sh j hj := by
    letI := hj.out
    exact extend Λ j
  shAdj j hj := by
    letI := hj.out
    exact openAdjunction Λ j }

private theorem total_sq {A B C D : Scheme.{u}}
    {t : A ⟶ B} {l : A ⟶ C} {r : B ⟶ D} {b : C ⟶ D} (sq : CommSq t l r b) :
    (totalFormalism Λ).sqIso t l r b sq.w = pullSquare Λ sq.flip := by
  simp only [ExchangeFormalism.sqIso, ExchangeFormalism.pbComp', totalFormalism,
    pullSquare, eqToIso_refl, Iso.refl_trans]

private theorem total_open {A B C D : Scheme.{u}}
    {t : A ⟶ B} {l : A ⟶ C} {r : B ⟶ D} {b : C ⟶ D}
    [IsOpenImmersion l] [IsOpenImmersion r] (sq : CommSq t l r b) :
    ((totalFormalism Λ).baseChange t l r b sq.w).natTrans = openExchange Λ sq := by
  rw [ExchangeFormalism.baseChange, total_sq Λ sq]
  exact (left_transport_mate (openAdjunction Λ r) (openAdjunction Λ l)
    (pullSquare Λ sq.flip)).symm

private theorem total_push {A B C D : Scheme.{u}}
    {t : A ⟶ B} {l : A ⟶ C} {r : B ⟶ D} {b : C ⟶ D} (sq : CommSq t l r b) :
    ((totalFormalism Λ).pfBaseChange t l r b sq.w).natTrans = pushExchange Λ sq := by
  rw [ExchangeFormalism.pfBaseChange, total_sq Λ sq]
  have h : (pullSquare Λ sq.flip).inv = (pullSquare Λ sq).hom := by
    simp only [pullSquare, Iso.trans_inv, Iso.symm_inv, Iso.trans_hom, Iso.symm_hom,
      eqToIso.inv, eqToIso.hom, Category.assoc]
  rw [h]
  exact (right_transport_mate (derivedUpperStarLowerStarAdjunction Λ r)
    (derivedUpperStarLowerStarAdjunction Λ l) (pullSquare Λ sq)).symm

private theorem total_comp {A B C : Scheme.{u}}
    (f : A ⟶ B) (g : B ⟶ C) (h : A ⟶ C) (hh : f ≫ g = h) :
    (totalFormalism Λ).pfComp' f g h hh =
      (pushComp Λ f g ≪≫ eqToIso (congrArg (fun a ↦ push Λ a) hh)).symm := by
  subst h
  simp only [ExchangeFormalism.pfComp', ExchangeFormalism.pbComp'_rfl,
    totalFormalism, pushComp, eqToIso_refl, Iso.trans_refl]
  rfl

private theorem total_open_unit {A B : Scheme.{u}} (j : A ⟶ B) [IsOpenImmersion j] :
    IsIso (openAdjunction Λ j).unit := by
  have : IsIso (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j).unit :=
    refinementOpenUnit_isIso Λ j
  simp only [openAdjunction, Adjunction.ofNatIsoRight_unit]
  infer_instance

private theorem total_cartesian_open {A B C D : Scheme.{u}}
    {t : A ⟶ B} {l : A ⟶ C} {r : B ⟶ D} {b : C ⟶ D}
    [IsOpenImmersion l] [IsOpenImmersion r] (sq : IsPullback t l r b) :
    IsIso (openExchange Λ sq.toCommSq) := by
  let := total_open_unit Λ r
  have hc (K : Ambient Λ B) : IsIso ((openAdjunction Λ l).counit.app
      ((pull Λ b).obj ((extend Λ r).obj K))) := by
    let e := (leftDerivedUpperStarIsoMapDerivedCategory Λ b).app
        ((extend Λ r).obj K) ≪≫
      (Functor.mapDerivedCategoryCompIso (openImmersionLowerShriek Λ r)
        (upperStar Λ b)).symm.app K
    have hc := cartesianDerivedCounit Λ sq K
    have ht : IsIso
        ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ l).counit.app
          ((pull Λ b).obj ((extend Λ r).obj K))) :=
      (NatTrans.isIso_app_iff_of_iso _ e).mpr hc
    simp only [openAdjunction, Adjunction.ofNatIsoRight_counit, NatTrans.comp_app,
      Functor.whiskerRight_app]
    infer_instance
  have : IsIso (Functor.whiskerLeft (extend Λ r ⋙ pull Λ b)
      (openAdjunction Λ l).counit) := by
    rw [NatTrans.isIso_iff_isIso_app]
    exact hc
  unfold openExchange
  infer_instance

private theorem total_has_baseChange : (totalFormalism Λ).HasBaseChange where
  isIso_baseChange sq := by
    rw [total_open Λ sq.toCommSq]
    exact total_cartesian_open Λ sq

private theorem exchangeLeft_unit
    {A C D : Type*} [Category A] [Category C] [Category D]
    {Jd : A ⥤ D} {Pd : D ⥤ A} {Jc : A ⥤ C} {Pc : C ⥤ A}
    {L : D ⥤ C} (ad : Jd ⊣ Pd) (ac : Jc ⊣ Pc) (q : Pd ≅ L ⋙ Pc) (K : A) :
    ad.unit.app K ≫ q.hom.app (Jd.obj K) =
      ac.unit.app K ≫ Pc.map (((Functor.leftUnitor _).inv ≫
        Adjunction.exchangeLeft ad ac (Functor.rightUnitor _ ≪≫ q)).app K) := by
  simpa using (Adjunction.unit_app_comp_map_exchangeLeft_app ad ac
    (Functor.rightUnitor _ ≪≫ q) K).symm

private theorem formalism_refinement (F : CompactSupportFormalism) [F.HasBaseChange]
    {X Y : Scheme} {f : X ⟶ Y} {c d : Compactification f}
    (r : c.Refinement d) (hr : IsPullback c.i (𝟙 X) r.hom d.i)
    [IsIso (F.shAdj d.i).unit] [IsIso (F.shAdj c.i).unit]
    (K : F.obj X)
    (e : (F.sh d.i).obj K ≅ (F.pf r.hom).obj ((F.sh c.i).obj K))
    (he : (F.shAdj d.i).homEquiv _ _ e.hom ≫
      ((F.pbComp' c.i r.hom d.i r.i_hom).hom.app _ ≫
        (F.pb c.i).map ((F.adj r.hom).counit.app _)) = (F.shAdj c.i).unit.app K) :
    (F.refinementComparison r hr).app K =
      (F.pf d.g).map e.hom ≫ (F.pfComp' r.hom d.g c.g r.hom_g).inv.app _ := by
  let q := F.pbComp' c.i r.hom d.i r.i_hom
  let β : F.sh c.i ⟶ F.sh d.i ⋙ F.pb r.hom :=
    (Functor.leftUnitor _).inv ≫ Adjunction.exchangeLeft
      (F.shAdj d.i) (F.shAdj c.i) (Functor.rightUnitor _ ≪≫ q)
  have hb : (F.baseChange (𝟙 X) c.i d.i r.hom hr.flip.w).natTrans =
      Functor.whiskerRight (F.pbId X).hom (F.sh c.i) ≫
        (Functor.leftUnitor _).hom ≫ β := by
    simpa only [β, q, Category.assoc, Iso.hom_inv_id_assoc] using
      F.baseChange_id_eq_exchangeLeft c.i d.i r.hom hr.flip.w r.i_hom
  have hi : IsIso (F.baseChange (𝟙 X) c.i d.i r.hom hr.flip.w).natTrans :=
    CompactSupportFormalism.HasBaseChange.isIso_baseChange (F := F) hr.flip
  have hi' : IsIso (Functor.whiskerRight (F.pbId X).hom (F.sh c.i) ≫
      (Functor.leftUnitor _).hom ≫ β) := by rw [← hb]; infer_instance
  have : IsIso ((Functor.leftUnitor (F.sh c.i)).hom ≫ β) :=
    IsIso.of_isIso_comp_left (Functor.whiskerRight (F.pbId X).hom (F.sh c.i)) _
  have : IsIso β := IsIso.of_isIso_comp_left (Functor.leftUnitor (F.sh c.i)).hom β
  have heq := normalized_arrow (F.shAdj d.i) (F.shAdj c.i) (F.adj r.hom) q β
    (exchangeLeft_unit (F.shAdj d.i) (F.shAdj c.i) q) K e he
  rw [CompactSupportFormalism.refinementComparison,
    ExchangeFormalism.refinementComparison_eq_of_baseChange _ c.i c.g d.i d.g r.hom
      hr.flip.w r.hom_g (asIso β) hb]
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    asIso_inv, NatIso.isIso_inv_app, Functor.comp_map, Functor.comp_obj]
  rw [Adjunction.homEquiv_unit] at heq
  simpa only [Functor.map_comp, Category.assoc] using
    congrArg (fun a ↦ (F.pf d.g).map a ≫
      (F.pfComp' r.hom d.g c.g r.hom_g).inv.app ((F.sh c.i).obj K)) heq.symm

private theorem formalism_baseChange (F : CompactSupportFormalism)
    [F.HasBaseChange]
    {X Y X' Y' : Scheme}
    {f : X ⟶ Y} {v : Y' ⟶ Y} {f' : X' ⟶ Y'} {u' : X' ⟶ X}
    (sq : IsPullback u' f' f v) (c : Compactification f)
    (b : F.pf c.g ⋙ F.pb v ⟶
      F.pb (pullback.fst c.g v) ⋙ F.pf (c.ofIsPullback sq).g)
    (o : F.pb u' ⋙ F.sh (c.ofIsPullback sq).i ⟶
      F.sh c.i ⋙ F.pb (pullback.fst c.g v)) [IsIso o]
    (D : Functor.CompactSupportExchangeData (F.sh c.i) (F.pf c.g) (F.pb v)
      (F.pb (pullback.fst c.g v)) (F.pf (c.ofIsPullback sq).g) (F.pb u')
      (F.sh (c.ofIsPullback sq).i) b (asIso o).symm)
    (hb : (F.pfBaseChange (pullback.fst c.g v) (c.ofIsPullback sq).g c.g v
      (c.isPullback_g_ofIsPullback sq).flip.w).natTrans = b)
    (ho : (F.baseChange u' (c.ofIsPullback sq).i c.i (pullback.fst c.g v)
      (c.isPullback_i_ofIsPullback sq).w).natTrans = o) :
    (F.shriekBaseChange c (c.ofIsPullback sq) (pullback.fst c.g v)
      (c.isPullback_i_ofIsPullback sq) (c.isPullback_g_ofIsPullback sq).flip).natTrans =
      D.map := by
  have : IsIso (F.baseChange u' (c.ofIsPullback sq).i c.i (pullback.fst c.g v)
      (c.isPullback_i_ofIsPullback sq).w).natTrans :=
    CompactSupportFormalism.HasBaseChange.isIso_baseChange (F := F)
      (c.isPullback_i_ofIsPullback sq)
  ext K
  rw [CompactSupportFormalism.shriekBaseChange,
    ExchangeFormalism.shriekBaseChange_app]
  have hp := congr_app hb ((F.sh c.i).obj K)
  have hi := IsIso.inv_eq_inv.mpr (congr_app ho K)
  have hc := congrArg₂ (fun a z ↦ a ≫ (F.pf (c.ofIsPullback sq).g).map z) hp hi
  refine hc.trans ?_
  simpa only [Iso.symm_hom, asIso_inv, NatIso.isIso_inv_app] using
    (D.component K).symm

private theorem invert_refinement_square
    {A B : Type*} [Category A] [Category B] (V : A ⥤ B)
    {a b : A} {a' b' : B} (e : a ≅ b) (e' : a' ≅ b')
    (c : V.obj a ⟶ a') (d : V.obj b ⟶ b')
    (h : V.map e.inv ≫ c = d ≫ e'.inv) :
    V.map e.hom ≫ d = c ≫ e'.hom := by
  apply (cancel_epi (V.map e.inv)).mp
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
    Category.id_comp]
  rw [reassoc_of% h, Iso.inv_hom_id, Category.comp_id]

private theorem total_pbComp {A B C : Scheme.{u}}
    (f : A ⟶ B) (g : B ⟶ C) (h : A ⟶ C) (hh : f ≫ g = h) :
    (totalFormalism Λ).pbComp' f g h hh =
      eqToIso (congrArg (fun a ↦ pull Λ a) hh.symm) ≪≫
        leftDerivedUpperStarComp Λ f g := by
  rfl

private theorem total_restriction {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d) (K : Ambient Λ X) :
    ((totalFormalism Λ).pbComp' c.i r.hom d.i r.i_hom).hom.app
        ((push Λ r.hom).obj ((extend Λ c.i).obj K)) ≫
      ((totalFormalism Λ).pb c.i).map
        (((totalFormalism Λ).adj r.hom).counit.app ((extend Λ c.i).obj K)) =
      refinementRestriction Λ r K := by
  exact congrArg
    (fun q : pull Λ d.i ≅ pull Λ r.hom ⋙ pull Λ c.i ↦
      q.hom.app ((push Λ r.hom).obj ((extend Λ c.i).obj K)) ≫
        (pull Λ c.i).map
          ((derivedUpperStarLowerStarAdjunction Λ r.hom).counit.app
            ((extend Λ c.i).obj K)))
    (total_pbComp Λ c.i r.hom d.i r.i_hom)

private theorem total_normalization {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d) (K : Ambient Λ X)
    (e : native_refinement_iso Λ r K)
    (he : native_normalization Λ r K e) :
    ((totalFormalism Λ).shAdj d.i).homEquiv _ _ e.hom ≫
      (((totalFormalism Λ).pbComp' c.i r.hom d.i r.i_hom).hom.app _ ≫
        ((totalFormalism Λ).pb c.i).map
          (((totalFormalism Λ).adj r.hom).counit.app _)) =
      ((totalFormalism Λ).shAdj c.i).unit.app K := by
  exact (congrArg
    (fun q ↦ (openAdjunction Λ d.i).homEquiv _ _ e.hom ≫ q)
    (total_restriction Λ r K)).trans he

private def total_data {X Y X' Y' : Scheme.{u}}
    {f : X ⟶ Y} {v : Y' ⟶ Y} {f' : X' ⟶ Y'} {u' : X' ⟶ X}
    (c : Compactification f) (sq : IsPullback u' f' f v)
    (ho : native_open_isIso Λ c sq) :
    letI := ho
    Functor.CompactSupportExchangeData
      ((totalFormalism Λ).sh c.i) ((totalFormalism Λ).pf c.g)
      ((totalFormalism Λ).pb v) ((totalFormalism Λ).pb (pullback.fst c.g v))
      ((totalFormalism Λ).pf (c.ofIsPullback sq).g) ((totalFormalism Λ).pb u')
      ((totalFormalism Λ).sh (c.ofIsPullback sq).i)
      (pushExchange Λ (c.isPullback_g_ofIsPullback sq).flip.toCommSq)
      (asIso (openExchange Λ (c.isPullback_i_ofIsPullback sq).toCommSq)).symm := by
  let := ho
  exact baseChangeData Λ c sq ho

private theorem total_data_map {X Y X' Y' : Scheme.{u}}
    {f : X ⟶ Y} {v : Y' ⟶ Y} {f' : X' ⟶ Y'} {u' : X' ⟶ X}
    (c : Compactification f) (sq : IsPullback u' f' f v)
    (ho : native_open_isIso Λ c sq) :
    (total_data Λ c sq ho).map = baseChange Λ c sq ho := by
  rfl

private theorem formalism_open_isIso (F : CompactSupportFormalism) [F.HasBaseChange]
    {X Y X' Y' : Scheme}
    {f : X ⟶ Y} {v : Y' ⟶ Y} {f' : X' ⟶ Y'} {u' : X' ⟶ X}
    (sq : IsPullback u' f' f v) (c : Compactification f) :
    IsIso (F.baseChange u' (c.ofIsPullback sq).i c.i (pullback.fst c.g v)
      (c.isPullback_i_ofIsPullback sq).w).natTrans :=
  CompactSupportFormalism.HasBaseChange.isIso_baseChange
    (F := F) (c.isPullback_i_ofIsPullback sq)

private def formalism_data (F : CompactSupportFormalism) [F.HasBaseChange]
    {X Y X' Y' : Scheme}
    {f : X ⟶ Y} {v : Y' ⟶ Y} {f' : X' ⟶ Y'} {u' : X' ⟶ X}
    (sq : IsPullback u' f' f v) (c : Compactification f) :
    letI := formalism_open_isIso F sq c
    Functor.CompactSupportExchangeData (F.sh c.i) (F.pf c.g) (F.pb v)
      (F.pb (pullback.fst c.g v)) (F.pf (c.ofIsPullback sq).g) (F.pb u')
      (F.sh (c.ofIsPullback sq).i)
      (F.pfBaseChange (pullback.fst c.g v) (c.ofIsPullback sq).g c.g v
        (c.isPullback_g_ofIsPullback sq).flip.w).natTrans
      (asIso (F.baseChange u' (c.ofIsPullback sq).i c.i (pullback.fst c.g v)
        (c.isPullback_i_ofIsPullback sq).w).natTrans).symm := by
  let := formalism_open_isIso F sq c
  exact Functor.compactSupportExchangeData (F.sh c.i) (F.pf c.g) (F.pb v)
    (F.pb (pullback.fst c.g v)) (F.pf (c.ofIsPullback sq).g) (F.pb u')
    (F.sh (c.ofIsPullback sq).i)
    (F.pfBaseChange (pullback.fst c.g v) (c.ofIsPullback sq).g c.g v
      (c.isPullback_g_ofIsPullback sq).flip.w).natTrans
    (asIso (F.baseChange u' (c.ofIsPullback sq).i c.i (pullback.fst c.g v)
      (c.isPullback_i_ofIsPullback sq).w).natTrans).symm

private theorem formalism_data_eq (F : CompactSupportFormalism) [F.HasBaseChange]
    {X Y X' Y' : Scheme}
    {f : X ⟶ Y} {v : Y' ⟶ Y} {f' : X' ⟶ Y'} {u' : X' ⟶ X}
    (sq : IsPullback u' f' f v) (c : Compactification f)
    (bc : F.pf c.g ⋙ F.pb v ⟶
      F.pb (pullback.fst c.g v) ⋙ F.pf (c.ofIsPullback sq).g)
    (oc : F.pb u' ⋙ F.sh (c.ofIsPullback sq).i ⟶
      F.sh c.i ⋙ F.pb (pullback.fst c.g v)) [IsIso oc]
    (D : Functor.CompactSupportExchangeData (F.sh c.i) (F.pf c.g) (F.pb v)
      (F.pb (pullback.fst c.g v)) (F.pf (c.ofIsPullback sq).g) (F.pb u')
      (F.sh (c.ofIsPullback sq).i) bc (asIso oc).symm)
    (hp : (F.pfBaseChange (pullback.fst c.g v) (c.ofIsPullback sq).g c.g v
      (c.isPullback_g_ofIsPullback sq).flip.w).natTrans = bc)
    (ho : (F.baseChange u' (c.ofIsPullback sq).i c.i (pullback.fst c.g v)
      (c.isPullback_i_ofIsPullback sq).w).natTrans = oc) :
    (formalism_data F sq c).map = D.map := by
  let := formalism_open_isIso F sq c
  exact (formalism_baseChange F sq c
    (F.pfBaseChange (pullback.fst c.g v) (c.ofIsPullback sq).g c.g v
      (c.isPullback_g_ofIsPullback sq).flip.w).natTrans
    (F.baseChange u' (c.ofIsPullback sq).i c.i (pullback.fst c.g v)
      (c.isPullback_i_ofIsPullback sq).w).natTrans
    (formalism_data F sq c) rfl rfl).symm.trans
    (formalism_baseChange F sq c bc oc D hp ho)

private theorem total_formalism_unit {X Z : Scheme.{u}}
    (j : X ⟶ Z) [IsOpenImmersion j] :
    IsIso ((totalFormalism Λ).shAdj j).unit := by
  exact total_open_unit Λ j

private def total_iso {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d) (K : Ambient Λ X)
    (e : native_refinement_iso Λ r K) :
    ((totalFormalism Λ).sh d.i).obj K ≅
      ((totalFormalism Λ).pf r.hom).obj (((totalFormalism Λ).sh c.i).obj K) := e

private theorem total_iso_hom {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d) (K : Ambient Λ X)
    (e : native_refinement_iso Λ r K) :
    (total_iso Λ r K e).hom = e.hom := by rfl

private theorem image_representation_heq {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) :
    HEq (image Λ c) (extend Λ c.i ⋙ push Λ c.g) := by rfl

-- Build explicit congruences before substituting the concrete derived categories.
-- Each auxiliary equality is checked by the kernel when it is introduced.

private meta def representationOfEq (h : Lean.Expr) : Lean.MetaM Lean.Expr := do
  let ty ← Lean.Meta.inferType h
  unless ty.isEq do throwError "expected equality"
  return Lean.mkAppN (Lean.mkConst ``heq_of_eq ty.getAppFn.constLevels!)
    (ty.getAppArgs.push h)

private meta def representationSymm (h : Lean.Expr) : Lean.MetaM Lean.Expr := do
  let ty ← Lean.Meta.inferType h
  let some (α, a, β, b) := ty.heq? | throwError "expected HEq"
  return Lean.mkAppN (Lean.mkConst ``HEq.symm ty.getAppFn.constLevels!) #[α, β, a, b, h]

private meta def representationTrans (h k : Lean.Expr) : Lean.MetaM Lean.Expr := do
  let ty ← Lean.Meta.inferType h
  let some (α, a, β, b) := ty.heq? | throwError "expected HEq"
  let some (_, _, γ, c) := (← Lean.Meta.inferType k).heq? | throwError "expected HEq"
  return Lean.mkAppN (Lean.mkConst ``HEq.trans ty.getAppFn.constLevels!)
    #[α, β, γ, a, b, c, h, k]

private meta def representationToEq (h : Lean.Expr) : Lean.MetaM Lean.Expr := do
  let ty ← Lean.Meta.inferType h
  let some (α, a, _, b) := ty.heq? | throwError "expected HEq"
  return Lean.mkAppN (Lean.mkConst ``eq_of_heq ty.getAppFn.constLevels!) #[α, a, b, h]

private meta def representationCheck (a b : Lean.Expr) : Lean.MetaM Lean.Expr := do
  let α ← Lean.Meta.inferType a
  let level ← Lean.Meta.getLevel α
  let ty := Lean.mkApp3 (Lean.mkConst ``Eq [level]) α a b
  let value := Lean.mkApp2 (Lean.mkConst ``Eq.refl [level]) α a
  let h ← try
    Lean.Meta.mkAuxTheorem ty value
      (zetaDelta := true) (kind? := `_representationReduction)
    catch ex =>
      throwError "Representation equality failed: {ex.toMessageData}"
  representationOfEq h

private meta def representationLetValue : Nat → Lean.Expr → Lean.MetaM Lean.Expr
  | 0, e => pure e
  | n + 1, e => do
    if e.getAppFn.isFVar then
      let decl ← Lean.Meta.getFVarLocalDecl e.getAppFn
      if let some value := decl.value? then
        return ← representationLetValue n (Lean.mkAppN value e.getAppArgs).headBeta
    return e

private meta def representationReduction (e : Lean.Expr) :
    Lean.MetaM (Option Lean.Expr) := do
  if let .letE _ _ v body _ := e then return some (body.instantiate1 v)
  if e.headBeta != e then return some e.headBeta
  if let some e' ← e.reduceProjStruct? then return some e'
  if e.isAppOf ``total_iso || e.isAppOf ``totalCategory || e.isAppOf ``Ambient ||
      e.isAppOf ``pull ||
      e.isAppOf ``push || e.isAppOf ``extend ||
      e.isAppOf ``CompactSupportFormalism.shriek || e.isAppOf ``ExchangeFormalism.shriek then
    return ← Lean.Meta.unfoldDefinition? e
  if e.getAppFn.isConst then
    if let some info ← Lean.getProjectionFnInfo? e.getAppFn.constName! then
      let es := e.getAppArgs
      if es.size > info.numParams then
        let major ← representationLetValue 32 es[info.numParams]!
        if major.isAppOf ``totalFormalism || major.isAppOf ``total_iso then
          if let some value ← Lean.Meta.unfoldDefinition? major then
            if value.getAppFn.isConstOf info.ctorName then
              let field := value.getAppArgs[info.numParams + info.i]!
              return some (Lean.mkAppN field (es.extract (info.numParams + 1) es.size)).headBeta
  return none

private meta def representationKnownReduction (e other : Lean.Expr) :
    Lean.MetaM (Option (Lean.Expr × Lean.Expr)) := do
  if e.isAppOf ``image then
    let es := e.getAppArgs
    let h ← Lean.Meta.mkAppM ``image_representation_heq #[es[0]!, es.back!]
    let some (_, _, _, b) := (← Lean.Meta.inferType h).heq? |
      throwError "expected image representation"
    return some (b, h)
  if e.isAppOf ``Iso.hom && other.isAppOf ``Iso.hom then
    let a ← representationLetValue 32 e.appArg!
    let b ← representationLetValue 32 other.appArg!
    if a == b then return none
  if e.isAppOf ``Iso.hom && e.appArg!.isAppOf ``total_iso then
    let value := e.appArg!
    let h := Lean.mkAppN (Lean.mkConst ``total_iso_hom value.getAppFn.constLevels!)
      value.getAppArgs
    let ty ← Lean.Meta.inferType h
    return some (ty.getAppArgs.back!, ← representationOfEq h)
  return none

private meta def representationCongruence : Nat →
    IO.Ref (Std.HashMap (Lean.Expr × Lean.Expr) Lean.Expr) →
    IO.Ref (Std.HashMap (Lean.Expr × Nat) Lean.Meta.CongrTheorem) →
    Lean.Expr → Lean.Expr → Lean.MetaM Lean.Expr
  | 0, _, _, _, _ => throwError "representation congruence exceeded its depth bound"
  | fuel + 1, cache, congrCache, a, b => do
    let a ← representationLetValue 32 a.consumeMData
    let b ← representationLetValue 32 b.consumeMData
    if a == b then return ← Lean.Meta.mkHEqRefl a
    if let some h := (← cache.get).get? (a, b) then return h
    let compute : Lean.MetaM Lean.Expr := do
      for ((sa, sb), sh) in (← cache.get).toArray do
        if sb == b && sa.getAppFn == a.getAppFn && sh.getAppFn.isConst &&
            (match sh.getAppFn.constName! with
              | .str _ n => n.startsWith "_nativeArrowComparison"
              | _ => false) then
          let localCache ← IO.mkRef {}
          let h ← representationCongruence fuel localCache congrCache a sa
          return ← representationTrans h sh
      if (← Lean.Meta.isProof a) && (← Lean.Meta.isProof b) then
        return ← Lean.Meta.mkAppM ``proof_irrel_heq #[a, b]
      if let some (a', h) ← representationKnownReduction a b then
        return ← representationTrans h
          (← representationCongruence fuel cache congrCache a' b)
      if let some (b', h) ← representationKnownReduction b a then
        return ← representationTrans
          (← representationCongruence fuel cache congrCache a b')
          (← representationSymm h)
      if let some a' ← representationReduction a then
        return ← representationTrans (← representationCheck a a')
          (← representationCongruence fuel cache congrCache a' b)
      if let some b' ← representationReduction b then
        return ← representationTrans
          (← representationCongruence fuel cache congrCache a b')
          (← representationSymm (← representationCheck b b'))
      if a.getAppFn == b.getAppFn && a.getAppFn.isConst && a.isApp &&
          a.getAppNumArgs == b.getAppNumArgs then
        let aa := a.getAppArgs
        let bb := b.getAppArgs
        let key := (a.getAppFn, aa.size)
        let ct ← match (← congrCache.get).get? key with
          | some ct => pure ct
          | none => do
            let ct ← Lean.Meta.withLCtx {} {} <|
              Lean.Meta.mkHCongrWithArity a.getAppFn aa.size
            let proof ← Lean.Meta.mkAuxTheorem ct.type ct.proof
              (kind? := `_representationCongruence)
            let ct := { ct with proof := proof }
            congrCache.modify fun m => m.insert key ct
            pure ct
        let mut args := #[]
        for i in [:aa.size] do
          let h ← representationCongruence fuel cache congrCache aa[i]! bb[i]!
          let h ← if ct.argKinds[i]! == .eq then representationToEq h else pure h
          args := args ++ #[aa[i]!, bb[i]!, h]
        let h := Lean.mkAppN ct.proof args
        return ← if (← Lean.Meta.inferType h).isHEq then pure h else representationOfEq h
      representationCheck a b
    let h ← compute
    let ty ← Lean.Meta.mkHEq a b
    let h ← if (← Lean.Meta.inferType h) == ty then pure h else
      Lean.Meta.mkAuxTheorem ty h (zetaDelta := true) (kind? := `_representationBridge)
    cache.modify fun m => m.insert (a, b) h
    return h

private theorem total_normalization_iso {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d) (K : Ambient Λ X)
    (e : native_refinement_iso Λ r K)
    (he : native_normalization Λ r K e) :
    ((totalFormalism Λ).shAdj d.i).homEquiv _ _ (total_iso Λ r K e).hom ≫
      (((totalFormalism Λ).pbComp' c.i r.hom d.i r.i_hom).hom.app _ ≫
        ((totalFormalism Λ).pb c.i).map
          (((totalFormalism Λ).adj r.hom).counit.app _)) =
      ((totalFormalism Λ).shAdj c.i).unit.app K := by
  let h := total_normalization Λ r K e he
  run_tac Lean.Elab.Tactic.withMainContext do
    let t ← Lean.Elab.Term.elabTerm (Lean.mkIdent `h) none
    let x ← Lean.instantiateMVars (← Lean.Meta.inferType t)
    let y ← Lean.instantiateMVars (← Lean.Elab.Tactic.getMainTarget)
    let cache ← IO.mkRef {}
    let congrCache ← IO.mkRef {}
    let eq ← representationToEq (← representationCongruence 512 cache congrCache x y)
    let result ← Lean.Meta.mkAppM ``Eq.mp #[eq, t]
    Lean.Elab.Tactic.closeMainGoal `representationCongruence result

private theorem total_canonical_data_map {X Y X' Y' : Scheme.{u}}
    {f : X ⟶ Y} {v : Y' ⟶ Y} {f' : X' ⟶ Y'} {u' : X' ⟶ X}
    (c : Compactification f) (sq : IsPullback u' f' f v)
    (ho : native_open_isIso Λ c sq) :
    letI := total_has_baseChange Λ
    (formalism_data (totalFormalism Λ) sq c).map = baseChange Λ c sq ho := by
  let := total_has_baseChange Λ
  let := ho
  exact (formalism_data_eq (totalFormalism Λ) sq c
    (pushExchange Λ (c.isPullback_g_ofIsPullback sq).flip.toCommSq)
    (openExchange Λ (c.isPullback_i_ofIsPullback sq).toCommSq)
    (total_data Λ c sq ho)
    (total_push Λ (c.isPullback_g_ofIsPullback sq).flip.toCommSq)
    (total_open Λ (c.isPullback_i_ofIsPullback sq).toCommSq)).trans
      (total_data_map Λ c sq ho)

private theorem total_canonical_refinement {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d) (K : Ambient Λ X)
    (e : native_refinement_iso Λ r K) :
    ((((totalFormalism Λ).pfComp' r.hom d.g c.g r.hom_g).app
      (((totalFormalism Λ).sh c.i).obj K) ≪≫
        ((totalFormalism Λ).pf d.g).mapIso (total_iso Λ r K e).symm).hom) =
      (refinementIso Λ r K e).hom := by
  dsimp only [total_iso]
  exact congrArg
    (fun q : push Λ c.g ≅ push Λ r.hom ⋙ push Λ d.g ↦
      (q.app ((extend Λ c.i).obj K) ≪≫ (push Λ d.g).mapIso e.symm).hom)
    (total_comp Λ r.hom d.g c.g r.hom_g)

private theorem formalism_refinement_inv (F : CompactSupportFormalism) [F.HasBaseChange]
    {X Y : Scheme} {f : X ⟶ Y} {c d : Compactification f}
    (r : c.Refinement d) (hr : IsPullback c.i (𝟙 X) r.hom d.i)
    [IsIso (F.shAdj d.i).unit] [IsIso (F.shAdj c.i).unit]
    (K : F.obj X)
    (e : (F.sh d.i).obj K ≅ (F.pf r.hom).obj ((F.sh c.i).obj K))
    (he : (F.shAdj d.i).homEquiv _ _ e.hom ≫
      ((F.pbComp' c.i r.hom d.i r.i_hom).hom.app _ ≫
        (F.pb c.i).map ((F.adj r.hom).counit.app _)) = (F.shAdj c.i).unit.app K) :
    (F.refinementComparison r hr).app K =
      (((F.pfComp' r.hom d.g c.g r.hom_g).app ((F.sh c.i).obj K) ≪≫
        (F.pf d.g).mapIso e.symm).inv) := by
  simpa only [Iso.trans_inv, Functor.mapIso_inv, Iso.symm_inv, Iso.app_inv] using
    formalism_refinement F r hr K e he

private theorem total_F_refinement {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d)
    (hr : IsPullback c.i (𝟙 X) r.hom d.i) (K : Ambient Λ X)
    (e : native_refinement_iso Λ r K) (he : native_normalization Λ r K e) :
    letI := total_has_baseChange Λ
    ((totalFormalism Λ).refinementComparison r hr).app K =
      ((((totalFormalism Λ).pfComp' r.hom d.g c.g r.hom_g).app
        (((totalFormalism Λ).sh c.i).obj K) ≪≫
          ((totalFormalism Λ).pf d.g).mapIso (total_iso Λ r K e).symm).inv) := by
  let hbc := total_has_baseChange Λ
  let huc := total_formalism_unit Λ c.i
  let hud := total_formalism_unit Λ d.i
  with_reducible_and_instances
    exact formalism_refinement_inv (totalFormalism Λ) r hr K (total_iso Λ r K e)
      (total_normalization_iso Λ r K e he)

private theorem formalism_baseChange_canonical (F : CompactSupportFormalism)
    [F.HasBaseChange] {X Y X' Y' : Scheme}
    {f : X ⟶ Y} {v : Y' ⟶ Y} {f' : X' ⟶ Y'} {u' : X' ⟶ X}
    (sq : IsPullback u' f' f v) (c : Compactification f) :
    (F.shriekBaseChange c (c.ofIsPullback sq) (pullback.fst c.g v)
      (c.isPullback_i_ofIsPullback sq) (c.isPullback_g_ofIsPullback sq).flip).natTrans =
        (formalism_data F sq c).map := by
  let := formalism_open_isIso F sq c
  exact formalism_baseChange F sq c
    (F.pfBaseChange (pullback.fst c.g v) (c.ofIsPullback sq).g c.g v
      (c.isPullback_g_ofIsPullback sq).flip.w).natTrans
    (F.baseChange u' (c.ofIsPullback sq).i c.i (pullback.fst c.g v)
      (c.isPullback_i_ofIsPullback sq).w).natTrans
    (formalism_data F sq c) rfl rfl

private theorem formalism_raw_boundary (F : CompactSupportFormalism) [F.HasBaseChange]
    {X Y X' Y' : Scheme}
    {f : X ⟶ Y} {v : Y' ⟶ Y} {f' : X' ⟶ Y'} {u' : X' ⟶ X}
    (sq : IsPullback u' f' f v) (c d : Compactification f)
    (r : c.Refinement d) (hr : IsPullback c.i (𝟙 X) r.hom d.i) (K : F.obj X) :
    (F.pb v).map ((F.refinementComparison r hr).app K) ≫
        (formalism_data F sq c).map.app K =
      (formalism_data F sq d).map.app K ≫
        (F.refinementComparison (r.ofIsPullback sq)
          (r.isPullback_ofIsPullback sq hr)).app ((F.pb u').obj K) := by
  have h := congr_app (F.shriekBaseChange_refinementComparison
    r hr (r.ofIsPullback sq) (r.isPullback_ofIsPullback sq hr) (pullback.fst c.g v)
    (c.isPullback_i_ofIsPullback sq) (c.isPullback_g_ofIsPullback sq).flip
    (pullback.fst d.g v) (d.isPullback_i_ofIsPullback sq)
    (d.isPullback_g_ofIsPullback sq).flip (r.ofIsPullback_hom_fst sq).symm) K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    TwoSquare.natTrans] at h
  rw [congr_app (formalism_baseChange_canonical F sq c) K,
    congr_app (formalism_baseChange_canonical F sq d) K] at h
  exact h

private theorem total_native_refinement_checked {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d)
    (hr : IsPullback c.i (𝟙 X) r.hom d.i) (K : Ambient Λ X)
    (e : native_refinement_iso Λ r K) (he : native_normalization Λ r K e) :
    letI := total_has_baseChange Λ
    ((totalFormalism Λ).refinementComparison r hr).app K =
      (refinementIso Λ r K e).inv := by
  let hbc := total_has_baseChange Λ
  exact (total_F_refinement Λ r hr K e he).trans
    ((Iso.inv_eq_inv _ _).mpr (total_canonical_refinement Λ r K e))

private theorem total_native_refinement_heq {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d)
    (hr : IsPullback c.i (𝟙 X) r.hom d.i) (K : Ambient Λ X)
    (e : native_refinement_iso Λ r K) (he : native_normalization Λ r K e) :
    letI := total_has_baseChange Λ
    HEq (((totalFormalism Λ).refinementComparison r hr).app K)
      (refinementIso Λ r K e).inv := by
  let hbc := total_has_baseChange Λ
  exact heq_of_eq (total_native_refinement_checked Λ r hr K e he)

private theorem total_native_data_heq {X Y X' Y' : Scheme.{u}}
    {f : X ⟶ Y} {v : Y' ⟶ Y} {f' : X' ⟶ Y'} {u' : X' ⟶ X}
    (c : Compactification f) (sq : IsPullback u' f' f v)
    (ho : native_open_isIso Λ c sq) (K : Ambient Λ X) :
    letI := total_has_baseChange Λ
    HEq ((formalism_data (totalFormalism Λ) sq c).map.app K)
      ((baseChange Λ c sq ho).app K) := by
  let hbc := total_has_baseChange Λ
  exact heq_of_eq (congr_app (total_canonical_data_map Λ c sq ho) K)

private theorem native_raw_pasting
    {X Y X' Y' : Scheme.{u}}
    {f : X ⟶ Y} {v : Y' ⟶ Y} {f' : X' ⟶ Y'} {u' : X' ⟶ X}
    (sq : IsPullback u' f' f v) (c d : Compactification f)
    (r : c.Refinement d) (hr : r.hom ⁻¹ᵁ d.i.opensRange = c.i.opensRange)
    (ho : IsIso (openExchange Λ (c.isPullback_i_ofIsPullback sq).toCommSq))
    (hd : IsIso (openExchange Λ (d.isPullback_i_ofIsPullback sq).toCommSq))
    (K : Ambient Λ X)
    (e : (extend Λ d.i).obj K ≅ (push Λ r.hom).obj ((extend Λ c.i).obj K))
    (he : (openAdjunction Λ d.i).homEquiv _ _ e.hom ≫
      refinementRestriction Λ r K = (openAdjunction Λ c.i).unit.app K)
    (e' : (extend Λ (d.ofIsPullback sq).i).obj ((pull Λ u').obj K) ≅
      (push Λ (r.ofIsPullback sq).hom).obj
        ((extend Λ (c.ofIsPullback sq).i).obj ((pull Λ u').obj K)))
    (he' : (openAdjunction Λ (d.ofIsPullback sq).i).homEquiv _ _ e'.hom ≫
      refinementRestriction Λ (r.ofIsPullback sq) ((pull Λ u').obj K) =
        (openAdjunction Λ (c.ofIsPullback sq).i).unit.app ((pull Λ u').obj K)) :
    (pull Λ v).map (refinementIso Λ r K e).inv ≫ (baseChange Λ c sq ho).app K =
      (baseChange Λ d sq hd).app K ≫
        (refinementIso Λ (r.ofIsPullback sq) ((pull Λ u').obj K) e').inv := by
  let F := totalFormalism Λ
  let (T : Scheme.{u}) : Category (F.obj T) := F.category T
  let hbc := total_has_baseChange Λ
  have hrc : IsPullback c.i (𝟙 X) r.hom d.i :=
    (IsOpenImmersion.isPullback (𝟙 X) c.i d.i r.hom
      (by simpa only [Category.id_comp] using r.i_hom) hr).flip
  let h := formalism_raw_boundary F sq c d r hrc K
  let ha := total_native_refinement_heq Λ r hrc K e he
  let hb := total_native_data_heq Λ c sq ho K
  let hc := total_native_data_heq Λ d sq hd K
  let hd' := total_native_refinement_heq Λ (r.ofIsPullback sq)
    (r.isPullback_ofIsPullback sq hrc) ((pull Λ u').obj K) e' he'
  run_tac Lean.Elab.Tactic.withMainContext do
    let cache ← IO.mkRef {}
    let congrCache ← IO.mkRef {}
    let bindings ← #[`hbc, `F].mapM fun name => do
      let f ← Lean.Elab.Term.elabTerm (Lean.mkIdent name) none
      let decl ← Lean.Meta.getFVarLocalDecl f
      return (f, decl.value?.getD f)
    let zeta (t : Lean.Expr) : Lean.Expr :=
      bindings.foldl (fun t (f, v) ↦ t.replaceFVar f v) t
    for name in #[`ha, `hb, `hc, `hd'] do
      let t ← Lean.Elab.Term.elabTerm (Lean.mkIdent name) none
      let ty ← Lean.Meta.withReducibleAndInstances <| Lean.Meta.whnf
        (zeta (← Lean.instantiateMVars (← Lean.Meta.inferType t)))
      let some (_, a, _, b) := ty.heq? | throwError "expected arrow comparison"
      let t ← Lean.Meta.mkAuxTheorem ty t (zetaDelta := true)
        (kind? := `_nativeArrowComparison)
      cache.modify fun m => m.insert (a, b) t
      let ts ← representationSymm t
      cache.modify fun m => m.insert (b, a) ts
    let t ← Lean.Elab.Term.elabTerm (Lean.mkIdent `h) none
    let actual := zeta (← Lean.instantiateMVars (← Lean.Meta.inferType t))
    let target := zeta (← Lean.instantiateMVars (← Lean.Elab.Tactic.getMainTarget))
    let eq ← representationToEq
      (← representationCongruence 512 cache congrCache actual target)
    let t ← Lean.Meta.mkAuxTheorem actual t (zetaDelta := true)
      (kind? := `_nativeRawPasting)
    let level ← Lean.Meta.getLevel actual
    let result := Lean.mkAppN (Lean.mkConst ``Eq.mp [level]) #[actual, target, eq, t]
    let result ← Lean.Meta.mkAuxTheorem target result (zetaDelta := true)
      (kind? := `_nativePastingTransport)
    Lean.Elab.Tactic.closeMainGoal `representationCongruence result

/-- Pasting the specified compact-support mate with one normalized boundary refinement.

Source: blueprint det-sf-comp-composition-base-change, proof clause (3);
lem-sfb-total-derived-cartesian-compact-support, the refinement-pasting equation.
(blueprint: lem-sfb-total-derived-boundary-exchange).

Proof: the boundary equality says the square formed by the two distinguished opens,
with identity on their common source, is Cartesian. It remains Cartesian after the
supplied base change. Transpose the normalized isomorphisms e and e' under the two
open adjunctions. Their normalization equations identify these adjuncts with the open
units followed by the inverse of the proper restriction comparison. That comparison
is invertible on extension by zero: the direct-image restriction to that open is
sectionwise the identity, and exact restriction of a K-injective resolution computes
the derived restriction there. The open units are invertible since extension by zero
is fully faithful. Thus the equations uniquely determine e and e'.
The canonical pullback composition comparisons satisfy the cocycle law. Taking
mates under the proper adjunctions gives horizontal pasting, with pushComp as its
compositor. Taking mates under the open adjunctions gives the same pasting for the
inverse open exchange. Substitute the two normalization equations, apply naturality
of the proper counits, and cancel the open unit and restriction isomorphisms. The
result equates the proper exchange followed by the two open mates on both paths.
After applying the final proper pushforward, its compositors cancel those in
refinementIso, giving the displayed component identity. Only the inverse open
exchanges require invertibility; no proper-exchange invertibility, arithmetic,
localizing hypothesis, density, or comparison family is used. In particular the
argument includes zero objects, empty opens, and nondense compactifications. -/
theorem normalizedBoundaryExchange
    {X Y X' Y' : Scheme.{u}}
    {f : X ⟶ Y} {v : Y' ⟶ Y} {f' : X' ⟶ Y'} {u' : X' ⟶ X}
    (sq : IsPullback u' f' f v) (c d : Compactification f)
    (r : c.Refinement d) (hr : r.hom ⁻¹ᵁ d.i.opensRange = c.i.opensRange)
    (ho : IsIso (openExchange Λ (c.isPullback_i_ofIsPullback sq).toCommSq))
    (hd : IsIso (openExchange Λ (d.isPullback_i_ofIsPullback sq).toCommSq))
    (K : Ambient Λ X)
    (e : (extend Λ d.i).obj K ≅ (push Λ r.hom).obj ((extend Λ c.i).obj K))
    (he : (openAdjunction Λ d.i).homEquiv _ _ e.hom ≫
      refinementRestriction Λ r K = (openAdjunction Λ c.i).unit.app K)
    (e' : (extend Λ (d.ofIsPullback sq).i).obj ((pull Λ u').obj K) ≅
      (push Λ (r.ofIsPullback sq).hom).obj
        ((extend Λ (c.ofIsPullback sq).i).obj ((pull Λ u').obj K)))
    (he' : (openAdjunction Λ (d.ofIsPullback sq).i).homEquiv _ _ e'.hom ≫
      refinementRestriction Λ (r.ofIsPullback sq) ((pull Λ u').obj K) =
        (openAdjunction Λ (c.ofIsPullback sq).i).unit.app ((pull Λ u').obj K)) :
    (pull Λ v).map (refinementIso Λ r K e).hom ≫ (baseChange Λ d sq hd).app K =
      (baseChange Λ c sq ho).app K ≫
        (refinementIso Λ (r.ofIsPullback sq) ((pull Λ u').obj K) e').hom := by
  exact invert_refinement_square (pull Λ v) (refinementIso Λ r K e)
    (refinementIso Λ (r.ofIsPullback sq) ((pull Λ u').obj K) e')
    ((baseChange Λ c sq ho).app K) ((baseChange Λ d sq hd).app K)
    (native_raw_pasting Λ sq c d r hr ho hd K e he e' he')

end AlgebraicGeometry.ProEtale.CondensedRing.IntegralCompactSupport
