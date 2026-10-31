/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleCompactSupportCoefficientChange
import all WeilConjectures.SixFunctors.EtaleRestrictionBaseChange
/-! # Scalar restriction and the local triangle compositor

Source: Stacks Project, Tags 0F7J and 0GL6.
(blueprint: lem-sf-etale-restriction-triangle).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Etale
private theorem scalar_exchange_paste
    (FA FB : CompactSupportFormalism) [FA.HasBaseChange] [FB.HasBaseChange]
    {U' U Z' Z : Scheme.{u}} (t : U' ⟶ U) (l : U' ⟶ Z')
    (r : U ⟶ Z) (b : Z' ⟶ Z) [IsOpenImmersion l] [IsOpenImmersion r]
    (sq : IsPullback t l r b) (s : ∀ W : Scheme.{u}, FB.obj W ⥤ FA.obj W)
    (qt : s U ⋙ FA.pb t ≅ FB.pb t ⋙ s U')
    (pt : s U' ⋙ FA.pf t ≅ FB.pf t ⋙ s U)
    (qb : s Z ⋙ FA.pb b ≅ FB.pb b ⋙ s Z')
    (pb : s Z' ⋙ FA.pf b ≅ FB.pf b ⋙ s Z)
    (cr : s U ⋙ FA.sh r ≅ FB.sh r ⋙ s Z)
    (cl : s U' ⋙ FA.sh l ≅ FB.sh l ⋙ s Z')
    (ht : (mateEquiv (FB.adj t) (FA.adj t)
      (TwoSquare.mk _ _ _ _ qt.hom)).natTrans = pt.inv)
    (hb : (mateEquiv (FB.adj b) (FA.adj b)
      (TwoSquare.mk _ _ _ _ qb.hom)).natTrans = pb.inv)
    (hc : CoeffCompatible (pasteTwoSquaresIso qt cl) (pasteTwoSquaresIso cr qb)
      (FA.baseChange t l r b sq.w).natTrans (FB.baseChange t l r b sq.w).natTrans) :
    have := CompactSupportFormalism.HasBaseChange.isIso_baseChange (F := FA) sq
    have := CompactSupportFormalism.HasBaseChange.isIso_baseChange (F := FB) sq
    CoeffCompatible (pasteTwoSquaresIso pt cr) (pasteTwoSquaresIso cl pb)
      (FA.exchange t l r b sq.w).natTrans (FB.exchange t l r b sq.w).natTrans := by
  dsimp only
  have := CompactSupportFormalism.HasBaseChange.isIso_baseChange (F := FA) sq
  have := CompactSupportFormalism.HasBaseChange.isIso_baseChange (F := FB) sq
  have h := CoeffCompatible.inv
    (e := asIso (FA.baseChange t l r b sq.w).natTrans)
    (e' := asIso (FB.baseChange t l r b sq.w).natTrans) hc
  intro K
  simpa only [pasteTwoSquaresIso_hom_app, ExchangeFormalism.exchange,
    TwoSquare.natTrans, Category.assoc] using
    Adjunction.mateEquiv_restrict (FA.adj t) (FA.adj b) (FB.adj t) (FB.adj b)
      (inv (FA.baseChange t l r b sq.w).natTrans)
      (inv (FB.baseChange t l r b sq.w).natTrans) qt pt qb pb cr cl ht hb
      (fun N ↦ by
        simpa only [pasteTwoSquaresIso_hom_app, Functor.comp_obj,
          Category.assoc, asIso_inv] using h N) K

private theorem scalarOpenPlus_exchange
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {U' U Z' Z : Scheme.{u}} (t : U' ⟶ U) (l : U' ⟶ Z')
    (r : U ⟶ Z) (b : Z' ⟶ Z) [IsOpenImmersion l] [IsOpenImmersion r]
    (sq : IsPullback t l r b) :
    let FA := derivedPlusFormalism (ModuleCat.{u + 1} A)
    let FB := derivedPlusFormalism (ModuleCat.{u + 1} B)
    have := CompactSupportFormalism.HasBaseChange.isIso_baseChange (F := FA) sq
    have := CompactSupportFormalism.HasBaseChange.isIso_baseChange (F := FB) sq
    CoeffCompatible
      (pasteTwoSquaresIso (scalarPushforwardPlus φ t) (scalarOpenPlus φ r))
      (pasteTwoSquaresIso (scalarOpenPlus φ l) (scalarPushforwardPlus φ b))
      (FA.exchange t l r b sq.w).natTrans (FB.exchange t l r b sq.w).natTrans := by
  exact scalar_exchange_paste
    (derivedPlusFormalism (ModuleCat.{u + 1} A))
    (derivedPlusFormalism (ModuleCat.{u + 1} B)) t l r b sq
    (fun W ↦ scalarRestrictionPlus φ W)
    (scalarPullbackPlus φ t) (scalarPushforwardPlus φ t)
    (scalarPullbackPlus φ b) (scalarPushforwardPlus φ b)
    (scalarOpenPlus φ r) (scalarOpenPlus φ l)
    (congrArg TwoSquare.natTrans (scalarPushforwardPlus_mate φ t))
    (congrArg TwoSquare.natTrans (scalarPushforwardPlus_mate φ b))
    (compactSupportRestrictionPlus_openBaseChange φ t l r b sq.w)

private theorem scalar_open_comp_paste
    (FA FB : CompactSupportFormalism) {X Y Z : Scheme.{u}}
    (k : X ⟶ Y) (j : Y ⟶ Z) [IsOpenImmersion k] [IsOpenImmersion j]
    (s : ∀ W : Scheme.{u}, FB.obj W ⥤ FA.obj W)
    (ck : s X ⋙ FA.sh k ≅ FB.sh k ⋙ s Y)
    (cj : s Y ⋙ FA.sh j ≅ FB.sh j ⋙ s Z)
    (ch : s X ⋙ FA.sh (k ≫ j) ≅ FB.sh (k ≫ j) ⋙ s Z)
    (qk : s Y ⋙ FA.pb k ≅ FB.pb k ⋙ s X)
    (qj : s Z ⋙ FA.pb j ≅ FB.pb j ⋙ s Y)
    (qh : s Z ⋙ FA.pb (k ≫ j) ≅ FB.pb (k ≫ j) ⋙ s X)
    (hck : mateEquiv (FB.shAdj k) (FA.shAdj k)
      (TwoSquare.mk _ _ _ _ ck.hom) = TwoSquare.mk _ _ _ _ qk.inv)
    (hcj : mateEquiv (FB.shAdj j) (FA.shAdj j)
      (TwoSquare.mk _ _ _ _ cj.hom) = TwoSquare.mk _ _ _ _ qj.inv)
    (hch : mateEquiv (FB.shAdj (k ≫ j)) (FA.shAdj (k ≫ j))
      (TwoSquare.mk _ _ _ _ ch.hom) = TwoSquare.mk _ _ _ _ qh.inv)
    (hq : CoeffCompatible qh (pasteTwoSquaresIso qj qk)
      (FA.pbComp' k j (k ≫ j) rfl).hom (FB.pbComp' k j (k ≫ j) rfl).hom) :
    CoeffCompatible ch (pasteTwoSquaresIso ck cj)
      (FA.shComp' k j (k ≫ j) rfl).hom (FB.shComp' k j (k ≫ j) rfl).hom := by
  have hs : TwoSquare.mk _ _ _ _ ch.hom =
      (((TwoSquare.mk _ _ _ _ ck.hom).vComp
        (TwoSquare.mk _ _ _ _ cj.hom)).whiskerRight
          (FA.shComp' k j (k ≫ j) rfl).hom).whiskerLeft
            (FB.shComp' k j (k ≫ j) rfl).inv := by
    apply (mateEquiv (FB.shAdj (k ≫ j)) (FA.shAdj (k ≫ j))).injective
    rw [hch, conjugateEquiv_mateEquiv_vcomp _
      ((FB.shAdj k).comp (FB.shAdj j)), mateEquiv_conjugateEquiv_vcomp _
      ((FA.shAdj k).comp (FA.shAdj j)), mateEquiv_hcomp,
      hck, hcj]
    have hc := congrArg Iso.inv
      (Equiv.apply_symm_apply
        (conjugateIsoEquiv ((FB.shAdj k).comp (FB.shAdj j)) (FB.shAdj (k ≫ j)))
        (FB.pbComp' k j (k ≫ j) rfl).symm)
    have hc' := congrArg Iso.hom
      (Equiv.apply_symm_apply
        (conjugateIsoEquiv ((FA.shAdj k).comp (FA.shAdj j)) (FA.shAdj (k ≫ j)))
        (FA.pbComp' k j (k ≫ j) rfl).symm)
    change conjugateEquiv _ _ (FB.shComp' k j (k ≫ j) rfl).inv =
      (FB.pbComp' k j (k ≫ j) rfl).hom at hc
    change conjugateEquiv _ _ (FA.shComp' k j (k ≫ j) rfl).hom =
      (FA.pbComp' k j (k ≫ j) rfl).inv at hc'
    rw [hc, hc']
    apply TwoSquare.ext
    intro M
    simp only [TwoSquare.whiskerTop_app, TwoSquare.whiskerBottom_app,
      TwoSquare.hComp_app, Category.assoc]
    dsimp only [TwoSquare.mk, TwoSquare.natTrans]
    apply (cancel_epi (qh.hom.app M)).1
    simp only [Iso.hom_inv_id_app]
    have hh := hq M
    simp only [pasteTwoSquaresIso_hom_app] at hh
    rw [reassoc_of% hh]
    simp only [Iso.hom_inv_id_app_assoc, ← Functor.map_comp_assoc,
      Iso.hom_inv_id_app]
    erw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.hom_inv_id_app]
    rfl
  intro L
  have h := congr_app hs L
  simp only [TwoSquare.whiskerLeft_app, TwoSquare.whiskerRight_app,
    TwoSquare.vComp_app, Category.assoc] at h
  rw [h]
  simp only [pasteTwoSquaresIso_hom_app, Category.assoc, ← Functor.map_comp,
    Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]

private theorem scalarOpenPlus_comp
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y Z : Scheme.{u}} (k : X ⟶ Y) (j : Y ⟶ Z) (h : X ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion j] [IsOpenImmersion h]
    (w : k ≫ j = h) :
    CoeffCompatible (scalarOpenPlus φ h)
      (pasteTwoSquaresIso (scalarOpenPlus φ k) (scalarOpenPlus φ j))
      ((derivedPlusFormalism (ModuleCat.{u + 1} A)).shComp' k j h w).hom
      ((derivedPlusFormalism (ModuleCat.{u + 1} B)).shComp' k j h w).hom := by
  subst h
  exact scalar_open_comp_paste
    (derivedPlusFormalism (ModuleCat.{u + 1} A))
    (derivedPlusFormalism (ModuleCat.{u + 1} B)) k j
    (fun W ↦ scalarRestrictionPlus φ W)
    (scalarOpenPlus φ k) (scalarOpenPlus φ j) (scalarOpenPlus φ (k ≫ j))
    (scalarPullbackPlus φ k) (scalarPullbackPlus φ j) (scalarPullbackPlus φ (k ≫ j))
    (scalarOpenPlus_mate φ k) (scalarOpenPlus_mate φ j)
    (scalarOpenPlus_mate φ (k ≫ j)) (scalarPullbackPlus_comp φ k j (k ≫ j) rfl)

private theorem scalar_triangle_paste
    (FA FB : CompactSupportFormalism) [FA.HasProperExchange] [FB.HasProperExchange]
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (T : Compactification.Triangle f g) (s : ∀ W : Scheme.{u}, FB.obj W ⥤ FA.obj W)
    (ci : s X ⋙ FA.sh T.cf.i ≅ FB.sh T.cf.i ⋙ s T.cf.Z)
    (cp : s T.cf.Z ⋙ FA.pf T.cf.g ≅ FB.pf T.cf.g ⋙ s Y)
    (cj : s Y ⋙ FA.sh T.cg.i ≅ FB.sh T.cg.i ⋙ s T.cg.Z)
    (cq : s T.cf.Z ⋙ FA.sh T.q ≅ FB.sh T.q ⋙ s T.cfg.Z)
    (cr : s T.cfg.Z ⋙ FA.pf T.p ≅ FB.pf T.p ⋙ s T.cg.Z)
    (cs : s T.cg.Z ⋙ FA.pf T.cg.g ≅ FB.pf T.cg.g ⋙ s Z)
    (cf : s X ⋙ FA.sh T.cfg.i ≅ FB.sh T.cfg.i ⋙ s T.cfg.Z)
    (ct : s T.cfg.Z ⋙ FA.pf T.cfg.g ≅ FB.pf T.cfg.g ⋙ s Z) :
    have := CompactSupportFormalism.HasBaseChange.isIso_baseChange (F := FA) T.isPullback
    have := CompactSupportFormalism.HasBaseChange.isIso_baseChange (F := FB) T.isPullback
    CoeffCompatible (pasteTwoSquaresIso cp cj) (pasteTwoSquaresIso cq cr)
        (FA.exchange T.cf.g T.q T.cg.i T.p T.isPullback.w).natTrans
        (FB.exchange T.cf.g T.q T.cg.i T.p T.isPullback.w).natTrans →
      CoeffCompatible (pasteTwoSquaresIso ci cq) cf
        (FA.shComp' T.cf.i T.q T.cfg.i T.i_q).inv
        (FB.shComp' T.cf.i T.q T.cfg.i T.i_q).inv →
      CoeffCompatible (pasteTwoSquaresIso cr cs) ct
        (FA.pfComp' T.p T.cg.g T.cfg.g T.p_g).inv
        (FB.pfComp' T.p T.cg.g T.cfg.g T.p_g).inv →
      CoeffCompatible (pasteTwoSquaresIso (pasteTwoSquaresIso ci cp)
        (pasteTwoSquaresIso cj cs)) (pasteTwoSquaresIso cf ct)
        (FA.compIso T).hom (FB.compIso T).hom := by
  dsimp only
  have := CompactSupportFormalism.HasBaseChange.isIso_baseChange (F := FA) T.isPullback
  have := CompactSupportFormalism.HasBaseChange.isIso_baseChange (F := FB) T.isPullback
  have := CompactSupportFormalism.HasProperExchange.isIso_exchange (F := FA) T.isPullback
  have := CompactSupportFormalism.HasProperExchange.isIso_exchange (F := FB) T.isPullback
  intro he ho hp
  have hm := (CoeffCompatible.associator_inv cp cj cs).comp
    ((he.whiskerRight cs).comp (CoeffCompatible.associator_hom cq cr cs))
  have hn := (CoeffCompatible.associator_inv ci cq (pasteTwoSquaresIso cr cs)).comp
    ((ho.whiskerRight (pasteTwoSquaresIso cr cs)).comp (hp.whiskerLeft cf))
  have hh := (CoeffCompatible.associator_hom ci cp (pasteTwoSquaresIso cj cs)).comp
    ((hm.whiskerLeft ci).comp hn)
  intro K
  simpa only [CompactSupportFormalism.compIso_hom_app, pasteTwoSquaresIso_hom_app,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.comp_obj,
    Functor.comp_map, Functor.map_comp,
    CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id, Category.assoc]
    using hh K

private theorem scalar_paste_component
    {C C' D D' E E' : Type*}
    [Category C] [Category C'] [Category D] [Category D'] [Category E] [Category E']
    {R : C' ⥤ C} {S : D' ⥤ D} {U : E' ⥤ E}
    {F : C ⥤ D} {F' : C' ⥤ D'} {G : D ⥤ E} {G' : D' ⥤ E'}
    {H : C ⥤ E} {H' : C' ⥤ E'}
    (cF : R ⋙ F ≅ F' ⋙ S) (cG : S ⋙ G ≅ G' ⋙ U) (cH : R ⋙ H ≅ H' ⋙ U)
    (α : F ⋙ G ⟶ H) (β : F' ⋙ G' ⟶ H')
    (h : CoeffCompatible (pasteTwoSquaresIso cF cG) cH α β) (K : C') :
    α.app (R.obj K) ≫ cH.hom.app K =
      G.map (cF.hom.app K) ≫ cG.hom.app (F'.obj K) ≫ U.map (β.app K) := by
  simpa only [pasteTwoSquaresIso_hom_app, Category.assoc] using (h K).symm

set_option maxHeartbeats 800000 in
-- Specializing the abstract formalism requires extra reduction of derived functor types.
private theorem scalar_triangle_compatible
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (T : Compactification.Triangle f g) :
    CoeffCompatible
      (pasteTwoSquaresIso (compactSupportCoefficientRestrictionPlus φ T.cf)
        (compactSupportCoefficientRestrictionPlus φ T.cg))
      (compactSupportCoefficientRestrictionPlus φ T.cfg)
      ((derivedPlusFormalism (ModuleCat.{u + 1} A)).compIso T).hom
      ((derivedPlusFormalism (ModuleCat.{u + 1} B)).compIso T).hom := by
  exact scalar_triangle_paste
    (derivedPlusFormalism (ModuleCat.{u + 1} A))
    (derivedPlusFormalism (ModuleCat.{u + 1} B)) T
    (fun W ↦ scalarRestrictionPlus φ W)
    (scalarOpenPlus φ T.cf.i) (scalarPushforwardPlus φ T.cf.g)
    (scalarOpenPlus φ T.cg.i) (scalarOpenPlus φ T.q)
    (scalarPushforwardPlus φ T.p) (scalarPushforwardPlus φ T.cg.g)
    (scalarOpenPlus φ T.cfg.i) (scalarPushforwardPlus φ T.cfg.g)
    (scalarOpenPlus_exchange φ T.cf.g T.q T.cg.i T.p T.isPullback)
    (CoeffCompatible.inv
      (e := (derivedPlusFormalism (ModuleCat.{u + 1} A)).shComp'
        T.cf.i T.q T.cfg.i T.i_q)
      (e' := (derivedPlusFormalism (ModuleCat.{u + 1} B)).shComp'
        T.cf.i T.q T.cfg.i T.i_q)
      (scalarOpenPlus_comp φ T.cf.i T.q T.cfg.i T.i_q))
    (scalarPushforwardPlus_comp φ T.p T.cg.g T.cfg.g T.p_g)

/-- Scalar restriction respects the local compositor on a compatible triangle.
Source: Stacks Project, Tag 0F7J (the compatible triangle construction), and Tag 0GL6.
(blueprint: lem-sf-etale-restriction-triangle).

Proof: expand CompactSupportFormalism.compIso_hom_app. It has three geometric
factors: the cartesian proper/open exchange, composition of extensions by zero,
and composition of proper direct images. Restriction commutes with the last factor
by uniqueness of the derived direct-image comparison, checked after the
right-derived unit on a bounded-below injective resolution. For the open factor,
transpose under the extension-by-zero adjunction. The composition identity for
inverse-image/restriction and the composite unit identify both transposes.
For the mixed factor, paste the restriction/inverse-image square with the
cartesian inverse-image square. Taking the proper and open mates gives the
restriction square for proper/open exchange. Substitute these three squares
in the expanded compositor, move the comparisons through by naturality, and
reassociate. The outer proper/open comparisons are precisely
compactSupportCoefficientRestrictionPlus for the three sides. Identity sides
reduce to adjunction triangle identities; no faithfulness of derived restriction
or scalar-extension hypothesis is needed. -/
theorem compactSupportRestrictionPlus_triangle
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (T : Compactification.Triangle f g)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))) :
    ((derivedPlusFormalism (ModuleCat.{u + 1} A)).compIso T).hom.app
        ((Sheaf.restrictScalars X.smallEtaleTopology φ).mapDerivedCategoryPlus.obj L) ≫
      (compactSupportCoefficientRestrictionPlus φ T.cfg).hom.app L =
    (rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A) T.cg).map
        ((compactSupportCoefficientRestrictionPlus φ T.cf).hom.app L) ≫
      (compactSupportCoefficientRestrictionPlus φ T.cg).hom.app
        ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} B) T.cf).obj L) ≫
      (Sheaf.restrictScalars Z.smallEtaleTopology φ).mapDerivedCategoryPlus.map
        (((derivedPlusFormalism (ModuleCat.{u + 1} B)).compIso T).hom.app L) := by
  exact scalar_paste_component _ _ _ _ _ (scalar_triangle_compatible φ T) L

end AlgebraicGeometry.Etale
