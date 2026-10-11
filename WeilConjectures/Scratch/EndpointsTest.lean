module

public import WeilConjectures.SixFunctors.ProEtale.Adic.OpenImmersion
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import WeilConjectures.SixFunctors.ProEtale.LowerShriek.OpenImmersion.Mono
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseDenseOpen

universe u
open CategoryTheory AlgebraicGeometry Limits

@[expose] public section

namespace AlgebraicGeometry.Scheme.ProEt

lemma exists_mem_of_mem_topology {X : Scheme.{u}} {V : X.ProEt} {S : Sieve V}
    (hS : S ∈ topology X V) (v : V.left) :
    ∃ (W : X.ProEt) (g : W ⟶ V) (w : W.left), S.arrows g ∧ g.left w = v := by
  obtain ⟨P, hP, hPS⟩ := mem_topology_iff.1 hS
  obtain ⟨𝒰, _, h𝒰⟩ := (mem_propQCPrecoverage_iff_exists_quasiCompactCover
    (P := @WeaklyEtale)).1 (mem_precoverage_iff.1 hP)
  have hmem : P.map (ProEt.forget X ⋙ CategoryTheory.Over.forget X) (𝒰.f (𝒰.idx v)) := by
    rw [h𝒰]
    exact ⟨_⟩
  obtain ⟨Z, hZ, a, ha, hZa⟩ := Presieve.map_iff.1 hmem
  obtain ⟨u, hu⟩ := 𝒰.covers v
  refine ⟨Z, a, (eqToHom hZ.symm) u, hPS _ _ ha, ?_⟩
  have h : a.left = eqToHom hZ ≫ 𝒰.f (𝒰.idx v) := hZa
  have key : ∀ {A B : Scheme.{u}} (e : A = B) (x : B), (eqToHom e) ((eqToHom e.symm) x) = x := by
    intro A B e x
    subst e
    rfl
  rw [h, Scheme.Hom.comp_apply]
  exact (congrArg (𝒰.f _) (key hZ u)).trans hu

end AlgebraicGeometry.Scheme.ProEt

namespace AlgebraicGeometry.ProEtale

open Opposite

variable {l : ℕ} [Fact l.Prime]

instance isLocallySurjective_toSheafify_weilCoefficients {X : Scheme.{u}}
    (P : X.ProEtᵒᵖ ⥤ WeilCoefficients.{u} l) :
    Presheaf.IsLocallySurjective (Scheme.ProEt.topology X)
      (toSheafify (Scheme.ProEt.topology X) P) := by
  have (Y : X.ProEt) : PreservesColimitsOfShape ((Scheme.ProEt.topology X).Cover Y)ᵒᵖ
      (forget (WeilCoefficients.{u} l)) :=
    PreservesFilteredColimitsOfSize.preserves_filtered_colimits _
  exact Presheaf.isLocallySurjective_toSheafify'.{u, u + 1} (J := Scheme.ProEt.topology X)
    (D := WeilCoefficients.{u} l) P

lemma exists_map_eq_zero_openImmersionLowerShriek {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (G : Sheaf (Scheme.ProEt.topology U) (WeilCoefficients.{u} l))
    (s : ToType (((j)_!open[WeilCoefficients.{u} l].obj G).obj.obj
      (op (Scheme.ProEt.mk (𝟙 X)))))
    (x : X) (hx : x ∉ Set.range j) :
    ∃ (W : X.ProEt) (g : W ⟶ Scheme.ProEt.mk (𝟙 X)) (w : W.left), g.left w = x ∧
      ((j)_!open[WeilCoefficients.{u} l].obj G).obj.map g.op s = 0 := by
  let Q := (openImmersionLocalization j).op.lan.obj G.obj
  have hS := Presheaf.imageSieve_mem (Scheme.ProEt.topology X)
    (toSheafify (Scheme.ProEt.topology X) Q) s
  obtain ⟨W, g, w, ⟨t, ht⟩, hw⟩ := Scheme.ProEt.exists_mem_of_mem_topology hS x
  refine ⟨W, g, w, hw, ?_⟩
  have hempty : IsEmpty (CostructuredArrow (openImmersionLocalization j).op (op W)) := by
    refine ⟨fun c ↦ hx ⟨(c.hom.unop.left ≫ c.left.unop.hom) w, ?_⟩⟩
    have h1 := c.hom.unop.w
    have h2 := g.w
    simp at h1 h2
    have e : (c.hom.unop.left ≫ (unop c.left).hom) ≫ j = g.left := by
      rw [Category.assoc, h1, ← h2]
      exact Category.comp_id _
    rw [← hw, ← e]
    rfl
  have hQ : IsZero (Q.obj (op W)) :=
    ((isColimitEquivIsInitialOfIsEmpty _ _).1
      ((openImmersionLocalization j).op.isPointwiseLeftKanExtensionLeftKanExtensionUnit
        G.obj (op W))).isZero
  have := ModuleCat.subsingleton_of_isZero hQ
  have e : ((j)_!open[WeilCoefficients.{u} l].obj G).obj.map g.op s =
      (toSheafify (Scheme.ProEt.topology X) Q).app (op W) t := ht.symm
  rw [e, Subsingleton.elim t 0, map_zero]

lemma globalSectionsToUpperStar_eq_zero_of_map_eq_zero {X : Scheme.{u}}
    (N : Sheaf (Scheme.ProEt.topology X) (WeilCoefficients.{u} l)) {V : Scheme.{u}} (f : V ⟶ X)
    [WeaklyEtale f] (g : Scheme.ProEt.mk f ⟶ Scheme.ProEt.mk (𝟙 X))
    (s : ToType ((Sheaf.Γ (Scheme.ProEt.topology X) (WeilCoefficients.{u} l)).obj N))
    (hs : N.obj.map g.op
      (((Sheaf.ΓNatIsoSheafSections _ _ (Scheme.ProEt.isTerminalMkId X)).hom.app N) s) = 0) :
    ((globalSectionsToUpperStar _ f).app N) s = 0 := by
  have h1 := (upperStarLowerStarAdjunction (WeilCoefficients.{u} l) f).unit_leftAdjointUniq_hom_app
    (localizationRestrictionLowerStarAdjunction (WeilCoefficients.{u} l) f inferInstance) N
  suffices h : (Sheaf.Γ _ (WeilCoefficients.{u} l)).map
      ((upperStarLowerStarAdjunction (WeilCoefficients.{u} l) f).unit.app N) s = 0 by
    rw [globalSectionsToUpperStar_app, ConcreteCategory.comp_apply]
    erw [h]
    rw [map_zero]
  have hinj : Function.Injective ((Sheaf.Γ _ (WeilCoefficients.{u} l)).map
      ((f)_*[WeilCoefficients.{u} l].map
        ((upperStarIsoLocalizationRestriction (WeilCoefficients.{u} l) f inferInstance).hom.app N))) :=
    (ConcreteCategory.bijective_of_isIso _).1
  apply hinj
  rw [map_zero]
  erw [← ConcreteCategory.comp_apply]
  rw [← Functor.map_comp]
  erw [h1]
  apply (ConcreteCategory.bijective_of_isIso ((Sheaf.ΓNatIsoSheafSections (Scheme.ProEt.topology X)
    (WeilCoefficients.{u} l) (Scheme.ProEt.isTerminalMkId X)).hom.app _)).1
  rw [map_zero]
  erw [← ConcreteCategory.comp_apply]
  rw [NatTrans.naturality, ConcreteCategory.comp_apply]
  simp [localizationRestrictionLowerStarAdjunction]
  have key {Y : X.ProEt} (φ : Y ⟶ Scheme.ProEt.mk (𝟙 X)) (m : Y ⟶ Scheme.ProEt.mk f) :
      N.obj.map φ.op (((Sheaf.ΓNatIsoSheafSections _ _ (Scheme.ProEt.isTerminalMkId X)).hom.app
        N) s) = 0 := by
    rw [(Scheme.ProEt.isTerminalMkId X).hom_ext φ (m ≫ g), op_comp, Functor.map_comp,
      ConcreteCategory.comp_apply, hs, map_zero]
  exact key _ (MorphismProperty.Over.homMk (pullback.snd _ _) rfl trivial)

open scoped ProEtale in
lemma exists_adicUpperStar_map_eq_zero_of_notMem_range {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] {M : AdicSheaf l U} (β : AdicSheaf.unit l X ⟶ (j)_!ᵃ[l].obj M) (x : X)
    (hx : x ∉ Set.range j) :
    ∃ (V : Scheme.{u}) (f : V ⟶ X) (_ : WeaklyEtale f) (v : V), f v = x ∧
      (f)^*ᵃ[l].map β = 0 := by
  let e := Sheaf.ΓNatIsoSheafSections (Scheme.ProEt.topology X) (WeilCoefficients.{u} l)
    (Scheme.ProEt.isTerminalMkId X)
  let c := (adicOpenImmersionLowerShriekComparison l j).app M
  let cT := ((sheafSections _ _).obj (op (Scheme.ProEt.mk (𝟙 X)))).mapIso (asIso c)
  let s := globalSectionOfModHom β
  obtain ⟨W, g, w, hw, h0⟩ := exists_map_eq_zero_openImmersionLowerShriek j M.X
    (cT.inv ((e.hom.app _) s)) x hx
  have hs : ((j)_!ᵃ[l].obj M).X.obj.map g.op ((e.hom.app _) s) = 0 := by
    have h1 := ConcreteCategory.congr_hom (c.hom.naturality g.op) (cT.inv ((e.hom.app _) s))
    simp only [ConcreteCategory.comp_apply] at h1
    erw [h0, map_zero] at h1
    have h5 : c.hom.app (op (Scheme.ProEt.mk (𝟙 X))) (cT.inv ((e.hom.app _) s)) =
        (e.hom.app _) s :=
      cT.inv_hom_id_apply _
    erw [h5] at h1
    exact h1.symm
  have h2 := globalSectionsToUpperStar_globalSectionOfModHom W.hom β
  rw [globalSectionsToUpperStar_eq_zero_of_map_eq_zero _ W.hom g s hs] at h2
  refine ⟨W.left, W.hom, inferInstance, w, ?_, ?_⟩
  · rw [← hw]
    have h3 := g.w
    simp at h3
    rw [← h3]
    rfl
  · have h4 : (adicUpperStarUnitIso l W.hom).inv ≫ (W.hom)^*ᵃ[l].map β = 0 := by
      apply (bijective_globalSectionOfModHom _).1
      rw [← h2, globalSectionOfModHom_eq]
      erw [Mod.zero_hom, Functor.map_zero]
      rfl
    rw [← cancel_epi (adicUpperStarUnitIso l W.hom).inv, h4, comp_zero]

attribute [local instance] Abelian.hasFiniteBiproducts

lemma eq_zero_of_upperStar_map_eq_zero_of_forall_specializes {Y : Scheme.{u}}
    {N : Sheaf (Scheme.ProEt.topology Y) (WeilCoefficients.{u} l)}
    (ψ : N ⟶ adicConstantSheaf l Y)
    (hψ : ∀ y : Y, ∃ (W : Scheme.{u}) (k : W ⟶ Y) (_ : WeaklyEtale k) (w : W), k w ⤳ y ∧
      (k)^*[WeilCoefficients.{u} l].map ψ = 0) :
    ψ = 0 := by
  ext U : 3
  ext x
  induction U using Opposite.rec with | op U => ?_
  change ψ.hom.app (op U) x = 0
  set c := ψ.hom.app (op U) x with hc
  refine adicConstantSheaf_ext (l := l) fun y ↦ ?_
  have : WeaklyEtale U.hom := U.prop
  obtain ⟨W, k, h, w, hw, hk⟩ := hψ (U.hom.base y)
  have hres : (localizationRestriction (WeilCoefficients.{u} l) k h).map ψ = 0 := by
    have := (upperStarIsoLocalizationRestriction (WeilCoefficients.{u} l) k h).hom.naturality ψ
    rw [hk, zero_comp] at this
    rw [← cancel_epi ((upperStarIsoLocalizationRestriction (WeilCoefficients.{u} l) k h).hom.app
      N), ← this, comp_zero]
  -- the restriction of `c` to `U ×_Y W` vanishes
  let b : W.ProEt := (MorphismProperty.Over.pullback @WeaklyEtale ⊤ k).obj U
  let ε : (MorphismProperty.Over.map ⊤ h).obj b ⟶ U :=
    MorphismProperty.Over.homMk (pullback.fst U.hom k) pullback.condition trivial
  have h1 : ψ.hom.app (op ((MorphismProperty.Over.map ⊤ h).obj b)) = 0 :=
    congrArg (fun φ ↦ φ.hom.app (op b)) hres
  have h2 := congrArg (fun φ ↦ φ x) (ψ.hom.naturality ε.op)
  simp only [h1] at h2
  have hz : ∀ p, c.down.1 ((pullback.fst U.hom k).base p) = 0 := by
    intro p
    have := congrArg (fun y ↦ y.down.1 p) h2
    simp only [comp_zero] at this
    exact this.symm
  -- `y` specializes from a point of `U ×_Y W`
  obtain ⟨y', hy', hy'w⟩ := Flat.generalizingMap U.hom hw
  obtain ⟨p, hp1, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := U.hom) (g := k) y' w hy'w
  rw [← (hy'.map c.down.1.continuous).eq, ← hp1, hz p]
  rfl

open scoped ProEtale in
theorem IsAdicLisseSheaf.eq_zero_of_forall_adicUpperStar_map_eq_zero {Y : Scheme.{u}}
    {N H : AdicSheaf l Y} (hH : IsAdicLisseSheaf H) (φ : N ⟶ H)
    (hφ : ∀ y : Y, ∃ (W : Scheme.{u}) (k : W ⟶ Y) (_ : WeaklyEtale k) (w : W), k w ⤳ y ∧
      (k)^*ᵃ[l].map φ = 0) :
    φ = 0 := by
  obtain ⟨R, hR, hRH⟩ := hH
  obtain ⟨ι, V, f, rfl⟩ := R.exists_eq_ofArrows
  have hf (i : ι) : WeaklyEtale (f i) :=
    Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ hR (.mk i)
  choose n e using fun i ↦ hRH (f i) (.mk i)
  refine ProEtale.eq_zero_of_adicUpperStar_map_eq_zero f hR φ fun i ↦ ?_
  rw [← cancel_mono (e i).some.hom, zero_comp]
  refine biproduct.hom_ext _ _ fun a ↦ ?_
  rw [zero_comp, Category.assoc]
  set ψ := (f i)^*ᵃ[l].map φ ≫ (e i).some.hom ≫
    biproduct.π (fun _ : Fin (n i) ↦ AdicSheaf.unit l (V i)) a
  apply Mod.hom_ext
  refine eq_zero_of_upperStar_map_eq_zero_of_forall_specializes ψ.hom fun v ↦ ?_
  obtain ⟨W, k, hk, w, hw, hkφ⟩ := hφ ((f i).base v)
  obtain ⟨v', hv', hv'w⟩ := Flat.generalizingMap (f i) hw
  obtain ⟨p, -, hp2⟩ := Scheme.Pullback.exists_preimage_pullback (f := k) (g := f i) w v'
    hv'w.symm
  refine ⟨_, pullback.snd k (f i), inferInstance, p, hp2 ▸ hv', ?_⟩
  -- the pullback of `ψ` to `W ×_Y V i` vanishes
  have hψ : (pullback.snd k (f i))^*ᵃ[l].map ψ = 0 := by
    have e1 := (adicUpperStarCompIso l (pullback.condition (f := k) (g := f i))).hom.naturality φ
    simp only [Functor.comp_map, hkφ, Functor.map_zero, zero_comp] at e1
    have e2 : (pullback.snd k (f i))^*ᵃ[l].map ((f i)^*ᵃ[l].map φ) = 0 := by
      rw [← cancel_epi ((adicUpperStarCompIso l
        (pullback.condition (f := k) (g := f i))).hom.app N), comp_zero]
      exact e1.symm
    simp only [ψ, Functor.map_comp, e2, zero_comp]
  exact congrArg Mod.Hom.hom hψ

open scoped ProEtale in
theorem IsAdicLisseSheaf.eq_zero_of_forall_adicUpperStar_map_eq_zero_of_lowerStar
    {X Y : Scheme.{u}} (g : Y ⟶ X) {N : AdicSheaf l X} {H : AdicSheaf l Y}
    (hH : IsAdicLisseSheaf H) (γ : N ⟶ (g)_*ᵃ[l].obj H)
    (hγ : ∀ y : Y, ∃ (V : Scheme.{u}) (f : V ⟶ X) (_ : WeaklyEtale f) (v : V) (y' : Y),
      y' ⤳ y ∧ f v = g y' ∧ (f)^*ᵃ[l].map γ = 0) :
    γ = 0 := by
  let adj := adicUpperStarLowerStarAdjunction l g
  suffices hφ : (adj.homEquiv _ _).symm γ = 0 by
    rw [← (adj.homEquiv _ _).apply_symm_apply γ, hφ, Adjunction.homEquiv_unit,
      Functor.map_zero, comp_zero]
  refine hH.eq_zero_of_forall_adicUpperStar_map_eq_zero _ fun y ↦ ?_
  obtain ⟨V, f, hf, v, y', hy', hfv, hfγ⟩ := hγ y
  obtain ⟨p, -, hp2⟩ := Scheme.Pullback.exists_preimage_pullback (f := f) (g := g) v y' hfv
  refine ⟨_, pullback.snd f g, inferInstance, p, hp2 ▸ hy', ?_⟩
  have e1 := (adicUpperStarCompIso l (pullback.condition (f := f) (g := g))).hom.naturality γ
  simp only [Functor.comp_map, hfγ, Functor.map_zero, zero_comp] at e1
  have e2 : (pullback.snd f g)^*ᵃ[l].map ((g)^*ᵃ[l].map γ) = 0 := by
    rw [← cancel_epi ((adicUpperStarCompIso l
      (pullback.condition (f := f) (g := g))).hom.app N), comp_zero]
    exact e1.symm
  rw [Adjunction.homEquiv_counit, Functor.map_comp, e2, zero_comp]

open scoped ProEtale in
theorem eq_zero_of_forall_specializes_notMem_range {U X Y : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (h : Y ⟶ U) {H : AdicSheaf l Y} (hH : IsAdicLisseSheaf H)
    (β : AdicSheaf.unit l X ⟶ (j)_!ᵃ[l].obj ((h)_*ᵃ[l].obj H))
    (hY : ∀ y : Y, ∃ y' : Y, y' ⤳ y ∧ ∃ x : X, x ∉ Set.range j ∧ j (h y') ⤳ x) :
    β = 0 := by
  suffices hγ : β ≫ (adicOpenImmersionLowerShriekToLowerStar l j).app _ ≫
      (adicLowerStarComp l h j).hom.app H = 0 by
    rw [← Category.assoc, Preadditive.IsIso.comp_right_eq_zero] at hγ
    exact (cancel_mono _).1 (hγ.trans zero_comp.symm)
  refine IsAdicLisseSheaf.eq_zero_of_forall_adicUpperStar_map_eq_zero_of_lowerStar (h ≫ j) hH _
    fun y ↦ ?_
  obtain ⟨y', hy', x, hx, hyx⟩ := hY y
  obtain ⟨V, f, hf, v₀, hv₀, hfβ⟩ := exists_adicUpperStar_map_eq_zero_of_notMem_range j β x hx
  obtain ⟨v, -, hv⟩ := Flat.generalizingMap f (hv₀ ▸ hyx)
  refine ⟨V, f, hf, v, y', hy', hv, ?_⟩
  rw [Functor.map_comp, hfβ, zero_comp]

end AlgebraicGeometry.ProEtale
