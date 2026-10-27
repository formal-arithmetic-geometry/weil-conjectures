/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.LogEtaleRestrictionStalkComparison

public import Sheaf.AlgebraicGeometry.FineLogEtaleDescentDatum
public import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous

import Sheaf.AlgebraicGeometry.LogUnitSectionLift

/-!
# Locality of the log condition and fine charts

Source: ILO, Exposé VI 1.1, p. 69; VIII 3.3.4(ii), 3.3.8, p. 107
(blueprint: lem-trf-log-condition-fine-chart-locality).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

private theorem chartCongruence_comap {A B P : Type u}
    [CommRing A] [CommRing B] [CommMonoid P] (r : A ≃+* B) (γ : P →* A) :
    divisorialChartCongruence γ.mrangeRestrict =
      (divisorialChartCongruence (r.toMonoidHom.comp γ).mrangeRestrict).comap
        (MulEquiv.prodCongr (MulEquiv.refl P) (Units.mapEquiv r.toMulEquiv))
        (map_mul _) := by
  unfold divisorialChartCongruence
  rw [Con.comap_conGen_equiv]
  apply congrArg conGen
  funext x y
  apply propext
  let H := MulEquiv.prodCongr (MulEquiv.refl P) (Units.mapEquiv r.toMulEquiv)
  constructor
  · rintro ⟨p, a, h, rfl, rfl⟩
    refine ⟨p, Units.mapEquiv r.toMulEquiv a, congrArg r h, ?_, ?_⟩
    · change (p, Units.mapEquiv r.toMulEquiv 1) = (p, 1)
      rw [map_one]
    · rfl
  · rintro ⟨p, a, h, hx, hy⟩
    refine ⟨p, (Units.mapEquiv r.toMulEquiv).symm a, ?_, ?_, ?_⟩
    · apply r.injective
      exact h.trans (congrArg Units.val
        ((Units.mapEquiv r.toMulEquiv).apply_symm_apply a)).symm
    · apply H.injective
      change H x = (p, Units.mapEquiv r.toMulEquiv 1)
      rw [map_one]
      exact hx
    · apply H.injective
      change H y = (1, Units.mapEquiv r.toMulEquiv ((Units.mapEquiv r.toMulEquiv).symm a))
      rw [MulEquiv.apply_symm_apply]
      exact hy

private theorem chartTransport {A B L K P : Type u}
    [CommRing A] [CommRing B] [CommMonoid L] [CommMonoid K] [CommMonoid P]
    (r : A ≃+* B) (E : L ≃* K) (α : L →* A) (δ : K →* B)
    (j : Aˣ →* L) (k : Bˣ →* K) (β : P →* L) (γ : P →* K)
    (hα : δ.comp E.toMonoidHom = r.toMonoidHom.comp α)
    (hj : E.toMonoidHom.comp j = k.comp (Units.map r.toMonoidHom))
    (hβ : γ = E.toMonoidHom.comp β)
    (hchart : Function.Surjective (β.coprod j) ∧
      Con.ker (β.coprod j) = divisorialChartCongruence (α.comp β).mrangeRestrict) :
    Function.Surjective (γ.coprod k) ∧
      Con.ker (γ.coprod k) = divisorialChartCongruence (δ.comp γ).mrangeRestrict := by
  let H := MulEquiv.prodCongr (MulEquiv.refl P) (Units.mapEquiv r.toMulEquiv)
  have hpair (x : P × Aˣ) : γ.coprod k (H x) = E (β.coprod j x) := by
    change γ x.1 * k (Units.map r.toMonoidHom x.2) = E (β x.1 * j x.2)
    rw [map_mul]
    exact congrArg₂ (· * ·) (DFunLike.congr_fun hβ x.1)
      (DFunLike.congr_fun hj x.2).symm
  have ha : δ.comp γ = r.toMonoidHom.comp (α.comp β) := by
    rw [hβ, ← MonoidHom.comp_assoc, hα, MonoidHom.comp_assoc]
  refine ⟨?_, ?_⟩
  · intro z
    obtain ⟨x, hx⟩ := hchart.1 (E.symm z)
    exact ⟨H x, (hpair x).trans ((congrArg E hx).trans (E.apply_symm_apply z))⟩
  · rw [ha]
    ext x y
    obtain ⟨x, rfl⟩ := H.surjective x
    obtain ⟨y, rfl⟩ := H.surjective y
    change γ.coprod k (H x) = γ.coprod k (H y) ↔ _
    rw [hpair, hpair, E.injective.eq_iff]
    change (Con.ker (β.coprod j)) x y ↔ _
    rw [hchart.2, chartCongruence_comap r (α.comp β)]
    rfl

private noncomputable def pointedRestrictionToOver {T : Scheme.{u}} (U : T.Etale)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ U.left) :
    (Scheme.pointSmallEtale s).fiber.Elements ⥤
      Over ((Scheme.pointSmallEtale (s ≫ U.hom)).fiber.elementsMk U (Over.homMk s)) where
  obj V := by
    let W : T.Etale := Scheme.Etale.mk (V.1.hom ≫ U.hom)
    let v : (Scheme.pointSmallEtale (s ≫ U.hom)).fiber.obj W :=
      Over.homMk V.2.left (by
        change V.2.left ≫ (V.1.hom ≫ U.hom) = s ≫ U.hom
        exact (Category.assoc _ _ _).symm.trans
          (congrArg (fun f : Spec (.of Ω) ⟶ U.left ↦ f ≫ U.hom) (Over.w V.2)))
    exact Over.mk (CategoryOfElements.homMk ⟨W, v⟩
      _ (MorphismProperty.Over.homMk V.1.hom rfl) (by
        apply Over.OverMorphism.ext
        change V.2.left ≫ V.1.hom = s
        exact Over.w V.2))
  map {V W} f := Over.homMk (CategoryOfElements.homMk _ _
    (MorphismProperty.Over.homMk f.val.left (by
      change f.val.left ≫ (W.1.hom ≫ U.hom) = V.1.hom ≫ U.hom
      exact (Category.assoc _ _ _).symm.trans
        (congrArg (fun g ↦ g ≫ U.hom) (MorphismProperty.Over.w f.val)))) (by
      apply Over.OverMorphism.ext
      change V.2.left ≫ f.val.left = W.2.left
      exact congrArg Over.Hom.left f.property)) (by
        apply Subtype.ext
        apply MorphismProperty.Over.Hom.ext
        exact MorphismProperty.Over.w f.val)

private noncomputable def pointedRestrictionFromOver {T : Scheme.{u}} (U : T.Etale)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ U.left) :
    Over ((Scheme.pointSmallEtale (s ≫ U.hom)).fiber.elementsMk U (Over.homMk s)) ⥤
      (Scheme.pointSmallEtale s).fiber.Elements where
  obj V := ⟨Scheme.Etale.mk V.hom.val.left,
    Over.homMk V.left.2.left (congrArg Over.Hom.left V.hom.property)⟩
  map {V W} f := CategoryOfElements.homMk _ _
    (MorphismProperty.Over.homMk f.left.val.left (by
      exact congrArg (fun g ↦ g.val.left) (Over.w f))) (by
        apply Over.OverMorphism.ext
        change V.left.2.left ≫ f.left.val.left = W.left.2.left
        exact congrArg Over.Hom.left f.left.property)

private noncomputable def pointedRestrictionEquiv {T : Scheme.{u}} (U : T.Etale)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ U.left) :
    (Scheme.pointSmallEtale s).fiber.Elements ≌
      Over ((Scheme.pointSmallEtale (s ≫ U.hom)).fiber.elementsMk U (Over.homMk s)) where
  functor := pointedRestrictionToOver U s
  inverse := pointedRestrictionFromOver U s
  unitIso := Iso.refl _
  counitIso := NatIso.ofComponents (fun V ↦ Over.isoMk
    (CategoryOfElements.isoMk _ _ (MorphismProperty.Over.isoMk (Iso.refl _)
      (by
        change 𝟙 V.left.1.left ≫ V.left.1.hom = V.hom.val.left ≫ U.hom
        rw [Category.id_comp, MorphismProperty.Over.w])) (by
        apply Over.OverMorphism.ext
        exact Category.comp_id _)) (by
          apply Subtype.ext
          apply MorphismProperty.Over.Hom.ext
          exact Category.id_comp _)) (by
            intro V W f
            apply Over.OverMorphism.ext
            apply Subtype.ext
            apply MorphismProperty.Over.Hom.ext
            exact (Category.comp_id _).trans (Category.id_comp _).symm)
  functor_unitIso_comp _ := by
    apply Over.OverMorphism.ext
    apply Subtype.ext
    apply MorphismProperty.Over.Hom.ext
    exact Category.comp_id _

private noncomputable def restrictionColimitIso {T : Scheme.{u}} (U : T.Etale)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ U.left)
    {A : Type*} [Category A] (Q : T.Etaleᵒᵖ ⥤ A)
    [HasColimit ((CategoryOfElements.π (Scheme.pointSmallEtale (s ≫ U.hom)).fiber).op ⋙ Q)]
    [HasColimit ((CategoryOfElements.π (Scheme.pointSmallEtale s).fiber).op ⋙
      (Scheme.Etale.etaleToOver U ⋙ Over.forget U).op ⋙ Q)] :
    colimit ((CategoryOfElements.π (Scheme.pointSmallEtale s).fiber).op ⋙
      (Scheme.Etale.etaleToOver U ⋙ Over.forget U).op ⋙ Q) ≅
    colimit ((CategoryOfElements.π (Scheme.pointSmallEtale (s ≫ U.hom)).fiber).op ⋙ Q) := by
  let F := (pointedRestrictionEquiv U s).functor ⋙ Over.forget _
  have : F.Initial := by dsimp [F]; infer_instance
  exact Functor.Final.colimitIso F.op
    ((CategoryOfElements.π (Scheme.pointSmallEtale (s ≫ U.hom)).fiber).op ⋙ Q)

private noncomputable def restrictionMonoidStalkIso {T : Scheme.{u}}
    (M : EtalePrelogStructure T) (U : T.Etale)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ U.left) :
    (M.etaleRestrict U).stalk s ≅ M.stalk (s ≫ U.hom) := by
  let : HasColimit
      ((CategoryOfElements.π (Scheme.pointSmallEtale (s ≫ U.hom)).fiber).op ⋙
        M.monoidSheaf.obj) := pointedEtaleCommMonStalkHasColimit M.monoidSheaf _
  let : HasColimit
      ((CategoryOfElements.π (Scheme.pointSmallEtale s).fiber).op ⋙
        (Scheme.Etale.etaleToOver U ⋙ Over.forget U).op ⋙ M.monoidSheaf.obj) :=
    pointedEtaleCommMonStalkHasColimit (M.etaleRestrict U).monoidSheaf s
  exact restrictionColimitIso U s M.monoidSheaf.obj

private noncomputable def restrictionRingStalkIso {T : Scheme.{u}} (U : T.Etale)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ U.left) :
    strictLocalRing U.left s ≅ strictLocalRing T (s ≫ U.hom) :=
  restrictionColimitIso U s T.etaleStructurePresheaf

private theorem restrictionMonoidStalkIso_germ {T : Scheme.{u}}
    (M : EtalePrelogStructure T) (U : T.Etale)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ U.left)
    (V : U.left.Etale) (v : (Scheme.pointSmallEtale s).fiber.obj V) :
    (M.etaleRestrict U).germ s V v ≫ (restrictionMonoidStalkIso M U s).hom =
      M.germ (s ≫ U.hom) (Scheme.Etale.mk (V.hom ≫ U.hom))
        (Over.homMk v.left (by
          change v.left ≫ (V.hom ≫ U.hom) = s ≫ U.hom
          exact (Category.assoc _ _ _).symm.trans
            (congrArg (fun f : Spec (.of Ω) ⟶ U.left ↦ f ≫ U.hom) (Over.w v)))) := by
  let : HasColimit
      ((CategoryOfElements.π (Scheme.pointSmallEtale (s ≫ U.hom)).fiber).op ⋙
        M.monoidSheaf.obj) := pointedEtaleCommMonStalkHasColimit M.monoidSheaf _
  exact Functor.Final.ι_colimitIso_hom
    ((pointedRestrictionEquiv U s).functor ⋙ Over.forget _).op
    ((CategoryOfElements.π (Scheme.pointSmallEtale (s ≫ U.hom)).fiber).op ⋙
      M.monoidSheaf.obj) (op ⟨V, v⟩)

private theorem restrictionRingStalkIso_germ {T : Scheme.{u}} (U : T.Etale)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ U.left)
    (V : U.left.Etale) (v : (Scheme.pointSmallEtale s).fiber.obj V) :
    strictLocalGerm U.left s V v ≫ (restrictionRingStalkIso U s).hom =
      strictLocalGerm T (s ≫ U.hom) (Scheme.Etale.mk (V.hom ≫ U.hom))
        (Over.homMk v.left (by
          change v.left ≫ (V.hom ≫ U.hom) = s ≫ U.hom
          exact (Category.assoc _ _ _).symm.trans
            (congrArg (fun f : Spec (.of Ω) ⟶ U.left ↦ f ≫ U.hom) (Over.w v)))) := by
  exact Functor.Final.ι_colimitIso_hom
    ((pointedRestrictionEquiv U s).functor ⋙ Over.forget _).op
    ((CategoryOfElements.π (Scheme.pointSmallEtale (s ≫ U.hom)).fiber).op ⋙
      T.etaleStructurePresheaf) (op ⟨V, v⟩)

private noncomputable def prelogIsoStalk {T : Scheme.{u}}
    {N M : EtalePrelogStructure T} (e : EtalePrelogStructure.Iso N M)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T) :
    N.stalk t ≅ M.stalk t :=
  HasColimit.isoOfNatIso
    (Functor.isoWhiskerLeft (CategoryOfElements.π (Scheme.pointSmallEtale t).fiber).op e.iso)

private theorem prelogIsoStalk_germ {T : Scheme.{u}}
    {N M : EtalePrelogStructure T} (e : EtalePrelogStructure.Iso N M)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T)
    (W : T.Etale) (w : (Scheme.pointSmallEtale t).fiber.obj W) :
    N.germ t W w ≫ (prelogIsoStalk e t).hom = e.iso.hom.app (op W) ≫ M.germ t W w := by
  let : HasColimit
      ((CategoryOfElements.π (Scheme.pointSmallEtale t).fiber).op ⋙ N.monoidSheaf.obj) :=
    pointedEtaleCommMonStalkHasColimit N.monoidSheaf t
  let : HasColimit
      ((CategoryOfElements.π (Scheme.pointSmallEtale t).fiber).op ⋙ M.monoidSheaf.obj) :=
    pointedEtaleCommMonStalkHasColimit M.monoidSheaf t
  exact HasColimit.isoOfNatIso_ι_hom
    (Functor.isoWhiskerLeft (CategoryOfElements.π (Scheme.pointSmallEtale t).fiber).op e.iso)
    (op ⟨W, w⟩)

private theorem prelogIsoStalk_alpha {T : Scheme.{u}}
    {N M : EtalePrelogStructure T} (e : EtalePrelogStructure.Iso N M)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T) :
    (M.stalkAlpha t).comp (prelogIsoStalk e t).hom.hom = N.stalkAlpha t := by
  apply CommMonCat.hom_ext_iff.mp
  change (prelogIsoStalk e t).hom ≫ CommMonCat.ofHom (M.stalkAlpha t) =
    CommMonCat.ofHom (N.stalkAlpha t)
  apply colimit.hom_ext (F := pointedEtaleStalkDiagram N.monoidSheaf t)
  intro j
  change colimit.ι (pointedEtaleStalkDiagram N.monoidSheaf t) j ≫
      ((prelogIsoStalk e t).hom ≫ CommMonCat.ofHom (M.stalkAlpha t)) =
    colimit.ι (pointedEtaleStalkDiagram N.monoidSheaf t) j ≫
      CommMonCat.ofHom (N.stalkAlpha t)
  rw [← Category.assoc]
  change (N.germ t j.unop.1 j.unop.2 ≫ (prelogIsoStalk e t).hom) ≫ _ = _
  rw [prelogIsoStalk_germ, Category.assoc]
  simp only [EtalePrelogStructure.stalkAlpha, EtalePrelogStructure.germ,
    pointedEtaleGerm, CommMonCat.ofHom_hom, colimit.ι_desc]
  have h := congrArg (fun f ↦ f.app (op j.unop.1)) e.alpha
  simpa only [NatTrans.comp_app, ← Category.assoc] using
    congrArg (fun f ↦ f ≫
      CommMonCat.ofHom (strictLocalGerm T t j.unop.1 j.unop.2).hom.toMonoidHom) h

private theorem restrictionStalk_alpha {T : Scheme.{u}}
    (M : EtalePrelogStructure T) (U : T.Etale)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ U.left) :
    (M.stalkAlpha (s ≫ U.hom)).comp (restrictionMonoidStalkIso M U s).hom.hom =
      (restrictionRingStalkIso U s).hom.hom.toMonoidHom.comp
        ((M.etaleRestrict U).stalkAlpha s) := by
  have h : (restrictionMonoidStalkIso M U s).hom ≫
      CommMonCat.ofHom (M.stalkAlpha (s ≫ U.hom)) =
    CommMonCat.ofHom ((M.etaleRestrict U).stalkAlpha s) ≫
      CommMonCat.ofHom (restrictionRingStalkIso U s).hom.hom.toMonoidHom := by
    apply colimit.hom_ext (F := pointedEtaleStalkDiagram (M.etaleRestrict U).monoidSheaf s)
    intro j
    rw [← Category.assoc]
    change ((M.etaleRestrict U).germ s j.unop.1 j.unop.2 ≫
        (restrictionMonoidStalkIso M U s).hom) ≫ _ = _
    rw [restrictionMonoidStalkIso_germ]
    simp only [EtalePrelogStructure.stalkAlpha, EtalePrelogStructure.germ,
      pointedEtaleGerm, CommMonCat.ofHom_hom, colimit.ι_desc_assoc, colimit.ι_desc]
    have h := restrictionRingStalkIso_germ U s j.unop.1 j.unop.2
    ext m
    exact (congrArg (fun f : Γ(j.unop.1.left, ⊤) ⟶ strictLocalRing T (s ≫ U.hom) ↦
      f ((M.etaleRestrict U).alpha.app (op j.unop.1) m)) h).symm
  exact congrArg CommMonCat.Hom.hom h

private noncomputable def localStalkIso {T : Scheme.{u}}
    (M : EtaleLogStructure T) (U : T.Etale) (N : EtaleLogStructure U.left)
    (e : EtalePrelogStructure.Iso N.toEtalePrelogStructure
      (M.toEtalePrelogStructure.etaleRestrict U))
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ U.left) :
    N.toEtalePrelogStructure.stalk s ≅ M.toEtalePrelogStructure.stalk (s ≫ U.hom) :=
  prelogIsoStalk e s ≪≫ restrictionMonoidStalkIso M.toEtalePrelogStructure U s

private theorem localStalkIso_alpha {T : Scheme.{u}}
    (M : EtaleLogStructure T) (U : T.Etale) (N : EtaleLogStructure U.left)
    (e : EtalePrelogStructure.Iso N.toEtalePrelogStructure
      (M.toEtalePrelogStructure.etaleRestrict U))
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ U.left) :
    (M.toEtalePrelogStructure.stalkAlpha (s ≫ U.hom)).comp
        (localStalkIso M U N e s).hom.hom =
      (restrictionRingStalkIso U s).hom.hom.toMonoidHom.comp
        (N.toEtalePrelogStructure.stalkAlpha s) := by
  change ((M.toEtalePrelogStructure.stalkAlpha (s ≫ U.hom)).comp
    (restrictionMonoidStalkIso M.toEtalePrelogStructure U s).hom.hom).comp
      (prelogIsoStalk e s).hom.hom = _
  rw [restrictionStalk_alpha, MonoidHom.comp_assoc, prelogIsoStalk_alpha]

private theorem localStalkIso_germ {T : Scheme.{u}}
    (M : EtaleLogStructure T) (U : T.Etale) (N : EtaleLogStructure U.left)
    (e : EtalePrelogStructure.Iso N.toEtalePrelogStructure
      (M.toEtalePrelogStructure.etaleRestrict U))
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ U.left)
    (V : U.left.Etale) (v : (Scheme.pointSmallEtale s).fiber.obj V) :
    N.toEtalePrelogStructure.germ s V v ≫ (localStalkIso M U N e s).hom =
      e.iso.hom.app (op V) ≫ M.toEtalePrelogStructure.germ (s ≫ U.hom)
        (Scheme.Etale.mk (V.hom ≫ U.hom)) (Over.homMk v.left (by
          change v.left ≫ (V.hom ≫ U.hom) = s ≫ U.hom
          exact (Category.assoc _ _ _).symm.trans
            (congrArg (fun f : Spec (.of Ω) ⟶ U.left ↦ f ≫ U.hom) (Over.w v)))) := by
  change N.toEtalePrelogStructure.germ s V v ≫
    ((prelogIsoStalk e s).hom ≫
      (restrictionMonoidStalkIso M.toEtalePrelogStructure U s).hom) = _
  rw [← Category.assoc, prelogIsoStalk_germ, Category.assoc, restrictionMonoidStalkIso_germ]

private theorem localStalkIso_units {T : Scheme.{u}}
    (M : EtaleLogStructure T) (U : T.Etale) (N : EtaleLogStructure U.left)
    (e : EtalePrelogStructure.Iso N.toEtalePrelogStructure
      (M.toEtalePrelogStructure.etaleRestrict U))
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ U.left) :
    (localStalkIso M U N e s).hom.hom.comp (N.unitsIn s) =
      (M.unitsIn (s ≫ U.hom)).comp
        (Units.map (restrictionRingStalkIso U s).hom.hom.toMonoidHom) := by
  ext a
  let n := (MulEquiv.ofBijective (Units.map (N.toEtalePrelogStructure.stalkAlpha s))
    (N.unitsBijective Ω s)).symm a
  let b := Units.map (restrictionRingStalkIso U s).hom.hom.toMonoidHom a
  let m := (MulEquiv.ofBijective
    (Units.map (M.toEtalePrelogStructure.stalkAlpha (s ≫ U.hom)))
    (M.unitsBijective Ω (s ≫ U.hom))).symm b
  have hn : Units.map (N.toEtalePrelogStructure.stalkAlpha s) n = a :=
    (MulEquiv.ofBijective _ (N.unitsBijective Ω s)).apply_symm_apply a
  have hm : Units.map (M.toEtalePrelogStructure.stalkAlpha (s ≫ U.hom)) m = b :=
    (MulEquiv.ofBijective _ (M.unitsBijective Ω (s ≫ U.hom))).apply_symm_apply b
  have h : Units.map (localStalkIso M U N e s).hom.hom n = m := by
    apply (M.unitsBijective Ω (s ≫ U.hom)).1
    apply Units.ext
    change M.toEtalePrelogStructure.stalkAlpha (s ≫ U.hom)
      ((localStalkIso M U N e s).hom n.val) = _
    exact (DFunLike.congr_fun (localStalkIso_alpha M U N e s) n.val).trans
      ((congrArg (fun a : (strictLocalRing U.left s)ˣ ↦
      (restrictionRingStalkIso U s).hom a.val) hn).trans (congrArg Units.val hm).symm)
  exact congrArg Units.val h

private theorem chartAt_congr {T : Scheme.{u}} (M : EtaleLogStructure T)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] {t t' : Spec (.of Ω) ⟶ T}
    (h : t = t') (W : T.Etale) (w : (Scheme.pointSmallEtale t).fiber.obj W)
    (w' : (Scheme.pointSmallEtale t').fiber.obj W) (hw : w.left = w'.left)
    {P : Type u} [CommMonoid P] (β : P →* M.monoidSheaf.obj.obj (op W)) :
    M.IsStalkChart t ((M.toEtalePrelogStructure.germ t W w).hom.comp β) →
      M.IsStalkChart t' ((M.toEtalePrelogStructure.germ t' W w').hom.comp β) := by
  subst t'
  have he : w = w' := Over.OverMorphism.ext hw
  subst w'
  exact id

/-- A single chart on a log structure identified with the restriction of `M` is
also a chart of `M` on the composite test object. No covering or finiteness
hypothesis is needed.

Source: ILO VI 1.1 and VIII 3.3.4(ii); Stacks, Tag 03EH.
(blueprint: lem-trf-log-condition-fine-chart-locality).

Proof: fix a geometric point `t` and a lift to the composite test object `V`.
Composing that lift with `V.hom` gives a geometric point `s` of `U.left`.
Pointed étale neighbourhoods of `s` identify with the slice of pointed étale
neighbourhoods of `t` over `(U,s)`. The slice forgetful functor is initial,
since the neighbourhood category is cofiltered. Its opposite is final, so
restriction induces canonical isomorphisms of the monoid stalks and of the
structure-ring stalks, carrying every germ to the same section's germ.
The given prelog isomorphism induces a monoid-stalk isomorphism compatible
with these ring isomorphisms. By uniqueness in the log-unit axiom it carries
the canonical units to the corresponding units. Thus the product map from
`P` times ring units is the original chart product map composed with these
isomorphisms. Its surjectivity is preserved. Its kernel is the pushout
congruence: the isomorphism on units takes each generating relation
`(pq,a) ~ (p,alpha(q)*a)` to the identical relation in the target ring,
and the inverse takes generators back. These are precisely the two
conditions in `IsStalkChart`. Apply the local chart hypothesis at `s` and
the original lift to `V`; this proves `IsChart` on the composite object. -/
private theorem EtaleLogStructure.isChart_of_etaleLocalization
    {T : Scheme.{u}} (M : EtaleLogStructure T) (U : T.Etale)
    (N : EtaleLogStructure U.left)
    (e : EtalePrelogStructure.Iso N.toEtalePrelogStructure
      (M.toEtalePrelogStructure.etaleRestrict U))
    (V : U.left.Etale) {P : Type u} [CommMonoid P]
    (β : P →* N.monoidSheaf.obj.obj (op V)) (hchart : N.IsChart V β) :
    M.IsChart (Scheme.Etale.mk (V.hom ≫ U.hom))
      ((e.iso.hom.app (op V)).hom.comp β) := by
  intro Ω _ _ t w
  obtain ⟨w : Spec (.of Ω) ⟶ V.left,
    rfl : w ≫ (V.hom ≫ U.hom) = t, rfl⟩ := Over.homMk_surjective w
  let s := w ≫ V.hom
  let v : (Scheme.pointSmallEtale s).fiber.obj V := Over.homMk w rfl
  let E := (localStalkIso M U N e s).commMonCatIsoToMulEquiv
  let R := (restrictionRingStalkIso U s).commRingCatIsoToRingEquiv
  let b := (N.toEtalePrelogStructure.germ s V v).hom.comp β
  let c := (M.toEtalePrelogStructure.germ (s ≫ U.hom)
    (Scheme.Etale.mk (V.hom ≫ U.hom)) (Over.homMk w (Category.assoc _ _ _).symm)).hom.comp
      ((e.iso.hom.app (op V)).hom.comp β)
  have hc : c = E.toMonoidHom.comp b := by
    ext p
    exact (congrArg (fun f ↦ f (β p)) (localStalkIso_germ M U N e s V v)).symm
  apply chartAt_congr M (Category.assoc w V.hom U.hom)
    (Scheme.Etale.mk (V.hom ≫ U.hom))
    (Over.homMk w (Category.assoc w V.hom U.hom).symm) (Over.homMk w rfl) rfl
    ((e.iso.hom.app (op V)).hom.comp β)
  exact chartTransport R E (N.toEtalePrelogStructure.stalkAlpha s)
    (M.toEtalePrelogStructure.stalkAlpha (s ≫ U.hom)) (N.unitsIn s)
    (M.unitsIn (s ≫ U.hom)) b c (localStalkIso_alpha M U N e s)
    (localStalkIso_units M U N e s) hc (hchart Ω s v)


/-- The map from sections whose image is a unit to unit sections. It is the
sectionwise underlying function of the canonical map of monoid sheaves.
Source: ILO VI 1.1 (blueprint: lem-trf-log-condition-fine-chart-locality). -/
noncomputable def EtalePrelogStructure.unitSectionMap {T : Scheme.{u}} (M : EtalePrelogStructure T)
    (W : T.Etale) :
    {m : M.monoidSheaf.obj.obj (op W) // IsUnit (M.alpha.app (op W) m)} →
      {r : Γ(W.left, ⊤) // IsUnit r} :=
  fun m ↦ ⟨M.alpha.app (op W) m.val, m.property⟩

/-- The log-unit condition descends along an arbitrary jointly surjective étale family.
The global log structure has precisely the given prelog sheaf and structural map.

Source: ILO VI 1.1 and VIII 3.3.8; Stacks, Tags 0217 and 00VM
(blueprint: lem-trf-log-condition-fine-chart-locality).

Proof (steps 1--2 of the node): lift each geometric point to a member of the cover.
The canonical monoid- and ring-stalk comparisons for étale restriction commute with
the structural maps. Transport reflection of units and bijectivity on unit groups
through these comparisons. These two proof fields equip exactly the given prelog
structure with a global log structure. The existing unique unit-section lifting
theorem then gives injectivity and surjectivity of `unitSectionMap` on every test
object: uniqueness identifies sections with the same unit image, and existence
supplies a section over every ring unit. -/
theorem logCondition_etale_local
    {T : Scheme.{u}} [IsLocallyNoetherian T] {ι : Type v} (U : ι → T.Etale)
    (hcover : ∀ x : T, ∃ (a : ι) (y : (U a).left), (U a).hom y = x)
    (M : EtalePrelogStructure T)
    (hlocal : ∀ a : ι, ∃ N : EtaleLogStructure (U a).left,
      N.toEtalePrelogStructure = M.etaleRestrict (U a)) :
    (∀ W : T.Etale, Function.Bijective (M.unitSectionMap W)) ∧
      ∃ N : EtaleLogStructure T, N.toEtalePrelogStructure = M := by
  have hfields (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T) :
      (∀ m : M.stalk t, IsUnit (M.stalkAlpha t m) → IsUnit m) ∧
        Function.Bijective (Units.map (M.stalkAlpha t)) := by
    obtain ⟨a, y, hy⟩ := hcover (t default)
    obtain ⟨s, hs, -⟩ := Scheme.exists_fac_of_etale_of_isSepClosed (U a).hom t y hy
    rw [← hs]
    obtain ⟨⟨L, hreflect, hbij⟩, hL⟩ := hlocal a
    change L = M.etaleRestrict (U a) at hL
    subst L
    let E := (restrictionMonoidStalkIso M (U a) s).commMonCatIsoToMulEquiv
    let R := (restrictionRingStalkIso (U a) s).commRingCatIsoToRingEquiv
    have hα : (M.stalkAlpha (s ≫ (U a).hom)).comp E.toMonoidHom =
        R.toMonoidHom.comp ((M.etaleRestrict (U a)).stalkAlpha s) :=
      restrictionStalk_alpha M (U a) s
    constructor
    · intro m hm
      have hn : IsUnit ((M.etaleRestrict (U a)).stalkAlpha s (E.symm m)) := by
        apply (MulEquiv.isUnit_map (f := R.toMulEquiv)).mp
        have he := DFunLike.congr_fun hα (E.symm m)
        change M.stalkAlpha (s ≫ (U a).hom) (E (E.symm m)) = _ at he
        exact (he.symm.trans (congrArg (M.stalkAlpha (s ≫ (U a).hom))
          (E.apply_symm_apply m))).symm ▸ hm
      have hn' := hreflect Ω s (E.symm m) hn
      exact E.apply_symm_apply m ▸ hn'.map E.toMonoidHom
    · have hunit : (Units.map (M.stalkAlpha (s ≫ (U a).hom))).comp
          (Units.map E.toMonoidHom) =
        (Units.map R.toMonoidHom).comp
          (Units.map ((M.etaleRestrict (U a)).stalkAlpha s)) := by
        ext z
        exact DFunLike.congr_fun hα z.val
      have hcomp : Function.Bijective
          ((Units.map (M.stalkAlpha (s ≫ (U a).hom))).comp
            (Units.map E.toMonoidHom)) := by
        rw [hunit]
        exact (Units.mapEquiv R.toMulEquiv).bijective.comp (hbij Ω s)
      exact (Function.Bijective.of_comp_iff _ (Units.mapEquiv E).bijective).mp hcomp
  let N : EtaleLogStructure T :=
    { toEtalePrelogStructure := M
      reflectsUnits := fun Ω _ _ t ↦ (hfields Ω t).1
      unitsBijective := fun Ω _ _ t ↦ (hfields Ω t).2 }
  refine ⟨?_, N, rfl⟩
  intro W
  constructor
  · intro m n h
    obtain ⟨z, hz, huniq⟩ := N.existsUnique_unit_section_lift (op W)
      m.property.unit
    apply Subtype.ext
    exact (huniq m.val (IsUnit.unit_spec m.property).symm).trans
      (huniq n.val ((congrArg Subtype.val h).symm.trans
        (IsUnit.unit_spec m.property).symm)).symm
  · intro r
    obtain ⟨m, hm, -⟩ := N.existsUnique_unit_section_lift (op W) r.property.unit
    refine ⟨⟨m, ?_⟩, ?_⟩
    · exact hm.symm ▸ r.property.unit.isUnit
    · apply Subtype.ext
      exact hm.trans (IsUnit.unit_spec r.property)

/-- Local charts, including charts on isomorphic local log structures, are the same
charts on the composite étale covering. Fine and fine saturated therefore descend.

Source: ILO VI 1.1 and VIII 3.3.4(ii), 3.3.8; Stacks, Tag 0217
(blueprint: lem-trf-log-condition-fine-chart-locality).

Proof (steps 3--4 of the node): compose the two jointly surjective étale families by
`lem-weil-pbc-etale-covering-composition`. The canonical monoid- and ring-stalk
comparisons carry the chart section on the localization to its germ on the composite
test object. Compatibility with the structural maps and uniqueness of log units
identify the chart product maps through these isomorphisms. Surjectivity and the
generated chart congruence are preserved, so the chart monoid is unchanged.
The composed covering and the finitely generated integral monoids give `IsFine`.
If all monoids are saturated, the identical witnesses give `IsFineSaturated`. -/
theorem fineChart_etale_local
    {T : Scheme.{u}} [IsLocallyNoetherian T] {ι : Type v} (U : ι → T.Etale)
    (hcover : ∀ x : T, ∃ (a : ι) (y : (U a).left), (U a).hom y = x)
    (M : EtaleLogStructure T) (N : ∀ a : ι, EtaleLogStructure (U a).left)
    (e : ∀ a : ι,
      EtalePrelogStructure.Iso (N a).toEtalePrelogStructure
        (M.toEtalePrelogStructure.etaleRestrict (U a)))
    (J : ι → Type w) (V : ∀ a : ι, J a → (U a).left.Etale)
    (hcoverV : ∀ (a : ι) (x : (U a).left),
      ∃ (j : J a) (y : (V a j).left), (V a j).hom y = x)
    (P : ∀ (a : ι), J a → Type u) [hP : ∀ (a : ι) (j : J a), CommMonoid (P a j)]
    (β : ∀ (a : ι) (j : J a), P a j →* (N a).monoidSheaf.obj.obj (op (V a j)))
    (hfg : ∀ (a : ι) (j : J a), Monoid.FG (P a j))
    (hintegral : ∀ (a : ι) (j : J a),
      Function.Injective (Algebra.GrothendieckGroup.of (M := P a j)))
    (hchart : ∀ (a : ι) (j : J a), (N a).IsChart (V a j) (β a j)) :
    (∀ x : T, ∃ (a : ι) (j : J a) (y : (V a j).left),
      ((V a j).hom ≫ (U a).hom) y = x) ∧
    (∀ (a : ι) (j : J a),
      M.IsChart (Scheme.Etale.mk ((V a j).hom ≫ (U a).hom))
        (((e a).iso.hom.app (op (V a j))).hom.comp (β a j))) ∧
    M.IsFine ∧
    ((∀ (a : ι) (j : J a), IsFineSaturatedMonoid (P a j)) → M.IsFineSaturated) := by
  have hcomposite : ∀ x : T, ∃ (a : ι) (j : J a) (y : (V a j).left),
      ((V a j).hom ≫ (U a).hom) y = x := by
    intro x
    obtain ⟨a, z, hz⟩ := hcover x
    obtain ⟨j, y, hy⟩ := hcoverV a z
    refine ⟨a, j, y, ?_⟩
    change (U a).hom ((V a j).hom y) = x
    rw [hy]
    exact hz
  have hcharts : ∀ (a : ι) (j : J a),
      M.IsChart (Scheme.Etale.mk ((V a j).hom ≫ (U a).hom))
        (((e a).iso.hom.app (op (V a j))).hom.comp (β a j)) := by
    intro a j
    exact M.isChart_of_etaleLocalization (U a) (N a) (e a) (V a j) (β a j) (hchart a j)
  have hpoint : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (t : Spec (.of Ω) ⟶ T), ∃ (a : ι) (j : J a),
        Nonempty ((Scheme.pointSmallEtale t).fiber.obj
          (Scheme.Etale.mk ((V a j).hom ≫ (U a).hom))) := by
    intro Ω _ _ t
    obtain ⟨a, j, y, hy⟩ := hcomposite (t default)
    obtain ⟨l, hl, -⟩ := Scheme.exists_fac_of_etale_of_isSepClosed
      ((V a j).hom ≫ (U a).hom) t y hy
    exact ⟨a, j, ⟨Over.homMk l hl⟩⟩
  refine ⟨hcomposite, hcharts, ?_, ?_⟩
  · intro Ω _ _ t
    obtain ⟨a, j, ⟨w⟩⟩ := hpoint Ω t
    exact ⟨Scheme.Etale.mk ((V a j).hom ≫ (U a).hom), w, P a j,
      hP a j, ((e a).iso.hom.app (op (V a j))).hom.comp (β a j),
      hfg a j, hintegral a j, hcharts a j⟩
  · intro hsat Ω _ _ t
    obtain ⟨a, j, ⟨w⟩⟩ := hpoint Ω t
    exact ⟨Scheme.Etale.mk ((V a j).hom ≫ (U a).hom), w, P a j,
      hP a j, ((e a).iso.hom.app (op (V a j))).hom.comp (β a j),
      hsat a j, hcharts a j⟩

private theorem prelogIsoStalk_units {T : Scheme.{u}} (N M : EtaleLogStructure T)
    (e : EtalePrelogStructure.Iso N.toEtalePrelogStructure M.toEtalePrelogStructure)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T)
    (a : (strictLocalRing T t)ˣ) :
    (prelogIsoStalk e t).hom (N.unitsIn t a) = M.unitsIn t a := by
  let n := (MulEquiv.ofBijective (Units.map (N.toEtalePrelogStructure.stalkAlpha t))
    (N.unitsBijective Ω t)).symm a
  let m := (MulEquiv.ofBijective (Units.map (M.toEtalePrelogStructure.stalkAlpha t))
    (M.unitsBijective Ω t)).symm a
  have hn : Units.map (N.toEtalePrelogStructure.stalkAlpha t) n = a :=
    (MulEquiv.ofBijective (Units.map (N.toEtalePrelogStructure.stalkAlpha t))
      (N.unitsBijective Ω t)).apply_symm_apply a
  have hm : Units.map (M.toEtalePrelogStructure.stalkAlpha t) m = a :=
    (MulEquiv.ofBijective (Units.map (M.toEtalePrelogStructure.stalkAlpha t))
      (M.unitsBijective Ω t)).apply_symm_apply a
  have h : Units.map (prelogIsoStalk e t).hom.hom n = m := by
    apply (M.unitsBijective Ω t).1
    apply Units.ext
    change M.toEtalePrelogStructure.stalkAlpha t ((prelogIsoStalk e t).hom n.val) =
      M.toEtalePrelogStructure.stalkAlpha t m.val
    have hα := DFunLike.congr_fun (prelogIsoStalk_alpha e t) n.val
    exact hα.trans ((congrArg Units.val hn).trans (congrArg Units.val hm).symm)
  exact congrArg Units.val h

/-- Composing any chart with an isomorphism over the structure sheaf preserves its
chart monoid, without requiring finiteness, integrality or saturation.

Source: ILO VI 1.1 and VIII 3.3.4(i)--(ii)
(blueprint: lem-trf-log-condition-fine-chart-locality).

Proof (step 4 of the node): at each geometric point, compatibility with the structure
sheaf leaves the ring-valued chart map unchanged. The isomorphism takes ring units
to the same log units by the log axiom. The induced pushout map is the composite
of the original chart isomorphism and the stalk isomorphism, hence is an isomorphism. -/
theorem EtaleLogStructure.isChart_comp_prelogIso
    {T : Scheme.{u}} [IsLocallyNoetherian T] (N M : EtaleLogStructure T)
    (e : EtalePrelogStructure.Iso N.toEtalePrelogStructure M.toEtalePrelogStructure)
    (W : T.Etale) {P : Type u} [CommMonoid P]
    (β : P →* N.monoidSheaf.obj.obj (op W)) (hchart : N.IsChart W β) :
    M.IsChart W ((e.iso.hom.app (op W)).hom.comp β) := by
  intro Ω _ _ t w
  let E := (prelogIsoStalk e t).commMonCatIsoToMulEquiv
  let b := (N.toEtalePrelogStructure.germ t W w).hom.comp β
  let c := (M.toEtalePrelogStructure.germ t W w).hom.comp
    ((e.iso.hom.app (op W)).hom.comp β)
  have hc : c = E.toMonoidHom.comp b := by
    ext p
    exact (congrArg (fun f ↦ f (β p)) (prelogIsoStalk_germ e t W w)).symm
  have hu : M.unitsIn t = E.toMonoidHom.comp (N.unitsIn t) := by
    ext a
    exact (prelogIsoStalk_units N M e t a).symm
  have hpair : c.coprod (M.unitsIn t) = E.toMonoidHom.comp (b.coprod (N.unitsIn t)) := by
    rw [hc, hu]
    ext p
    simp only [MonoidHom.coprod_apply, MonoidHom.comp_apply, map_mul]
  have hα : (M.toEtalePrelogStructure.stalkAlpha t).comp c =
      (N.toEtalePrelogStructure.stalkAlpha t).comp b := by
    rw [hc, ← MonoidHom.comp_assoc]
    exact congrArg (fun f ↦ f.comp b) (prelogIsoStalk_alpha e t)
  obtain ⟨hsurj, hker⟩ := hchart Ω t w
  constructor
  · rw [hpair]
    exact E.surjective.comp hsurj
  · change Con.ker (c.coprod (M.unitsIn t)) = _
    rw [hα, ← hker]
    ext x y
    change c.coprod (M.unitsIn t) x = c.coprod (M.unitsIn t) y ↔
      b.coprod (N.unitsIn t) x = b.coprod (N.unitsIn t) y
    rw [hpair]
    exact E.injective.eq_iff

end AlgebraicGeometry
