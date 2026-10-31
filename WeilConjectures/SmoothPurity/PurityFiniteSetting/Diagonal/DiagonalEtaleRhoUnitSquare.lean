/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.DiagonalEtaleComparison.DiagonalEtaleRestrictedDualizingData
import all WeilConjectures.AlgebraicGeometry.Section.SectionExceptionalFibreCoherence
import all WeilConjectures.SmoothPurity.PurityFiniteSetting.DiagonalEtaleComparison.DiagonalEtaleSourceEndpoint
import all WeilConjectures.SmoothPurity.PurityFiniteSetting.SectionRestriction.PuritySectionRestrictionEtaleFunctorial
import all WeilConjectures.SmoothPurity.PurityFiniteSetting.SectionRestriction.PuritySectionBaseComparisonLaws
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Dnc.ComparisonPullbackDerivedCoherence
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Diagonal.DiagonalEtaleLocalityUnitChange
import WeilConjectures.SmoothPurity.PurityFiniteSetting.ComparisonPullbackRestrictionCoherence
import all Mathlib.CategoryTheory.Limits.HasLimits
import all Mathlib.Logic.Small.Defs

/-! # Target-open locality and coefficient-unit change

Source: diagonal-dualizing proof Steps 1--2; orientation-charts proof Step 3.
(blueprint: lem-pur-diagonal-etale-rho-unit-square).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option maxRecDepth 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting

attribute [local irreducible] Etale.upperStar Etale.lowerStar
  Etale.rightDerivedUpperShriek Etale.rightDerivedUpperShriekAdjunction
  Functor.mapDerivedCategory Functor.rightDerivedFunctor conjugateIsoEquiv

private theorem locality_comp (P : PurityFiniteSetting.{u})
    {W X Y Z : Scheme.{u}}
    [W.Over (Spec (.of P.field.k))] [X.Over (Spec (.of P.field.k))]
    [Y.Over (Spec (.of P.field.k))] [Z.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (W ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
    [QuasiCompact (W ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z ↘ Spec (.of P.field.k))]
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    (h' : X ⟶ Z) (h'' : W ⟶ Z)
    [f.IsOver (Spec (.of P.field.k))] [g.IsOver (Spec (.of P.field.k))]
    [h.IsOver (Spec (.of P.field.k))] [h'.IsOver (Spec (.of P.field.k))]
    [h''.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] [Etale f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g] [Etale g]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [IsSeparated h'] [LocallyOfFiniteType h'] [QuasiCompact h']
    [IsSeparated h''] [LocallyOfFiniteType h''] [QuasiCompact h'']
    [IsNoetherian W] [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
    [HasCompactification h] [HasCompactification h'] [HasCompactification h'']
    (w : h' = g ≫ h) (w' : h'' = f ≫ h') :
    (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).leftDerivedFunctor.mapIso
        (Etale.sectionStructuralLocalityIso P.Coefficient g h h' w.symm) ≪≫
      Etale.sectionStructuralLocalityIso P.Coefficient f h' h'' w'.symm =
    (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) f g).symm.app
        (Etale.dualizingComplex P.Coefficient h) ≪≫
      Etale.sectionStructuralLocalityIso P.Coefficient (f ≫ g) h h''
        (by rw [Category.assoc, ← w, ← w']) := by
  have hs := SectionRestriction.source_comp_eq P f g h h' h'' w w'
  rw [SectionRestriction.sourceEtale_locality_congr P (f ≫ g) h h''
      (by rw [Category.assoc, ← w, ← w']),
    SectionRestriction.sourceEtale_locality_congr P f h' h'' w'.symm,
    SectionRestriction.sourceEtale_locality_congr P g h h' w.symm] at hs
  have hi := congrArg Iso.symm hs
  simp only [Iso.trans_symm, Iso.symm_symm_eq, Functor.mapIso_symm] at hi
  exact hi.symm

private theorem locality_comp_field (P : PurityFiniteSetting.{u})
    {W X Y Z : Scheme.{u}}
    (aZ : Z ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aZ] [QuasiCompact aZ]
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    (h' : X ⟶ Z) (h'' : W ⟶ Z)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] [Etale f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g] [Etale g]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [IsSeparated h'] [LocallyOfFiniteType h'] [QuasiCompact h']
    [IsSeparated h''] [LocallyOfFiniteType h''] [QuasiCompact h'']
    [IsNoetherian W] [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
    [HasCompactification h] [HasCompactification h'] [HasCompactification h'']
    (w : h' = g ≫ h) (w' : h'' = f ≫ h') :
    (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).leftDerivedFunctor.mapIso
        (Etale.sectionStructuralLocalityIso P.Coefficient g h h' w.symm) ≪≫
      Etale.sectionStructuralLocalityIso P.Coefficient f h' h'' w'.symm =
    (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) f g).symm.app
        (Etale.dualizingComplex P.Coefficient h) ≪≫
      Etale.sectionStructuralLocalityIso P.Coefficient (f ≫ g) h h''
        (by rw [Category.assoc, ← w, ← w']) := by
  let : Z.Over (Spec (.of P.field.k)) := ⟨aZ⟩
  let : Y.Over (Spec (.of P.field.k)) := ⟨h ≫ aZ⟩
  let : X.Over (Spec (.of P.field.k)) := ⟨g ≫ h ≫ aZ⟩
  let : W.Over (Spec (.of P.field.k)) := ⟨f ≫ g ≫ h ≫ aZ⟩
  let : LocallyOfFiniteType (Z ↘ Spec (.of P.field.k)) := ‹LocallyOfFiniteType aZ›
  let : QuasiCompact (Z ↘ Spec (.of P.field.k)) := ‹QuasiCompact aZ›
  let : LocallyOfFiniteType (Y ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType (h ≫ aZ))
  let : QuasiCompact (Y ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (QuasiCompact (h ≫ aZ))
  let : LocallyOfFiniteType (X ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType (g ≫ h ≫ aZ))
  let : QuasiCompact (X ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (QuasiCompact (g ≫ h ≫ aZ))
  let : LocallyOfFiniteType (W ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType (f ≫ g ≫ h ≫ aZ))
  let : QuasiCompact (W ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (QuasiCompact (f ≫ g ≫ h ≫ aZ))
  let : h.IsOver (Spec (.of P.field.k)) := ⟨rfl⟩
  let : g.IsOver (Spec (.of P.field.k)) := ⟨rfl⟩
  let : f.IsOver (Spec (.of P.field.k)) := ⟨rfl⟩
  let : h'.IsOver (Spec (.of P.field.k)) := ⟨by
    change h' ≫ aZ = g ≫ h ≫ aZ
    rw [w, Category.assoc]⟩
  let : h''.IsOver (Spec (.of P.field.k)) := ⟨by
    change h'' ≫ aZ = f ≫ g ≫ h ≫ aZ
    rw [w', w, Category.assoc, Category.assoc]⟩
  exact locality_comp P f g h h' h'' w w'

private theorem pull_square_factor (A : Type (u + 1)) [CommRing A]
    {O Q U W X : Scheme.{u}} (k : O ⟶ Q) (r : Q ⟶ U) (s : Q ⟶ W)
    (j : U ⟶ X) (b : W ⟶ X) (t : O ⟶ U) (l : O ⟶ W)
    (hr : r ≫ j = s ≫ b) (hk : k ≫ r = t) (hl : k ≫ s = l)
    (ht : l ≫ b = t ≫ j) (M : Etale.DerivedCategoryModule A X) :
    (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) k s l hl.symm).hom.app
        ((Etale.upperStar (ModuleCat.{u + 1} A) b).leftDerivedFunctor.obj M) ≫
      (Etale.upperStar (ModuleCat.{u + 1} A) k).leftDerivedFunctor.map
        (Etale.sectionCoherencePullbackIso A r j s b hr M).inv =
    (Etale.sectionCoherencePullbackIso A l b t j ht M).hom ≫
      (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) k r t hk.symm).hom.app
        ((Etale.upperStar (ModuleCat.{u + 1} A) j).leftDerivedFunctor.obj M) := by
  have ha := Etale.leftDerivedUpperStarComp_assoc'_app (ModuleCat.{u + 1} A)
    k s b l (s ≫ b) (l ≫ b) hl.symm rfl rfl M
  have hb := Etale.leftDerivedUpperStarComp_assoc'_app (ModuleCat.{u + 1} A)
    k r j t (s ≫ b) (l ≫ b) hk.symm hr.symm ht M
  have he := Etale.sectionPullback_endpoint A r j s b (r ≫ j) (s ≫ b)
    rfl hr hr.symm rfl M
  change Etale.sectionCoherencePullbackIso A r j s b hr M = _ at he
  rw [he]
  apply (cancel_epi
    ((Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) l b).hom.app M)).mp
  simp only [Etale.sectionCoherencePullbackIso, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv, Iso.app_hom, Iso.app_inv, NatTrans.comp_app, Functor.map_comp,
    Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [← reassoc_of% ha]
  have hc := ((Etale.upperStar (ModuleCat.{u + 1} A) k).leftDerivedFunctor.mapIso
    ((Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) s b).app M)).hom_inv_id
  simp only [Functor.mapIso_hom, Functor.mapIso_inv, Iso.app_hom, Iso.app_inv] at hc
  rw [reassoc_of% hc]
  exact hb

private theorem paste_open_locality {C : Type*} [Category C]
    {A B D E H J K L M Q : C}
    {α : A ⟶ B} {ℓ₀ : B ⟶ D} {β : E ⟶ H} {ℓ : H ⟶ Q}
    {ℓ₁ : J ⟶ E} {β₁ : K ⟶ L} {ℓ₂ : L ⟶ H} {β₀ : A ⟶ M} {ℓ₃ : M ⟶ Q}
    (c₀ : D ≅ E) (c₁ : B ≅ J) (d₀ : A ≅ K) (e : J ≅ K) (d₁ : M ≅ L)
    (hn : ℓ₀ ≫ c₀.hom = c₁.hom ≫ ℓ₁)
    (hp : d₀.hom ≫ e.inv = α ≫ c₁.hom)
    (hb : e.hom ≫ β₁ ≫ ℓ₂ = ℓ₁ ≫ β)
    (hc : ℓ₂ ≫ ℓ = d₁.inv ≫ ℓ₃)
    (hn' : β₀ ≫ d₁.hom = d₀.hom ≫ β₁) :
    α ≫ ℓ₀ ≫ c₀.hom ≫ β ≫ ℓ = β₀ ≫ ℓ₃ := by
  rw [reassoc_of% hn, ← reassoc_of% hp, ← reassoc_of% hb,
    Iso.inv_hom_id_assoc, hc, ← reassoc_of% hn', Iso.hom_inv_id_assoc]

@[irreducible]
private def openDualizingMap (P : PurityFiniteSetting.{u})
    {U Y : Scheme.{u}} [IsNoetherian U] [IsNoetherian Y]
    (h : U ⟶ Y) [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [HasCompactification h]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (V : Y.Opens) (O : U.Opens) (q : O.toScheme ⟶ V.toScheme)
    [IsSeparated q] [LocallyOfFiniteType q] [QuasiCompact q] [HasCompactification q]
    (hq : O.ι ≫ h = q ≫ V.ι) :
    (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) O.ι).leftDerivedFunctor.obj
        (Etale.dualizingComplex P.Coefficient h) ≅
      Etale.dualizingComplex P.Coefficient q := by
  let sq := (isPullback_morphismRestrict h V).flip
  let k := sq.lift O.ι q hq
  have hk : k ≫ (h ⁻¹ᵁ V).ι = O.ι := sq.lift_fst _ _ _
  have hkv : k ≫ (h ∣_ V) = q := sq.lift_snd _ _ _
  have : IsOpenImmersion (k ≫ (h ⁻¹ᵁ V).ι) := by rw [hk]; infer_instance
  have : IsOpenImmersion k := IsOpenImmersion.of_comp k (h ⁻¹ᵁ V).ι
  let := P.noetherian (V.ι ≫ aY)
  let := P.noetherian ((h ∣_ V) ≫ V.ι ≫ aY)
  let := P.noetherian (O.ι ≫ h ≫ aY)
  let := Dnc.compactifiable P (h ∣_ V) (V.ι ≫ aY)
  let := Etale.isIso_rightDerivedUpperShriekBaseChangeMap_of_isOpenImmersion
    P.Coefficient sq
  let := (Etale.isIso_dualizingComplexBaseChangeMap_iff P.Coefficient sq).2
    (inferInstanceAs (IsIso
      ((Etale.rightDerivedUpperShriekBaseChangeMap P.Coefficient sq).app (𝟙_ _))))
  exact (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
      k (h ⁻¹ᵁ V).ι O.ι hk.symm).app _ ≪≫
    (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) k).leftDerivedFunctor.mapIso
      (asIso (Etale.dualizingComplexBaseChangeMap P.Coefficient sq)) ≪≫
    Etale.sectionStructuralLocalityIso P.Coefficient k (h ∣_ V) q hkv

private theorem open_locality (P : PurityFiniteSetting.{u})
    {U X Y : Scheme.{u}} [IsNoetherian U] [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [HasCompactification f]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (V : Y.Opens)
    (j : U ⟶ X) [Etale j] [IsSeparated j] [LocallyOfFiniteType j] [QuasiCompact j]
    (h : U ⟶ Y) [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [HasCompactification h] (he : j ≫ f = h)
    (O : U.Opens) (jO : O.toScheme ⟶ (f ⁻¹ᵁ V).toScheme)
    [Etale jO] [IsSeparated jO] [LocallyOfFiniteType jO] [QuasiCompact jO]
    (q : O.toScheme ⟶ V.toScheme)
    [IsSeparated q] [LocallyOfFiniteType q] [QuasiCompact q] [HasCompactification q]
    (hj : jO ≫ (f ⁻¹ᵁ V).ι = O.ι ≫ j) (hq : jO ≫ (f ∣_ V) = q) :
    let := Dnc.compactifiable P (f ∣_ V) (V.ι ≫ aY)
    let := P.noetherian (V.ι ≫ aY)
    let := P.noetherian ((f ∣_ V) ≫ V.ι ≫ aY)
    let := P.noetherian (O.ι ≫ h ≫ aY)
    (Etale.sectionCoherencePullbackIso P.Coefficient jO (f ⁻¹ᵁ V).ι O.ι j hj
      (Etale.dualizingComplex P.Coefficient f)).hom ≫
      (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) O.ι).leftDerivedFunctor.map
        (Etale.sectionStructuralLocalityIso P.Coefficient j f h he).hom ≫
      (openDualizingMap P h aY V O q (by
        rw [← he, ← Category.assoc, ← hj, Category.assoc,
          ← morphismRestrict_ι, ← Category.assoc, hq])).hom =
    (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) jO).leftDerivedFunctor.map
        (Etale.dualizingComplexBaseChangeMap P.Coefficient
          (isPullback_morphismRestrict f V).flip) ≫
      (Etale.sectionStructuralLocalityIso P.Coefficient jO (f ∣_ V) q hq).hom := by
  let := P.noetherian (V.ι ≫ aY)
  let := P.noetherian ((f ∣_ V) ≫ V.ι ≫ aY)
  let := P.noetherian ((h ∣_ V) ≫ V.ι ≫ aY)
  let := P.noetherian (O.ι ≫ h ≫ aY)
  let := Dnc.compactifiable P (f ∣_ V) (V.ι ≫ aY)
  let := Dnc.compactifiable P (h ∣_ V) (V.ι ≫ aY)
  let sqf := (isPullback_morphismRestrict f V).flip
  let sqh := (isPullback_morphismRestrict h V).flip
  let jV := sqf.lift ((h ⁻¹ᵁ V).ι ≫ j) (h ∣_ V) (by
    rw [Category.assoc, he]
    exact sqh.w)
  have hjV : jV ≫ (f ⁻¹ᵁ V).ι = (h ⁻¹ᵁ V).ι ≫ j := sqf.lift_fst _ _ _
  have hjVf : jV ≫ (f ∣_ V) = h ∣_ V := sqf.lift_snd _ _ _
  have sqj : IsPullback (h ⁻¹ᵁ V).ι jV j (f ⁻¹ᵁ V).ι := by
    have hs : IsPullback (h ⁻¹ᵁ V).ι (jV ≫ (f ∣_ V)) (j ≫ f) V.ι := by
      rw [hjVf, he]
      exact sqh
    exact hs.of_bot hjV.symm sqf
  have : Etale jV := MorphismProperty.of_isPullback sqj inferInstance
  have : IsSeparated jV := MorphismProperty.of_isPullback sqj inferInstance
  have : LocallyOfFiniteType jV := MorphismProperty.of_isPullback sqj inferInstance
  have : QuasiCompact jV := MorphismProperty.of_isPullback sqj inferInstance
  have hqo : O.ι ≫ h = q ≫ V.ι := by
    rw [← he, ← Category.assoc, ← hj, Category.assoc,
      ← morphismRestrict_ι, ← Category.assoc, hq]
  let k := sqh.lift O.ι q hqo
  have hk : k ≫ (h ⁻¹ᵁ V).ι = O.ι := sqh.lift_fst _ _ _
  have hkq : k ≫ (h ∣_ V) = q := sqh.lift_snd _ _ _
  have hkj : k ≫ jV = jO := by
    apply (cancel_mono (f ⁻¹ᵁ V).ι).mp
    rw [Category.assoc, hjV, ← Category.assoc, hk, hj]
  have : IsOpenImmersion (k ≫ (h ⁻¹ᵁ V).ι) := by rw [hk]; infer_instance
  have : IsOpenImmersion k := IsOpenImmersion.of_comp k (h ⁻¹ᵁ V).ι
  have hb := Etale.structural_locality_baseChange P.Coefficient j f jV (f ∣_ V)
    h he (h ∣_ V) hjVf V.ι (f ⁻¹ᵁ V).ι (h ⁻¹ᵁ V).ι sqf sqj sqh
  have hc := locality_comp_field P (V.ι ≫ aY) k jV (f ∣_ V) (h ∣_ V) q
    hjVf.symm hkq.symm
  have hp := pull_square_factor P.Coefficient k (h ⁻¹ᵁ V).ι jV j
    (f ⁻¹ᵁ V).ι O.ι jO sqj.w hk hkj hj
    (Etale.dualizingComplex P.Coefficient f)
  have hc' :
      (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) k).leftDerivedFunctor.map
          (Etale.sectionStructuralLocalityIso P.Coefficient jV (f ∣_ V)
            (h ∣_ V) hjVf).hom ≫
        (Etale.sectionStructuralLocalityIso P.Coefficient k (h ∣_ V) q hkq).hom =
      (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
        k jV jO hkj.symm).inv.app _ ≫
        (Etale.sectionStructuralLocalityIso P.Coefficient jO (f ∣_ V) q hq).hom := by
    subst jO
    exact congrArg Iso.hom hc
  let C := ModuleCat.{u + 1} P.Coefficient
  let F := (Etale.upperStar C k).leftDerivedFunctor
  have hn := (Etale.leftDerivedUpperStarComp C k (h ⁻¹ᵁ V).ι O.ι hk.symm).hom.naturality
    (Etale.sectionStructuralLocalityIso P.Coefficient j f h he).hom
  have hn' := (Etale.leftDerivedUpperStarComp C k jV jO hkj.symm).hom.naturality
    (Etale.dualizingComplexBaseChangeMap P.Coefficient sqf)
  have hbF := congrArg (fun z ↦ F.map z) hb
  simp only [Functor.map_comp] at hbF
  dsimp only [Functor.comp_map] at hn hn'
  unfold openDualizingMap
  change (Etale.sectionCoherencePullbackIso P.Coefficient jO (f ⁻¹ᵁ V).ι O.ι j hj
      (Etale.dualizingComplex P.Coefficient f)).hom ≫
      (Etale.upperStar C O.ι).leftDerivedFunctor.map
        (Etale.sectionStructuralLocalityIso P.Coefficient j f h he).hom ≫
      (Etale.leftDerivedUpperStarComp C k (h ⁻¹ᵁ V).ι O.ι hk.symm).hom.app _ ≫
      F.map (Etale.dualizingComplexBaseChangeMap P.Coefficient sqh) ≫
      (Etale.sectionStructuralLocalityIso P.Coefficient k (h ∣_ V) q hkq).hom = _
  exact paste_open_locality
    ((Etale.leftDerivedUpperStarComp C k (h ⁻¹ᵁ V).ι O.ι hk.symm).app
      (Etale.dualizingComplex P.Coefficient h))
    ((Etale.leftDerivedUpperStarComp C k (h ⁻¹ᵁ V).ι O.ι hk.symm).app
      ((Etale.upperStar C j).leftDerivedFunctor.obj (Etale.dualizingComplex P.Coefficient f)))
    ((Etale.leftDerivedUpperStarComp C k jV jO hkj.symm).app
      ((Etale.upperStar C (f ⁻¹ᵁ V).ι).leftDerivedFunctor.obj
        (Etale.dualizingComplex P.Coefficient f)))
    (F.mapIso (Etale.sectionCoherencePullbackIso P.Coefficient
      (h ⁻¹ᵁ V).ι j jV (f ⁻¹ᵁ V).ι sqj.w (Etale.dualizingComplex P.Coefficient f)))
    ((Etale.leftDerivedUpperStarComp C k jV jO hkj.symm).app
      (Etale.dualizingComplex P.Coefficient (f ∣_ V))) hn hp hbF hc' hn'

private theorem rho_locality (P : PurityFiniteSetting.{u})
    {U X Y : Scheme.{u}} [IsNoetherian U] [IsNoetherian X] [IsNoetherian Y]
    (d : ℕ) (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [SmoothOfRelativeDimension d f] [HasCompactification f]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (V : Y.affineOpens) (H : P.AffineDiagonalGeometry f aY d V)
    (j : U ⟶ X) [Etale j] [IsSeparated j] [LocallyOfFiniteType j] [QuasiCompact j]
    (h : U ⟶ Y) [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [HasCompactification h] (he : j ≫ f = h)
    (O : U.Opens) (jO : O.toScheme ⟶ (f ⁻¹ᵁ V.1).toScheme)
    [Etale jO] [IsSeparated jO] [LocallyOfFiniteType jO] [QuasiCompact jO]
    (q : O.toScheme ⟶ V.1.toScheme)
    [IsSeparated q] [LocallyOfFiniteType q] [QuasiCompact q] [HasCompactification q]
    (hj : jO ≫ (f ⁻¹ᵁ V.1).ι = O.ι ≫ j) (hq : jO ≫ (f ∣_ V.1) = q) :
    let := Dnc.compactifiable P (f ∣_ V.1) (V.1.ι ≫ aY)
    let := P.noetherian (V.1.ι ≫ aY)
    let := P.noetherian ((f ∣_ V.1) ≫ V.1.ι ≫ aY)
    let := P.noetherian (O.ι ≫ h ≫ aY)
    let C := ModuleCat.{u + 1} P.Coefficient
    let νU := (ProEtale.comparisonUpperStar C U).mapDerivedCategory
    let νO := (ProEtale.comparisonUpperStar C O.toScheme).mapDerivedCategory
    (OrientationRefinement.pull P jO).mapIso (OrientationRefinement.rho P f aY d V H) ≪≫
        Dnc.pullComparison P jO (Etale.dualizingComplex P.Coefficient (f ∣_ V.1)) ≪≫
        νO.mapIso (Etale.sectionStructuralLocalityIso P.Coefficient jO (f ∣_ V.1) q hq) =
      (OrientationCounit.restrictionAlong P j (f ⁻¹ᵁ V.1) O jO hj).app
          (Etale.dualizingComplex P.Coefficient f) ≪≫
        (OrientationRefinement.pull P O.ι).mapIso
          (νU.mapIso (Etale.sectionStructuralLocalityIso P.Coefficient j f h he)) ≪≫
        Dnc.pullComparison P O.ι (Etale.dualizingComplex P.Coefficient h) ≪≫
        νO.mapIso (openDualizingMap P h aY V.1 O q (by
          rw [← he, ← Category.assoc, ← hj, Category.assoc,
            ← morphismRestrict_ι, ← Category.assoc, hq])) := by
  let := Dnc.compactifiable P (f ∣_ V.1) (V.1.ι ≫ aY)
  let := P.noetherian (V.1.ι ≫ aY)
  let := P.noetherian ((f ∣_ V.1) ≫ V.1.ι ≫ aY)
  let := P.noetherian (O.ι ≫ h ≫ aY)
  let C := ModuleCat.{u + 1} P.Coefficient
  let νO := (ProEtale.comparisonUpperStar C O.toScheme).mapDerivedCategory
  let := Etale.isIso_rightDerivedUpperShriekBaseChangeMap_of_isOpenImmersion
    P.Coefficient (isPullback_morphismRestrict f V.1).flip
  let := (Etale.isIso_dualizingComplexBaseChangeMap_iff P.Coefficient
    (isPullback_morphismRestrict f V.1).flip).2
    (inferInstanceAs (IsIso ((Etale.rightDerivedUpperShriekBaseChangeMap P.Coefficient
      (isPullback_morphismRestrict f V.1).flip).app (𝟙_ _))))
  let β := asIso (Etale.dualizingComplexBaseChangeMap P.Coefficient
    (isPullback_morphismRestrict f V.1).flip)
  have hn := congrArg Iso.hom (Dnc.pullComparison_naturality P jO β)
  have hm := congrArg Iso.hom (Dnc.pullComparison_naturality P O.ι
    (Etale.sectionStructuralLocalityIso P.Coefficient j f h he))
  simp only [Iso.trans_hom, Functor.mapIso_hom] at hn hm
  have ho := open_locality P f aY V.1 j h he O jO q hj hq
  have hr := diagonalEtaleComparison_restriction P j (f ⁻¹ᵁ V.1) O jO hj
    (Etale.dualizingComplex P.Coefficient f)
  apply Iso.ext
  change (OrientationRefinement.pull P jO).map
      ((Dnc.pullComparison P (f ⁻¹ᵁ V.1).ι (Etale.dualizingComplex P.Coefficient f)).hom ≫
        (ProEtale.comparisonUpperStar C (f ⁻¹ᵁ V.1).toScheme).mapDerivedCategory.map β.hom) ≫
      (Dnc.pullComparison P jO (Etale.dualizingComplex P.Coefficient (f ∣_ V.1))).hom ≫
      νO.map (Etale.sectionStructuralLocalityIso P.Coefficient jO (f ∣_ V.1) q hq).hom = _
  simp only [Functor.map_comp, Category.assoc, Iso.trans_hom, Functor.mapIso_hom]
  rw [reassoc_of% hn, ← νO.map_comp]
  simp only [β, asIso_hom]
  rw [← ho]
  simp only [νO.map_comp]
  dsimp only [C, νO, Etale.ordinaryFinitePullback, OrientationRefinement.pull] at hr ⊢
  rw [reassoc_of% hr, ← reassoc_of% hm]

private theorem rho_unit_locality (P : PurityFiniteSetting.{u})
    {U X Y : Scheme.{u}} [IsNoetherian U] [IsNoetherian X] [IsNoetherian Y]
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient)
    (d : ℕ) (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [SmoothOfRelativeDimension d f] [HasCompactification f]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (V : Y.affineOpens) (H : P.AffineDiagonalGeometry f aY d V)
    (j : U ⟶ X) [Etale j] [IsSeparated j] [LocallyOfFiniteType j] [QuasiCompact j]
    (h : U ⟶ Y) [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [HasCompactification h] [HasCompactification (j ≫ f)] (he : j ≫ f = h)
    (O : U.Opens) (jO : O.toScheme ⟶ (f ⁻¹ᵁ V.1).toScheme)
    [Etale jO] [IsSeparated jO] [LocallyOfFiniteType jO] [QuasiCompact jO]
    (q : O.toScheme ⟶ V.1.toScheme)
    [IsSeparated q] [LocallyOfFiniteType q] [QuasiCompact q] [HasCompactification q]
    (hj : jO ≫ (f ⁻¹ᵁ V.1).ι = O.ι ≫ j) (hq : jO ≫ (f ∣_ V.1) = q) :
    let := Dnc.compactifiable P (f ∣_ V.1) (V.1.ι ≫ aY)
    let := P.noetherian (V.1.ι ≫ aY)
    let := P.noetherian ((f ∣_ V.1) ≫ V.1.ι ≫ aY)
    let := P.noetherian (O.ι ≫ h ≫ aY)
    let C := ModuleCat.{u + 1} P.Coefficient
    let νX := (ProEtale.comparisonUpperStar C X).mapDerivedCategory
    let νU := (ProEtale.comparisonUpperStar C U).mapDerivedCategory
    let νO := (ProEtale.comparisonUpperStar C O.toScheme).mapDerivedCategory
    let rf := (OrientationRefinement.rho P f aY d V H).symm ≪≫
      (OrientationRefinement.pull P (f ⁻¹ᵁ V.1).ι).mapIso
        (νX.mapIso (OrientationCounit.unitChange P f))
    Dnc.pullComparison P jO (Etale.dualizingComplex P.Coefficient (f ∣_ V.1)) ≪≫
        νO.mapIso (Etale.sectionStructuralLocalityIso P.Coefficient jO (f ∣_ V.1) q hq) =
      (OrientationRefinement.pull P jO).mapIso rf ≪≫
        (OrientationCounit.restrictionAlong P j (f ⁻¹ᵁ V.1) O jO hj).app
          (P.diagonalOrdinaryDualizing f) ≪≫
        (OrientationRefinement.pull P O.ι).mapIso
          (νU.mapIso (P.diagonalEtaleLocality N j f ≪≫ P.diagonalDualizingCongr he)) ≪≫
        (OrientationRefinement.pull P O.ι).mapIso
          (νU.mapIso (OrientationCounit.unitChange P h).symm) ≪≫
        Dnc.pullComparison P O.ι (Etale.dualizingComplex P.Coefficient h) ≪≫
        νO.mapIso (openDualizingMap P h aY V.1 O q (by
          rw [← he, ← Category.assoc, ← hj, Category.assoc,
            ← morphismRestrict_ι, ← Category.assoc, hq])) := by
  let := Dnc.compactifiable P (f ∣_ V.1) (V.1.ι ≫ aY)
  let := P.noetherian (V.1.ι ≫ aY)
  let := P.noetherian ((f ∣_ V.1) ≫ V.1.ι ≫ aY)
  let := P.noetherian (O.ι ≫ h ≫ aY)
  let C := ModuleCat.{u + 1} P.Coefficient
  let νX := (ProEtale.comparisonUpperStar C X).mapDerivedCategory
  let νU := (ProEtale.comparisonUpperStar C U).mapDerivedCategory
  let F := OrientationRefinement.pull P jO
  let T := OrientationRefinement.pull P O.ι
  let W := OrientationRefinement.pull P (f ⁻¹ᵁ V.1).ι
  let cj := OrientationCounit.restrictionAlong P j (f ⁻¹ᵁ V.1) O jO hj
  let uf := OrientationCounit.unitChange P f
  let uh := OrientationCounit.unitChange P h
  let ell := P.diagonalEtaleLocality N j f ≪≫ P.diagonalDualizingCongr he
  let loc := Etale.sectionStructuralLocalityIso P.Coefficient j f h he
  have hc : F.mapIso (W.mapIso (νX.mapIso uf)) ≪≫
      cj.app (P.diagonalOrdinaryDualizing f) =
      cj.app (Etale.dualizingComplex P.Coefficient f) ≪≫
        T.mapIso (νU.mapIso ((Etale.ordinaryFinitePullback P.Coefficient j).mapIso uf)) := by
    apply Iso.ext
    exact cj.hom.naturality uf.hom
  have hu : T.mapIso (νU.mapIso
        ((Etale.ordinaryFinitePullback P.Coefficient j).mapIso uf)) ≪≫
        T.mapIso (νU.mapIso ell) ≪≫ T.mapIso (νU.mapIso uh.symm) =
      T.mapIso (νU.mapIso loc) := by
    simp only [← Functor.mapIso_trans, ← Iso.trans_assoc]
    rw [diagonalEtaleLocality_unitChange P N j f h he]
    simp only [uh, loc, Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl]
  let νO := (ProEtale.comparisonUpperStar C O.toScheme).mapDerivedCategory
  let D := Dnc.pullComparison P O.ι (Etale.dualizingComplex P.Coefficient h) ≪≫
    νO.mapIso (openDualizingMap P h aY V.1 O q (by
      rw [← he, ← Category.assoc, ← hj, Category.assoc,
        ← morphismRestrict_ι, ← Category.assoc, hq]))
  have hr := rho_locality P d f aY V H j h he O jO q hj hq
  change F.mapIso (OrientationRefinement.rho P f aY d V H) ≪≫
      (Dnc.pullComparison P jO (Etale.dualizingComplex P.Coefficient (f ∣_ V.1)) ≪≫
        νO.mapIso (Etale.sectionStructuralLocalityIso P.Coefficient jO (f ∣_ V.1) q hq)) =
      cj.app (Etale.dualizingComplex P.Coefficient f) ≪≫ T.mapIso (νU.mapIso loc) ≪≫ D at hr
  have hr' := congrArg
    (fun e ↦ (F.mapIso (OrientationRefinement.rho P f aY d V H)).symm ≪≫ e) hr
  simp only [Iso.symm_self_id_assoc] at hr'
  dsimp only
  change Dnc.pullComparison P jO (Etale.dualizingComplex P.Coefficient (f ∣_ V.1)) ≪≫
      νO.mapIso (Etale.sectionStructuralLocalityIso P.Coefficient jO (f ∣_ V.1) q hq) =
    F.mapIso ((OrientationRefinement.rho P f aY d V H).symm ≪≫
      W.mapIso (νX.mapIso uf)) ≪≫ cj.app (P.diagonalOrdinaryDualizing f) ≪≫
      T.mapIso (νU.mapIso ell) ≪≫ T.mapIso (νU.mapIso uh.symm) ≪≫ D
  rw [hr', F.mapIso_trans]
  simp only [Iso.trans_assoc]
  have hc' := congrArg
    (fun z ↦ F.mapIso (OrientationRefinement.rho P f aY d V H).symm ≪≫ z ≪≫
      T.mapIso (νU.mapIso ell) ≪≫ T.mapIso (νU.mapIso uh.symm) ≪≫ D) hc
  simp only [Iso.trans_assoc] at hc'
  rw [hc']
  have hu' := congrArg
    (fun z ↦ F.mapIso (OrientationRefinement.rho P f aY d V H).symm ≪≫
      cj.app (Etale.dualizingComplex P.Coefficient f) ≪≫ z ≪≫ D) hu
  simpa only [Iso.trans_assoc, Functor.mapIso_symm, F, OrientationRefinement.pull]
    using hu'.symm

private theorem paste_two_squares {C : Type*} [Category C]
    {A B D E F G H I : C}
    (sj : A ≅ I) (sv : D ≅ I) (a : A ≅ B) (b : D ≅ E)
    (cj : B ≅ F) (cv : E ≅ G) (ej : F ≅ H) (ev : G ≅ H) (r : H ≅ I)
    (hj : sj = a ≪≫ cj ≪≫ ej ≪≫ r) (hv : sv = b ≪≫ cv ≪≫ ev ≪≫ r) :
    (sj ≪≫ sv.symm) ≪≫ b = a ≪≫ cj ≪≫ ej ≪≫ ev.symm ≪≫ cv.symm := by
  rw [hj, hv]
  simp only [Iso.trans_symm, Iso.trans_assoc, Iso.self_symm_id_assoc,
    Iso.symm_self_id, Iso.trans_refl]

/-- Target-open rho and coefficient-unit change commute with normalized locality.
This statement concerns dualizing objects only: no diagonal source or alpha occurs.
Source: diagonal-dualizing proof Step 2 and final canonicity paragraph;
orientation-charts proof Step 3, first paragraph.

Proof: first take O to be the full inverse image of the target open under j followed
by f. The squares for j and jO are Cartesian. Apply source-etale/base-change
interchange to their specified compact-support mates, and transpose under the
sum-extension and exceptional adjunctions. This gives compatibility of rho with
the normalized locality maps. For arbitrary O, factor its inclusion through that
full inverse image; locality composition and inverse-image associativity identify
the resulting comparison with restrictionAlong for the actual commuting square.
Apply naturality of the same transformations to the inverse isomorphism from the
monoidal unit to the degree-zero coefficient object. This gives exactly unitChange
on both sides, rather than a chosen identification of dualizing objects. Repeat
for v, and paste through the common restricted source. Equality w identifies the
two composites to Y and contributes diagonalDualizingCongr w. The internal
locality maps cancel, leaving inverse B and the two restrictionAlong constraints
shown below. All identities are natural transformations on unbounded categories;
there is no positivity-of-rank or nonemptiness condition.
(blueprint: lem-pur-diagonal-etale-rho-unit-square). -/
theorem diagonalEtaleRhoUnitSquare (P : PurityFiniteSetting.{u})
    {X Z Y : Scheme.{u}} (d : ℕ) (f : X ⟶ Y) (g : Z ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [SmoothOfRelativeDimension d f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [SmoothOfRelativeDimension d g]
    [IsNoetherian X] [IsNoetherian Z] [IsNoetherian Y]
    [HasCompactification f] [HasCompactification g]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (V : Y.affineOpens)
    (H : P.AffineDiagonalGeometry f aY d V)
    (K : P.AffineDiagonalGeometry g aY d V)
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient)
    (U : Scheme.{u}) [IsNoetherian U]
    (j : U ⟶ X) [Etale j] [IsSeparated j] [LocallyOfFiniteType j] [QuasiCompact j]
    (v : U ⟶ Z) [Etale v] [IsSeparated v] [LocallyOfFiniteType v] [QuasiCompact v]
    (w : v ≫ g = j ≫ f)
    [HasCompactification (j ≫ f)] [HasCompactification (v ≫ g)]
    (O : U.Opens) (jO : O.toScheme ⟶ (f ⁻¹ᵁ V.1).toScheme)
    (vO : O.toScheme ⟶ (g ⁻¹ᵁ V.1).toScheme)
    (hj : jO ≫ (f ⁻¹ᵁ V.1).ι = O.ι ≫ j)
    (hv : vO ≫ (g ⁻¹ᵁ V.1).ι = O.ι ≫ v) :
    let νX := (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory
    let νZ := (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) Z).mapDerivedCategory
    let νU := (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) U).mapDerivedCategory
    let T := OrientationRefinement.pull P O.ι
    let cj := OrientationCounit.restrictionAlong P j (f ⁻¹ᵁ V.1) O jO hj
    let cv := OrientationCounit.restrictionAlong P v (g ⁻¹ᵁ V.1) O vO hv
    let B := (P.diagonalEtaleLocality N v g) ≪≫
      (P.diagonalDualizingCongr w) ≪≫ (P.diagonalEtaleLocality N j f).symm
    let rf := (OrientationRefinement.rho P f aY d V H).symm ≪≫
      (OrientationRefinement.pull P (f ⁻¹ᵁ V.1).ι).mapIso
        (νX.mapIso (OrientationCounit.unitChange P f))
    let rg := (OrientationRefinement.rho P g aY d V K).symm ≪≫
      (OrientationRefinement.pull P (g ⁻¹ᵁ V.1).ι).mapIso
        (νZ.mapIso (OrientationCounit.unitChange P g))
    let L := DiagonalEtaleComparison.restrictedDualizingTransport P f g aY V N U j v w
      O jO vO hj hv
    L.hom ≫ (OrientationRefinement.pull P vO).map rg.hom =
      (OrientationRefinement.pull P jO).map rf.hom ≫
        (cj.app (P.diagonalOrdinaryDualizing f)).hom ≫
        (T.mapIso (νU.mapIso B)).inv ≫
        (cv.app (P.diagonalOrdinaryDualizing g)).inv := by
  let C := ModuleCat.{u + 1} P.Coefficient
  let νX := (ProEtale.comparisonUpperStar C X).mapDerivedCategory
  let νZ := (ProEtale.comparisonUpperStar C Z).mapDerivedCategory
  let νU := (ProEtale.comparisonUpperStar C U).mapDerivedCategory
  let νO := (ProEtale.comparisonUpperStar C O.toScheme).mapDerivedCategory
  let T := OrientationRefinement.pull P O.ι
  let cj := OrientationCounit.restrictionAlong P j (f ⁻¹ᵁ V.1) O jO hj
  let cv := OrientationCounit.restrictionAlong P v (g ⁻¹ᵁ V.1) O vO hv
  let B := P.diagonalEtaleLocality N v g ≪≫ P.diagonalDualizingCongr w ≪≫
    (P.diagonalEtaleLocality N j f).symm
  let rf := (OrientationRefinement.rho P f aY d V H).symm ≪≫
    (OrientationRefinement.pull P (f ⁻¹ᵁ V.1).ι).mapIso
      (νX.mapIso (OrientationCounit.unitChange P f))
  let rg := (OrientationRefinement.rho P g aY d V K).symm ≪≫
    (OrientationRefinement.pull P (g ⁻¹ᵁ V.1).ι).mapIso
      (νZ.mapIso (OrientationCounit.unitChange P g))
  let L := DiagonalEtaleComparison.restrictedDualizingTransport P f g aY V N U j v w
    O jO vO hj hv
  let := P.noetherian (V.1.ι ≫ aY)
  let := P.noetherian ((f ∣_ V.1) ≫ V.1.ι ≫ aY)
  let := P.noetherian ((g ∣_ V.1) ≫ V.1.ι ≫ aY)
  let := P.noetherian (O.ι ≫ j ≫ f ≫ aY)
  let := Dnc.compactifiable P (f ∣_ V.1) (V.1.ι ≫ aY)
  let := Dnc.compactifiable P (g ∣_ V.1) (V.1.ι ≫ aY)
  have : Etale (jO ≫ (f ⁻¹ᵁ V.1).ι) := by rw [hj]; infer_instance
  have : Etale jO := Etale.of_comp jO (f ⁻¹ᵁ V.1).ι
  have : Etale (vO ≫ (g ⁻¹ᵁ V.1).ι) := by rw [hv]; infer_instance
  have : Etale vO := Etale.of_comp vO (g ⁻¹ᵁ V.1).ι
  have : IsSeparated (jO ≫ (f ⁻¹ᵁ V.1).ι) := by rw [hj]; infer_instance
  have : IsSeparated jO := IsSeparated.of_comp jO (f ⁻¹ᵁ V.1).ι
  have : IsSeparated (vO ≫ (g ⁻¹ᵁ V.1).ι) := by rw [hv]; infer_instance
  have : IsSeparated vO := IsSeparated.of_comp vO (g ⁻¹ᵁ V.1).ι
  let q := jO ≫ (f ∣_ V.1)
  let := Dnc.compactifiable P q (V.1.ι ≫ aY)
  have hq : vO ≫ (g ∣_ V.1) = q := by
    apply (cancel_mono V.1.ι).mp
    rw [Category.assoc, Category.assoc, morphismRestrict_ι, morphismRestrict_ι,
      ← Category.assoc, hv, ← Category.assoc, hj]
    simp only [Category.assoc, w]
  let sj := Dnc.pullComparison P jO (Etale.dualizingComplex P.Coefficient (f ∣_ V.1)) ≪≫
    νO.mapIso (Etale.sectionStructuralLocalityIso P.Coefficient jO (f ∣_ V.1) q rfl)
  let sv := Dnc.pullComparison P vO (Etale.dualizingComplex P.Coefficient (g ∣_ V.1)) ≪≫
    νO.mapIso (Etale.sectionStructuralLocalityIso P.Coefficient vO (g ∣_ V.1) q hq)
  let ej := T.mapIso (νU.mapIso (P.diagonalEtaleLocality N j f))
  let ev := T.mapIso (νU.mapIso
    (P.diagonalEtaleLocality N v g ≪≫ P.diagonalDualizingCongr w))
  have hqo : O.ι ≫ (j ≫ f) = q ≫ V.1.ι := by
    rw [← Category.assoc, ← hj, Category.assoc, ← morphismRestrict_ι]
    simp only [q, Category.assoc]
  let r := T.mapIso (νU.mapIso (OrientationCounit.unitChange P (j ≫ f)).symm) ≪≫
    Dnc.pullComparison P O.ι (Etale.dualizingComplex P.Coefficient (j ≫ f)) ≪≫
    νO.mapIso (openDualizingMap P (j ≫ f) aY V.1 O q hqo)
  have hs : sj = (OrientationRefinement.pull P jO).mapIso rf ≪≫
      cj.app (P.diagonalOrdinaryDualizing f) ≪≫ ej ≪≫ r := by
    simpa only [diagonalDualizingCongr, eqToIso_refl, Iso.trans_refl, Iso.trans_assoc]
      using rho_unit_locality P N d f aY V H j (j ≫ f) rfl O jO q hj rfl
  have ht : sv = (OrientationRefinement.pull P vO).mapIso rg ≪≫
      cv.app (P.diagonalOrdinaryDualizing g) ≪≫ ev ≪≫ r := by
    exact rho_unit_locality P N d g aY V K v (j ≫ f) w O vO q hv hq
  have hL : L = sj ≪≫ sv.symm := by
    dsimp only [L, sj, sv]
    rw [DiagonalEtaleComparison.locality_tensorMate P.Coefficient N jO (f ∣_ V.1),
      DiagonalEtaleComparison.locality_tensorMate_congr
        P.Coefficient N vO (g ∣_ V.1) q hq]
    unfold DiagonalEtaleComparison.restrictedDualizingTransport
    simp only [Iso.trans_symm, Functor.mapIso_trans, Functor.mapIso_symm,
      Iso.trans_assoc]
    rfl
  have hp := paste_two_squares sj sv
    ((OrientationRefinement.pull P jO).mapIso rf)
    ((OrientationRefinement.pull P vO).mapIso rg)
    (cj.app (P.diagonalOrdinaryDualizing f))
    (cv.app (P.diagonalOrdinaryDualizing g)) ej ev r hs ht
  have hB : (T.mapIso (νU.mapIso B)).symm = ej ≪≫ ev.symm := by
    simp only [B, ej, ev, Functor.mapIso_trans, Functor.mapIso_symm,
      Iso.trans_symm, Iso.symm_symm_eq, Iso.trans_assoc]
  rw [← hL] at hp
  have hh := congrArg Iso.hom hp
  change L.hom ≫ (OrientationRefinement.pull P vO).map rg.hom =
    (OrientationRefinement.pull P jO).map rf.hom ≫
      (cj.app (P.diagonalOrdinaryDualizing f)).hom ≫
      (T.mapIso (νU.mapIso B)).inv ≫
      (cv.app (P.diagonalOrdinaryDualizing g)).inv
  rw [← Iso.symm_hom, hB]
  simpa only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc] using hh

end WeilConjectures.PurityFiniteSetting
