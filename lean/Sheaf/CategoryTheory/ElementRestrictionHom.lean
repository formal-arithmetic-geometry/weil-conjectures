/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Z5
-/
module

public import Sheaf.CategoryTheory.RingedPresentationData

import WeilConjectures.Algebra.Homology.HomComplexComponents
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all Sheaf.CategoryTheory.ContinuousRingedToposModuleDirectImage
import Sheaf.CategoryTheory.RingedEquivalenceModuleHom
import Sheaf.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
import all Sheaf.CategoryTheory.ElementSiteDescent

/-! # Auxiliary ringed presentation comparisons -/

@[expose] public noncomputable section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory

attribute [local irreducible] homComplexFunctor homComplexπ
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

private theorem comparisonFanIso {D : Type*} [Category D] {ι : Type*}
    {X Y : D} {f g : ι → D} (π : ∀ i, X ⟶ f i) (τ : ∀ i, Y ⟶ g i)
    (hπ : IsLimit (Fan.mk X π)) (hτ : IsLimit (Fan.mk Y τ)) (e : ∀ i, f i ≅ g i) :
    ∃ a : X ≅ Y, ∀ i, a.hom ≫ τ i = π i ≫ (e i).hom := by
  let a := Fan.IsLimit.lift hτ (fun i ↦ π i ≫ (e i).hom)
  let b := Fan.IsLimit.lift hπ (fun i ↦ τ i ≫ (e i).inv)
  have ha (i) : a ≫ τ i = π i ≫ (e i).hom := Fan.IsLimit.fac hτ _ i
  have hb (i) : b ≫ π i = τ i ≫ (e i).inv := Fan.IsLimit.fac hπ _ i
  refine ⟨⟨a, b, ?_, ?_⟩, ha⟩
  · apply Fan.IsLimit.hom_ext hπ
    intro i
    change (a ≫ b) ≫ π i = (𝟙 X) ≫ π i
    rw [Category.assoc, hb, ← Category.assoc, ha, Category.assoc,
      Iso.hom_inv_id, Category.comp_id, Category.id_comp]
  · apply Fan.IsLimit.hom_ext hτ
    intro i
    change (b ≫ a) ≫ τ i = (𝟙 Y) ≫ τ i
    rw [Category.assoc, ha, ← Category.assoc, hb, Category.assoc,
      Iso.inv_hom_id, Category.comp_id, Category.id_comp]

private theorem factor_differential
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    (F : C ⥤ D) [F.Additive]
    {Hn Hm A B E : C} {Kn Km A' B' E' : D}
    (dH : Hn ⟶ Hm) (dK : Kn ⟶ Km)
    (a : Hn ⟶ A) (b : Hn ⟶ B) (c : Hm ⟶ E)
    (α : A ⟶ E) (β : B ⟶ E)
    (a' : Kn ⟶ A') (b' : Kn ⟶ B') (c' : Km ⟶ E')
    (α' : A' ⟶ E') (β' : B' ⟶ E')
    (en : F.obj Hn ⟶ Kn) (em : F.obj Hm ⟶ Km)
    (sa : F.obj A ⟶ A') (sb : F.obj B ⟶ B') (sc : F.obj E ⟶ E') (t : ℤˣ)
    (hH : dH ≫ c = a ≫ α - t • (b ≫ β))
    (hK : dK ≫ c' = a' ≫ α' - t • (b' ≫ β'))
    (ha : en ≫ a' = F.map a ≫ sa) (hb : en ≫ b' = F.map b ≫ sb)
    (hc : em ≫ c' = F.map c ≫ sc)
    (hα : F.map α ≫ sc = sa ≫ α') (hβ : F.map β ≫ sc = sb ≫ β') :
    (en ≫ dK) ≫ c' = (F.map dH ≫ em) ≫ c' := by
  simp only [Category.assoc, hK, Preadditive.comp_sub,
    Linear.comp_units_smul]
  rw [← Category.assoc en a', ha, Category.assoc,
    ← Category.assoc en b', hb, Category.assoc]
  rw [hc, ← Category.assoc (F.map dH), ← F.map_comp, hH]
  simp only [Functor.map_sub, Functor.map_units_smul, Functor.map_comp,
    Preadditive.sub_comp, Linear.units_smul_comp, Category.assoc, hα, hβ]

private theorem factor_naturality
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {X Y A B : C} {X' Y' A' B' : D}
    (f : X ⟶ Y) (g : X' ⟶ Y') (π : X ⟶ A) (τ : Y ⟶ B)
    (π' : X' ⟶ A') (τ' : Y' ⟶ B')
    (ex : F.obj X ⟶ X') (ey : F.obj Y ⟶ Y')
    (ea : F.obj A ⟶ A') (eb : F.obj B ⟶ B') (a : A ⟶ B) (b : A' ⟶ B')
    (hf : f ≫ τ = π ≫ a) (hg : g ≫ τ' = π' ≫ b)
    (hx : ex ≫ π' = F.map π ≫ ea) (hy : ey ≫ τ' = F.map τ ≫ eb)
    (hab : F.map a ≫ eb = ea ≫ b) :
    (F.map f ≫ ey) ≫ τ' = (ex ≫ g) ≫ τ' := by
  rw [Category.assoc, hy, ← Category.assoc, ← F.map_comp, hf, F.map_comp,
    Category.assoc, hab, ← Category.assoc, ← hx, Category.assoc,
    Category.assoc, hg]

private def complexBifunctorComparison
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    (F : C ⥤ D) [F.Additive]
    (H : (CochainComplex C ℤ)ᵒᵖ × CochainComplex C ℤ ⥤ CochainComplex C ℤ)
    (K : (CochainComplex D ℤ)ᵒᵖ × CochainComplex D ℤ ⥤ CochainComplex D ℤ)
    (a : ∀ X n, F.obj ((H.obj X).X n) ≅
      (K.obj (((F.mapHomologicalComplex (.up ℤ)).op.prod
        (F.mapHomologicalComplex (.up ℤ))).obj X)).X n)
    (hd : ∀ X n m, n + 1 = m →
      (a X n).hom ≫ (K.obj (((F.mapHomologicalComplex (.up ℤ)).op.prod
        (F.mapHomologicalComplex (.up ℤ))).obj X)).d n m =
      F.map ((H.obj X).d n m) ≫ (a X m).hom)
    (hf : ∀ {X Y} (f : X ⟶ Y) n,
      F.map ((H.map f).f n) ≫ (a Y n).hom =
        (a X n).hom ≫ (K.map (((F.mapHomologicalComplex (.up ℤ)).op.prod
          (F.mapHomologicalComplex (.up ℤ))).map f)).f n) :
    H ⋙ F.mapHomologicalComplex (.up ℤ) ≅
      ((F.mapHomologicalComplex (.up ℤ)).op.prod (F.mapHomologicalComplex (.up ℤ))) ⋙ K :=
  NatIso.ofComponents
    (fun X ↦ HomologicalComplex.Hom.isoOfComponents (a X) (fun n m h ↦ hd X n m h))
    (fun f ↦ HomologicalComplex.hom_ext _ _ (fun n ↦ hf f n))

/-- Construct a comparison of complex bifunctors from their product projections. -/
private def complexComparisonFromProjections
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    (F : C ⥤ D) [F.Additive]
    (h : C → C → C) (k : D → D → D)
    (hm : ∀ {L L' M M'}, (L' ⟶ L) → (M ⟶ M') → (h L M ⟶ h L' M'))
    (km : ∀ {L L' M M'}, (L' ⟶ L) → (M ⟶ M') → (k L M ⟶ k L' M'))
    (H : (CochainComplex C ℤ)ᵒᵖ × CochainComplex C ℤ ⥤ CochainComplex C ℤ)
    (K : (CochainComplex D ℤ)ᵒᵖ × CochainComplex D ℤ ⥤ CochainComplex D ℤ)
    (πH : ∀ (L M : CochainComplex C ℤ) (n p q : ℤ) (_hpq : p + n = q),
      (H.obj (op L, M)).X n ⟶ h (L.X p) (M.X q))
    (πK : ∀ (L M : CochainComplex D ℤ) (n p q : ℤ) (_hpq : p + n = q),
      (K.obj (op L, M)).X n ⟶ k (L.X p) (M.X q))
    (limK : ∀ L M n, IsLimit (Fan.mk ((K.obj (op L, M)).X n)
      (fun p ↦ πK L M n p (p + n) rfl)))
    (e : ∀ L M, F.obj (h L M) ≅ k (F.obj L) (F.obj M))
    (he : ∀ {L L' M M'} (f : L' ⟶ L) (g : M ⟶ M'),
      F.map (hm f g) ≫ (e L' M').hom = (e L M).hom ≫ km (F.map f) (F.map g))
    (a : ∀ L M n, F.obj ((H.obj (op L, M)).X n) ≅
      (K.obj (op ((F.mapHomologicalComplex (.up ℤ)).obj L),
        (F.mapHomologicalComplex (.up ℤ)).obj M)).X n)
    (fac : ∀ L M n p q (hpq : p + n = q), (a L M n).hom ≫
      πK ((F.mapHomologicalComplex (.up ℤ)).obj L)
        ((F.mapHomologicalComplex (.up ℤ)).obj M) n p q hpq =
      F.map (πH L M n p q hpq) ≫ (e (L.X p) (M.X q)).hom)
    (hdH : ∀ L M n m p q q' p' (_hnm : n + 1 = m) (hpq : p + m = q)
      (hq' : p + n = q') (hp' : p' + n = q),
      (H.obj (op L, M)).d n m ≫ πH L M m p q hpq =
        πH L M n p q' hq' ≫ hm (𝟙 (L.X p)) (M.d q' q) -
          n.negOnePow • (πH L M n p' q hp' ≫ hm (L.d p p') (𝟙 (M.X q))))
    (hdK : ∀ L M n m p q q' p' (_hnm : n + 1 = m) (hpq : p + m = q)
      (hq' : p + n = q') (hp' : p' + n = q),
      (K.obj (op L, M)).d n m ≫ πK L M m p q hpq =
        πK L M n p q' hq' ≫ km (𝟙 (L.X p)) (M.d q' q) -
          n.negOnePow • (πK L M n p' q hp' ≫ km (L.d p p') (𝟙 (M.X q))))
    (hfH : ∀ {X Y} (f : X ⟶ Y) n p q (hpq : p + n = q),
      (H.map f).f n ≫ πH Y.1.unop Y.2 n p q hpq =
        πH X.1.unop X.2 n p q hpq ≫ hm (f.1.unop.f p) (f.2.f q))
    (hfK : ∀ {X Y} (f : X ⟶ Y) n p q (hpq : p + n = q),
      (K.map f).f n ≫ πK Y.1.unop Y.2 n p q hpq =
        πK X.1.unop X.2 n p q hpq ≫ km (f.1.unop.f p) (f.2.f q)) :
    H ⋙ F.mapHomologicalComplex (.up ℤ) ≅
      ((F.mapHomologicalComplex (.up ℤ)).op.prod (F.mapHomologicalComplex (.up ℤ))) ⋙ K := by
  let Fc := F.mapHomologicalComplex (.up ℤ)
  refine complexBifunctorComparison F H K (fun X n ↦ a X.1.unop X.2 n) ?_ ?_
  · intro X n m hnm
    let L := X.1.unop
    let M := X.2
    apply (limK (Fc.obj L) (Fc.obj M) m).hom_ext
    rintro ⟨p⟩
    let q := p + m
    let q' := p + n
    let p' := p + m - n
    have hp' : p' + n = q := by dsimp [p', q]; omega
    refine factor_differential F _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (hdH L M n m p q q' p' hnm rfl rfl hp')
      (hdK (Fc.obj L) (Fc.obj M) n m p q q' p' hnm rfl rfl hp')
      (fac L M n p q' rfl) (fac L M n p' q hp') (fac L M m p q rfl) ?_ ?_
    · change F.map (hm (𝟙 (L.X p)) (M.d q' q)) ≫ (e (L.X p) (M.X q)).hom =
        (e (L.X p) (M.X q')).hom ≫ km (𝟙 (F.obj (L.X p))) (F.map (M.d q' q))
      simpa only [Functor.map_id] using he (𝟙 (L.X p)) (M.d q' q)
    · change F.map (hm (L.d p p') (𝟙 (M.X q))) ≫ (e (L.X p) (M.X q)).hom =
        (e (L.X p') (M.X q)).hom ≫ km (F.map (L.d p p')) (𝟙 (F.obj (M.X q)))
      simpa only [Functor.map_id] using he (L.d p p') (𝟙 (M.X q))
  · intro X Y f n
    apply (limK (Fc.obj Y.1.unop) (Fc.obj Y.2) n).hom_ext
    rintro ⟨p⟩
    let q := p + n
    exact factor_naturality F _ _
      (πH X.1.unop X.2 n p q rfl) (πH Y.1.unop Y.2 n p q rfl)
      (πK (Fc.obj X.1.unop) (Fc.obj X.2) n p q rfl)
      (πK (Fc.obj Y.1.unop) (Fc.obj Y.2) n p q rfl)
      (a X.1.unop X.2 n).hom (a Y.1.unop Y.2 n).hom
      (e (X.1.unop.X p) (X.2.X q)).hom (e (Y.1.unop.X p) (Y.2.X q)).hom
      (hm (f.1.unop.f p) (f.2.f q))
      (km (F.map (f.1.unop.f p)) (F.map (f.2.f q)))
      (hfH f n p q rfl) (hfK ((Fc.op.prod Fc).map f) n p q rfl)
      (fac X.1.unop X.2 n p q rfl) (fac Y.1.unop Y.2 n p q rfl)
      (he (f.1.unop.f p) (f.2.f q))

section HomComplexComparison
set_option backward.isDefEq.respectTransparency true
variable {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (R : Sheaf J CommRingCat.{u}) (S : Sheaf K CommRingCat.{u})
    (F : PresentationModules R ⥤ PresentationModules S) [F.Additive]
    [PreservesLimitsOfShape (Discrete ℤ) F]
    (e : ∀ M N : PresentationModules R,
      F.obj (SheafOfModules.homObj (R := R) M N) ≅
        SheafOfModules.homObj (R := S) (F.obj M) (F.obj N))
    (he : ∀ {M M' N N' : PresentationModules R} (f : M' ⟶ M) (g : N ⟶ N'),
      F.map (SheafOfModules.homObjMap (R := R) f g) ≫ (e M' N').hom =
        (e M N).hom ≫ SheafOfModules.homObjMap (R := S) (F.map f) (F.map g))

private theorem homComplexDegreeIso_exists
    (L M : CochainComplex (PresentationModules R) ℤ) (n : ℤ) :
    ∃ a : F.obj ((homComplex (R := R) L M).X n) ≅
        (homComplex (R := S) ((F.mapHomologicalComplex (.up ℤ)).obj L)
          ((F.mapHomologicalComplex (.up ℤ)).obj M)).X n,
      ∀ p : ℤ, a.hom ≫
        homComplexπ (R := S) ((F.mapHomologicalComplex (.up ℤ)).obj L)
          ((F.mapHomologicalComplex (.up ℤ)).obj M) n p (p + n) rfl =
        F.map (homComplexπ (R := R) L M n p (p + n) rfl) ≫
          (e (L.X p) (M.X (p + n))).hom := by
  exact comparisonFanIso
    (fun p ↦ F.map (homComplexπ (R := R) L M n p (p + n) rfl))
    (fun p ↦ homComplexπ (R := S) ((F.mapHomologicalComplex (.up ℤ)).obj L)
      ((F.mapHomologicalComplex (.up ℤ)).obj M) n p (p + n) rfl)
    (isLimitFanMkObjOfIsLimit F
      (fun p ↦ SheafOfModules.homObj (R := R) (L.X p) (M.X (p + n)))
      (fun p ↦ homComplexπ (R := R) L M n p (p + n) rfl)
      (homComplexIsLimit (R := R) L M n))
    (homComplexIsLimit (R := S) ((F.mapHomologicalComplex (.up ℤ)).obj L)
      ((F.mapHomologicalComplex (.up ℤ)).obj M) n)
    (fun p ↦ e (L.X p) (M.X (p + n)))

private def homComplexDegreeIso
    (L M : CochainComplex (PresentationModules R) ℤ) (n : ℤ) :
    F.obj ((homComplex (R := R) L M).X n) ≅
      (homComplex (R := S) ((F.mapHomologicalComplex (.up ℤ)).obj L)
        ((F.mapHomologicalComplex (.up ℤ)).obj M)).X n :=
  (homComplexDegreeIso_exists R S F e L M n).choose

private theorem homComplexDegreeIso_fac
    (L M : CochainComplex (PresentationModules R) ℤ) (n p q : ℤ) (hpq : p + n = q) :
    (homComplexDegreeIso R S F e L M n).hom ≫
      homComplexπ (R := S) ((F.mapHomologicalComplex (.up ℤ)).obj L)
        ((F.mapHomologicalComplex (.up ℤ)).obj M) n p q hpq =
      F.map (homComplexπ (R := R) L M n p q hpq) ≫ (e (L.X p) (M.X q)).hom := by
  subst q
  exact (homComplexDegreeIso_exists R S F e L M n).choose_spec p

attribute [local irreducible] homComplexDegreeIso

include e he in
private theorem homComplexComparison :
    Nonempty (Functor.uncurry.obj (homComplexFunctor (R := R)) ⋙
      F.mapHomologicalComplex (.up ℤ) ≅
      ((F.mapHomologicalComplex (.up ℤ)).op.prod (F.mapHomologicalComplex (.up ℤ))) ⋙
        Functor.uncurry.obj (homComplexFunctor (R := S))) := by
  exact ⟨complexComparisonFromProjections F
    (SheafOfModules.homObj (R := R)) (SheafOfModules.homObj (R := S))
    (fun f g ↦ SheafOfModules.homObjMap (R := R) f g)
    (fun f g ↦ SheafOfModules.homObjMap (R := S) f g)
    (Functor.uncurry.obj (homComplexFunctor (R := R)))
    (Functor.uncurry.obj (homComplexFunctor (R := S)))
    (homComplexπ (R := R)) (homComplexπ (R := S)) (homComplexIsLimit (R := S)) e
    (fun f g ↦ he f g) (homComplexDegreeIso R S F e)
    (homComplexDegreeIso_fac R S F e) (homComplex_d_π (R := R))
    (homComplex_d_π (R := S))
    (fun f n p q hpq ↦ homComplexFunctor_map_f_π (R := R) f.1.unop f.2 n p q hpq)
    (fun f n p q hpq ↦ homComplexFunctor_map_f_π (R := S) f.1.unop f.2 n p q hpq)⟩

end HomComplexComparison

/-- A site equivalence with an invertible structural ring map transports modules. -/
private theorem siteEquivalenceModules
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : D ⥤ C) [F.IsContinuous K J]
    (L : Sheaf K (Type u) ⥤ Sheaf J (Type u))
    (adj : L ⊣ F.sheafPushforwardContinuous (Type u) K J)
    [L.IsEquivalence] [(F.sheafPushforwardContinuous (Type u) K J).IsEquivalence]
    (R : Sheaf J CommRingCat.{u}) (S : Sheaf K CommRingCat.{u})
    (φ : S ⟶ (F.sheafPushforwardContinuous CommRingCat K J).obj R) (hφ : IsIso φ) :
    ∃ T : RingedPresentationEquivalenceCore S R,
      Nonempty (T.modules.inverse ≅ SheafOfModules.pushforward.{u} (F := F)
        ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).map φ)) := by
  let := hφ
  let φs : (sheafCompose K (forget CommRingCat.{u})).obj S ⟶
      (F.sheafPushforwardContinuous (Type u) K J).obj
        ((sheafCompose J (forget CommRingCat.{u})).obj R) :=
    (sheafCompose K (forget CommRingCat.{u})).map φ
  have : IsIso φs := inferInstanceAs
    (IsIso ((sheafCompose K (forget CommRingCat.{u})).map φ))
  let p := siteContinuousRingedTopos F L adj R S φ
  have : p.inverse.IsEquivalence := inferInstanceAs L.IsEquivalence
  have : IsIso p.ringMap := by
    change IsIso ((adj.homEquiv ((sheafCompose K (forget CommRingCat.{u})).obj S)
      ((sheafCompose J (forget CommRingCat.{u})).obj R)).symm φs)
    rw [Adjunction.homEquiv_counit]
    infer_instance
  obtain ⟨T, ⟨t⟩, _, _⟩ := ringed_equivalence_module_hom (R := R) (S := S) p
  exact ⟨T, ⟨t ≪≫ Iso.refl _⟩⟩

section DerivedComparison
set_option backward.isDefEq.respectTransparency true
variable {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (R : Sheaf J CommRingCat.{u}) (S : Sheaf K CommRingCat.{u})
    (F : PresentationModules R ⥤ PresentationModules S)
    (ha : F.Additive) (hl : PreservesFiniteLimits F) (hc : PreservesFiniteColimits F)

private theorem derivedComparison
    (hk : ∀ I : CochainComplex (PresentationModules R) ℤ,
      I.IsKInjective → ((presentationComplexMap (R := R) (S := S) F ha).obj I).IsKInjective)
    (c : Functor.uncurry.obj (homComplexFunctor (R := R)) ⋙
      presentationComplexMap (R := R) (S := S) F ha ≅
      ((presentationComplexMap (R := R) (S := S) F ha).op.prod
        (presentationComplexMap (R := R) (S := S) F ha)) ⋙
        Functor.uncurry.obj (homComplexFunctor (R := S))) :
    Nonempty (presentationRHom R ⋙ presentationDerivedMap (R := R) (S := S) F ha hl hc ≅
      ((presentationDerivedMap (R := R) (S := S) F ha hl hc).op.prod
        (presentationDerivedMap (R := R) (S := S) F ha hl hc)) ⋙
        presentationRHom S) := by
  let := HasDerivedCategory.standard (PresentationModules R)
  let := HasDerivedCategory.standard (PresentationModules S)
  let := ha
  let := hl
  let := hc
  let A := PresentationModules R
  let B := PresentationModules S
  let : IsGrothendieckAbelian.{u} A :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{u, u, u}
      J R).1
  let : IsGrothendieckAbelian.{u} B :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{u, u, u}
      K S).1
  let KR := CochainComplex A ℤ
  let KS := CochainComplex B ℤ
  let QR := DerivedCategory.Q (C := A)
  let QS := DerivedCategory.Q (C := B)
  let HR := Functor.uncurry.obj (homComplexFunctor (R := R))
  let HS := Functor.uncurry.obj (homComplexFunctor (R := S))
  let Fc := F.mapHomologicalComplex (.up ℤ)
  let Fd := F.mapDerivedCategory
  let IR := CochainComplex.kInjectiveResolutionFunctor.{u} A
  let ηR := CochainComplex.toKInjectiveResolution.{u} A
  let IS := CochainComplex.kInjectiveResolutionFunctor.{u} B
  let ηS := CochainComplex.toKInjectiveResolution.{u} B
  obtain ⟨eR⟩ := derivedInternalHomOfUniverses_comparison.{u, u, u, u + 1} J R IR ηR
    (fun M ↦ ⟨(CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} A M).2,
      CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{u} A M⟩)
  obtain ⟨eS⟩ := derivedInternalHomOfUniverses_comparison.{u, u, u, u + 1} K S IS ηS
    (fun M ↦ ⟨(CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} B M).2,
      CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{u} B M⟩)
  let Z := (𝟭 KRᵒᵖ).prod IR
  let G := Z ⋙ (Fc.op.prod Fc)
  have hG (X : KRᵒᵖ × KR) : CochainComplex.IsKInjective (G.obj X).2 :=
    hk (IR.obj X.2) (CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{u} A X.2)
  let α := Functor.whiskerLeft G
    (Functor.whiskerRight (NatTrans.prod (𝟙 (𝟭 KSᵒᵖ)) ηS) (HS ⋙ QS))
  have : IsIso α := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro X
    have : CochainComplex.IsKInjective (G.obj X).2 := hG X
    have : CochainComplex.IsKInjective (IS.obj (G.obj X).2) :=
      CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{u} B _
    have : QuasiIso (ηS.app (G.obj X).2) :=
      (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} B _).2
    change IsIso (QS.map
      ((((homComplexFunctor (R := S)).map (𝟙 (G.obj X).1.unop).op).app (G.obj X).2) ≫
        ((homComplexFunctor (R := S)).obj (G.obj X).1).map (ηS.app (G.obj X).2)))
    apply (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr
    exact quasiIso_homComplex_mapOfUniverses.{u, u, u} (R := S)
      (I' := (G.obj X).2) (I := IS.obj (G.obj X).2)
      (L' := (G.obj X).1.unop) (L := (G.obj X).1.unop)
      (ηS.app (G.obj X).2) (𝟙 (G.obj X).1.unop)
  let rep : G ⋙ (QS.op.prod QS) ⋙ presentationRHom S ≅ G ⋙ HS ⋙ QS :=
    Functor.isoWhiskerLeft G eS ≪≫ (asIso α).symm
  let ηQ := Functor.whiskerRight ηR QR
  have : IsIso ηQ := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro X
    change IsIso (QR.map (ηR.app X))
    apply (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr
    exact (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} A X).2
  let β : QR.op.prod QR ≅ Z ⋙ (QR.op.prod QR) :=
    (Functor.leftUnitor (QR.op.prod QR)).symm ≪≫
      NatIso.prod (Iso.refl QR.op) (asIso ηQ)
  let factors : QR ⋙ Fd ≅ Fc ⋙ QS := F.mapDerivedCategoryFactors
  let factors₂ : (QR.op.prod QR) ⋙ (Fd.op.prod Fd) ≅
      (Fc.op.prod Fc) ⋙ (QS.op.prod QS) := NatIso.prod (NatIso.op factors).symm factors
  let left : (QR.op.prod QR) ⋙ (presentationRHom R ⋙ Fd) ≅ G ⋙ HS ⋙ QS :=
    Functor.isoWhiskerRight eR Fd ≪≫
      Functor.isoWhiskerLeft (Z ⋙ HR) factors ≪≫
      Functor.isoWhiskerRight (Functor.isoWhiskerLeft Z c) QS
  let right : (QR.op.prod QR) ⋙ ((Fd.op.prod Fd) ⋙ presentationRHom S) ≅
      G ⋙ HS ⋙ QS :=
    Functor.isoWhiskerRight (Functor.isoWhiskerRight β (Fd.op.prod Fd))
        (presentationRHom S) ≪≫
      Functor.isoWhiskerRight (Functor.isoWhiskerLeft Z factors₂) (presentationRHom S) ≪≫ rep
  exact ⟨(Localization.fullyFaithfulWhiskeringLeft (QR.op.prod QR)
    ((HomologicalComplex.quasiIso A (.up ℤ)).op.prod
      (HomologicalComplex.quasiIso A (.up ℤ))) _).preimageIso (left ≪≫ right.symm)⟩

end DerivedComparison

section ElementHom
variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u}) (A : Sheaf J (Type u))

private def elementSliceLift (e : A.obj.Elementsᵒᵖ) :
    Over ((elementProjection A).obj e) ⥤ Over e where
  obj V := Over.mk ((CategoryOfElements.homMk e.unop
    ⟨op V.left, A.obj.map V.hom.op e.unop.2⟩ V.hom.op rfl).op)
  map {V W} f := Over.homMk
    ((CategoryOfElements.homMk
      ⟨op W.left, A.obj.map W.hom.op e.unop.2⟩
      ⟨op V.left, A.obj.map V.hom.op e.unop.2⟩ f.left.op (by
        change A.obj.map f.left.op (A.obj.map W.hom.op e.unop.2) = _
        rw [← Functor.map_comp_apply, ← op_comp, Over.w])).op) (by
          apply Quiver.Hom.unop_inj
          apply Subtype.ext
          change (W.hom.op ≫ f.left.op) = V.hom.op
          rw [← op_comp, Over.w])
  map_id V := by
    apply Over.OverMorphism.ext
    apply Quiver.Hom.unop_inj
    apply Subtype.ext
    rfl
  map_comp f g := by
    apply Over.OverMorphism.ext
    apply Quiver.Hom.unop_inj
    apply Subtype.ext
    rfl

set_option backward.isDefEq.respectTransparency false in
private def elementHomFwd
    (M N : PresentationModules R) (e : A.obj.Elementsᵒᵖ)
    (φ : (PresheafOfModules.restrictOver R.obj ((elementProjection A).obj e)).obj M.val ⟶
      (PresheafOfModules.restrictOver R.obj ((elementProjection A).obj e)).obj N.val) :
    (PresheafOfModules.restrictOver (presentationElementRing R A).obj e).obj
        ((elementModulePullback (localCoefficientRings R) A).obj M).val ⟶
      (PresheafOfModules.restrictOver (presentationElementRing R A).obj e).obj
        ((elementModulePullback (localCoefficientRings R) A).obj N).val where
  app W := φ.app (op ((Over.post (elementProjection A)).obj W.unop))
  naturality f := by
    ext x
    exact PresheafOfModules.naturality_apply φ
      ((Over.post (elementProjection A)).op.map f) x

private def elementHomBwd
    (M N : PresentationModules R) (e : A.obj.Elementsᵒᵖ)
    (ψ : (PresheafOfModules.restrictOver (presentationElementRing R A).obj e).obj
        ((elementModulePullback (localCoefficientRings R) A).obj M).val ⟶
      (PresheafOfModules.restrictOver (presentationElementRing R A).obj e).obj
        ((elementModulePullback (localCoefficientRings R) A).obj N).val) :
    (PresheafOfModules.restrictOver R.obj ((elementProjection A).obj e)).obj M.val ⟶
      (PresheafOfModules.restrictOver R.obj ((elementProjection A).obj e)).obj N.val where
  app V := ψ.app (op ((elementSliceLift A e).obj V.unop))
  naturality f := by
    ext x
    exact PresheafOfModules.naturality_apply ψ ((elementSliceLift A e).op.map f) x

private theorem elementHomBwd_fwd
    (M N : PresentationModules R) (e : A.obj.Elementsᵒᵖ)
    (φ : (PresheafOfModules.restrictOver R.obj ((elementProjection A).obj e)).obj M.val ⟶
      (PresheafOfModules.restrictOver R.obj ((elementProjection A).obj e)).obj N.val) :
    elementHomBwd R A M N e (elementHomFwd R A M N e φ) = φ := by
  rfl

private theorem elementHomFwd_bwd
    (M N : PresentationModules R) (e : A.obj.Elementsᵒᵖ)
    (ψ : (PresheafOfModules.restrictOver (presentationElementRing R A).obj e).obj
        ((elementModulePullback (localCoefficientRings R) A).obj M).val ⟶
      (PresheafOfModules.restrictOver (presentationElementRing R A).obj e).obj
        ((elementModulePullback (localCoefficientRings R) A).obj N).val) :
    elementHomFwd R A M N e (elementHomBwd R A M N e ψ) = ψ := by
  ext W x
  let V := (elementSliceLift A e).obj ((Over.post (elementProjection A)).obj W.unop)
  let a : V ⟶ W.unop := Over.homMk
    ((CategoryOfElements.homMk W.unop.left.unop V.left.unop (𝟙 _) (by
      change A.obj.map (𝟙 _) W.unop.left.unop.2 =
        A.obj.map W.unop.hom.unop.1 e.unop.2
      rw [Functor.map_id_apply, W.unop.hom.unop.2])).op) (by
        apply Quiver.Hom.unop_inj
        apply Subtype.ext
        change W.unop.hom.unop.1 ≫ 𝟙 _ = W.unop.hom.unop.1
        simp)
  have he (P : PresentationModules R)
      (y : P.val.obj (op ((elementProjection A).obj W.unop.left))) :
      ((PresheafOfModules.restrictOver (presentationElementRing R A).obj e).obj
        ((elementModulePullback (localCoefficientRings R) A).obj P).val).map a.op y = y := by
    change P.val.map (𝟙 _) y = y
    rw [P.val.map_id]
    rfl
  change ψ.app (op V) x = ψ.app W x
  exact (congrArg (ψ.app (op V)) (he M x).symm).trans
    ((PresheafOfModules.naturality_apply ψ a.op x).trans (he N _))

set_option backward.isDefEq.respectTransparency false in
private def elementHomObjIso (M N : PresentationModules R) :
    (elementModulePullback (localCoefficientRings R) A).obj (SheafOfModules.homObj (R := R) M N) ≅
      SheafOfModules.homObj (R := presentationElementRing R A)
        ((elementModulePullback (localCoefficientRings R) A).obj M)
        ((elementModulePullback (localCoefficientRings R) A).obj N) :=
  (SheafOfModules.fullyFaithfulForget
    (localCoefficientRings (presentationElementRing R A))).preimageIso
    (PresheafOfModules.isoMk (fun e ↦ by
      letI : Module ((presentationElementRing R A).obj.obj e)
          ((PresheafOfModules.restrictOver (presentationElementRing R A).obj e.unop).obj
            ((elementModulePullback (localCoefficientRings R) A).obj M).val ⟶
          (PresheafOfModules.restrictOver (presentationElementRing R A).obj e.unop).obj
            ((elementModulePullback (localCoefficientRings R) A).obj N).val) :=
        Module.compHom _ ((PresheafOfModules.sectionsSMulHom
          ((PresheafOfModules.restrictOver (presentationElementRing R A).obj e.unop).obj
            ((elementModulePullback (localCoefficientRings R) A).obj N).val)).comp
          (PresheafOfModules.overSections (R := (presentationElementRing R A).obj) e.unop))
      exact {
        hom := ModuleCat.ofHom (R := (presentationElementRing R A).obj.obj e)
          { toFun := elementHomFwd R A M N e.unop
            map_add' _ _ := rfl
            map_smul' _ _ := rfl }
        inv := ModuleCat.ofHom (R := (presentationElementRing R A).obj.obj e)
          { toFun := elementHomBwd R A M N e.unop
            map_add' _ _ := rfl
            map_smul' _ _ := rfl }
        hom_inv_id := by ext φ : 2; exact elementHomBwd_fwd R A M N e.unop φ
        inv_hom_id := by ext ψ : 2; exact elementHomFwd_bwd R A M N e.unop ψ })
      (by intro e d f; rfl))

private theorem elementHomObjIso_naturality
    {M M' N N' : PresentationModules R} (f : M' ⟶ M) (g : N ⟶ N') :
    (elementModulePullback (localCoefficientRings R) A).map
        (SheafOfModules.homObjMap (R := R) f g) ≫ (elementHomObjIso R A M' N').hom =
      (elementHomObjIso R A M N).hom ≫ SheafOfModules.homObjMap (R := presentationElementRing R A)
        ((elementModulePullback (localCoefficientRings R) A).map f)
        ((elementModulePullback (localCoefficientRings R) A).map g) := by
  ext e φ
  rfl

end ElementHom

private theorem elementDerivedHom
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) (A : Sheaf J (Type u)) :
    Nonempty (presentationRHom R ⋙
      presentationDerivedMap (R := R) (S := presentationElementRing R A)
      (elementModulePullback (localCoefficientRings R) A)
        (presentationElementRestriction_additive R A)
        (presentationElementRestriction_exact R A).1
        (presentationElementRestriction_exact R A).2.1 ≅
      ((presentationDerivedMap (R := R) (S := presentationElementRing R A)
      (elementModulePullback (localCoefficientRings R) A)
        (presentationElementRestriction_additive R A)
        (presentationElementRestriction_exact R A).1
        (presentationElementRestriction_exact R A).2.1).op.prod
      (presentationDerivedMap (R := R) (S := presentationElementRing R A)
      (elementModulePullback (localCoefficientRings R) A)
        (presentationElementRestriction_additive R A)
        (presentationElementRestriction_exact R A).1
        (presentationElementRestriction_exact R A).2.1)) ⋙
      presentationRHom (presentationElementRing R A)) := by
  let F := elementModulePullback (localCoefficientRings R) A
  let := presentationElementRestriction_additive R A
  obtain ⟨adj⟩ := elementModuleExtension_adjunction (localCoefficientRings R) A
  let := adj.isRightAdjoint
  obtain ⟨c⟩ := homComplexComparison R (presentationElementRing R A) F
    (elementHomObjIso R A) (fun f g ↦ elementHomObjIso_naturality R A f g)
  exact derivedComparison R (presentationElementRing R A) F
    (presentationElementRestriction_additive R A) (presentationElementRestriction_exact R A).1
    (presentationElementRestriction_exact R A).2.1 (fun I hI ↦ by
      let := hI
      exact presentationElementRestriction_kInjective R A I) c

private def closedComparisonTransport
    {A B : Type*} [Category A] [Category B]
    (H : Aᵒᵖ × A ⥤ A) (K : Bᵒᵖ × B ⥤ B) {F G : A ⥤ B}
    (p : F ≅ G) (a : H ⋙ G ≅ (G.op.prod G) ⋙ K) :
    H ⋙ F ≅ (F.op.prod F) ⋙ K :=
  Functor.isoWhiskerLeft H p ≪≫ a ≪≫
    Functor.isoWhiskerRight (NatIso.prod (NatIso.op p) p.symm) K

private def closedComparisonComp
    {A B E : Type*} [Category A] [Category B] [Category E]
    (H : Aᵒᵖ × A ⥤ A) (K : Bᵒᵖ × B ⥤ B) (L : Eᵒᵖ × E ⥤ E)
    (F : A ⥤ B) (G : B ⥤ E)
    (a : H ⋙ F ≅ (F.op.prod F) ⋙ K) (b : K ⋙ G ≅ (G.op.prod G) ⋙ L) :
    H ⋙ (F ⋙ G) ≅ ((F ⋙ G).op.prod (F ⋙ G)) ⋙ L :=
  (Functor.associator H F G).symm ≪≫ Functor.isoWhiskerRight a G ≪≫
    Functor.associator (F.op.prod F) K G ≪≫
    Functor.isoWhiskerLeft (F.op.prod F) b

section IteratedElements
variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {A B : Sheaf J (Type u)} (b : B ⟶ A)

private def elementFibre : Sheaf (elementTopology A) (Type u) :=
  (fibreFunctor A).obj (Over.mk b)

private def flattenElements : (elementFibre b).obj.Elementsᵒᵖ ⥤ B.obj.Elementsᵒᵖ where
  obj e := op ⟨e.unop.1.unop.unop.1, e.unop.2.val⟩
  map {e d} f := (CategoryOfElements.homMk
    ⟨d.unop.1.unop.unop.1, d.unop.2.val⟩
    ⟨e.unop.1.unop.unop.1, e.unop.2.val⟩ f.unop.1.unop.unop.1
      (congrArg Subtype.val f.unop.2)).op
  map_id e := by apply Quiver.Hom.unop_inj; apply Subtype.ext; rfl
  map_comp f g := by apply Quiver.Hom.unop_inj; apply Subtype.ext; rfl

private def flattenElementsPreimage
    {e d : (elementFibre b).obj.Elementsᵒᵖ}
    (f : (flattenElements b).obj e ⟶ (flattenElements b).obj d) : e ⟶ d :=
  (CategoryOfElements.homMk d.unop e.unop
    ((CategoryOfElements.homMk d.unop.1.unop.unop e.unop.1.unop.unop f.unop.1 (by
      change A.obj.map f.unop.1 d.unop.1.unop.unop.2 = e.unop.1.unop.unop.2
      calc
        _ = A.obj.map f.unop.1 (b.hom.app _ d.unop.2.val) :=
          congrArg (A.obj.map f.unop.1) d.unop.2.property.symm
        _ = b.hom.app _ (B.obj.map f.unop.1 d.unop.2.val) :=
          (NatTrans.naturality_apply b.hom f.unop.1 d.unop.2.val).symm
        _ = b.hom.app _ e.unop.2.val := congrArg (b.hom.app _) f.unop.2
        _ = _ := e.unop.2.property)).op.op)
    (by apply Subtype.ext; exact f.unop.2)).op

/-- The fibre condition identifies its chosen base section with the image section. -/
private def flattenBaseIso :
    elementProjection (elementFibre b) ≅ flattenElements b ⋙ elementMap b :=
  NatIso.ofComponents (fun e ↦ {
    hom := (CategoryOfElements.homMk
      (((flattenElements b ⋙ elementMap b).obj e).unop)
      (((elementProjection (elementFibre b)).obj e).unop) (𝟙 _)
      (by
        change A.obj.map (𝟙 _) (b.hom.app _ e.unop.2.val) = e.unop.1.unop.unop.2
        rw [Functor.map_id_apply]
        exact e.unop.2.property)).op
    inv := (CategoryOfElements.homMk
      (((elementProjection (elementFibre b)).obj e).unop)
      (((flattenElements b ⋙ elementMap b).obj e).unop) (𝟙 _)
      (by
        change A.obj.map (𝟙 _) e.unop.1.unop.unop.2 = b.hom.app _ e.unop.2.val
        rw [Functor.map_id_apply]
        exact e.unop.2.property.symm)).op
    hom_inv_id := by
      apply Quiver.Hom.unop_inj
      apply Subtype.ext
      exact Category.id_comp _
    inv_hom_id := by
      apply Quiver.Hom.unop_inj
      apply Subtype.ext
      exact Category.id_comp _ }) (by
    intro e d f
    apply Quiver.Hom.unop_inj
    apply Subtype.ext
    change 𝟙 _ ≫ f.unop.1.unop.unop.1 = f.unop.1.unop.unop.1 ≫ 𝟙 _
    simp only [Category.comp_id, Category.id_comp])

private theorem flattenElements_equivalence : (flattenElements b).IsEquivalence := by
  let F := flattenElements b
  have : F.Faithful := ⟨fun h ↦ by
    apply Quiver.Hom.unop_inj
    apply Subtype.ext
    apply Quiver.Hom.unop_inj
    apply Quiver.Hom.unop_inj
    apply Subtype.ext
    exact congrArg (fun f ↦ f.unop.1) h⟩
  have : F.Full := ⟨fun f ↦ ⟨flattenElementsPreimage b f, by
    apply Quiver.Hom.unop_inj
    apply Subtype.ext
    rfl⟩⟩
  have : F.EssSurj := ⟨fun e ↦ ⟨op ⟨op ((elementMap b).obj e),
    ⟨e.unop.2, rfl⟩⟩, ⟨Iso.refl _⟩⟩⟩
  exact {}

private theorem elementCover_iff
    {D : Type u} [SmallCategory D] {K : GrothendieckTopology D}
    (X : Sheaf K (Type u)) (e : X.obj.Elementsᵒᵖ) (S : Sieve e) :
    S ∈ elementTopology X e ↔
      S.functorPushforward (elementProjection X) ∈ K ((elementProjection X).obj e) := by
  rw [projection_topology X, ← liftedTopology_eq_restricted X]
  rfl

private theorem flattenElements_dense :
    (flattenElements b).IsDenseSubsite (elementTopology (elementFibre b)) (elementTopology B) := by
  let F := flattenElements b
  have : F.IsEquivalence := flattenElements_equivalence b
  refine { functorPushforward_mem_iff := ?_ }
  intro e S
  rw [elementCover_iff B, elementCover_iff (elementFibre b), elementCover_iff A]
  rw [← Sieve.functorPushforward_comp, ← Sieve.functorPushforward_comp]
  rfl

private theorem furtherElementCore (R : Sheaf J CommRingCat.{u}) :
    ∃ T : RingedPresentationCore (presentationElementRing R A) (presentationElementRing R B)
        (elementModulePullbackOver (localCoefficientRings R) b
          (presentationElementRestriction_continuous b)),
      T.unit = Iso.refl _ := by
  let RA := presentationElementRing R A
  let RB := presentationElementRing R B
  let X := elementFibre b
  let RX := presentationElementRing RA X
  let P := flattenElements b
  have : P.IsEquivalence := flattenElements_equivalence b
  have : P.IsDenseSubsite (elementTopology X) (elementTopology B) :=
    flattenElements_dense b
  let G := P.sheafPushforwardContinuous (Type u) (elementTopology X) (elementTopology B)
  let L := G.asEquivalence.inverse
  let adj : L ⊣ G := G.asEquivalence.symm.toAdjunction
  obtain ⟨T, ⟨t⟩⟩ := siteEquivalenceModules P L adj RB RX (𝟙 _) (by
    change IsIso (𝟙 RX)
    infer_instance)
  let F : PresentationModules RA ⥤ PresentationModules RB :=
    elementModulePullbackOver (localCoefficientRings R) b
      (presentationElementRestriction_continuous b)
  let H : PresentationModules RA ⥤ PresentationModules RX :=
    elementModulePullback (localCoefficientRings RA) X
  have ha : F.Additive := by
    constructor
    intro M N f g
    ext V x
    rfl
  have hH : H.Additive := presentationElementRestriction_additive RA X
  have hT : T.modules.functor.Additive :=
    Functor.additive_of_preserves_binary_products T.modules.functor
  let : (elementMap b).IsContinuous (elementTopology B) (elementTopology A) :=
    presentationElementRestriction_continuous b
  let : (P ⋙ elementMap b).IsContinuous (elementTopology X) (elementTopology A) :=
    Functor.isContinuous_comp _ _ _ (elementTopology B) _
  -- The underlying object is unchanged, but its two section labels agree only propositionally.
  let φP : localCoefficientRings RX ⟶
      (P.sheafPushforwardContinuous RingCat.{u} (elementTopology X)
        (elementTopology B)).obj (localCoefficientRings RB) :=
    (sheafCompose (elementTopology X) (forget₂ CommRingCat RingCat)).map (𝟙 RX)
  let q₀ : F ⋙ SheafOfModules.pushforward (F := P) φP ≅ H :=
    SheafOfModules.pushforwardComp (F := P) (G := elementMap b)
      (J := elementTopology X) (K := elementTopology B) (K' := elementTopology A)
      (S := localCoefficientRings RX) (R := localCoefficientRings RB)
      (R' := localCoefficientRings RA) φP (𝟙 (localCoefficientRings RB)) ≪≫
    SheafOfModules.pushforwardCongr₂
      (F := elementProjection X) (G := P ⋙ elementMap b)
      (J := elementTopology X) (K := elementTopology A)
      (T := localCoefficientRings RX) (S := localCoefficientRings RA)
      (φ := φP ≫ (P.sheafPushforwardContinuous RingCat.{u} (elementTopology X)
        (elementTopology B)).map (𝟙 (localCoefficientRings RB)))
      (ψ := 𝟙 (localCoefficientRings RX)) (flattenBaseIso b) (by
        ext e x
        change R.obj.map (𝟙 _) x = x
        exact Functor.map_id_apply R.obj _ x)
  let q : F ⋙ T.modules.inverse ≅ H := Functor.isoWhiskerLeft F t ≪≫ q₀
  let q' : H ⋙ T.modules.functor ≅ F :=
    Functor.isoWhiskerRight q.symm T.modules.functor ≪≫
      Functor.associator F T.modules.inverse T.modules.functor ≪≫
      Functor.isoWhiskerLeft F T.modules.counitIso ≪≫ Functor.rightUnitor F
  have hHl : PreservesFiniteLimits H := (presentationElementRestriction_exact RA X).1
  have hHc : PreservesFiniteColimits H := (presentationElementRestriction_exact RA X).2.1
  have hHs : PreservesColimitsOfShape ℕ H := (presentationElementRestriction_exact RA X).2.2
  have hFl : PreservesFiniteLimits F := by
    have : PreservesFiniteLimits (F ⋙ T.modules.inverse) :=
      preservesFiniteLimits_of_natIso q.symm
    exact preservesFiniteLimits_of_reflects_of_preserves F T.modules.inverse
  have hFc : PreservesFiniteColimits F := by
    have : PreservesFiniteColimits (F ⋙ T.modules.inverse) :=
      preservesFiniteColimits_of_natIso q.symm
    exact preservesFiniteColimits_of_reflects_of_preserves F T.modules.inverse
  have hFs : PreservesColimitsOfShape ℕ F := by
    have : PreservesColimitsOfShape ℕ (F ⋙ T.modules.inverse) :=
      preservesColimitsOfShape_of_natIso q.symm
    exact preservesColimitsOfShape_of_reflects_of_preserves F T.modules.inverse
  have hk (I : CochainComplex (PresentationModules RA) ℤ) (hI : I.IsKInjective) :
      CochainComplex.IsKInjective ((presentationComplexMap (R := RA) (S := RB) F ha).obj I) := by
    let := hI
    have : CochainComplex.IsKInjective ((H.mapHomologicalComplex (.up ℤ)).obj I) :=
      presentationElementRestriction_kInjective RA X I
    have : CochainComplex.IsKInjective ((T.modules.functor.mapHomologicalComplex (.up ℤ)).obj
        ((H.mapHomologicalComplex (.up ℤ)).obj I)) := inferInstance
    exact CochainComplex.isKInjective_of_iso
      (L₁ := (T.modules.functor.mapHomologicalComplex (.up ℤ)).obj
        ((H.mapHomologicalComplex (.up ℤ)).obj I))
      ((Functor.mapHomologicalComplexCompIso q' (.up ℤ)).app I)
  have hh : Nonempty (presentationRHom RA ⋙
      presentationDerivedMap (R := RA) (S := RB) F ha hFl hFc ≅
      ((presentationDerivedMap (R := RA) (S := RB) F ha hFl hFc).op.prod
        (presentationDerivedMap (R := RA) (S := RB) F ha hFl hFc)) ⋙ presentationRHom RB) := by
    let := HasDerivedCategory.standard (PresentationModules RA)
    let := HasDerivedCategory.standard (PresentationModules RX)
    let := HasDerivedCategory.standard (PresentationModules RB)
    obtain ⟨a⟩ := elementDerivedHom RA X
    obtain ⟨c⟩ := T.forwardHom
    let d : F.mapDerivedCategory ≅ H.mapDerivedCategory ⋙ T.modules.functor.mapDerivedCategory :=
      Functor.mapDerivedCategoryNatIso q'.symm ≪≫
        Functor.mapDerivedCategoryCompIso H T.modules.functor
    exact ⟨closedComparisonTransport (presentationRHom RA) (presentationRHom RB) d
      (closedComparisonComp (presentationRHom RA) (presentationRHom RX) (presentationRHom RB)
        H.mapDerivedCategory T.modules.functor.mapDerivedCategory a c)⟩
  exact ⟨{
    additive := ha
    finiteLimits := hFl
    finiteColimits := hFc
    sequentialColimits := hFs
    unit := Iso.refl _
    kInjective := hk
    internalHom := hh }, rfl⟩

end IteratedElements

section RepresentableComparison
variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}

private abbrev representableSheaf (U : C) : Sheaf J (Type u) :=
  (presheafToSheaf J (Type u)).obj (yoneda.obj U)

private def representableElementFunctor (U : C) :
    Over U ⥤ (representableSheaf (J := J) U).obj.Elementsᵒᵖ where
  obj X := op ⟨op X.left, (toSheafify J (yoneda.obj U)).app (op X.left) X.hom⟩
  map {X Y} f := (CategoryOfElements.homMk
    ⟨op Y.left, (toSheafify J (yoneda.obj U)).app (op Y.left) Y.hom⟩
    ⟨op X.left, (toSheafify J (yoneda.obj U)).app (op X.left) X.hom⟩ f.left.op (by
      rw [← NatTrans.naturality_apply]
      change (toSheafify J (yoneda.obj U)).app (op X.left) (f.left ≫ Y.hom) = _
      rw [Over.w])).op
  map_id X := by apply Quiver.Hom.unop_inj; apply Subtype.ext; rfl
  map_comp f g := by apply Quiver.Hom.unop_inj; apply Subtype.ext; rfl

private theorem representableElement_equivalence (U : C) :
    ∃ h : (representableElementFunctor (J := J) U).IsContinuous (J.over U)
        (elementTopology (representableSheaf (J := J) U)),
      let _ := h
      ((representableElementFunctor (J := J) U).sheafPushforwardContinuous (Type u)
        (J.over U) (elementTopology (representableSheaf (J := J) U))).IsEquivalence := by
  let A := representableSheaf (J := J) U
  let F := representableElementFunctor (J := J) U
  obtain ⟨_, _, _, _, _, E, _, r, hr, hm⟩ :=
    exists_localizedSheavesOverRepresentable_general J U
  obtain ⟨_, _, ⟨T, ⟨t⟩⟩, _⟩ := element_site_descent A
  let P := (Functor.whiskeringLeft _ _ (Type u)).obj F.op
  let c : E.inverse ⋙ sheafToPresheaf (J.over U) (Type u) ≅
      elementFibrePresheafFunctor A ⋙ P :=
    NatIso.ofComponents (fun H ↦ NatIso.ofComponents (fun X ↦ (r H X.unop).toIso) (by
      intro X Y f
      ext z
      apply Subtype.ext
      exact hr H Y.unop X.unop f.unop z)) (by
        intro H G f
        ext X z
        apply Subtype.ext
        exact hm H G f X.unop z)
  let d : (T.inverse ⋙ sheafToPresheaf (elementTopology A) (Type u)) ⋙ P ≅
      E.inverse ⋙ sheafToPresheaf (J.over U) (Type u) :=
    Functor.isoWhiskerRight t P ≪≫ c.symm
  have h : F.IsContinuous (J.over U) (elementTopology A) := by
    constructor
    intro H
    let q : F.op ⋙ H.obj ≅ (E.inverse.obj (T.functor.obj H)).obj :=
      Functor.isoWhiskerLeft F.op
        ((sheafToPresheaf (elementTopology A) (Type u)).mapIso (T.unitIso.app H)) ≪≫
          d.app (T.functor.obj H)
    exact (isSheaf_iff_isSheaf_of_type _ _).mp
      ((Presheaf.isSheaf_of_iso_iff q).mpr (E.inverse.obj (T.functor.obj H)).property)
  let := h
  let G := F.sheafPushforwardContinuous (Type u) (J.over U) (elementTopology A)
  let q : T.inverse ⋙ G ≅ E.inverse :=
    Functor.fullyFaithfulCancelRight (sheafToPresheaf (J.over U) (Type u)) d
  have : (T.inverse ⋙ G).IsEquivalence := Functor.isEquivalence_of_iso q.symm
  exact ⟨h, Functor.isEquivalence_of_comp_left T.inverse G⟩

private theorem representableModule_comparison
    (R : Sheaf J CommRingCat.{u}) (U : C) :
    ∃ E : RingedPresentationEquivalenceCore (R.over U)
        (presentationElementRing R (representableSheaf (J := J) U)),
      Nonempty (SheafOfModules.overFunctor (localCoefficientRings R) U ⋙
        E.modules.functor ≅ elementModulePullback (localCoefficientRings R)
          (representableSheaf (J := J) U)) := by
  let A := representableSheaf (J := J) U
  let F := representableElementFunctor (J := J) U
  obtain ⟨h, hG⟩ := representableElement_equivalence (J := J) U
  let := h
  let G := F.sheafPushforwardContinuous (Type u) (J.over U) (elementTopology A)
  let : G.IsEquivalence := hG
  let L := G.asEquivalence.inverse
  let adj : L ⊣ G := G.asEquivalence.symm.toAdjunction
  obtain ⟨T, ⟨t⟩⟩ := siteEquivalenceModules F L adj
    (presentationElementRing R A) (R.over U) (𝟙 _) (by
      change IsIso (𝟙 (R.over U))
      infer_instance)
  let H := elementModulePullback (localCoefficientRings R) A
  let q : H ⋙ T.modules.inverse ≅ SheafOfModules.overFunctor
      (localCoefficientRings R) U :=
    Functor.isoWhiskerLeft H t ≪≫ Iso.refl _
  exact ⟨T, ⟨Functor.isoWhiskerRight q.symm T.modules.functor ≪≫
    Functor.associator H T.modules.inverse T.modules.functor ≪≫
    Functor.isoWhiskerLeft H T.modules.counitIso ≪≫ Functor.rightUnitor H⟩⟩

end RepresentableComparison
/-- The closed exact restriction functors on the element site and its further
localizations, including the comparison with the original site-object slices.

Source: Stacks Project, sites-modules.tex, Tags 04IE and 04J4;
sites-cohomology.tex, Tags 08FI and 08JB; sites.tex, Tag 00Y1.
(blueprint: lem-weil-pbc-element-restriction-hom).

Proof: the element-site extension-by-zero functor is exact and left adjoint to
restriction, so restriction preserves K-injectives, as proved already by
presentationElementRestriction_kInjective. It is also left adjoint to
module direct image, hence preserves colimits, and its sectionwise construction
preserves finite limits and addition. At an element (U,s), the further slice is
C/U: the section on an arrow V → U is forced to be s restricted to V. Thus sheaf
Hom restricts sectionwise. Restriction preserves products, so the products and
the differential dφ = d_I φ - (-1)^n φ d_L in the Hom complex restrict as well.
Compute derived Hom with a K-injective target to obtain its natural comparison.
Repeat on an element site for a map B → A. Both successive restrictions evaluate
M at the same underlying U and give the canonical relocalization isomorphism.
Finally the fibre/extension equivalence over the sheafified representable
identifies the ring with R|U, the module restriction with the usual overFunctor,
and their Hom computations. Transport the module operations through this
fibre equivalence to get the indicated exact module equivalence. -/
theorem element_restriction_hom
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) :
    ∃ (s : ∀ {A B : Sheaf J (Type u)} (b : B ⟶ A),
        RingedPresentationCore (presentationElementRing R A) (presentationElementRing R B)
          (elementModulePullbackOver.{u, u} (localCoefficientRings R) b
            (presentationElementRestriction_continuous b))),
      (∀ A : Sheaf J (Type u),
        Nonempty (presentationRHom R ⋙
          presentationDerivedMap (R := R) (S := presentationElementRing R A)
            (elementModulePullback.{u, u} (localCoefficientRings R) A)
            (presentationElementRestriction_additive R A)
            (presentationElementRestriction_exact R A).1
            (presentationElementRestriction_exact R A).2.1 ≅
          ((presentationDerivedMap (R := R) (S := presentationElementRing R A)
            (elementModulePullback.{u, u} (localCoefficientRings R) A)
              (presentationElementRestriction_additive R A)
              (presentationElementRestriction_exact R A).1
              (presentationElementRestriction_exact R A).2.1).op.prod
            (presentationDerivedMap (R := R) (S := presentationElementRing R A)
            (elementModulePullback.{u, u} (localCoefficientRings R) A)
              (presentationElementRestriction_additive R A)
              (presentationElementRestriction_exact R A).1
              (presentationElementRestriction_exact R A).2.1)) ⋙
            presentationRHom (presentationElementRing R A))) ∧
      (∀ {A B : Sheaf J (Type u)} (b : B ⟶ A), (s b).unit = Iso.refl _) ∧
      ∀ U : C,
        ∃ E : RingedPresentationEquivalenceCore (R.over U)
          (presentationElementRing R ((presheafToSheaf J (Type u)).obj (yoneda.obj U))),
          Nonempty (SheafOfModules.overFunctor.{u} (localCoefficientRings R) U ⋙
            E.modules.functor ≅ elementModulePullback.{u, u} (localCoefficientRings R)
              ((presheafToSheaf J (Type u)).obj (yoneda.obj U))) := by
  classical
  exact ⟨fun {A B} b ↦ (furtherElementCore b R).choose,
    elementDerivedHom R, fun b ↦ (furtherElementCore b R).choose_spec,
    representableModule_comparison R⟩

end CategoryTheory
