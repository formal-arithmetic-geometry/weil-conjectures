/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q136
-/
module

public import Sheaf.CategoryTheory.DerivedInjectiveBoundary
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.Algebra.Homology.ConcreteCategory
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
import Mathlib.Algebra.Homology.DerivedCategory.KInjective

/-!
# Signed cone boundaries and descent through injective representatives

Source: Stacks Project, derived.tex, Tags 014Z, 070I, 070J, 05TH and 05TI;
homology.tex, Tag 0117. (blueprint: lem-pur-injective-cone-boundary-descent)
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v r m w z

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
  [HasDerivedCategory.{w} C] {A : Type r} [CommRing A]
  [HasDerivedCategory.{z} (ModuleCat.{m} A)]

/-- The derived-unit comparison before taking cohomology, for a specified injective model.
Source: Stacks, Tags 05TH and 05TI.
(blueprint: lem-pur-injective-cone-boundary-descent) -/
def injectiveConeModelIso (T : C ⥤ ModuleCat.{m} A) [T.Additive]
    (I : CochainComplex.Plus C) [∀ n : ℤ, Injective (I.obj.X n)]
    (K : DerivedCategory.Plus C) (e : DerivedCategory.Plus.Q.obj I ≅ K) :
    DerivedCategory.Q.obj ((T.mapHomologicalComplex (.up ℤ)).obj I.obj) ≅
      DerivedCategory.Plus.ι.obj (T.rightDerivedFunctorPlus.obj K) :=
  (DerivedCategory.quotientCompQhIso (ModuleCat.{m} A)).symm.app
      ((T.mapHomologicalComplex (.up ℤ)).obj I.obj) ≪≫
    DerivedCategory.Plus.ι.mapIso
      (asIso (T.rightDerivedFunctorPlusUnit.app ((HomotopyCategory.Plus.quotient C).obj I))
        ≪≫ T.rightDerivedFunctorPlus.mapIso e)

/-- Coordinates `(b,a)` in the cone, with the unshifted summand written first.
Source: Stacks, Tag 014Z, the displayed cone differential.
(blueprint: lem-pur-injective-cone-boundary-descent) -/
def injectiveConeVector (R : ShortComplex (CochainComplex (ModuleCat.{m} A) ℤ))
    (n : ℤ) (b : R.X₂.X n) (a : R.X₁.X (n + 1)) :
    (CochainComplex.mappingCone R.f).X n :=
  (CochainComplex.mappingCone.inr R.f).f n b +
    (CochainComplex.mappingCone.inl R.f).v (n + 1) n (by omega) a

/-- The cohomology map of the signed cone roof, in the actual homology modules.
The roof itself is Mathlib's `triangleOfSESδ`, whose definition is the inverse
of `Q(q)` followed by the negative projection and the shift comparison.
Source: Stacks, Tag 014Z; homology.tex, Tag 0117.
(blueprint: lem-pur-injective-cone-boundary-descent) -/
def injectiveConeHomology
    (R : ShortComplex (CochainComplex (ModuleCat.{m} A) ℤ)) (hR : R.ShortExact)
    (n : ℤ) : R.X₃.homology n ⟶ R.X₁.homology (n + 1) :=
  (DerivedCategory.homologyFunctorFactors (ModuleCat.{m} A) n).inv.app R.X₃ ≫
    (DerivedCategory.homologyFunctor (ModuleCat.{m} A) 0).shiftMap
      (DerivedCategory.triangleOfSESδ hR) n (n + 1) (by omega) ≫
    (DerivedCategory.homologyFunctorFactors (ModuleCat.{m} A) (n + 1)).hom.app R.X₁

variable (S F G : C ⥤ ModuleCat.{m} A) [S.Additive] [F.Additive] [G.Additive]
  (ι : S ⟶ F) (π : F ⟶ G) (w₀ : ι ≫ π = 0)

/-- The canonical cone map induced by a chain map of injective models.
Source: Stacks, Tag 014Z, functorial cone calculation.
(blueprint: lem-pur-injective-cone-boundary-descent) -/
def injectiveBoundaryConeMap (I J : CochainComplex.Plus C) (b : I ⟶ J) :
    CochainComplex.mappingCone (injectiveBoundaryRow S F G ι π w₀ I).f ⟶
      CochainComplex.mappingCone (injectiveBoundaryRow S F G ι π w₀ J).f :=
  CochainComplex.mappingCone.map _ _
    ((S.mapHomologicalComplex (.up ℤ)).map b.hom)
    ((F.mapHomologicalComplex (.up ℤ)).map b.hom)
    ((NatTrans.mapHomologicalComplex ι (.up ℤ)).naturality b.hom).symm

/-- The coordinate, quasi-isomorphism, and positive lift clauses of the cone statement.
This merely packages the clauses for one row, using Mathlib's cone and homology.
Source: Stacks, Tag 014Z and Tag 0117.
(blueprint: lem-pur-injective-cone-boundary-descent) -/
def InjectiveConeRowProperties
    (R : ShortComplex (CochainComplex (ModuleCat.{m} A) ℤ)) (hR : R.ShortExact) : Prop :=
  (∀ (n : ℤ) (b : R.X₂.X n) (a : R.X₁.X (n + 1)),
    (CochainComplex.mappingCone R.f).d n (n + 1) (injectiveConeVector R n b a) =
      injectiveConeVector R (n + 1)
        (R.X₂.d n (n + 1) b + R.f.f (n + 1) a) (-R.X₁.d (n + 1) (n + 1 + 1) a)) ∧
  (∀ (n : ℤ) (b : R.X₂.X n) (a : R.X₁.X (n + 1)),
    (CochainComplex.mappingCone.descShortComplex R).f n (injectiveConeVector R n b a) =
      R.g.f n b ∧
    (R.X₁.shiftFunctorObjXIso 1 n (n + 1) rfl).hom
      ((CochainComplex.mappingCone.triangle R.f).mor₃.f n
        (injectiveConeVector R n b a)) = -a) ∧
  QuasiIso (CochainComplex.mappingCone.descShortComplex R) ∧
  (∀ n : ℤ, injectiveConeHomology R hR n = hR.δ n (n + 1) rfl) ∧
  (∀ (n : ℤ) (c : R.X₃.X n) (hc : R.X₃.d n (n + 1) c = 0),
    (∃ b : R.X₂.X n, R.g.f n b = c) ∧
    ∀ (b : R.X₂.X n) (_hb : R.g.f n b = c),
      (∃! a : R.X₁.X (n + 1), R.f.f (n + 1) a = R.X₂.d n (n + 1) b) ∧
      ∀ (a : R.X₁.X (n + 1)) (_ha : R.f.f (n + 1) a = R.X₂.d n (n + 1) b),
        ∃ ha' : R.X₁.d (n + 1) (n + 1 + 1) a = 0,
          injectiveConeHomology R hR n
            (R.X₃.homologyπ n
              (R.X₃.cyclesMk c (n + 1) (ComplexShape.next_eq' _ rfl) hc)) =
          R.X₁.homologyπ (n + 1)
            (R.X₁.cyclesMk a (n + 1 + 1) (ComplexShape.next_eq' _ rfl) ha'))

set_option backward.isDefEq.respectTransparency false in
omit [HasDerivedCategory (ModuleCat.{m} A)] in
private theorem coneVector_d
    (R : ShortComplex (CochainComplex (ModuleCat.{m} A) ℤ))
    (n : ℤ) (b : R.X₂.X n) (a : R.X₁.X (n + 1)) :
    (CochainComplex.mappingCone R.f).d n (n + 1) (injectiveConeVector R n b a) =
      injectiveConeVector R (n + 1)
        (R.X₂.d n (n + 1) b + R.f.f (n + 1) a) (-R.X₁.d (n + 1) (n + 1 + 1) a) := by
  have h₁ := CochainComplex.mappingCone.inr_f_d R.f n (n + 1)
  have h₂ := CochainComplex.mappingCone.inl_v_d R.f (n + 1) n (n + 1 + 1)
    (by omega) (by omega)
  have h₁b := congrArg (fun t ↦ t b) h₁
  have h₂a := congrArg (fun t ↦ t a) h₂
  change (CochainComplex.mappingCone R.f).d n (n + 1)
      ((CochainComplex.mappingCone.inr R.f).f n b) =
    (CochainComplex.mappingCone.inr R.f).f (n + 1) (R.X₂.d n (n + 1) b) at h₁b
  change (CochainComplex.mappingCone R.f).d n (n + 1)
      ((CochainComplex.mappingCone.inl R.f).v (n + 1) n (by omega) a) =
    (CochainComplex.mappingCone.inr R.f).f (n + 1) (R.f.f (n + 1) a) -
      (CochainComplex.mappingCone.inl R.f).v (n + 1 + 1) (n + 1) (by omega)
        (R.X₁.d (n + 1) (n + 1 + 1) a) at h₂a
  dsimp only [injectiveConeVector]
  rw [((CochainComplex.mappingCone R.f).d n (n + 1)).hom.map_add, h₁b, h₂a,
    ((CochainComplex.mappingCone.inr R.f).f (n + 1)).hom.map_add,
    ((CochainComplex.mappingCone.inl R.f).v (n + 1 + 1) (n + 1) (by omega)).hom.map_neg]
  abel

set_option backward.isDefEq.respectTransparency false in
omit [HasDerivedCategory (ModuleCat.{m} A)] in
private theorem coneVector_desc
    (R : ShortComplex (CochainComplex (ModuleCat.{m} A) ℤ))
    (n : ℤ) (b : R.X₂.X n) (a : R.X₁.X (n + 1)) :
    (CochainComplex.mappingCone.descShortComplex R).f n (injectiveConeVector R n b a) =
      R.g.f n b := by
  dsimp only [injectiveConeVector]
  rw [((CochainComplex.mappingCone.descShortComplex R).f n).hom.map_add]
  simp only [← ModuleCat.comp_apply,
    CochainComplex.mappingCone.inr_f_descShortComplex_f,
    CochainComplex.mappingCone.inl_v_descShortComplex_f, ModuleCat.hom_zero, LinearMap.zero_apply,
    add_zero]

set_option backward.isDefEq.respectTransparency false in
omit [HasDerivedCategory (ModuleCat.{m} A)] in
private theorem coneVector_projection
    (R : ShortComplex (CochainComplex (ModuleCat.{m} A) ℤ))
    (n : ℤ) (b : R.X₂.X n) (a : R.X₁.X (n + 1)) :
    (R.X₁.shiftFunctorObjXIso 1 n (n + 1) rfl).hom
      ((CochainComplex.mappingCone.triangle R.f).mor₃.f n
        (injectiveConeVector R n b a)) = -a := by
  have h₁ : (CochainComplex.mappingCone.inr R.f).f n ≫
      (CochainComplex.mappingCone.triangle R.f).mor₃.f n ≫
        (R.X₁.shiftFunctorObjXIso 1 n (n + 1) rfl).hom = 0 := by simp
  have h₂ : (CochainComplex.mappingCone.inl R.f).v (n + 1) n (by omega) ≫
      (CochainComplex.mappingCone.triangle R.f).mor₃.f n ≫
        (R.X₁.shiftFunctorObjXIso 1 n (n + 1) rfl).hom = -𝟙 _ := by simp
  dsimp only [injectiveConeVector]
  rw [((CochainComplex.mappingCone.triangle R.f).mor₃.f n).hom.map_add,
    (R.X₁.shiftFunctorObjXIso 1 n (n + 1) rfl).hom.hom.map_add]
  change ((CochainComplex.mappingCone.inr R.f).f n ≫
      (CochainComplex.mappingCone.triangle R.f).mor₃.f n ≫
        (R.X₁.shiftFunctorObjXIso 1 n (n + 1) rfl).hom) b +
    ((CochainComplex.mappingCone.inl R.f).v (n + 1) n (by omega) ≫
      (CochainComplex.mappingCone.triangle R.f).mor₃.f n ≫
        (R.X₁.shiftFunctorObjXIso 1 n (n + 1) rfl).hom) a = -a
  rw [h₁, h₂]
  change (0 : R.X₁.X (n + 1)) + -a = -a
  exact zero_add _

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem coneHomology_eq
    (R : ShortComplex (CochainComplex (ModuleCat.{m} A) ℤ)) (hR : R.ShortExact)
    (n : ℤ) : injectiveConeHomology R hR n = hR.δ n (n + 1) rfl := by
  have := CochainComplex.mappingCone.quasiIso_descShortComplex hR
  apply (cancel_epi (HomologicalComplex.homologyMap
    (CochainComplex.mappingCone.descShortComplex R) n)).1
  dsimp only [injectiveConeHomology]
  erw [(DerivedCategory.homologyFunctorFactors (ModuleCat.{m} A) n).inv.naturality_assoc]
  dsimp only [Functor.comp_map]
  change (DerivedCategory.homologyFunctorFactors (ModuleCat.{m} A) n).inv.app _ ≫
    ((DerivedCategory.homologyFunctor (ModuleCat.{m} A) 0).shift n).map
      (DerivedCategory.Q.map (CochainComplex.mappingCone.descShortComplex R)) ≫ _ = _
  rw [← Functor.shiftMap_comp'_assoc]
  rw [DerivedCategory.descShortComplex_triangleOfSESδ]
  erw [DerivedCategory.shiftMap_homologyFunctor_map_Q
    (CochainComplex.mappingCone.triangle R.f).mor₃ n (n + 1) (by omega)]
  have hh := CochainComplex.mappingCone.homologySequenceδ_triangleh hR n (n + 1) rfl
  rw [CochainComplex.homologySequenceδ_quotient_mapTriangle_obj] at hh
  simpa [Category.assoc] using congrArg
      (fun f ↦ (HomotopyCategory.homologyFunctorFactors (ModuleCat.{m} A) (.up ℤ) n).inv.app
        (CochainComplex.mappingCone R.f) ≫ f ≫
        (HomotopyCategory.homologyFunctorFactors (ModuleCat.{m} A) (.up ℤ) (n + 1)).hom.app
          R.X₁) hh

private theorem coneRow_properties
    (R : ShortComplex (CochainComplex (ModuleCat.{m} A) ℤ)) (hR : R.ShortExact) :
    InjectiveConeRowProperties R hR := by
  refine ⟨coneVector_d R, fun n b a ↦ ⟨coneVector_desc R n b a,
    coneVector_projection R n b a⟩,
    CochainComplex.mappingCone.quasiIso_descShortComplex hR, coneHomology_eq R hR, ?_⟩
  intro n c hc
  have hdegree := (HomologicalComplex.shortExact_iff_degreewise_shortExact R).1 hR
  refine ⟨(hdegree n).moduleCat_surjective_g c, ?_⟩
  intro b hb
  have hz : R.g.f (n + 1) (R.X₂.d n (n + 1) b) = 0 := by
    rw [← ModuleCat.comp_apply, ← R.g.comm n (n + 1), ModuleCat.comp_apply, hb, hc]
  obtain ⟨a, ha⟩ := (ShortComplex.moduleCat_exact_iff _).1
    (hdegree (n + 1)).exact _ hz
  refine ⟨⟨a, ha, fun a' ha' ↦ (hdegree (n + 1)).moduleCat_injective_f
    (ha'.trans ha.symm)⟩, ?_⟩
  intro a ha
  have ha' : R.X₁.d (n + 1) (n + 1 + 1) a = 0 :=
    hR.d_eq_zero_of_f_eq_d_apply n (n + 1) b a ha (n + 1 + 1)
  refine ⟨ha', ?_⟩
  rw [coneHomology_eq]
  exact hR.δ_apply n (n + 1) rfl c hc b hb a ha (n + 1 + 1)
    (ComplexShape.next_eq' _ rfl)

omit [EnoughInjectives C] in
private theorem model_chainMap
    (I J : CochainComplex.Plus C) [∀ n : ℤ, Injective (J.obj.X n)]
    (K L : DerivedCategory.Plus C)
    (e : DerivedCategory.Plus.Q.obj I ≅ K) (e' : DerivedCategory.Plus.Q.obj J ≅ L)
    (f : K ⟶ L) :
    ∃ b : I ⟶ J, DerivedCategory.Plus.Q.map b ≫ e'.hom = e.hom ≫ f ∧
      ∀ (b' : I ⟶ J) (_hb : DerivedCategory.Plus.Q.map b' ≫ e'.hom = e.hom ≫ f),
        Nonempty (Homotopy b.hom b'.hom) := by
  have hJ : J.obj.IsKInjective := by
    obtain ⟨n, hn⟩ := J.property
    exact CochainComplex.isKInjective_of_injective J.obj n
  have bij := DerivedCategory.Plus.Qh_map_bijective_of_isKInjective
    ((HomotopyCategory.Plus.quotient C).obj I)
    ((HomotopyCategory.Plus.quotient C).obj J) hJ
  obtain ⟨b, hb⟩ := bij.2 (e.hom ≫ f ≫ e'.inv)
  obtain ⟨b, rfl⟩ := (HomotopyCategory.Plus.quotient C).map_surjective b
  have hb' : DerivedCategory.Plus.Q.map b ≫ e'.hom = e.hom ≫ f := by
    change DerivedCategory.Plus.Qh.map ((HomotopyCategory.Plus.quotient C).map b) ≫
      e'.hom = _
    rw [hb]
    simp
  refine ⟨b, hb', fun b' hb'₁ ↦ ?_⟩
  have heq : (HomotopyCategory.Plus.quotient C).map b =
      (HomotopyCategory.Plus.quotient C).map b' := by
    apply bij.1
    apply (cancel_mono e'.hom).1
    exact hb'.trans hb'₁.symm
  exact ⟨HomotopyCategory.homotopyOfEq _ _
    (congrArg (fun t ↦ (HomotopyCategory.Plus.ι C).map t) heq)⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem modelIso_naturality (T : C ⥤ ModuleCat.{m} A) [T.Additive]
    (I J : CochainComplex.Plus C)
    [∀ n : ℤ, Injective (I.obj.X n)] [∀ n : ℤ, Injective (J.obj.X n)]
    (K L : DerivedCategory.Plus C)
    (e : DerivedCategory.Plus.Q.obj I ≅ K) (e' : DerivedCategory.Plus.Q.obj J ≅ L)
    (b : I ⟶ J) (f : K ⟶ L)
    (hf : DerivedCategory.Plus.Q.map b ≫ e'.hom = e.hom ≫ f) :
    DerivedCategory.Q.map ((T.mapHomologicalComplex (.up ℤ)).map b.hom) ≫
      (injectiveConeModelIso T J L e').hom =
    (injectiveConeModelIso T I K e).hom ≫
      DerivedCategory.Plus.ι.map (T.rightDerivedFunctorPlus.map f) := by
  have h₁ := (DerivedCategory.quotientCompQhIso (ModuleCat.{m} A)).inv.naturality
    ((T.mapHomologicalComplex (.up ℤ)).map b.hom)
  have h₂ := T.rightDerivedFunctorPlusUnit.naturality
    ((HomotopyCategory.Plus.quotient C).map b)
  dsimp only [injectiveConeModelIso, Iso.trans_hom, Iso.app_hom, Iso.symm_hom,
    Functor.mapIso_hom, asIso_hom]
  simp only [Category.assoc]
  erw [reassoc_of% h₁]
  have hu := congrArg (fun t ↦ DerivedCategory.Plus.ι.map t) h₂
  simp only [Functor.map_comp] at hu
  erw [reassoc_of% hu]
  have he := congrArg (fun t ↦ DerivedCategory.Plus.ι.map
    (T.rightDerivedFunctorPlus.map t)) hf
  convert! (congrArg
      (fun t ↦ (DerivedCategory.quotientCompQhIso (ModuleCat.{m} A)).inv.app
        ((T.mapHomologicalComplex (.up ℤ)).obj I.obj) ≫
        DerivedCategory.Plus.ι.map
          (T.rightDerivedFunctorPlusUnit.app ((HomotopyCategory.Plus.quotient C).obj I)) ≫ t)
      he) using 1 <;>
    simp only [Functor.map_comp, Functor.comp_map, DerivedCategory.Plus.Q,
      Category.assoc]
  rfl

private def modelRoof
    (h : ∀ (J : C) [Injective J], (ShortComplex.mk (ι.app J) (π.app J)
      (NatTrans.congr_app w₀ J)).ShortExact)
    (I : CochainComplex.Plus C) [∀ n : ℤ, Injective (I.obj.X n)]
    (K : DerivedCategory.Plus C) (e : DerivedCategory.Plus.Q.obj I ≅ K) :
    DerivedCategory.Plus.ι.obj (G.rightDerivedFunctorPlus.obj K) ⟶
      (DerivedCategory.Plus.ι.obj (S.rightDerivedFunctorPlus.obj K))⟦(1 : ℤ)⟧ :=
  (injectiveConeModelIso G I K e).inv ≫
    DerivedCategory.triangleOfSESδ (injectiveBoundaryRow_shortExact S F G ι π w₀ h I) ≫
      (shiftFunctor (DerivedCategory (ModuleCat.{m} A)) (1 : ℤ)).map
        (injectiveConeModelIso S I K e).hom

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem modelRoof_naturality
    (h : ∀ (J : C) [Injective J], (ShortComplex.mk (ι.app J) (π.app J)
      (NatTrans.congr_app w₀ J)).ShortExact)
    (I J : CochainComplex.Plus C)
    [∀ n : ℤ, Injective (I.obj.X n)] [∀ n : ℤ, Injective (J.obj.X n)]
    (K L : DerivedCategory.Plus C)
    (e : DerivedCategory.Plus.Q.obj I ≅ K) (e' : DerivedCategory.Plus.Q.obj J ≅ L)
    (f : K ⟶ L) :
    DerivedCategory.Plus.ι.map (G.rightDerivedFunctorPlus.map f) ≫
        modelRoof S F G ι π w₀ h J L e' =
      modelRoof S F G ι π w₀ h I K e ≫
        (DerivedCategory.Plus.ι.map (S.rightDerivedFunctorPlus.map f))⟦(1 : ℤ)⟧' := by
  obtain ⟨b, hb, _⟩ := model_chainMap I J K L e e' f
  let φ : injectiveBoundaryRow S F G ι π w₀ I ⟶
      injectiveBoundaryRow S F G ι π w₀ J :=
    { τ₁ := (S.mapHomologicalComplex (.up ℤ)).map b.hom
      τ₂ := (F.mapHomologicalComplex (.up ℤ)).map b.hom
      τ₃ := (G.mapHomologicalComplex (.up ℤ)).map b.hom
      comm₁₂ := (NatTrans.mapHomologicalComplex ι (.up ℤ)).naturality b.hom
      comm₂₃ := (NatTrans.mapHomologicalComplex π (.up ℤ)).naturality b.hom }
  have hd := DerivedCategory.triangleOfSESδ_naturality
    (injectiveBoundaryRow_shortExact S F G ι π w₀ h I)
    (injectiveBoundaryRow_shortExact S F G ι π w₀ h J) φ
  apply (cancel_epi (injectiveConeModelIso G I K e).hom).1
  dsimp only [modelRoof]
  rw [← Category.assoc, ← modelIso_naturality G I J K L e e' b f hb]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Functor.map_comp, ← modelIso_naturality S I J K L e e' b f hb,
    Functor.map_comp]
  simpa only [φ, Category.assoc] using congrArg
    (fun t ↦ t ≫ (injectiveConeModelIso S J L e').hom⟦(1 : ℤ)⟧') hd.symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem modelIso_homology (T : C ⥤ ModuleCat.{m} A) [T.Additive]
    (I : CochainComplex.Plus C) [∀ n : ℤ, Injective (I.obj.X n)]
    (K : DerivedCategory.Plus C) (e : DerivedCategory.Plus.Q.obj I ≅ K) (n : ℤ) :
    (DerivedCategory.homologyFunctorFactors (ModuleCat.{m} A) n).inv.app
        ((T.mapHomologicalComplex (.up ℤ)).obj I.obj) ≫
      (DerivedCategory.homologyFunctor (ModuleCat.{m} A) n).map
        (injectiveConeModelIso T I K e).hom =
    (injectiveHomologyModelIso T I K e n).hom := by
  dsimp only [injectiveConeModelIso, injectiveHomologyModelIso,
    DerivedCategory.Plus.homologyFunctorObjQIso, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.app_hom, Iso.app_inv, Functor.mapIso_hom, asIso_hom]
  simp only [Category.assoc]
  change _ =
    (HomotopyCategory.homologyFunctorFactors (ModuleCat.{m} A) (.up ℤ) n).inv.app
      ((T.mapHomologicalComplex (.up ℤ)).obj I.obj) ≫
    (DerivedCategory.homologyFunctorFactorsh (ModuleCat.{m} A) n).inv.app
      ((HomotopyCategory.quotient _ _).obj
        ((T.mapHomologicalComplex (.up ℤ)).obj I.obj)) ≫ _
  rw [DerivedCategory.homologyFunctorFactorsh_inv_app_quotient_obj]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Functor.map_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem modelRoof_homology
    (h : ∀ (J : C) [Injective J], (ShortComplex.mk (ι.app J) (π.app J)
      (NatTrans.congr_app w₀ J)).ShortExact)
    (I : CochainComplex.Plus C) [∀ n : ℤ, Injective (I.obj.X n)]
    (K : DerivedCategory.Plus C) (e : DerivedCategory.Plus.Q.obj I ≅ K) (n : ℤ) :
    (injectiveHomologyModelIso G I K e n).hom ≫
      (DerivedCategory.homologyFunctor (ModuleCat.{m} A) 0).shiftMap
        (modelRoof S F G ι π w₀ h I K e) n (n + 1) (by omega) ≫
      (injectiveHomologyModelIso S I K e (n + 1)).inv =
    (injectiveBoundaryRow_shortExact S F G ι π w₀ h I).δ n (n + 1) rfl := by
  apply (cancel_mono (injectiveHomologyModelIso S I K e (n + 1)).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← modelIso_homology G, ← modelIso_homology S]
  dsimp only [modelRoof]
  rw [Functor.shiftMap_comp', Functor.shiftMap_comp]
  simp only [DerivedCategory.shift_homologyFunctor]
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id,
    Functor.map_id, Category.id_comp]
  simpa only [injectiveBoundaryRow, injectiveConeHomology, Category.assoc,
    Iso.hom_inv_id_app_assoc] using
    congrArg (fun t ↦ t ≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{m} A) (n + 1)).inv.app
        ((S.mapHomologicalComplex (.up ℤ)).obj I.obj) ≫
      (DerivedCategory.homologyFunctor (ModuleCat.{m} A) (n + 1)).map
        (injectiveConeModelIso S I K e).hom)
      (coneHomology_eq (injectiveBoundaryRow S F G ι π w₀ I)
        (injectiveBoundaryRow_shortExact S F G ι π w₀ h I) n)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
omit [EnoughInjectives C] [HasDerivedCategory C] [HasDerivedCategory (ModuleCat.{m} A)] in
private theorem coneMap_vector (I J : CochainComplex.Plus C) (b : I ⟶ J)
    (n : ℤ) (x : F.obj (I.obj.X n)) (a : S.obj (I.obj.X (n + 1))) :
    (injectiveBoundaryConeMap S F G ι π w₀ I J b).f n
        (injectiveConeVector (injectiveBoundaryRow S F G ι π w₀ I) n x a) =
      injectiveConeVector (injectiveBoundaryRow S F G ι π w₀ J) n
        (F.map (b.hom.f n) x) (S.map (b.hom.f (n + 1)) a) := by
  have hleft : (CochainComplex.mappingCone.inl
        (injectiveBoundaryRow S F G ι π w₀ I).f).v (n + 1) n (by omega) ≫
      (injectiveBoundaryConeMap S F G ι π w₀ I J b).f n =
      S.map (b.hom.f (n + 1)) ≫ (CochainComplex.mappingCone.inl
        (injectiveBoundaryRow S F G ι π w₀ J).f).v (n + 1) n (by omega) := by
    simp [injectiveBoundaryConeMap, CochainComplex.mappingCone.map]
  have hright : (CochainComplex.mappingCone.inr
        (injectiveBoundaryRow S F G ι π w₀ I).f).f n ≫
      (injectiveBoundaryConeMap S F G ι π w₀ I J b).f n =
      F.map (b.hom.f n) ≫ (CochainComplex.mappingCone.inr
        (injectiveBoundaryRow S F G ι π w₀ J).f).f n := by
    simp [injectiveBoundaryConeMap, CochainComplex.mappingCone.map]
  dsimp only [injectiveConeVector]
  rw [(injectiveBoundaryConeMap S F G ι π w₀ I J b).f n |>.hom.map_add]
  exact congrArg₂ (· + ·) (congrArg (fun t ↦ t x) hright)
    (congrArg (fun t ↦ t a) hleft)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
omit [EnoughInjectives C] [HasDerivedCategory C] [HasDerivedCategory (ModuleCat.{m} A)] in
private theorem coneMap_homotopy (I J : CochainComplex.Plus C) (b b' : I ⟶ J)
    (k : Homotopy b.hom b'.hom) :
    Nonempty (Homotopy (injectiveBoundaryConeMap S F G ι π w₀ I J b)
      (injectiveBoundaryConeMap S F G ι π w₀ I J b')) := by
  let R := ShortComplex.mk ((NatTrans.mapHomologicalComplex ι (.up ℤ)).app I.obj)
    ((NatTrans.mapHomologicalComplex π (.up ℤ)).app I.obj)
    (injectiveBoundaryRow S F G ι π w₀ I).zero
  let R' := ShortComplex.mk ((NatTrans.mapHomologicalComplex ι (.up ℤ)).app J.obj)
    ((NatTrans.mapHomologicalComplex π (.up ℤ)).app J.obj)
    (injectiveBoundaryRow S F G ι π w₀ J).zero
  let B (c : I ⟶ J) : CochainComplex.mappingCone R.f ⟶
      CochainComplex.mappingCone R'.f :=
    CochainComplex.mappingCone.map _ _
      ((S.mapHomologicalComplex (.up ℤ)).map c.hom)
      ((F.mapHomologicalComplex (.up ℤ)).map c.hom)
      ((NatTrans.mapHomologicalComplex ι (.up ℤ)).naturality c.hom).symm
  change Nonempty (Homotopy (B b) (B b'))
  let H : ∀ i j, (CochainComplex.mappingCone R.f).X i ⟶
      (CochainComplex.mappingCone R'.f).X j := fun i j ↦
    (CochainComplex.mappingCone.snd R.f).v i i (add_zero i) ≫
      F.map (k.hom i j) ≫ (CochainComplex.mappingCone.inr R'.f).f j -
    (CochainComplex.mappingCone.fst R.f).1.v i (i + 1) rfl ≫
      S.map (k.hom (i + 1) (j + 1)) ≫
        (CochainComplex.mappingCone.inl R'.f).v (j + 1) j (by omega)
  have hleft (i j : ℤ) :
      (CochainComplex.mappingCone.inl R.f).v (i + 1) i (by omega) ≫ H i j =
        -(S.map (k.hom (i + 1) (j + 1)) ≫
          (CochainComplex.mappingCone.inl R'.f).v (j + 1) j (by omega)) := by
    simp [H, Preadditive.comp_sub]
  have hleftPrev (i : ℤ) :
      (CochainComplex.mappingCone.inl R.f).v (i + 1) i (by omega) ≫ H i (i - 1) =
        -(S.map (k.hom (i + 1) i) ≫
          (CochainComplex.mappingCone.inl R'.f).v i (i - 1) (by omega)) := by
    have hh := hleft i (i - 1)
    have hc (j l : ℤ) (e : j + 1 = l) :
        S.map (k.hom (i + 1) (j + 1)) ≫
          (CochainComplex.mappingCone.inl R'.f).v (j + 1) j (by omega) =
        S.map (k.hom (i + 1) l) ≫
          (CochainComplex.mappingCone.inl R'.f).v l j (by omega) := by
      subst l
      rfl
    exact hh.trans (congrArg Neg.neg (hc (i - 1) i (by omega)))
  have hright (i j : ℤ) :
      (CochainComplex.mappingCone.inr R.f).f i ≫ H i j =
        F.map (k.hom i j) ≫ (CochainComplex.mappingCone.inr R'.f).f j := by
    simp [H, Preadditive.comp_sub]
  have hmapleft (c : I ⟶ J) (i : ℤ) :
      (CochainComplex.mappingCone.inl R.f).v (i + 1) i (by omega) ≫
        (B c).f i =
      S.map (c.hom.f (i + 1)) ≫
        (CochainComplex.mappingCone.inl R'.f).v (i + 1) i (by omega) := by
    simp [B, R, R',
      CochainComplex.mappingCone.map]
  have hmapright (c : I ⟶ J) (i : ℤ) :
      (CochainComplex.mappingCone.inr R.f).f i ≫
        (B c).f i =
      F.map (c.hom.f i) ≫ (CochainComplex.mappingCone.inr R'.f).f i := by
    simp [B, R, R',
      CochainComplex.mappingCone.map]
  refine ⟨{ hom := H, zero := ?_, comm := ?_ }⟩
  · intro i j hij
    have h₁ := k.zero i j hij
    have h₂ := k.zero (i + 1) (j + 1) (by simpa using hij)
    simp [H, h₁, h₂]
  · intro i
    rw [dNext_eq H (show (ComplexShape.up ℤ).Rel i (i + 1) from rfl),
      prevD_eq H (show (ComplexShape.up ℤ).Rel (i - 1) i by dsimp; omega)]
    apply CochainComplex.mappingCone.ext_from R.f (i + 1) i rfl
    · have hs := congrArg S.map (k.comm (i + 1))
      simp only [dNext_eq k.hom
          (show (ComplexShape.up ℤ).Rel (i + 1) (i + 1 + 1) from rfl),
        prevD_eq k.hom (show (ComplexShape.up ℤ).Rel i (i + 1) from rfl),
        Functor.map_add, Functor.map_comp] at hs
      have hn := ι.naturality (k.hom (i + 1) i)
      simp only [Preadditive.comp_add]
      rw [hmapleft, ← Category.assoc,
        CochainComplex.mappingCone.inl_v_d R.f (i + 1) i (i + 1 + 1) (by omega) (by omega)]
      simp only [Preadditive.sub_comp, Category.assoc]
      rw [hright, hleft, ← Category.assoc _ (H i (i - 1)), hleftPrev, hmapleft]
      simp only [Preadditive.comp_neg, Preadditive.neg_comp, sub_neg_eq_add]
      have hassoc := Category.assoc (S.map (k.hom (i + 1) i))
        ((CochainComplex.mappingCone.inl R'.f).v i (i - 1) (by omega))
        ((CochainComplex.mappingCone R'.f).d (i - 1) i)
      rw [hassoc]
      rw [CochainComplex.mappingCone.inl_v_d R'.f i (i - 1) (i + 1)
        (by omega) (by omega)]
      dsimp only [R, R', injectiveBoundaryRow, Functor.mapHomologicalComplex_obj_X,
        Functor.mapHomologicalComplex_obj_d, NatTrans.mapHomologicalComplex_app_f] at *
      simp only [Preadditive.comp_sub]
      rw [hs]
      simp only [Preadditive.add_comp, Category.assoc]
      rw [← reassoc_of% hn]
      abel
    · have hf := congrArg F.map (k.comm i)
      simp only [dNext_eq k.hom (show (ComplexShape.up ℤ).Rel i (i + 1) from rfl),
        prevD_eq k.hom (show (ComplexShape.up ℤ).Rel (i - 1) i by dsimp; omega),
        Functor.map_add, Functor.map_comp] at hf
      simp only [Preadditive.comp_add]
      rw [hmapright, ← Category.assoc, CochainComplex.mappingCone.inr_f_d,
        Category.assoc, hright, ← Category.assoc _ (H i (i - 1)), hright, hmapright]
      rw [Category.assoc, CochainComplex.mappingCone.inr_f_d]
      dsimp only [R, R', injectiveBoundaryRow, Functor.mapHomologicalComplex_obj_d] at *
      simpa only [R, R', injectiveBoundaryRow, Functor.mapHomologicalComplex_obj_X,
        Preadditive.add_comp, Category.assoc] using
        congrArg (fun t ↦ t ≫ (CochainComplex.mappingCone.inr R'.f).f i) hf

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem exists_roof
    (h : ∀ (J : C) [Injective J], (ShortComplex.mk (ι.app J) (π.app J)
      (NatTrans.congr_app w₀ J)).ShortExact) :
    ∃ β : G.rightDerivedFunctorPlus ⟶
        S.rightDerivedFunctorPlus ⋙ shiftFunctor (DerivedCategory.Plus (ModuleCat.{m} A)) 1,
      ∀ (I : CochainComplex.Plus C) [∀ n : ℤ, Injective (I.obj.X n)]
        (K : DerivedCategory.Plus C) (e : DerivedCategory.Plus.Q.obj I ≅ K),
      DerivedCategory.Plus.ι.map (β.app K) ≫
          (DerivedCategory.Plus.ι.commShiftIso (1 : ℤ)).hom.app
            (S.rightDerivedFunctorPlus.obj K) = modelRoof S F G ι π w₀ h I K e := by
  classical
  let Q := (InjectiveObject.ι C).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh
  have model (K : DerivedCategory.Plus C) :
      ∃ I : CochainComplex.Plus C, (∀ n : ℤ, Injective (I.obj.X n)) ∧
        Nonempty (DerivedCategory.Plus.Q.obj I ≅ K) := by
    let M := Q.objPreimage K
    obtain ⟨L, hL⟩ := HomotopyCategory.Plus.quotient_obj_surjective M
    let I := (InjectiveObject.ι C).mapCochainComplexPlus.obj L
    exact ⟨I, fun n ↦ inferInstanceAs (Injective (L.obj.X n).obj),
      ⟨Q.mapIso (eqToIso hL) ≪≫ Q.objObjPreimageIso K⟩⟩
  choose I hI e using model
  let e (K : DerivedCategory.Plus C) := Classical.choice (e K)
  let β : G.rightDerivedFunctorPlus ⟶
      S.rightDerivedFunctorPlus ⋙ shiftFunctor (DerivedCategory.Plus (ModuleCat.{m} A)) (1 : ℤ) :=
    { app := fun K ↦ DerivedCategory.Plus.ι.preimage
        (modelRoof S F G ι π w₀ h (I K) K (e K) ≫
          (DerivedCategory.Plus.ι.commShiftIso (1 : ℤ)).inv.app
            (S.rightDerivedFunctorPlus.obj K))
      naturality := fun {K L} f ↦ by
        apply DerivedCategory.Plus.ι.map_injective
        simp only [Functor.map_comp, Functor.map_preimage, Functor.comp_map]
        rw [← Category.assoc, modelRoof_naturality S F G ι π w₀ h
          (I K) (I L) K L (e K) (e L) f, Category.assoc]
        simpa only [Category.assoc, Functor.comp_map] using congrArg
          (fun t ↦ modelRoof S F G ι π w₀ h (I K) K (e K) ≫ t)
          ((DerivedCategory.Plus.ι.commShiftIso (1 : ℤ)).inv.naturality
            (S.rightDerivedFunctorPlus.map f)) }
  refine ⟨β, ?_⟩
  intro J hJ K eJ
  have heq := modelRoof_naturality S F G ι π w₀ h J (I K) K K eJ (e K) (𝟙 K)
  simp only [Functor.map_id, Category.id_comp, Category.comp_id] at heq
  dsimp only [β]
  rw [Functor.map_preimage, Category.assoc, Iso.inv_hom_id_app]
  convert heq using 1 <;> simp only [Functor.comp_obj, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The signed cone roofs descend through right-derived units, agree with the normalized
injective snake boundary, and are functorial for all derived morphisms and all choices
of injective representatives.

Source: Stacks Project, derived.tex, Tag 014Z, section-canonical-delta-functor;
Tags 070I, 070J, 05TH, 05TI; homology.tex, Tag 0117.
(blueprint: lem-pur-injective-cone-boundary-descent)

Proof:
1. Exactness on injectives makes the termwise row short exact. The cone has
   differential `(db + u(a), -da)`; its map to the quotient is `v(b)`, a
   quasi-isomorphism by lem-pc-cone-short-exact-quasi-iso. Its signed roof is
   Mathlib's triangleOfSESδ, with negative projection as in Tag 014Z.
2. Given a cycle c and a lift b, exactness gives the unique a with u(a)=db.
   Injectivity gives da=0. The cone cycle (b,-a) maps to c and, under negative
   projection, to +a. Thus the roof sends [c] to [a].
3. Changing b by u(t) changes a by dt. Changing c by de and lifting e to f
   allows b to be changed by df, leaving db unchanged. Addition and scalar
   multiplication of lifts prove linearity. The Tag 0117 snake chase is the
   same lift calculation, so the roof cohomology is exactly the snake boundary
   (lem-weil-pbc-complex-ses-homology-long-exact).
4. The diagonal cone map induced by h commutes with the quotient and negative
   projection, giving the boundary square. A homotopy k induces the cone
   homotopy (F(k),-S(k)); its cross terms cancel by naturality of u.
   Hence all comparisons depend only on the homotopy class
   (lem-weil-pbc-homotopic-maps-equal-cohomology).
5. Choose bounded-below injective representatives using
   lem-weil-pbc-dplus-injective-representative. Every derived morphism lifts
   uniquely up to homotopy by lem-weil-pbc-kinjective-hom-derived. Transport
   the roofs by the isomorphisms of lem-weil-pbc-right-derived-plus-injective.
   Unit naturality and step 4 give a natural transformation on all of D+.
6. Apply the same square to the comparison between any two representatives.
   Its inverse lifts too, giving a homotopy equivalence. The transported roof
   is therefore independent of representatives. Step 3 and the same unit
   comparisons identify its cohomology with lem-pur-derived-injective-boundary
   in every integer degree and at every derived object. -/
theorem exists_injectiveConeBoundaryDescent
    (h : ∀ (J : C) [Injective J], (ShortComplex.mk (ι.app J) (π.app J)
      (NatTrans.congr_app w₀ J)).ShortExact) :
    ∃ (β : G.rightDerivedFunctorPlus ⟶
        S.rightDerivedFunctorPlus ⋙ shiftFunctor (DerivedCategory.Plus (ModuleCat.{m} A)) 1)
      (δ : ∀ n : ℤ,
        G.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor (ModuleCat.{m} A) n ⟶
        S.rightDerivedFunctorPlus ⋙
          DerivedCategory.Plus.homologyFunctor (ModuleCat.{m} A) (n + 1)),
      InjectiveBoundaryNormalized S F G ι π w₀ h δ ∧
      (∀ (K : DerivedCategory.Plus C) (n : ℤ),
        (δ n).app K = (DerivedCategory.homologyFunctor (ModuleCat.{m} A) 0).shiftMap
          (DerivedCategory.Plus.ι.map (β.app K) ≫
            (DerivedCategory.Plus.ι.commShiftIso (1 : ℤ)).hom.app
              (S.rightDerivedFunctorPlus.obj K)) n (n + 1) (by omega)) ∧
      (∀ (I : CochainComplex.Plus C) [∀ n : ℤ, Injective (I.obj.X n)],
        InjectiveConeRowProperties (injectiveBoundaryRow S F G ι π w₀ I)
          (injectiveBoundaryRow_shortExact S F G ι π w₀ h I) ∧
        ∀ (K : DerivedCategory.Plus C) (e : DerivedCategory.Plus.Q.obj I ≅ K),
          (injectiveConeModelIso G I K e).hom ≫ DerivedCategory.Plus.ι.map (β.app K) ≫
            (DerivedCategory.Plus.ι.commShiftIso (1 : ℤ)).hom.app
              (S.rightDerivedFunctorPlus.obj K) =
          DerivedCategory.triangleOfSESδ
              (injectiveBoundaryRow_shortExact S F G ι π w₀ h I) ≫
            (shiftFunctor (DerivedCategory (ModuleCat.{m} A)) (1 : ℤ)).map
              (injectiveConeModelIso S I K e).hom) ∧
      (∀ (I J : CochainComplex.Plus C)
        [∀ n : ℤ, Injective (I.obj.X n)] [∀ n : ℤ, Injective (J.obj.X n)] (b : I ⟶ J),
        (∀ (n : ℤ) (x : (F.obj (I.obj.X n))) (a : S.obj (I.obj.X (n + 1))),
          (injectiveBoundaryConeMap S F G ι π w₀ I J b).f n
              (injectiveConeVector (injectiveBoundaryRow S F G ι π w₀ I) n x a) =
            injectiveConeVector (injectiveBoundaryRow S F G ι π w₀ J) n
              (F.map (b.hom.f n) x) (S.map (b.hom.f (n + 1)) a)) ∧
        injectiveBoundaryConeMap S F G ι π w₀ I J b ≫
            CochainComplex.mappingCone.descShortComplex (injectiveBoundaryRow S F G ι π w₀ J) =
          CochainComplex.mappingCone.descShortComplex (injectiveBoundaryRow S F G ι π w₀ I) ≫
            (G.mapHomologicalComplex (.up ℤ)).map b.hom ∧
        injectiveBoundaryConeMap S F G ι π w₀ I J b ≫
            (CochainComplex.mappingCone.triangle
              (injectiveBoundaryRow S F G ι π w₀ J).f).mor₃ =
          (CochainComplex.mappingCone.triangle
              (injectiveBoundaryRow S F G ι π w₀ I).f).mor₃ ≫
            ((S.mapHomologicalComplex (.up ℤ)).map b.hom)⟦(1 : ℤ)⟧' ∧
        (∀ n : ℤ,
          HomologicalComplex.homologyMap ((G.mapHomologicalComplex (.up ℤ)).map b.hom) n ≫
              injectiveConeHomology (injectiveBoundaryRow S F G ι π w₀ J)
                (injectiveBoundaryRow_shortExact S F G ι π w₀ h J) n =
            injectiveConeHomology (injectiveBoundaryRow S F G ι π w₀ I)
                (injectiveBoundaryRow_shortExact S F G ι π w₀ h I) n ≫
              HomologicalComplex.homologyMap ((S.mapHomologicalComplex (.up ℤ)).map b.hom)
                (n + 1)) ∧
        ∀ (b' : I ⟶ J) (_hb : Homotopy b.hom b'.hom),
          Nonempty (Homotopy (injectiveBoundaryConeMap S F G ι π w₀ I J b)
            (injectiveBoundaryConeMap S F G ι π w₀ I J b')) ∧
          DerivedCategory.Plus.Q.map b = DerivedCategory.Plus.Q.map b') ∧
      (∀ (I J : CochainComplex.Plus C)
        [∀ n : ℤ, Injective (I.obj.X n)] [∀ n : ℤ, Injective (J.obj.X n)]
        (K L : DerivedCategory.Plus C)
        (e : DerivedCategory.Plus.Q.obj I ≅ K) (e' : DerivedCategory.Plus.Q.obj J ≅ L)
        (f : K ⟶ L),
        ∃ b : I ⟶ J, DerivedCategory.Plus.Q.map b ≫ e'.hom = e.hom ≫ f ∧
          ∀ (b' : I ⟶ J) (_hb : DerivedCategory.Plus.Q.map b' ≫ e'.hom = e.hom ≫ f),
            Nonempty (Homotopy b.hom b'.hom)) := by
  classical
  obtain ⟨β, hβ⟩ := exists_roof S F G ι π w₀ h
  obtain ⟨δ, hδ⟩ := exists_injectiveBoundary S F G ι π w₀ h
  refine ⟨β, δ, hδ, ?_, ?_, ?_, ?_⟩
  · intro K n
    let Q := (InjectiveObject.ι C).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh
    let M := Q.objPreimage K
    obtain ⟨L, hL⟩ := HomotopyCategory.Plus.quotient_obj_surjective M
    let I := (InjectiveObject.ι C).mapCochainComplexPlus.obj L
    have : ∀ n : ℤ, Injective (I.obj.X n) :=
      fun n ↦ inferInstanceAs (Injective (L.obj.X n).obj)
    let e : DerivedCategory.Plus.Q.obj I ≅ K :=
      Q.mapIso (eqToIso hL) ≪≫ Q.objObjPreimageIso K
    apply (cancel_epi (injectiveHomologyModelIso G I K e n).hom).1
    apply (cancel_mono (injectiveHomologyModelIso S I K e (n + 1)).inv).1
    rw [Category.assoc, hδ I K e n, hβ I K e]
    exact (modelRoof_homology S F G ι π w₀ h I K e n).symm
  · intro I hI
    refine ⟨coneRow_properties _ _, ?_⟩
    intro K e
    rw [hβ I K e]
    simp [modelRoof]
  · intro I J hI hJ b
    let φ : injectiveBoundaryRow S F G ι π w₀ I ⟶
        injectiveBoundaryRow S F G ι π w₀ J :=
      { τ₁ := (S.mapHomologicalComplex (.up ℤ)).map b.hom
        τ₂ := (F.mapHomologicalComplex (.up ℤ)).map b.hom
        τ₃ := (G.mapHomologicalComplex (.up ℤ)).map b.hom
        comm₁₂ := (NatTrans.mapHomologicalComplex ι (.up ℤ)).naturality b.hom
        comm₂₃ := (NatTrans.mapHomologicalComplex π (.up ℤ)).naturality b.hom }
    refine ⟨coneMap_vector S F G ι π w₀ I J b, ?_, ?_, ?_, ?_⟩
    · exact CochainComplex.mappingCone.descShortComplex_naturality φ
    · exact (CochainComplex.mappingCone.triangleMap _ _ φ.τ₁ φ.τ₂ φ.comm₁₂.symm).comm₃.symm
    · intro n
      rw [coneHomology_eq, coneHomology_eq]
      exact (HomologicalComplex.HomologySequence.δ_naturality φ
        (injectiveBoundaryRow_shortExact S F G ι π w₀ h I)
        (injectiveBoundaryRow_shortExact S F G ι π w₀ h J) n (n + 1) rfl).symm
    · intro b' hb
      refine ⟨coneMap_homotopy S F G ι π w₀ I J b b' hb, ?_⟩
      have heq : (HomotopyCategory.Plus.quotient C).map b =
          (HomotopyCategory.Plus.quotient C).map b' := by
        apply (HomotopyCategory.Plus.ι C).map_injective
        exact HomotopyCategory.eq_of_homotopy _ _ hb
      exact congrArg DerivedCategory.Plus.Qh.map heq
  · intro I J hI hJ K L e e' f
    exact model_chainMap I J K L e e' f

end CategoryTheory.Functor
