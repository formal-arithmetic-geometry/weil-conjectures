/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q43
-/
module
public import Sheaf.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Homology.HomComplex
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomModule
public import Mathlib.Algebra.Homology.Linear
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import WeilConjectures.Algebra.Homology.HomComplexComponents
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Sheaf.Algebra.Homology.ComplexColimitHomotopyColimit
/-! # Scalar telescopes for a functorial K-injective Hom representative
Source: Stacks Project, derived.tex, Tag 070I (lemma-K-injective), Tags 093W and 0949;
sites-cohomology.tex, Section 0A8X (section-hom-complexes)
(blueprint: lem-sfb-kinjective-hom-scalar-telescope).
The resolution functor is arbitrary and is not required to be linear. The two explicit
sequence diagrams have the same Hom-complex objects, and their colimits are taken in
complexes, hence termwise. Their derived comparison preserves every colimit leg.
-/
@[expose] public noncomputable section
set_option autoImplicit false
universe c v r w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
namespace CategoryTheory
/-- Naturality and K-injective detection identify the two scalar lifts up to homotopy. -/
private theorem scalar_resolution_homotopy
    {D : Type*} [Category* D] [Abelian D] [HasDerivedCategory.{w} D]
    {S : Type*} [CommRing S] [Linear S D]
    (I : CochainComplex D ℤ ⥤ CochainComplex D ℤ)
    (η : 𝟭 (CochainComplex D ℤ) ⟶ I)
    (P : CochainComplex D ℤ) [QuasiIso (η.app P)] [(I.obj P).IsKInjective]
    (s : S) : Nonempty (Homotopy (I.map (s • 𝟙 P)) (s • 𝟙 (I.obj P))) := by
  constructor
  apply HomotopyCategory.homotopyOfEq
  apply (CochainComplex.IsKInjective.Qh_map_bijective _ (I.obj P)).injective
  have he : η.app P ≫ I.map (s • 𝟙 P) = η.app P ≫ (s • 𝟙 (I.obj P)) := by
    rw [← η.naturality]
    change (s • 𝟙 P) ≫ η.app P = _
    simp only [Linear.smul_comp, Linear.comp_smul,
      Category.id_comp, Category.comp_id]
  have hq : DerivedCategory.Q.map (I.map (s • 𝟙 P)) =
      DerivedCategory.Q.map (s • 𝟙 (I.obj P)) := by
    rw [← cancel_epi (DerivedCategory.Q.map (η.app P)), ← Functor.map_comp,
      ← Functor.map_comp, he]
  apply (cancel_mono ((DerivedCategory.quotientCompQhIso D).hom.app (I.obj P))).1
  change (HomotopyCategory.quotient D (.up ℤ) ⋙ DerivedCategory.Qh).map _ ≫ _ =
    (HomotopyCategory.quotient D (.up ℤ) ⋙ DerivedCategory.Qh).map _ ≫ _
  rw [(DerivedCategory.quotientCompQhIso D).hom.naturality,
    (DerivedCategory.quotientCompQhIso D).hom.naturality, hq]

/-- Compare the distinguished telescope triangles using the identity on the coproduct. -/
private theorem sequential_colimit_derived_iso
    {D : Type*} [Category* D] [Abelian D] [HasDerivedCategory.{w} D]
    [HasCountableCoproducts D] [HasFilteredColimitsOfSize.{0, 0} D]
    [AB5OfSize.{0, 0} D]
    (X : CochainComplex D ℤ) (f g : X ⟶ X)
    (hfg : DerivedCategory.Q.map f = DerivedCategory.Q.map g) :
    ∃ e : DerivedCategory.Q.obj (colimit (Functor.ofSequence (fun _ : ℕ ↦ f))) ≅
        DerivedCategory.Q.obj (colimit (Functor.ofSequence (fun _ : ℕ ↦ g))),
      ∀ n : ℕ,
        DerivedCategory.Q.map (colimit.ι (Functor.ofSequence (fun _ : ℕ ↦ f)) n) ≫ e.hom =
        DerivedCategory.Q.map (colimit.ι (Functor.ofSequence (fun _ : ℕ ↦ g)) n) := by
  classical
  let F := Functor.ofSequence (fun _ : ℕ ↦ f)
  let G := Functor.ofSequence (fun _ : ℕ ↦ g)
  let B : Cofan (fun _ : ℕ ↦ X) := Cofan.mk (∐ fun _ : ℕ ↦ X) (Sigma.ι _)
  have hB : IsColimit B := coproductIsCoproduct _
  let u (a : X ⟶ X) : B.pt ⟶ B.pt :=
    Sigma.desc (fun n : ℕ ↦ B.inj n - a ≫ B.inj (n + 1))
  let q (E : ℕ ⥤ CochainComplex D ℤ) (hE : ∀ n, E.obj n = X) : B.pt ⟶ colimit E :=
    Sigma.desc (fun n ↦ eqToHom (hE n).symm ≫ colimit.ι E n)
  obtain ⟨p₁, _, _, _, ⟨hQB⟩, e₁, _, _, hT₁, _⟩ :=
    complex_colimit_homotopyColimit F B hB (colimit.cocone F) (colimit.isColimit F)
      (u f) (fun n ↦ by simp [u, B, F])
      (q F (fun _ ↦ rfl)) (fun n ↦ by simp [q, B])
  obtain ⟨p₂, _, _, _, _, e₂, _, _, hT₂, _⟩ :=
    complex_colimit_homotopyColimit G B hB (colimit.cocone G) (colimit.isColimit G)
      (u g) (fun n ↦ by simp [u, B, G])
      (q G (fun _ ↦ rfl)) (fun n ↦ by simp [q, B])
  have hu : DerivedCategory.Q.map (u f) = DerivedCategory.Q.map (u g) := by
    apply hQB.hom_ext
    rintro ⟨n⟩
    change DerivedCategory.Q.map (B.inj n) ≫ _ = DerivedCategory.Q.map (B.inj n) ≫ _
    rw [← Functor.map_comp, ← Functor.map_comp]
    simp only [u, B, Cofan.inj, Cofan.mk_ι_app, Sigma.ι_desc, Functor.map_sub, Functor.map_comp]
    rw [hfg]
  let t₁ := Triangle.mk (DerivedCategory.Q.map (u f))
    (DerivedCategory.Q.map (q F (fun _ ↦ rfl)))
    (e₁.inv ≫ (DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle (u f))).mor₃)
  let t₂ := Triangle.mk (DerivedCategory.Q.map (u g))
    (DerivedCategory.Q.map (q G (fun _ ↦ rfl)))
    (e₂.inv ≫ (DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle (u g))).mor₃)
  let e := Pretriangulated.isoTriangleOfIso₁₂ t₁ t₂ hT₁ hT₂
    (Iso.refl _) (Iso.refl _) (by simpa [t₁, t₂] using hu)
  refine ⟨Triangle.π₃.mapIso e, fun n ↦ ?_⟩
  have he := e.hom.comm₂
  change DerivedCategory.Q.map (q F (fun _ ↦ rfl)) ≫ e.hom.hom₃ =
    e.hom.hom₂ ≫ DerivedCategory.Q.map (q G (fun _ ↦ rfl)) at he
  have he₂ : e.hom.hom₂ = 𝟙 _ := by simp [e]
  rw [he₂, Category.id_comp] at he
  change DerivedCategory.Q.map (colimit.ι F n) ≫ e.hom.hom₃ =
    DerivedCategory.Q.map (colimit.ι G n)
  have hn := congrArg (DerivedCategory.Q.map (B.inj n) ≫ ·) he
  simpa only [← Category.assoc, ← Functor.map_comp, q, B, Cofan.inj, Cofan.mk_ι_app, Sigma.ι_desc,
    eqToHom_refl, Category.id_comp] using hn
variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R : Sheaf J CommRingCat.{max c v r})
attribute [local irreducible] homComplexFunctor homComplexπ homComplexIsLimit
set_option backward.isDefEq.respectTransparency false
set_option hygiene false in
local notation "Mod" => ringedSiteModules.{max c v r}
  ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)
omit [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}] in
private lemma homMap_add {M M' N N' : Mod} (f : M' ⟶ M) (g g' : N ⟶ N') :
    SheafOfModules.homObjMap.{max c v r, v, c, max c v r} (R := R) f (g + g') =
      SheafOfModules.homObjMap.{max c v r, v, c, max c v r} f g +
        SheafOfModules.homObjMap.{max c v r, v, c, max c v r} f g' := by
  apply SheafOfModules.hom_ext
  ext U φ
  rfl
omit [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}] in
private lemma homMap_zero {M M' N N' : Mod} (f : M' ⟶ M) :
    SheafOfModules.homObjMap.{max c v r, v, c, max c v r} (R := R) f (0 : N ⟶ N') = 0 := by
  apply SheafOfModules.hom_ext
  ext U φ
  rfl

/-- Postcompose each graded Hom factor with the specified degree −1 map. -/
private noncomputable def homPostHomotopyComponent
    {M N : CochainComplex Mod ℤ} {f g : M ⟶ N} (A : CochainComplex Mod ℤ)
    (h : Homotopy f g) (n m : ℤ) :
    (homComplex.{c, v, max c v r, max c v r} (R := R) A M).X n ⟶
      (homComplex.{c, v, max c v r, max c v r} (R := R) A N).X m :=
  Fan.IsLimit.lift (homComplexIsLimit.{c, v, max c v r, max c v r} A N m) fun p ↦
    homComplexπ.{c, v, max c v r, max c v r} A M n p (p + n) rfl ≫
      SheafOfModules.homObjMap.{max c v r, v, c, max c v r}
        (R := R) (𝟙 (A.X p)) (h.hom (p + n) (p + m))
omit [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}] in
private lemma homPostHomotopyComponent_π
    {M N : CochainComplex Mod ℤ} {f g : M ⟶ N} (A : CochainComplex Mod ℤ)
    (h : Homotopy f g) (n m p q q' : ℤ) (hpq : p + m = q) (hpq' : p + n = q') :
    homPostHomotopyComponent.{c, v, r} J R A h n m ≫
      homComplexπ.{c, v, max c v r, max c v r} A N m p q hpq =
      homComplexπ.{c, v, max c v r, max c v r} A M n p q' hpq' ≫
        SheafOfModules.homObjMap.{max c v r, v, c, max c v r}
        (R := R) (𝟙 (A.X p)) (h.hom q' q) := by
  subst q q'
  exact (homComplexIsLimit.{c, v, max c v r, max c v r} A N m).fac _ ⟨p⟩
attribute [local irreducible] homPostHomotopyComponent

private lemma additive_homotopy_cancellation {G : Type*} [AddCommGroup G]
    (a b c x : G) : a + b + c = (a - x) + (b + x) + c := by
  abel

attribute [local irreducible] SheafOfModules.homObj SheafOfModules.homObjMap

set_option backward.isDefEq.respectTransparency true in
set_option maxHeartbeats 600000 in
-- The component proof rewrites sheaf-Hom expressions with dependent integer degrees.
/-- The mixed differential terms cancel because consecutive signs are opposite. -/
private noncomputable def homPostHomotopy
    {M N : CochainComplex Mod ℤ} {f g : M ⟶ N} (A : CochainComplex Mod ℤ)
    (h : Homotopy f g) :
    Homotopy
      (C := homComplex.{c, v, max c v r, max c v r} (R := R) A M)
      (D := homComplex.{c, v, max c v r, max c v r} (R := R) A N)
      (((homComplexFunctor.{c, v, max c v r, max c v r} (R := R)).obj (op A)).map f)
      (((homComplexFunctor.{c, v, max c v r, max c v r} (R := R)).obj (op A)).map g) where
  hom := homPostHomotopyComponent.{c, v, r} J R A h
  zero n m hnm := by
    apply homComplex_hom_ext.{c, v, max c v r, max c v r} (L := A) (M := N)
    intro p q hpq
    rw [homPostHomotopyComponent_π.{c, v, r} J R A h n m p q (p + n) hpq rfl]
    rw [h.zero (p + n) q (by simp only [ComplexShape.up_Rel] at hnm ⊢; omega)]
    rw [homMap_zero.{c, v, r} J R, comp_zero, zero_comp]
  comm n := by
    apply homComplex_hom_ext.{c, v, max c v r, max c v r} (L := A) (M := N)
    intro p q hpq
    subst q
    have hn : (ComplexShape.up ℤ).Rel n (n + 1) := rfl
    have hm : (ComplexShape.up ℤ).Rel (n - 1) n := by simp
    rw [dNext_eq _ hn, prevD_eq _ hm]
    simp only [Preadditive.add_comp, Category.assoc]
    erw [homComplexFunctor_obj_map_f_π.{c, v, max c v r, max c v r} (L := A) f n p (p + n) rfl,
      homComplexFunctor_obj_map_f_π.{c, v, max c v r, max c v r} (L := A) g n p (p + n) rfl,
      homPostHomotopyComponent_π.{c, v, r} J R A h (n + 1) n p (p + n) (p + (n + 1)) rfl rfl,
      homComplex_d_π.{c, v, max c v r, max c v r} A N (n - 1) n p (p + n) (p + (n - 1)) (p + 1)
        (by omega) rfl rfl (by omega)]
    simp only [Preadditive.comp_sub, Linear.comp_units_smul, ← Category.assoc]
    rw [homPostHomotopyComponent_π.{c, v, r} J R A h n (n - 1) p (p + (n - 1)) (p + n) rfl rfl,
      homPostHomotopyComponent_π.{c, v, r} J R A h n (n - 1) (p + 1) (p + n) (p + (n + 1))
        (by omega) (by omega),
      homComplex_d_π.{c, v, max c v r, max c v r} A M n (n + 1) p (p + (n + 1)) (p + n) (p + 1)
        rfl rfl rfl (by omega)]
    simp only [Preadditive.sub_comp, Linear.units_smul_comp, Category.assoc,
      SheafOfModules.homObjMap_comp_homObjMap, Category.id_comp, Category.comp_id]
    have hc := h.comm (p + n)
    rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel (p + n) (p + (n + 1)) by
        simp only [ComplexShape.up_Rel]; omega),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel (p + (n - 1)) (p + n) by
        simp only [ComplexShape.up_Rel]; omega)] at hc
    rw [hc, homMap_add.{c, v, r} J R, homMap_add.{c, v, r} J R]
    simp only [Preadditive.comp_add]
    have hs : (n - 1).negOnePow = -n.negOnePow := by
      have := Int.negOnePow_succ (n - 1)
      simp only [sub_add_cancel] at this
      rw [this, neg_neg]
    rw [hs]
    simp only [Units.neg_smul, sub_neg_eq_add]
    exact additive_homotopy_cancellation _ _ _ _

attribute [local irreducible] homPostHomotopy
attribute [local semireducible] SheafOfModules.homObj SheafOfModules.homObjMap

/-- Multiplication by a global section on a complex, using the canonical sectionwise action.
Source: Stacks Project, Section 0A8X; the scalar-Hom telescope argument
(blueprint: lem-sfb-kinjective-hom-scalar-telescope). -/
def kInjectiveHomScalarEndomorphism
    (s : RingCat.sectionsSubring
      (R.obj ⋙ forget₂ CommRingCat.{max c v r} RingCat.{max c v r}))
    (K : CochainComplex (ringedSiteModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ) :
    K ⟶ K :=
  letI : Linear (RingCat.sectionsSubring
      (R.obj ⋙ forget₂ CommRingCat.{max c v r} RingCat.{max c v r}))
      (ringedSiteModules.{max c v r}
        ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) :=
    SheafOfModules.homLinear R.obj
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R).property
  s • 𝟙 K
omit [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}] in
private lemma homMap_scalar
    (s : RingCat.sectionsSubring
      (R.obj ⋙ forget₂ CommRingCat.{max c v r} RingCat.{max c v r}))
    (M N : Mod) :
    letI : Linear (RingCat.sectionsSubring
        (R.obj ⋙ forget₂ CommRingCat.{max c v r} RingCat.{max c v r})) Mod :=
      SheafOfModules.homLinear R.obj
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R).property
    SheafOfModules.homObjMap.{max c v r, v, c, max c v r} (R := R) (𝟙 M) (s • 𝟙 N) =
      s • 𝟙 (SheafOfModules.homObj.{max c v r, v, c, max c v r} (R := R) M N) := by
  let : Linear (RingCat.sectionsSubring
      (R.obj ⋙ forget₂ CommRingCat.{max c v r} RingCat.{max c v r})) Mod :=
    SheafOfModules.homLinear R.obj
    ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R).property
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  change (PresheafOfModules.restrictOver R.obj U.unop).map (𝟙 M.val) ≫ φ ≫
    (PresheafOfModules.restrictOver R.obj U.unop).map (s • 𝟙 N).val = (s.1 U) • φ
  ext W x
  change s.1 (op W.unop.left) • ((φ.app W).hom x) =
    R.obj.map W.unop.hom.op (s.1 U) • ((φ.app W).hom x)
  have hs : R.obj.map W.unop.hom.op (s.1 U) = s.1 (op W.unop.left) :=
    s.2 W.unop.hom.op
  exact congrArg (fun a ↦ a • ((φ.app W).hom x)) hs.symm
omit [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}] in
private lemma homComplex_map_scalar
    (s : RingCat.sectionsSubring
      (R.obj ⋙ forget₂ CommRingCat.{max c v r} RingCat.{max c v r}))
    (A M : CochainComplex Mod ℤ) :
    ((homComplexFunctor.{c, v, max c v r, max c v r} (R := R)).obj (op A)).map
       (kInjectiveHomScalarEndomorphism.{c, v, r} J R s M) =
      kInjectiveHomScalarEndomorphism.{c, v, r} J R s
        (homComplex.{c, v, max c v r, max c v r} (R := R) A M) := by
  let : Linear (RingCat.sectionsSubring
      (R.obj ⋙ forget₂ CommRingCat.{max c v r} RingCat.{max c v r})) Mod :=
    SheafOfModules.homLinear R.obj
    ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R).property
  apply HomologicalComplex.hom_ext
  intro n
  apply homComplex_hom_ext.{c, v, max c v r, max c v r}
  intro p q hpq
  rw [homComplexFunctor_obj_map_f_π.{c, v, max c v r, max c v r}]
  change homComplexπ.{c, v, max c v r, max c v r} A M n p q hpq ≫
    SheafOfModules.homObjMap.{max c v r, v, c, max c v r} (R := R) (𝟙 (A.X p)) (s • 𝟙 (M.X q)) =
      (s • 𝟙 ((homComplex.{c, v, max c v r, max c v r} (R := R) A M).X n)) ≫
        homComplexπ.{c, v, max c v r, max c v r} A M n p q hpq
  rw [homMap_scalar.{c, v, r} J R, Linear.comp_smul, Linear.smul_comp,
    Category.comp_id, Category.id_comp]
/-- The sequence with constant term Hom(A,I(P)) and transition Hom(A,I(s_P)).
Source: Stacks Project, Tag 070I and Section 0A8X; the scalar-Hom telescope argument
(blueprint: lem-sfb-kinjective-hom-scalar-telescope). -/
def kInjectiveHomFunctorialScalarTower
    (I : CochainComplex (ringedSiteModules.{max c v r}
        ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ ⥤
      CochainComplex (ringedSiteModules.{max c v r}
        ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ)
    (s : RingCat.sectionsSubring (R.obj ⋙ forget₂ CommRingCat.{max c v r} RingCat.{max c v r}))
    (A P : CochainComplex (ringedSiteModules.{max c v r}
        ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ) :
    ℕ ⥤ CochainComplex (ringedSiteModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ :=
  Functor.ofSequence
    (X := fun _n : ℕ ↦ homComplex.{c, v, max c v r, max c v r} (R := R) A (I.obj P))
    (fun _n ↦ ((homComplexFunctor.{c, v, max c v r, max c v r} (R := R)).obj (op A)).map
        (I.map (kInjectiveHomScalarEndomorphism.{c, v, r} J R s P)))
/-- The sequence with constant term X = Hom(A,I(P)) and scalar transition s_X.
Source: Stacks Project, Section 0A8X and Tags 093W, 0949; the scalar-Hom telescope argument
(blueprint: lem-sfb-kinjective-hom-scalar-telescope). -/
def kInjectiveHomScalarTower
    (I : CochainComplex (ringedSiteModules.{max c v r}
        ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ ⥤
      CochainComplex (ringedSiteModules.{max c v r}
        ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ)
    (s : RingCat.sectionsSubring (R.obj ⋙ forget₂ CommRingCat.{max c v r} RingCat.{max c v r}))
    (A P : CochainComplex (ringedSiteModules.{max c v r}
        ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ) :
    ℕ ⥤ CochainComplex (ringedSiteModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ :=
  Functor.ofSequence
    (X := fun _n : ℕ ↦ homComplex.{c, v, max c v r, max c v r} (R := R) A (I.obj P))
    (fun _n ↦ kInjectiveHomScalarEndomorphism.{c, v, r} J R s
      (homComplex.{c, v, max c v r, max c v r} (R := R) A (I.obj P)))
/-- The functorial-resolution and scalar transitions on Hom(A,I(P)) are homotopic;
their termwise colimits become isomorphic in D(R), compatibly with every leg, including zero.
Source: Stacks Project, Tag 070I (lemma-K-injective), Tags 093W, 0949 and Section 0A8X
(blueprint: lem-sfb-kinjective-hom-scalar-telescope).
Proof:
1. Write J₀ = I(P), a = I(s_P), b = s_J₀. Naturality of η and linearity of η_P give
η_P followed by a = s_P followed by η_P = η_P followed by b. Cancel Q(η_P), an
isomorphism, to obtain Q(a) = Q(b). The K-injective mapping-class bijection
(lem-weil-pbc-kinjective-hom-derived, Tag 070I) gives h with a-b = dh+hd.
2. On a degree-n family f in the Hom complex set H(f)^p = h^(p+n) f^p.
The Hom differential is d(f) = d_J₀ f - (-1)^n f d_A. Thus dH(f) has the term
(+(-1)^n) hf d_A while Hd(f) has its negative. They cancel, giving
dH+Hd = (dh+hd) postcomposition = t₁-t₂. Postcomposition with b is scalar s_X.
3. For each tower take B = the direct sum of its copies of X and set
u_k e_n = e_n - e_(n+1) t_k. The complex-colimit/homotopy-colimit theorem
(lem-kun-complex-colimit-hocolim) gives a canonical quasi-isomorphism
p_k : Cone(u_k) → C_k. It is q_k on the unshifted summand, zero on the shifted
summand, and satisfies p_k v_k e_n = j_n^(k) for every n. Exact filtered colimits
apply to the small filtered category of natural numbers, without monic transitions.
4. The telescope theorem also says the Q(e_n) form a coproduct cocone and supplies
   distinguished triangles Q(B) → Q(B) → Q(C_k). Homotopy invariance gives
   Q(t₁) = Q(t₂). Testing on Q(e_n) gives Q(u₁) = Q(u₂).
5. Complete the identity square on Q(B), Q(B) to an isomorphism of these
   distinguished triangles. Its third component γ satisfies Q(q₁) ≫ γ = Q(q₂).
   Precomposition with Q(e_n) gives the required equality on every colimit leg,
   including zero. No boundedness or continuity hypothesis is used. -/
theorem kInjectiveHom_scalar_telescope
    [AB5OfSize.{max c v r, max c v r} (ringedSiteModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R))]
    [HasDerivedCategory.{w} (ringedSiteModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R))]
    (I : CochainComplex (ringedSiteModules.{max c v r}
        ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ ⥤
      CochainComplex (ringedSiteModules.{max c v r}
        ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ)
    (η : 𝟭 (CochainComplex (ringedSiteModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ) ⟶ I)
    (hI : ∀ M : CochainComplex (ringedSiteModules.{max c v r}
        ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ,
      QuasiIso (η.app M) ∧ (I.obj M).IsKInjective)
    (s : RingCat.sectionsSubring (R.obj ⋙ forget₂ CommRingCat.{max c v r} RingCat.{max c v r}))
    (A P : CochainComplex (ringedSiteModules.{max c v r}
        ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ) :
    Nonempty (Homotopy
      (((homComplexFunctor.{c, v, max c v r, max c v r} (R := R)).obj (op A)).map
        (I.map (kInjectiveHomScalarEndomorphism.{c, v, r} J R s P)))
      (kInjectiveHomScalarEndomorphism.{c, v, r} J R s
        (homComplex.{c, v, max c v r, max c v r} (R := R) A (I.obj P)))) ∧
    ∃ γ : DerivedCategory.Q.obj
        (colimit (kInjectiveHomFunctorialScalarTower.{c, v, r} J R I s A P)) ≅
        DerivedCategory.Q.obj (colimit (kInjectiveHomScalarTower.{c, v, r} J R I s A P)),
      ∀ n : ℕ,
        DerivedCategory.Q.map
          (colimit.ι (kInjectiveHomFunctorialScalarTower.{c, v, r} J R I s A P) n) ≫
          γ.hom =
        DerivedCategory.Q.map (colimit.ι (kInjectiveHomScalarTower.{c, v, r} J R I s A P) n) := by
  let : Linear (RingCat.sectionsSubring
      (R.obj ⋙ forget₂ CommRingCat.{max c v r} RingCat.{max c v r})) Mod :=
    SheafOfModules.homLinear R.obj
    ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R).property
  have : QuasiIso (η.app P) := (hI P).1
  have : (I.obj P).IsKInjective := (hI P).2
  obtain ⟨h⟩ := scalar_resolution_homotopy I η P s
  have ht := homPostHomotopy.{c, v, r} J R A h
  change Homotopy
    (((homComplexFunctor.{c, v, max c v r, max c v r} (R := R)).obj (op A)).map
      (I.map (kInjectiveHomScalarEndomorphism.{c, v, r} J R s P)))
    (((homComplexFunctor.{c, v, max c v r, max c v r} (R := R)).obj (op A)).map
      (kInjectiveHomScalarEndomorphism.{c, v, r} J R s (I.obj P))) at ht
  rw [homComplex_map_scalar.{c, v, r} J R] at ht
  refine ⟨⟨ht⟩, ?_⟩
  have : AB5OfSize.{0, 0} Mod := AB5OfSize_shrink Mod
  have : HasColimitsOfSize.{0, 0} Mod :=
    hasColimitsOfSizeShrink.{0, 0, max c v r, max c v r} Mod
  exact sequential_colimit_derived_iso _ _ _ (DerivedCategory.Q_map_eq_of_homotopy Mod ht)
end CategoryTheory
