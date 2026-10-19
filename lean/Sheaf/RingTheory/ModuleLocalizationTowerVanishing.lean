/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups NO and H1
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.Algebra.Module.ULift
public import Mathlib.RingTheory.Localization.Away.Basic
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Sheaf.RingTheory.ModuleLocalizationFilteredColimit
import WeilConjectures.CategoryTheory.DerivedCategory.Coproducts
import WeilConjectures.CategoryTheory.DerivedCategory.ProjectiveSingleHom
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import Mathlib.Algebra.Module.LocalizedModule.IsLocalization

/-!
# Localization detects vanishing of the multiplication tower

Source: Stacks Project, More on Algebra, Tag 091P, equivalence (1) and (3)
(blueprint: lem-weil-pbc-module-localization-tower-vanishing).
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false in
private lemma triangle_hom_bijective {C : Type*} [Category C] [Preadditive C]
    [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (D : Pretriangulated.Triangle C) (hD : D ∈ distTriang C) (Y : C)
    (h : ∀ n : ℤ, ∀ g : D.obj₃⟦n⟧ ⟶ Y, g = 0) :
    Function.Bijective (fun g : D.obj₂ ⟶ Y ↦ D.mor₁ ≫ g) := by
  constructor
  · intro g g' he
    have hz : D.mor₁ ≫ (g - g') = 0 := by
      simpa only [Preadditive.comp_sub] using sub_eq_zero.mpr he
    obtain ⟨t, ht⟩ := D.yoneda_exact₂ hD (g - g') hz
    have ht0 : t = 0 := by
      apply (cancel_epi ((shiftFunctorZero C ℤ).hom.app D.obj₃)).mp
      simpa using h 0 ((shiftFunctorZero C ℤ).hom.app D.obj₃ ≫ t)
    exact sub_eq_zero.mp (by simpa [ht0] using ht)
  · intro g
    obtain ⟨t, ht⟩ := D.invRotate.yoneda_exact₂
      (Pretriangulated.inv_rot_of_distTriang _ hD) g (h (-1) _)
    exact ⟨t, ht.symm⟩

set_option backward.isDefEq.respectTransparency false in
private lemma triangle_hom_zero {C : Type*} [Category C] [Preadditive C]
    [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (D : Pretriangulated.Triangle C) (hD : D ∈ distTriang C) (Y : C)
    (hb : Function.Injective (fun g : D.obj₂ ⟶ Y ↦ D.mor₁ ≫ g))
    (hs : Function.Surjective (fun g : D.obj₂⟦(1 : ℤ)⟧ ⟶ Y ↦
      D.mor₁⟦(1 : ℤ)⟧' ≫ g)) (g : D.obj₃ ⟶ Y) : g = 0 := by
  have hz : D.mor₂ ≫ g = 0 := by
    apply hb
    simpa only [Category.assoc, comp_zero, zero_comp] using
      congrArg (fun z ↦ z ≫ g) (Pretriangulated.comp_distTriang_mor_zero₁₂ D hD)
  obtain ⟨t, ht⟩ := D.yoneda_exact₃ hD g hz
  obtain ⟨s, hs⟩ := hs t
  rw [ht, ← hs, ← Category.assoc, Pretriangulated.comp_distTriang_mor_zero₃₁ D hD, zero_comp]

private lemma bijective_conjugate_iff {X Y : Type*} (e : X ≃ Y)
    (a : X → X) (b : Y → Y) (h : ∀ x, e (a x) = b (e x)) :
    Function.Bijective a ↔ Function.Bijective b := by
  constructor
  · intro ha
    have eq : b = e ∘ a ∘ e.symm := by
      funext y
      simpa using (h (e.symm y)).symm
    rw [eq]
    exact e.bijective.comp (ha.comp e.symm.bijective)
  · intro hb
    have eq : a = e.symm ∘ b ∘ e := by
      funext x
      simpa using (congrArg e.symm (h x))
    rw [eq]
    exact e.symm.bijective.comp (hb.comp e.bijective)

set_option backward.isDefEq.respectTransparency false in
private lemma precomp_shift_twice_bijective {C : Type*} [Category C]
    [HasShift C ℤ] {X X' Y : C} (d : X ⟶ X') (q r : ℤ)
    (h : Function.Bijective (fun g : X'⟦q + r⟧ ⟶ Y ↦ d⟦q + r⟧' ≫ g)) :
    Function.Bijective (fun g : (X'⟦q⟧)⟦r⟧ ⟶ Y ↦ (d⟦q⟧')⟦r⟧' ≫ g) := by
  let eX := (shiftFunctorAdd C q r).app X
  let eX' := (shiftFunctorAdd C q r).app X'
  have eq : (fun g : (X'⟦q⟧)⟦r⟧ ⟶ Y ↦ (d⟦q⟧')⟦r⟧' ≫ g) =
      (fun g ↦ eX.inv ≫ g) ∘
        (fun g : X'⟦q + r⟧ ⟶ Y ↦ d⟦q + r⟧' ≫ g) ∘
          (fun g ↦ eX'.hom ≫ g) := by
    funext g
    dsimp [eX, eX']
    apply (cancel_epi eX.hom).mp
    simp [eX]
  rw [eq]
  simpa [Iso.homCongr] using (Iso.homCongr eX (Iso.refl Y)).bijective.comp
    (h.comp (Iso.homCongr eX' (Iso.refl Y)).symm.bijective)

private noncomputable def scalarTelescopeCofan (A : Type u) [CommRing A] :
    Cofan (fun _ : ℕ ↦ ModuleCat.of A (ULift.{v} A)) :=
  Cofan.mk (ModuleCat.of A (ℕ →₀ ULift.{v} A))
    (fun n ↦ ModuleCat.ofHom (Finsupp.lsingle n))

set_option backward.isDefEq.respectTransparency false in
private noncomputable def scalarTelescopeIsColimit (A : Type u) [CommRing A] :
    IsColimit (scalarTelescopeCofan.{u, v} A) := by
  refine Cofan.IsColimit.mk _
    (fun s ↦ ModuleCat.ofHom (Finsupp.lsum A (fun n ↦ (s.inj n).hom))) ?_ ?_
  · intro s n
    ext x
    simp [scalarTelescopeCofan]
  · intro s g hg
    apply ModuleCat.hom_ext
    apply Finsupp.lhom_ext
    intro n x
    have h := ConcreteCategory.congr_hom (hg n) x
    simpa [scalarTelescopeCofan] using h

private noncomputable def scalarTelescopeDifferential {A : Type u} [CommRing A] (f : A) :
    ModuleCat.of A (ℕ →₀ ULift.{v} A) ⟶ ModuleCat.of A (ℕ →₀ ULift.{v} A) :=
  ModuleCat.ofHom (LinearMap.id - f • Finsupp.lmapDomain (ULift.{v} A) A Nat.succ)

set_option backward.isDefEq.respectTransparency false in
private lemma scalarTelescopeDifferential_inj {A : Type u} [CommRing A] (f : A)
    (n : ℕ) :
    (scalarTelescopeCofan.{u, v} A).inj n ≫ scalarTelescopeDifferential f =
      (scalarTelescopeCofan.{u, v} A).inj n -
        f • (scalarTelescopeCofan.{u, v} A).inj (n + 1) := by
  ext x
  simp [scalarTelescopeCofan, scalarTelescopeDifferential,
    Finsupp.lmapDomain_apply, Finsupp.smul_single]

private lemma scalarTelescopeDifferential_mono {A : Type u} [CommRing A] (f : A) :
    Mono (scalarTelescopeDifferential.{u, v} f) := by
  rw [ModuleCat.mono_iff_injective]
  apply LinearMap.ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  intro x hx
  ext n
  have hx' : ∀ n, x n = 0 := by
    intro n
    induction n with
    | zero =>
      have h := congrArg (fun y : ℕ →₀ ULift.{v} A ↦ y 0) hx
      simpa [scalarTelescopeDifferential, Finsupp.lmapDomain_apply,
        Finsupp.mapDomain_of_notMem_range, Nat.succ_ne_zero] using h
    | succ n ih =>
      have h := congrArg (fun y : ℕ →₀ ULift.{v} A ↦ y (n + 1)) hx
      simpa [scalarTelescopeDifferential, Finsupp.lmapDomain_apply,
        Finsupp.mapDomain_apply Nat.succ_injective, ih] using h
  exact congrArg ULift.down (hx' n)

set_option backward.isDefEq.respectTransparency false in
lemma telescope_shortExact {C : Type*} [Category C] [Abelian C]
    (E : ℕ ⥤ C) [HasColimit E] (c : Cofan E.obj) (hc : IsColimit c)
    (d : c.pt ⟶ c.pt) [Mono d]
    (hd : ∀ n, c.inj n ≫ d =
      c.inj n - E.map (homOfLE (Nat.le_succ n)) ≫ c.inj (n + 1)) :
    ∃ (e : c.pt ⟶ colimit E) (he : d ≫ e = 0),
      (ShortComplex.mk d e he).ShortExact := by
  let e := Cofan.IsColimit.desc hc (fun n ↦ colimit.ι E n)
  have he : d ≫ e = 0 := by
    apply Cofan.IsColimit.hom_ext hc
    intro n
    rw [← Category.assoc, hd]
    simp [e, Preadditive.sub_comp, Category.assoc, Cofan.IsColimit.fac, colimit.w]
  let cocone (s : CokernelCofork d) : Cocone E :=
    { pt := s.pt
      ι :=
        { app := fun n ↦ c.inj n ≫ s.π
          naturality := by
            intro n m a
            have hs (k : ℕ) :
                E.map (homOfLE (Nat.le_succ k)) ≫ c.inj (k + 1) ≫ s.π =
                  c.inj k ≫ s.π := by
              have hz := congrArg (fun z ↦ c.inj k ≫ z) s.condition
              rw [← Category.assoc, hd] at hz
              exact (sub_eq_zero.mp (by
                simpa [Preadditive.sub_comp] using hz)).symm
            have hall (m : ℕ) (hnm : n ≤ m) :
                E.map (homOfLE hnm) ≫ c.inj m ≫ s.π = c.inj n ≫ s.π := by
              induction m, hnm using Nat.le_induction with
              | base => simp
              | succ k hnk ih =>
                rw [show homOfLE (Nat.le_trans hnk (Nat.le_succ k)) =
                  homOfLE hnk ≫ homOfLE (Nat.le_succ k) from Subsingleton.elim _ _]
                rw [E.map_comp, Category.assoc, hs k]
                exact ih
            dsimp only [Functor.const]
            rw [Category.comp_id]
            rw [show a = homOfLE (leOfHom a) from Subsingleton.elim _ _]
            exact hall m (leOfHom a) } }
  have hco : IsColimit (CokernelCofork.ofπ e he) := by
    refine Cofork.IsColimit.mk _ (fun s ↦ colimit.desc E (cocone s)) ?_ ?_
    · intro s
      apply Cofan.IsColimit.hom_ext hc
      intro n
      simp [e, cocone, Cofan.IsColimit.fac_assoc]
    · intro s m hm
      apply colimit.hom_ext (F := E)
      intro n
      have hn := congrArg (fun z ↦ c.inj n ≫ z) hm
      simpa [e, cocone, Category.assoc, Cofan.IsColimit.fac_assoc] using hn
  refine ⟨e, he, ?_⟩
  exact
    { exact := ShortComplex.exact_of_g_is_cokernel _ hco
      mono_f := inferInstance
      epi_g := epi_of_isColimit_cofork hco }

set_option backward.isDefEq.respectTransparency false in
private lemma scalarTelescope_localization_iso {A : Type u} [CommRing A] (f : A) :
    let E := Functor.ofSequence (X := fun _ : ℕ ↦ ModuleCat.of A (ULift.{v} A))
      (fun _ ↦ ModuleCat.ofHom (LinearMap.lsmul A (ULift.{v} A) f))
    Nonempty (colimit E ≅ ModuleCat.of A (ULift.{v} (Localization.Away f))) := by
  obtain ⟨e, _⟩ := ModuleCat.localization_away_colimit f (ULift.{v} A)
  let l : ULift.{v} A →ₗ[A] ULift.{v} (Localization.Away f) :=
    ULift.moduleEquiv.symm.toLinearMap.comp
      ((Algebra.linearMap A (Localization.Away f)).comp ULift.moduleEquiv.toLinearMap)
  have : IsLocalizedModule (Submonoid.powers f) l := by
    dsimp [l]
    infer_instance
  exact ⟨(e.trans (IsLocalizedModule.iso (Submonoid.powers f) l)).toModuleIso⟩

set_option backward.isDefEq.respectTransparency false in
private lemma scalarTelescope_triangle {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{max u v} A)] (f : A) :
    let S := DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0
    ∃ (ε : S.obj (ModuleCat.of A (ℕ →₀ ULift.{v} A)) ⟶
        S.obj (ModuleCat.of A (ULift.{v} (Localization.Away f))))
      (δ : S.obj (ModuleCat.of A (ULift.{v} (Localization.Away f))) ⟶
        (S.obj (ModuleCat.of A (ℕ →₀ ULift.{v} A)))⟦(1 : ℤ)⟧),
      Pretriangulated.Triangle.mk (S.map (scalarTelescopeDifferential f)) ε δ ∈ distTriang _ := by
  dsimp only
  let E := Functor.ofSequence (X := fun _ : ℕ ↦ ModuleCat.of A (ULift.{v} A))
    (fun _ ↦ ModuleCat.ofHom (LinearMap.lsmul A (ULift.{v} A) f))
  have : Mono (scalarTelescopeDifferential.{u, v} f) := scalarTelescopeDifferential_mono f
  obtain ⟨ε, hε, hS⟩ := telescope_shortExact E (scalarTelescopeCofan A)
    (scalarTelescopeIsColimit A) (scalarTelescopeDifferential f) (fun n ↦ by
      rw [scalarTelescopeDifferential_inj]
      congr 1
      ext x
      rw [show E.map (homOfLE (Nat.le_succ n)) =
        ModuleCat.ofHom (LinearMap.lsmul A (ULift.{v} A) f) from
        Functor.ofSequence_map_homOfLE_succ _ _]
      change f • Finsupp.single (n + 1) x = Finsupp.single (n + 1) (f • x)
      simp)
  let SC := ShortComplex.mk (scalarTelescopeDifferential f) ε hε
  let F := HomologicalComplex.single (ModuleCat.{max u v} A) (.up ℤ) 0
  have hs : (SC.map F).ShortExact := hS.map_of_exact F
  obtain ⟨e⟩ := scalarTelescope_localization_iso.{u, v} f
  let e' := (DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).mapIso e
  refine ⟨DerivedCategory.Q.map (F.map ε) ≫ e'.hom,
    e'.inv ≫ DerivedCategory.triangleOfSESδ hs, ?_⟩
  apply Pretriangulated.isomorphic_distinguished _ (DerivedCategory.triangleOfSES_distinguished hs)
  refine Pretriangulated.Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) e'.symm ?_ ?_ ?_
  all_goals simp [DerivedCategory.triangleOfSES, SC, F]
  rfl

set_option backward.isDefEq.respectTransparency false in
private noncomputable def scalarTelescope_derivedIsColimit {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{max u v} A)] (q : ℤ) :
    let S := DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0
    IsColimit (Cofan.mk ((S.obj (scalarTelescopeCofan.{u, v} A).pt)⟦q⟧)
      (fun n ↦ (S.map ((scalarTelescopeCofan A).inj n))⟦q⟧')) := by
  dsimp only
  let F := HomologicalComplex.single (ModuleCat.{max u v} A) (.up ℤ) 0
  let : IsGrothendieckAbelian.{max u v} (ModuleCat.{max u v} A) :=
    IsGrothendieckAbelian.of_equivalence
      (ModuleCat.restrictScalarsEquivalenceOfRingEquiv
        (ULift.ringEquiv : ULift.{v} A ≃+* A)).symm
  let : Abelian.HasKInjectiveResolutions (ModuleCat.{max u v} A) :=
    Abelian.hasKInjectiveResolutions_of_isGrothendieckAbelian.{max u v}
  have hc := isColimitCofanMkObjOfIsColimit F _ _ (scalarTelescopeIsColimit.{u, v} A)
  have hc' := DerivedCategory.isColimitCofanMkQObj hc
  exact isColimitCofanMkObjOfIsColimit (shiftFunctor _ q) _ _ hc'

set_option backward.isDefEq.respectTransparency false in
private lemma scalarTelescope_roos_hom_bijective {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{max u v} A)] (f : A)
    (K : DerivedCategory (ModuleCat.{max u v} A)) [HasProduct (fun _ : ℕ ↦ K)]
    (q : ℤ) :
    let S := DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0
    Function.Bijective
      (fun g : (S.obj (ModuleCat.of A (ℕ →₀ ULift.{v} A)))⟦q⟧ ⟶ K ↦
        (S.map (scalarTelescopeDifferential f))⟦q⟧' ≫ g) ↔
      Function.Bijective
        (fun g : (S.obj (ModuleCat.of A (ULift.{v} A)))⟦q⟧ ⟶ ∏ᶜ (fun _ : ℕ ↦ K) ↦
          g ≫ towerTransitionEndomorphism (K := fun _ : ℕ ↦ K) (fun _ : ℕ ↦ f • 𝟙 K)) := by
  dsimp only
  let S := DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0
  let c := scalarTelescopeCofan.{u, v} A
  let e := Equiv.ofBijective
    (fun g : (S.obj c.pt)⟦q⟧ ⟶ K ↦ fun n ↦ (S.map (c.inj n))⟦q⟧' ≫ g)
    (Cofan.IsColimit.bijective (scalarTelescope_derivedIsColimit (A := A) q) K)
  let e' := Equiv.ofBijective
    (fun g : (S.obj (ModuleCat.of A (ULift.{v} A)))⟦q⟧ ⟶ ∏ᶜ (fun _ : ℕ ↦ K) ↦
      fun n ↦ g ≫ Pi.π _ n)
    (Fan.IsLimit.bijective (productIsProduct (fun _ : ℕ ↦ K)) _)
  let b := fun t : ℕ → ((S.obj (ModuleCat.of A (ULift.{v} A)))⟦q⟧ ⟶ K) ↦
    fun n ↦ t n - f • t (n + 1)
  have h₁ := bijective_conjugate_iff e
    (fun g ↦ (S.map (scalarTelescopeDifferential f))⟦q⟧' ≫ g) b (by
      intro g
      funext n
      change (S.map (c.inj n))⟦q⟧' ≫
          (S.map (scalarTelescopeDifferential f))⟦q⟧' ≫ g =
        (S.map (c.inj n))⟦q⟧' ≫ g - f • ((S.map (c.inj (n + 1)))⟦q⟧' ≫ g)
      rw [← Category.assoc, ← Functor.map_comp, ← S.map_comp]
      rw [scalarTelescopeDifferential_inj]
      simp [Functor.map_sub, Functor.map_smul, Preadditive.sub_comp, Linear.smul_comp, c])
  have h₂ := bijective_conjugate_iff e'
    (fun g ↦ g ≫ towerTransitionEndomorphism (K := fun _ : ℕ ↦ K) (fun _ : ℕ ↦ f • 𝟙 K)) b (by
      intro g
      funext n
      change (g ≫ towerTransitionEndomorphism (K := fun _ : ℕ ↦ K)
        (fun _ : ℕ ↦ f • 𝟙 K)) ≫ Pi.π _ n = _
      simp [towerTransitionEndomorphism, towerProductShift, Preadditive.comp_sub,
        Preadditive.sub_comp, Category.assoc, Linear.comp_smul, b, e'])
  exact h₁.trans h₂.symm

private lemma bijective_square_iff {X Y X' Y' : Type*} (e : X ≃ X') (e' : Y ≃ Y')
    (a : X → Y) (b : X' → Y') (h : ∀ x, e' (a x) = b (e x)) :
    Function.Bijective a ↔ Function.Bijective b := by
  constructor
  · intro ha
    have eq : b = e' ∘ a ∘ e.symm := by
      funext y
      simpa using (h (e.symm y)).symm
    rw [eq]
    exact e'.bijective.comp (ha.comp e.symm.bijective)
  · intro hb
    have eq : a = e'.symm ∘ b ∘ e := by
      funext x
      simpa using congrArg e'.symm (h x)
    rw [eq]
    exact e'.symm.bijective.comp (hb.comp e.bijective)

set_option backward.isDefEq.respectTransparency false in
private noncomputable def liftedUnitHomEquiv {A : Type u} [CommRing A]
    (M : ModuleCat.{max u v} A) :
    (ModuleCat.of A (ULift.{v} A) ⟶ M) ≃ M where
  toFun g := g (ULift.up 1)
  invFun x := ModuleCat.ofHom
    ((LinearMap.toSpanSingleton A M x).comp ULift.moduleEquiv.toLinearMap)
  left_inv g := by
    apply ModuleCat.hom_ext
    ext x
    change x.down • g (ULift.up 1) = g x
    rw [← g.hom.map_smul]
    congr 1
    apply ULift.ext
    simp
  right_inv x := by simp

set_option backward.isDefEq.respectTransparency false in
private lemma isIso_of_liftedUnit_hom_bijective {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{max u v} A)]
    {X Y : DerivedCategory (ModuleCat.{max u v} A)} (d : X ⟶ Y)
    (h : ∀ q : ℤ, Function.Bijective
      (fun g : ((DerivedCategory.singleFunctor _ 0).obj
        (ModuleCat.of A (ULift.{v} A)))⟦q⟧ ⟶ X ↦ g ≫ d)) : IsIso d := by
  let P := ModuleCat.of A (ULift.{v} A)
  let S := DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0
  have : Projective P := inferInstance
  rw [DerivedCategory.isIso_iff]
  intro n
  let adj : shiftFunctor (DerivedCategory (ModuleCat.{max u v} A)) (-n) ⊣
      shiftFunctor _ n := (shiftEquiv' _ (-n) n (by simp)).toAdjunction
  have hb : Function.Bijective (fun g : S.obj P ⟶ X⟦n⟧ ↦ g ≫ d⟦n⟧') :=
    (bijective_square_iff (adj.homEquiv (S.obj P) X)
      (adj.homEquiv (S.obj P) Y) _ _ (fun g ↦
        adj.homEquiv_naturality_right g d)).mp (h (-n))
  let eX := DerivedCategory.singleFunctorZeroHomEquiv P (X⟦n⟧)
  let eY := DerivedCategory.singleFunctorZeroHomEquiv P (Y⟦n⟧)
  have hb' : Function.Bijective (fun g : P ⟶
      (DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) 0).obj (X⟦n⟧) ↦
        g ≫ (DerivedCategory.homologyFunctor _ 0).map (d⟦n⟧')) :=
    (bijective_square_iff eX eY _ _ (fun g ↦ by
      simp [eX, eY, DerivedCategory.singleFunctorZeroHomEquiv_apply])).mp hb
  have hi : IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) 0).map
      (d⟦n⟧')) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact (bijective_square_iff (liftedUnitHomEquiv _) (liftedUnitHomEquiv _)
      _ _ (fun g ↦ rfl)).mp hb'
  exact (NatIso.isIso_map_iff ((DerivedCategory.homologyFunctor
    (ModuleCat.{max u v} A) 0).isoShift n) d).mp hi

private lemma precomp_units_bijective_iff {C : Type*} [Category C] [Preadditive C]
    {X X' Y : C} (d : X ⟶ X') (a : ℤˣ) :
    Function.Bijective (fun g : X' ⟶ Y ↦ (a • d) ≫ g) ↔
      Function.Bijective (fun g : X' ⟶ Y ↦ d ≫ g) := by
  have he : (fun g : X' ⟶ Y ↦ (a • d) ≫ g) =
      (fun g : X ⟶ Y ↦ a • g) ∘ (fun g : X' ⟶ Y ↦ d ≫ g) := by
    funext g
    simp [Linear.units_smul_comp]
  rw [he]
  exact Function.Bijective.of_comp_iff'
    (MulAction.bijective a : Function.Bijective (fun g : X ⟶ Y ↦ a • g)) _

set_option backward.isDefEq.respectTransparency false in
private lemma triangle_orthogonal_iff {C : Type*} [Category C] [Preadditive C]
    [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (D : Pretriangulated.Triangle C) (hD : D ∈ distTriang C) (Y : C) :
    (∀ q : ℤ, ∀ g : D.obj₃⟦q⟧ ⟶ Y, g = 0) ↔
      ∀ q : ℤ, Function.Bijective (fun g : D.obj₂⟦q⟧ ⟶ Y ↦ D.mor₁⟦q⟧' ≫ g) := by
  constructor
  · intro h q
    have hz (n : ℤ) (g : (D.obj₃⟦q⟧)⟦n⟧ ⟶ Y) : g = 0 := by
      let e := (shiftFunctorAdd C q n).app D.obj₃
      apply (cancel_epi e.hom).mp
      rw [h (q + n) (e.hom ≫ g), comp_zero]
    have hb := triangle_hom_bijective ((shiftFunctor (Pretriangulated.Triangle C) q).obj D)
      (D.shift_distinguished hD q) Y hz
    exact (precomp_units_bijective_iff (D.mor₁⟦q⟧') q.negOnePow).mp hb
  · intro h q g
    have hb := (precomp_units_bijective_iff (D.mor₁⟦q⟧') q.negOnePow).mpr (h q)
    have hs := (precomp_units_bijective_iff ((D.mor₁⟦q⟧')⟦(1 : ℤ)⟧')
      q.negOnePow).mpr (precomp_shift_twice_bijective D.mor₁ q 1 (h (q + 1)))
    apply triangle_hom_zero ((shiftFunctor (Pretriangulated.Triangle C) q).obj D)
      (D.shift_distinguished hD q) Y hb.injective _ g
    change Function.Surjective (fun g : (D.obj₂⟦q⟧)⟦(1 : ℤ)⟧ ⟶ Y ↦
      (q.negOnePow • D.mor₁⟦q⟧')⟦(1 : ℤ)⟧' ≫ g)
    simpa only [Functor.map_units_smul] using hs.surjective

namespace DerivedCategory

/-- Vanishing of any derived limit of the multiplication-by-`f` tower is equivalent to
vanishing of every Hom group from the shifted degree-zero localization.
`ULift` only places the localization in the chosen module universe; it is linearly
isomorphic to the original localization by `ULift.moduleEquiv`.

Source: Stacks Project, More on Algebra, Tag 091P, equivalence (1) and (3)
(blueprint: lem-weil-pbc-module-localization-tower-vanishing).

Proof: Use the free telescope resolution in Tag 091P directly. Its free module is
`P = ℕ →₀ ULift A`; the differential is `1 - f * successor` and is injective by
induction on the coordinates, without cancelling `f`. The cokernel is the colimit
of the sequence `A --f--> A --f--> ...`: a map killing the differential is precisely
a compatible cocone. The existing module-localization colimit theorem identifies this
cokernel with `ULift (A[1/f])`. Applying the degree-zero complex functor and localization
therefore gives a distinguished triangle `P[0] → P[0] → A[1/f][0] → P[0][1]`.

The coproduct property of `P[0]`, including after every shift, identifies precomposition
by the telescope differential with `(x_n) ↦ (x_n - f x_(n+1))` on families of maps.
The product property identifies postcomposition by the Roos endomorphism with the same
map. Exactness of Hom on the telescope triangle says all shifted Hom groups from the
localization vanish exactly when these maps are bijective in every degree. Shifts of
`ULift A[0]` detect isomorphisms: their Hom groups compute the elements of cohomology,
by projectivity of `ULift A`. Thus bijectivity is equivalent to the Roos endomorphism
being an isomorphism. In the given Roos triangle this is equivalent to `IsZero T`.
All constructions respect the stated universes, and no boundedness or regularity
hypothesis is used. -/
theorem module_localization_tower_vanishing_iff {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{max u v} A)] (f : A)
    (K : DerivedCategory (ModuleCat.{max u v} A)) [HasProduct (fun _ : ℕ ↦ K)]
    (T : DerivedCategory (ModuleCat.{max u v} A))
    (hT : IsDerivedLimit (K := fun _ : ℕ ↦ K) (fun _ ↦ f • 𝟙 K) T) :
    IsZero T ↔ ∀ (q : ℤ), ∀ (g :
      ((singleFunctor (ModuleCat.{max u v} A) 0).obj
        (ModuleCat.of A (ULift.{v} (Localization.Away f))))⟦q⟧ ⟶ K), g = 0 := by
  obtain ⟨p, δ, hD⟩ := hT
  have hzero : IsZero T ↔ IsIso
      (towerTransitionEndomorphism (K := fun _ : ℕ ↦ K) (fun _ : ℕ ↦ f • 𝟙 K)) :=
    Pretriangulated.Triangle.isZero₁_iff_isIso₂
      (Pretriangulated.Triangle.mk p (towerTransitionEndomorphism (K := fun _ : ℕ ↦ K)
        (fun _ : ℕ ↦ f • 𝟙 K)) δ) hD
  rw [hzero]
  let S := singleFunctor (ModuleCat.{max u v} A) 0
  obtain ⟨ε, δ', hL⟩ := scalarTelescope_triangle.{u, v, w} f
  let D := Pretriangulated.Triangle.mk (S.map (scalarTelescopeDifferential f)) ε δ'
  have he := triangle_orthogonal_iff D hL K
  change IsIso _ ↔ ∀ q : ℤ, ∀ g : D.obj₃⟦q⟧ ⟶ K, g = 0
  rw [he]
  constructor
  · intro hi q
    apply (scalarTelescope_roos_hom_bijective f K q).mpr
    simpa [Iso.homCongr] using
      (Iso.homCongr (Iso.refl ((S.obj (ModuleCat.of A (ULift.{v} A)))⟦q⟧))
        (asIso (towerTransitionEndomorphism (K := fun _ : ℕ ↦ K) (fun _ : ℕ ↦ f • 𝟙 K)))).bijective
  · intro h
    apply isIso_of_liftedUnit_hom_bijective
    intro q
    exact (scalarTelescope_roos_hom_bijective f K q).mp (h q)


end DerivedCategory
