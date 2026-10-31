/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.CategoryTheory.SiteCechEdgeNormalization
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import WeilConjectures.CategoryTheory.Sites.InjectiveModuleCechAcyclic
import WeilConjectures.Algebra.Homology.FirstQuadrantAugmentation
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! # Čech refinement pentagon before cohomology

Source: Stacks 01FD, 03AX, 03FC and 08J6.
(blueprint: lem-weil-pbc-ringed-site-cech-refinement-pentagon)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction

namespace CategoryTheory

attribute [local instance] Functor.additive_of_preserves_binary_products

namespace RingedPentagon

section Complexes

variable {C : Type u} [SmallCategory C] {T : Type u} {U : C}
  {f : T → C} {hom : ∀ t, f t ⟶ U} (S : SiteCechComplex f hom)
  {E : Type*} [Category E] [Abelian E]
  (P : E ⥤ Cᵒᵖ ⥤ AddCommGrpCat.{u}) [P.Additive]

private noncomputable abbrev doubleComplex (L : CochainComplex E ℕ) :=
  HomologicalComplex₂.flip
    (((P ⋙ S.complexFunctor).mapHomologicalComplex (.up ℕ)).obj L)

private def restriction (F : Cᵒᵖ ⥤ AddCommGrpCat.{u}) :
    F.obj (op U) ⟶ S.cochains F 0 :=
  AddCommGrpCat.ofHom (AddMonoidHom.pi fun t : Fin (0 + 1) → T ↦
    (F.map (S.pr 0 t 0 ≫ hom (t 0)).op).hom)

private theorem restriction_d (F : Cᵒᵖ ⥤ AddCommGrpCat.{u}) :
    restriction S F ≫ (S.complex F).d 0 1 = 0 := by
  apply AddCommGrpCat.ext
  intro x
  funext t
  have h (k : Fin 2) : F.map (S.indexMap t k.succAbove).op
      (F.map (S.pr 0 (t ∘ k.succAbove) 0 ≫ hom (t (k.succAbove 0))).op x) =
      F.map (S.pr 1 t 0 ≫ hom (t 0)).op x := by
    rw [← ConcreteCategory.comp_apply, ← F.map_comp, ← op_comp]
    rw [← Category.assoc, S.indexMap_pr, S.comm]
  change (∑ k : Fin 2, (-1 : ℤ) ^ k.val •
    F.map (S.indexMap t k.succAbove).op
      (F.map (S.pr 0 (t ∘ k.succAbove) 0 ≫ hom (t (k.succAbove 0))).op x)) = 0
  simp only [Fin.sum_univ_two, h, Fin.val_zero, pow_zero, one_smul,
    Fin.val_one, pow_one, neg_smul, add_neg_cancel]

private noncomputable def restrictionToZero (L : CochainComplex E ℕ) :
    ((P ⋙ (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)).mapHomologicalComplex
      (.up ℕ)).obj L ⟶ (doubleComplex S P L).X 0 where
  f q := restriction S (P.obj (L.X q))
  comm' q r _ := by
    apply AddCommGrpCat.ext
    intro x
    funext t
    exact congrArg (fun k ↦ k x)
      ((P.map (L.d q r)).naturality (S.pr 0 t 0 ≫ hom (t 0)).op)

private theorem restrictionToZero_d (L : CochainComplex E ℕ) :
    restrictionToZero S P L ≫ (doubleComplex S P L).d 0 1 = 0 := by
  apply HomologicalComplex.hom_ext
  intro n
  exact restriction_d S (P.obj (L.X n))

private noncomputable def alpha (L : CochainComplex E ℕ) :
    ((P ⋙ (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)).mapHomologicalComplex
      (.up ℕ)).obj L ⟶ (doubleComplex S P L).total (.up ℕ) where
  f q := (restrictionToZero S P L).f q ≫
    (doubleComplex S P L).ιTotal (.up ℕ) 0 q q (by simp)
  comm' q r h := by
    have hr : q + 1 = r := h
    subst r
    let D := doubleComplex S P L
    let a := restrictionToZero S P L
    simp only [HomologicalComplex₂.total_d, Category.assoc,
      Preadditive.comp_add, HomologicalComplex₂.ι_D₁, HomologicalComplex₂.ι_D₂]
    rw [D.d₁_eq (.up ℕ) (by simp : (ComplexShape.up ℕ).Rel 0 1)
      q (q + 1) (by simp [Nat.add_comm]),
      D.d₂_eq (.up ℕ) 0 (by simp : (ComplexShape.up ℕ).Rel q (q + 1)) (q + 1) (by simp)]
    have hz := congrArg (fun k ↦ k.f q) (restrictionToZero_d S P L)
    change (restrictionToZero S P L).f q ≫ (D.d 0 1).f q = 0 at hz
    have hs₁ : ComplexShape.ε₁ (.up ℕ) (.up ℕ) (.up ℕ) (0, q) = 1 := rfl
    have hs₂ : ComplexShape.ε₂ (.up ℕ) (.up ℕ) (.up ℕ) (0, q) = 1 := by
      change (-1 : ℤˣ) ^ 0 = 1
      exact pow_zero _
    simp only [hs₁, hs₂, one_smul, ← Category.assoc, hz, zero_comp, zero_add]
    rw [a.comm q (q + 1)]

private noncomputable def beta {A : E} (L : CochainComplex E ℕ)
    (i : A ⟶ L.X 0) (hi : i ≫ L.d 0 1 = 0) :
    S.complex (P.obj A) ⟶ (doubleComplex S P L).total (.up ℕ) where
  f p := S.cochainsMap (P.map i) p ≫
    (doubleComplex S P L).ιTotal (.up ℕ) p 0 p (by simp)
  comm' p r h := by
    have hr : p + 1 = r := h
    subst r
    let D := doubleComplex S P L
    let a := (P ⋙ S.complexFunctor).map i
    have hz : a ≫ (P ⋙ S.complexFunctor).map (L.d 0 1) = 0 := by
      rw [← Functor.map_comp, hi, Functor.map_zero]
    have hz' := congrArg (fun k ↦ k.f p) hz
    simp only [HomologicalComplex.comp_f, HomologicalComplex.zero_f] at hz'
    simp only [HomologicalComplex₂.total_d, Category.assoc,
      Preadditive.comp_add, HomologicalComplex₂.ι_D₁, HomologicalComplex₂.ι_D₂]
    rw [D.d₁_eq (.up ℕ) (by simp : (ComplexShape.up ℕ).Rel p (p + 1))
      0 (p + 1) (by simp),
      D.d₂_eq (.up ℕ) p (by simp : (ComplexShape.up ℕ).Rel 0 1) (p + 1) (by simp)]
    have hs₁ : ComplexShape.ε₁ (.up ℕ) (.up ℕ) (.up ℕ) (p, 0) = 1 := rfl
    simp only [hs₁, one_smul]
    change a.f p ≫ (D.d p (p + 1)).f 0 ≫ D.ιTotal (.up ℕ) (p + 1) 0 (p + 1) _ +
      a.f p ≫ (_ • (D.X p).d 0 1 ≫ D.ιTotal (.up ℕ) p 1 (p + 1) _) = _
    simp only [← Category.assoc]
    have hz'' : a.f p ≫
        (ComplexShape.ε₂ (.up ℕ) (.up ℕ) (.up ℕ) (p, 0) •
          ((D.X p).d 0 1 ≫ D.ιTotal (.up ℕ) p 1 (p + 1) (by simp))) = 0 := by
      rw [Units.smul_def, Preadditive.comp_zsmul, ← Category.assoc]
      change _ • ((a.f p ≫ ((P ⋙ S.complexFunctor).map
        (L.d 0 1)).f p) ≫ _) = 0
      rw [hz', zero_comp, smul_zero]
    rw [hz'', add_zero]
    exact congrArg (fun k ↦ k ≫ D.ιTotal (.up ℕ) (p + 1) 0 (p + 1) (by simp))
      (a.comm p (p + 1))


private noncomputable def totalMap {L L' : CochainComplex E ℕ} (b : L ⟶ L') :
    (doubleComplex S P L).total (.up ℕ) ⟶ (doubleComplex S P L').total (.up ℕ) :=
  HomologicalComplex₂.total.map
    ((HomologicalComplex₂.flipFunctor _ _ _).map
      (((P ⋙ S.complexFunctor).mapHomologicalComplex (.up ℕ)).map b)) (.up ℕ)

private theorem alpha_naturality {L L' : CochainComplex E ℕ} (b : L ⟶ L') :
    alpha S P L ≫ totalMap S P b =
      ((P ⋙ (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)).mapHomologicalComplex
        (.up ℕ)).map b ≫ alpha S P L' := by
  apply HomologicalComplex.hom_ext
  intro n
  simp only [HomologicalComplex.comp_f, alpha, Category.assoc,
    totalMap, HomologicalComplex₂.ιTotal_map]
  rw [← Category.assoc, ← Category.assoc]
  congr 1
  apply AddCommGrpCat.ext
  intro x
  funext t
  exact congrArg (fun k ↦ k x)
    ((P.map (b.f n)).naturality (S.pr 0 t 0 ≫ hom (t 0)).op)

private theorem beta_naturality {L L' : CochainComplex E ℕ} (b : L ⟶ L')
    {A : E} (i : A ⟶ L.X 0) (hi : i ≫ L.d 0 1 = 0)
    (i' : A ⟶ L'.X 0) (hi' : i' ≫ L'.d 0 1 = 0)
    (hb : i ≫ b.f 0 = i') :
    beta S P L i hi ≫ totalMap S P b = beta S P L' i' hi' := by
  apply HomologicalComplex.hom_ext
  intro n
  simp only [HomologicalComplex.comp_f, beta, Category.assoc,
    totalMap, HomologicalComplex₂.ιTotal_map]
  rw [← Category.assoc]
  have h := congrArg (fun k ↦ ((P ⋙ S.complexFunctor).map k).f n) hb
  simp only [Functor.map_comp, HomologicalComplex.comp_f] at h
  exact congrArg (fun k ↦ k ≫ (doubleComplex S P L').ιTotal (.up ℕ) n 0 n
    (Nat.add_zero n)) h

end Complexes

private theorem cech_zero_glue
    {C : Type u} [SmallCategory C]
    {J : Precoverage C} [J.HasIsos] [J.IsStableUnderComposition]
    [J.IsStableUnderBaseChange] [J.HasPullbacks]
    {T : Type u} {U : C} (f : T → C) (hom : ∀ t, f t ⟶ U)
    (hcover : Presieve.ofArrows f hom ∈ J U) (S : SiteCechComplex f hom)
    (I : Sheaf J.toGrothendieck AddCommGrpCat.{u})
    (c : S.cochains I.obj 0) (hc : S.differentialValue I.obj 0 c = 0) :
    ∃! x : I.obj.obj (op U), ∀ t, I.obj.map
      (S.pr 0 t 0 ≫ hom (t 0)).op x = c t := by
  classical
  let P := I.obj ⋙ forget AddCommGrpCat
  have hs : Presieve.IsSheaf J.toGrothendieck P :=
    (isSheaf_iff_isSheaf_of_type _ _).mp
      (Presheaf.isSheaf_comp_of_isSheaf _ I.obj (forget AddCommGrpCat) I.property)
  have hg := (Presieve.isSheafFor_arrows_iff P hom).mp
    (hs.isSheafFor_of_mem_precoverage hcover)
  let a (i : T) := I.obj.map (eqToHom (S.W_zero (fun _ ↦ i)).symm).op (c (fun _ ↦ i))
  have transport (t : Fin 1 → T) (i : T) (ht : t = fun _ ↦ i)
      (Z : C) (g : Z ⟶ f i) :
      I.obj.map (g ≫ eqToHom (by simpa only [ht] using (S.W_zero t).symm)).op
        (c t) = I.obj.map g.op (a i) := by
    subst t
    rw [op_comp, I.obj.map_comp]
    rfl
  have ha : Presieve.Arrows.Compatible P hom a := by
    intro i j Z gi gj hij
    let t : Fin 2 → T := Fin.cons i (fun _ ↦ j)
    let g : ∀ k : Fin 2, Z ⟶ f (t k) := Fin.cases gi (fun _ ↦ gj)
    obtain ⟨b, hb, _⟩ := S.universal 1 t Z g (by
      intro k
      fin_cases k
      · rfl
      · exact hij.symm)
    have he := congrArg (fun s ↦ I.obj.map b.op (s t)) hc
    change I.obj.map b.op (∑ k : Fin 2, (-1 : ℤ) ^ k.val •
      I.obj.map (S.indexMap t k.succAbove).op (c (t ∘ k.succAbove))) =
        I.obj.map b.op 0 at he
    simp only [Fin.sum_univ_two,
      Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul,
      map_add, map_neg, map_zero] at he
    have ht0 : t ∘ (0 : Fin 2).succAbove = (fun _ ↦ j) := by
      funext k
      fin_cases k
      rfl
    have ht1 : t ∘ (1 : Fin 2).succAbove = (fun _ ↦ i) := by
      funext k
      fin_cases k
      rfl
    have hm (k : Fin 2) : b ≫ S.indexMap t k.succAbove =
        g (k.succAbove 0) ≫
          eqToHom (S.W_zero (t ∘ k.succAbove)).symm := by
      have : IsIso (S.pr 0 (t ∘ k.succAbove) 0) := by
        rw [S.pr_zero]
        infer_instance
      apply (cancel_mono (S.pr 0 (t ∘ k.succAbove) 0)).mp
      rw [Category.assoc, S.indexMap_pr, hb, Category.assoc, S.pr_zero]
      simp
    simp only [← ConcreteCategory.comp_apply, ← I.obj.map_comp, ← op_comp, hm] at he
    change I.obj.map (gj ≫ eqToHom (S.W_zero (t ∘ (0 : Fin 2).succAbove)).symm).op
      (c (t ∘ (0 : Fin 2).succAbove)) +
      -I.obj.map (gi ≫ eqToHom (S.W_zero (t ∘ (1 : Fin 2).succAbove)).symm).op
        (c (t ∘ (1 : Fin 2).succAbove)) = 0 at he
    rw [transport _ j ht0 Z gj, transport _ i ht1 Z gi] at he
    exact (add_neg_eq_zero.mp he).symm
  obtain ⟨x, hx, hu⟩ := hg a ha
  have hx' : ∀ t, I.obj.map (S.pr 0 t 0 ≫ hom (t 0)).op x = c t := by
    intro t
    obtain ⟨i, rfl⟩ : ∃ i, t = (fun _ : Fin 1 ↦ i) := ⟨t 0, by
      funext k
      fin_cases k
      rfl⟩
    have he := congrArg (fun y ↦ I.obj.map (S.pr 0 (fun _ ↦ i) 0).op y) (hx i)
    dsimp [P, a] at he
    rw [← ConcreteCategory.comp_apply, ← I.obj.map_comp] at he
    rw [← ConcreteCategory.comp_apply, ← I.obj.map_comp] at he
    simp only [← op_comp, S.pr_zero, eqToHom_trans, eqToHom_refl] at he
    simp only [op_id, I.obj.map_id, ConcreteCategory.id_apply] at he
    simpa only [S.pr_zero] using he
  refine ⟨x, hx', ?_⟩
  intro y hy
  apply hu y
  intro i
  have he := congrArg
    (fun z ↦ I.obj.map (eqToHom (S.W_zero (fun _ : Fin 1 ↦ i)).symm).op z)
    (hy (fun _ ↦ i))
  dsimp [P, a] at he ⊢
  change I.obj.map (eqToHom (S.W_zero (fun _ ↦ i)).symm).op
    (I.obj.map (S.pr 0 (fun _ ↦ i) 0 ≫ hom i).op y) = _ at he
  rw [← ConcreteCategory.comp_apply, ← I.obj.map_comp] at he
  simp only [← op_comp, S.pr_zero, ← Category.assoc, eqToHom_trans, eqToHom_refl,
    Category.id_comp] at he
  exact he

private theorem site_row_augmentation_quasiIso
    {C : Type u} [SmallCategory C] {J : Precoverage C}
    [J.HasIsos] [J.IsStableUnderComposition] [J.IsStableUnderBaseChange] [J.HasPullbacks]
    {T : Type u} {U : C} {f : T → C} {hom : ∀ t, f t ⟶ U}
    (hcover : Presieve.ofArrows f hom ∈ J U) (S : SiteCechComplex f hom)
    (A : Sheaf J.toGrothendieck AddCommGrpCat.{u})
    (hpos : ∀ r : ℕ, 0 < r → IsZero ((S.cohomologyFunctor r).obj A.obj))
    (e : (CochainComplex.single₀ AddCommGrpCat.{u}).obj (A.obj.obj (op U)) ⟶
      S.complex A.obj) (he : e.f 0 = restriction S A.obj) : QuasiIso e := by
  refine ⟨fun n ↦ ?_⟩
  cases n with
  | succ n =>
    rw [quasiIsoAt_iff_exactAt e (n + 1)
      (CochainComplex.exactAt_succ_single_obj _ n)]
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    exact hpos (n + 1) (by omega)
  | zero =>
    rw [CochainComplex.quasiIsoAt₀_iff]
    rw [ShortComplex.quasiIso_iff_isIso_liftCycles _ (by simp) (by simp) (by simp)]
    let L := S.complex A.obj
    let Q := L.sc' 0 0 1
    have hw : e.f 0 ≫ L.d 0 1 = 0 := by
      rw [e.comm]
      simp
    let k := Q.liftCycles (e.f 0) hw
    change IsIso k
    have hinj : Function.Injective k := by
      intro x y hxy
      have hres : ∀ t, A.obj.map (S.pr 0 t 0 ≫ hom (t 0)).op x =
          A.obj.map (S.pr 0 t 0 ≫ hom (t 0)).op y := by
        intro t
        have h := congrArg (fun z ↦ Q.iCycles z t) hxy
        change (k ≫ Q.iCycles) x t = (k ≫ Q.iCycles) y t at h
        rw [Q.liftCycles_i, he] at h
        exact h
      have hc : S.differentialValue A.obj 0
          (fun t ↦ A.obj.map (S.pr 0 t 0 ≫ hom (t 0)).op x) = 0 := by
        exact ConcreteCategory.congr_hom (restriction_d S A.obj) x
      obtain ⟨z, _, hu⟩ := cech_zero_glue f hom hcover S A _ hc
      exact (hu x (fun _ ↦ rfl)).trans (hu y (fun t ↦ (hres t).symm)).symm
    have hsurj : Function.Surjective k := by
      intro y
      let c := Q.iCycles y
      have hc : S.differentialValue A.obj 0 c = 0 := by
        exact ConcreteCategory.congr_hom Q.iCycles_g y
      obtain ⟨x, hx, _⟩ := cech_zero_glue f hom hcover S A c hc
      refine ⟨x, ?_⟩
      apply (AddCommGrpCat.mono_iff_injective Q.iCycles).mp inferInstance
      change (k ≫ Q.iCycles) x = _
      rw [Q.liftCycles_i, he]
      exact funext hx
    exact (ConcreteCategory.isIso_iff_bijective k).mpr ⟨hinj, hsurj⟩

section RowComparison

variable {C : Type u} [SmallCategory C] {J : Precoverage C}
  [J.HasIsos] [J.IsStableUnderComposition] [J.IsStableUnderBaseChange] [J.HasPullbacks]
  {T : Type u} {U : C} {f : T → C} {hom : ∀ t, f t ⟶ U}
  (hcover : Presieve.ofArrows f hom ∈ J U) (S : SiteCechComplex f hom)
  {E : Type*} [Category E] [Abelian E]
  (P : E ⥤ Cᵒᵖ ⥤ AddCommGrpCat.{u}) [P.Additive]

include hcover in
private theorem alpha_quasiIso (L : CochainComplex E ℕ)
    (hsh : ∀ n, Presheaf.IsSheaf J.toGrothendieck (P.obj (L.X n)))
    (hpos : ∀ n p : ℕ, 0 < p →
      IsZero ((S.cohomologyFunctor p).obj (P.obj (L.X n)))) :
    QuasiIso (alpha S P L) := by
  apply HomologicalComplex₂.quasiIso_of_column_augmentation
    (doubleComplex S P L) _ (restrictionToZero S P L)
    (restrictionToZero_d S P L) (alpha S P L) (fun _ ↦ rfl)
  intro n
  exact site_row_augmentation_quasiIso hcover S ⟨P.obj (L.X n), hsh n⟩
    (hpos n) _ (CochainComplex.fromSingle₀Equiv_symm_apply_f_zero _ _)

end RowComparison

private theorem mapped_cech_projection_ext
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (u : C ⥤ D) [PreservesFiniteLimits u]
    {X : C} (hX : IsTerminal X) {I : Type u}
    {U : I → C} {v : ∀ i, U i ⟶ X} (S : SiteCechComplex U v)
    (p : ℕ) (t : Fin (p + 1) → I) {Z : D}
    (f g : Z ⟶ u.obj (S.W p t))
    (h : ∀ k, f ≫ u.map (S.pr p t k) = g ≫ u.map (S.pr p t k)) : f = g := by
  classical
  have he (c : Fan (fun k : Fin (p + 1) ↦ U (t k))) :
      ∃! b : c.pt ⟶ S.W p t, ∀ k, b ≫ S.pr p t k = c.proj k :=
    S.universal p t c.pt c.proj (fun k ↦ hX.hom_ext _ _)
  let hc : IsLimit (Fan.mk (S.W p t) (S.pr p t)) :=
    Fan.IsLimit.mk _ (fun c ↦ (he c).choose)
      (fun c ↦ (he c).choose_spec.1)
      (fun c m hm ↦ (he c).choose_spec.2 m hm)
  exact (isLimitFanMkObjOfIsLimit u (fun k ↦ U (t k)) (S.pr p t) hc).hom_ext
    (fun ⟨k⟩ ↦ h k)

private theorem cech_refinement_exists_unique
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (u : C ⥤ D) [PreservesFiniteLimits u]
    {X : C} (hX : IsTerminal X) {I₀ I₁ : Type u}
    {U : I₀ → C} {v : ∀ i, U i ⟶ X}
    {V : I₁ → D} {w : ∀ j, V j ⟶ u.obj X}
    (S : SiteCechComplex U v) (T : SiteCechComplex V w)
    (r : I₁ → I₀) (a : ∀ j, V j ⟶ u.obj (U (r j)))
    (aTuple : ∀ (p : ℕ) (j : Fin (p + 1) → I₁),
      T.W p j ⟶ u.obj (S.W p (r ∘ j)))
    (haTuple : ∀ (p : ℕ) (j : Fin (p + 1) → I₁) (k : Fin (p + 1)),
      aTuple p j ≫ u.map (S.pr p (r ∘ j) k) = T.pr p j k ≫ a (j k))
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{u}) (G : Dᵒᵖ ⥤ AddCommGrpCat.{u})
    (h : F ⟶ u.op ⋙ G) :
    ∃! γ : S.complex F ⟶ T.complex G,
      ∀ (p : ℕ) (s : S.cochains F p) (j : Fin (p + 1) → I₁),
        (γ.f p s) j = G.map (aTuple p j).op (h.app _ (s (r ∘ j))) := by
  classical
  have hi (p : ℕ) (j : Fin (p + 2) → I₁) (k : Fin (p + 2)) :
      T.indexMap j k.succAbove ≫ aTuple p (j ∘ k.succAbove) =
        aTuple (p + 1) j ≫ u.map (S.indexMap (r ∘ j) k.succAbove) := by
    apply mapped_cech_projection_ext u hX S p (r ∘ (j ∘ k.succAbove))
    intro l
    rw [Category.assoc, haTuple, ← Category.assoc, T.indexMap_pr]
    rw [Category.assoc, ← u.map_comp]
    erw [S.indexMap_pr]
    exact (haTuple (p + 1) j (k.succAbove l)).symm
  let c (p : ℕ) : S.cochains F p ⟶ T.cochains G p :=
    AddCommGrpCat.ofHom
      { toFun := fun s j ↦ G.map (aTuple p j).op (h.app _ (s (r ∘ j)))
        map_zero' := by ext j; simp
        map_add' := by intros; ext j; simp }
  have hc (p : ℕ) :
      c p ≫ (T.complex G).d p (p + 1) = (S.complex F).d p (p + 1) ≫ c (p + 1) := by
    simp only [SiteCechComplex.complex, CochainComplex.of_d]
    apply AddCommGrpCat.ext
    intro s
    funext j
    change (∑ k : Fin (p + 2), (-1 : ℤ) ^ k.val •
      G.map (T.indexMap j k.succAbove).op
        (G.map (aTuple p (j ∘ k.succAbove)).op
          (h.app _ (s (r ∘ (j ∘ k.succAbove)))))) =
      G.map (aTuple (p + 1) j).op
        (h.app _ (∑ k : Fin (p + 2), (-1 : ℤ) ^ k.val •
          F.map (S.indexMap (r ∘ j) k.succAbove).op
            (s ((r ∘ j) ∘ k.succAbove))))
    simp only [map_sum, map_zsmul]
    apply Finset.sum_congr rfl
    intro k _
    congr 1
    have hn := NatTrans.naturality_apply h
      (S.indexMap (r ∘ j) k.succAbove).op
      (s ((r ∘ j) ∘ k.succAbove))
    change G.map (T.indexMap j k.succAbove).op
        (G.map (aTuple p (j ∘ k.succAbove)).op _) =
      G.map (aTuple (p + 1) j).op (h.app _ (F.map _ _))
    rw [hn]
    change G.map (T.indexMap j k.succAbove).op
        (G.map (aTuple p (j ∘ k.succAbove)).op _) =
      G.map (aTuple (p + 1) j).op
        (G.map (u.map (S.indexMap (r ∘ j) k.succAbove)).op _)
    simp only [← AddCommGrpCat.comp_apply, Category.assoc, ← G.map_comp, ← op_comp, hi]
    rfl
  let γ : S.complex F ⟶ T.complex G := CochainComplex.ofHom c hc
  refine ⟨γ, fun _ _ _ ↦ rfl, ?_⟩
  intro γ' hγ'
  apply HomologicalComplex.Hom.ext
  funext p
  apply AddCommGrpCat.ext
  intro s
  funext j
  exact hγ' p s j


private noncomputable def mappedCech
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (u : C ⥤ D) [PreservesFiniteLimits u]
    {X : C} (hX : IsTerminal X) {I : Type u}
    {U : I → C} {v : ∀ i, U i ⟶ X} (S : SiteCechComplex U v) :
    SiteCechComplex (fun i ↦ u.obj (U i)) (fun i ↦ u.map (v i)) where
  W p t := u.obj (S.W p t)
  pr p t k := u.map (S.pr p t k)
  comm p t k := by simp only [← u.map_comp, S.comm]
  universal p t Z a _ := by
    classical
    have he (c : Fan (fun k : Fin (p + 1) ↦ U (t k))) :
        ∃! b : c.pt ⟶ S.W p t, ∀ k, b ≫ S.pr p t k = c.proj k :=
      S.universal p t c.pt c.proj (fun k ↦ hX.hom_ext _ _)
    let hc : IsLimit (Fan.mk (S.W p t) (S.pr p t)) :=
      Fan.IsLimit.mk _ (fun c ↦ (he c).choose)
        (fun c ↦ (he c).choose_spec.1)
        (fun c m hm ↦ (he c).choose_spec.2 m hm)
    let hd := isLimitFanMkObjOfIsLimit u (fun k ↦ U (t k)) (S.pr p t) hc
    refine ⟨hd.lift (Fan.mk Z a), (fun k ↦ hd.fac _ ⟨k⟩), ?_⟩
    intro b hb
    apply hd.hom_ext
    intro k
    exact (hb k.as).trans (hd.fac (Fan.mk Z a) k).symm
  W_zero t := congrArg u.obj (S.W_zero t)
  pr_zero t := by simp only [S.pr_zero, eqToHom_map]
  indexMap t a := u.map (S.indexMap t a)
  indexMap_pr t a k := by rw [← u.map_comp, S.indexMap_pr]

section Refinement

variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  (u : C ⥤ D) [PreservesFiniteLimits u]
  {X : C} (hX : IsTerminal X) {I₀ I₁ : Type u}
  {U : I₀ → C} {v : ∀ i, U i ⟶ X}
  {V : I₁ → D} {w : ∀ j, V j ⟶ u.obj X}
  (S : SiteCechComplex U v) (T : SiteCechComplex V w)
  (r : I₁ → I₀) (a : ∀ j, V j ⟶ u.obj (U (r j)))
  (aTuple : ∀ (p : ℕ) (j : Fin (p + 1) → I₁),
    T.W p j ⟶ u.obj (S.W p (r ∘ j)))
  (haTuple : ∀ (p : ℕ) (j : Fin (p + 1) → I₁) (k : Fin (p + 1)),
    aTuple p j ≫ u.map (S.pr p (r ∘ j) k) = T.pr p j k ≫ a (j k))

private noncomputable def refineComplex
    (G : Dᵒᵖ ⥤ AddCommGrpCat.{u}) :
    S.complex (u.op ⋙ G) ⟶ T.complex G :=
  (cech_refinement_exists_unique u hX S T r a aTuple haTuple
    (u.op ⋙ G) G (𝟙 _)).choose

private theorem refineComplex_f (G : Dᵒᵖ ⥤ AddCommGrpCat.{u})
    (p : ℕ) (s : S.cochains (u.op ⋙ G) p) (j : Fin (p + 1) → I₁) :
    ((refineComplex u hX S T r a aTuple haTuple G).f p s) j =
      G.map (aTuple p j).op (s (r ∘ j)) :=
  (cech_refinement_exists_unique u hX S T r a aTuple haTuple
    (u.op ⋙ G) G (𝟙 _)).choose_spec.1 p s j

private theorem refineComplex_naturality
    {G G' : Dᵒᵖ ⥤ AddCommGrpCat.{u}} (f : G ⟶ G') :
    S.complexMap (Functor.whiskerLeft u.op f) ≫
      refineComplex u hX S T r a aTuple haTuple G' =
    refineComplex u hX S T r a aTuple haTuple G ≫ T.complexMap f := by
  apply HomologicalComplex.hom_ext
  intro p
  apply AddCommGrpCat.ext
  intro s
  funext j
  change ((refineComplex u hX S T r a aTuple haTuple G').f p
    (S.cochainsMap (Functor.whiskerLeft u.op f) p s)) j =
      f.app _ (((refineComplex u hX S T r a aTuple haTuple G).f p s) j)
  rw [refineComplex_f, refineComplex_f]
  exact ConcreteCategory.congr_hom (f.naturality (aTuple p j).op).symm _

private noncomputable def refineDouble
    {E : Type*} [Category E] [Abelian E]
    (P : E ⥤ Dᵒᵖ ⥤ AddCommGrpCat.{u}) [P.Additive] (L : CochainComplex E ℕ) :
    doubleComplex S (P ⋙ (Functor.whiskeringLeft _ _ _).obj u.op) L ⟶
      doubleComplex T P L where
  f p :=
    { f q := (refineComplex u hX S T r a aTuple haTuple (P.obj (L.X q))).f p
      comm' q q' _ := by
        have h := congrArg (fun k ↦ k.f p)
          (refineComplex_naturality u hX S T r a aTuple haTuple (P.map (L.d q q')))
        exact h.symm }
  comm' p p' h := by
    apply HomologicalComplex.hom_ext
    intro q
    exact (refineComplex u hX S T r a aTuple haTuple (P.obj (L.X q))).comm p p'

private noncomputable def refineTotal
    {E : Type*} [Category E] [Abelian E]
    (P : E ⥤ Dᵒᵖ ⥤ AddCommGrpCat.{u}) [P.Additive] (L : CochainComplex E ℕ) :=
  HomologicalComplex₂.total.map (refineDouble u hX S T r a aTuple haTuple P L) (.up ℕ)

private theorem refine_alpha
    {E : Type*} [Category E] [Abelian E]
    (P : E ⥤ Dᵒᵖ ⥤ AddCommGrpCat.{u}) [P.Additive] (L : CochainComplex E ℕ)
    (huX : IsTerminal (u.obj X)) :
    alpha S (P ⋙ (Functor.whiskeringLeft _ _ _).obj u.op) L ≫
        refineTotal u hX S T r a aTuple haTuple P L = alpha T P L := by
  apply HomologicalComplex.hom_ext
  intro n
  simp only [HomologicalComplex.comp_f, alpha, Category.assoc,
    refineTotal, HomologicalComplex₂.ιTotal_map]
  rw [← Category.assoc]
  congr 1
  apply AddCommGrpCat.ext
  intro x
  funext j
  change ((refineComplex u hX S T r a aTuple haTuple (P.obj (L.X n))).f 0
    (restriction S (u.op ⋙ P.obj (L.X n)) x)) j =
      (P.obj (L.X n)).map (T.pr 0 j 0 ≫ w (j 0)).op x
  rw [refineComplex_f]
  change (P.obj (L.X n)).map (aTuple 0 j).op
    ((P.obj (L.X n)).map (u.map (S.pr 0 (r ∘ j) 0 ≫ v (r (j 0)))).op x) = _
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
  rw [huX.hom_ext (aTuple 0 j ≫ u.map (S.pr 0 (r ∘ j) 0 ≫ v (r (j 0))))
    (T.pr 0 j 0 ≫ w (j 0))]

end Refinement

end RingedPentagon

/-- The chain-level pentagon and three lower squares for refinement of the two
Čech-resolution totals. The intermediary totals are the actual Čech-first totals.

Source: Stacks 01FD, proof diagram; 03FC and 03AX
(blueprint: lem-weil-pbc-ringed-site-cech-refinement-pentagon).

Proof: In every resolution degree the tuple restriction formula gives a Čech cochain
map, because the two omitted-coordinate maps have equal projections. Naturality in
resolution differentials makes these a double-complex map and hence a total map t.
Coefficient maps b and lam similarly totalize to l and s. Insert the augmented
coefficient map h followed by the target augmentation in resolution degree zero to
define delta. The strict lift identity gives betaM l = delta s. The tuple formula
for gamma and naturality of the target augmentation give gamma betaN = delta t.
Construct aL and aP by restriction of global sections on the Čech-zero axis. For aL,
rows are acyclic by injectivity of L; for aP they identify with the injective rows
of the target on the image covering. Thus both augmentations are quasi-isomorphisms.
Coefficient naturality gives the first two lower squares. The third holds since
restriction first to u(U_rj) and then to V_j equals restriction directly to V_j.
All maps preserve Čech degree, hence respect the total sign (-1)^t d_I.
-/
theorem ringedSite_cech_refinement_pentagon
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    [HasFiniteLimits C] [HasFiniteLimits D]
    (J : Precoverage C) (K : Precoverage D)
    [J.HasIsos] [J.IsStableUnderComposition] [J.IsStableUnderBaseChange] [J.HasPullbacks]
    [K.HasIsos] [K.IsStableUnderComposition] [K.IsStableUnderBaseChange] [K.HasPullbacks]
    (u : C ⥤ D) [PreservesFiniteLimits u]
    (hcover : ∀ (Y : C) (S : Presieve Y), S ∈ J Y → S.map u ∈ K (u.obj Y))
    [u.IsContinuous J.toGrothendieck K.toGrothendieck]
    [PreservesFiniteLimits (sheafPullback u (Type u) J.toGrothendieck K.toGrothendieck)]
    [PreservesFiniteColimits (sheafPullback u (Type u) J.toGrothendieck K.toGrothendieck)]
    (R : Sheaf J.toGrothendieck RingCat.{u}) (R' : Sheaf K.toGrothendieck RingCat.{u})
    (ρ : R ⟶ (u.sheafPushforwardContinuous RingCat.{u}
      J.toGrothendieck K.toGrothendieck).obj R')
    [EnoughInjectives (ringedSiteModules.{u} R)]
    [EnoughInjectives (ringedSiteModules.{u} R')]
    (M : ringedSiteModules.{u} R) (N : ringedSiteModules.{u} R')
    (h : M ⟶ (SheafOfModules.pushforward.{u} ρ).obj N)
    {X : C} (hX : IsTerminal X) (huX : IsTerminal (u.obj X))
    {I₀ I₁ : Type u} [Finite I₀] [Finite I₁]
    (U : I₀ → C) (v : ∀ i, U i ⟶ X)
    (V : I₁ → D) (w : ∀ j, V j ⟶ u.obj X)
    (hU : Presieve.ofArrows U v ∈ J X)
    (hV : Presieve.ofArrows V w ∈ K (u.obj X))
    (S : SiteCechComplex U v) (T : SiteCechComplex V w)
    (r : I₁ → I₀) (a : ∀ j, V j ⟶ u.obj (U (r j)))
    (aTuple : ∀ (p : ℕ) (j : Fin (p + 1) → I₁),
      T.W p j ⟶ u.obj (S.W p (r ∘ j)))
    (haTuple : ∀ (p : ℕ) (j : Fin (p + 1) → I₁) (k : Fin (p + 1)),
      aTuple p j ≫ u.map (S.pr p (r ∘ j) k) = T.pr p j k ≫ a (j k))
    (γ : S.complex M.val.presheaf ⟶ T.complex N.val.presheaf)
    (hγ : ∀ (p : ℕ) (s : S.cochains M.val.presheaf p) (j : Fin (p + 1) → I₁),
      (γ.f p s) j = N.val.presheaf.map (aTuple p j).op
        ((h.val.app (op (S.W p (r ∘ j)))) (s (r ∘ j))))
    (IM : InjectiveResolution M) (IN : InjectiveResolution N)
    (L : CochainComplex (ringedSiteModules.{u} R) ℕ)
    (lam : ((SheafOfModules.pushforward.{u} ρ).mapHomologicalComplex (.up ℕ)).obj
      IN.cocomplex ⟶ L) (b : IM.cocomplex ⟶ L)
    (hL : ∀ n : ℕ, Injective (L.X n))
    (hb : IM.ι.f 0 ≫ b.f 0 = h ≫
      (SheafOfModules.pushforward.{u} ρ).map (IN.ι.f 0) ≫ lam.f 0)
    (dM : S.Augmentations (SheafOfModules.forget R ⋙
      PresheafOfModules.toPresheaf R.obj) IM)
    (dN : T.Augmentations (SheafOfModules.forget R' ⋙
      PresheafOfModules.toPresheaf R'.obj) IN) :
    let P := SheafOfModules.forget R ⋙ PresheafOfModules.toPresheaf R.obj
    let F := P ⋙ (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op X)
    let Q := (HomologicalComplex₂.flip
      (((P ⋙ S.complexFunctor).mapHomologicalComplex (.up ℕ)).obj L)).total (.up ℕ)
    let B := (HomologicalComplex₂.flip
      (((P ⋙ S.complexFunctor).mapHomologicalComplex (.up ℕ)).obj
        (((SheafOfModules.pushforward.{u} ρ).mapHomologicalComplex (.up ℕ)).obj
          IN.cocomplex))).total (.up ℕ)
    ∃ (aL : (F.mapHomologicalComplex (.up ℕ)).obj L ⟶ Q)
      (aP : (F.mapHomologicalComplex (.up ℕ)).obj
        (((SheafOfModules.pushforward.{u} ρ).mapHomologicalComplex (.up ℕ)).obj
          IN.cocomplex) ⟶ B)
      (l : (S.resolutionDoubleComplex P IM).total (.up ℕ) ⟶ Q)
      (s : B ⟶ Q)
      (t : B ⟶ (T.resolutionDoubleComplex (SheafOfModules.forget R' ⋙
        PresheafOfModules.toPresheaf R'.obj) IN).total (.up ℕ))
      (delta : S.complex M.val.presheaf ⟶ B),
      QuasiIso aL ∧ QuasiIso aP ∧
      dM.beta ≫ l = delta ≫ s ∧
      γ ≫ dN.beta = delta ≫ t ∧
      dM.alpha ≫ l = (F.mapHomologicalComplex (.up ℕ)).map b ≫ aL ∧
      aP ≫ s = (F.mapHomologicalComplex (.up ℕ)).map lam ≫ aL ∧
      aP ≫ t = dN.alpha  := by
  classical
  have _ := hV
  let P := SheafOfModules.forget R ⋙ PresheafOfModules.toPresheaf R.obj
  let P' := SheafOfModules.forget R' ⋙ PresheafOfModules.toPresheaf R'.obj
  let G := SheafOfModules.pushforward.{u} ρ
  let : G.Additive := ⟨by intro A B f g; rfl⟩
  let H := (G.mapHomologicalComplex (.up ℕ)).obj IN.cocomplex
  let i : M ⟶ H.X 0 := h ≫ G.map (IN.ι.f 0)
  have hi : i ≫ H.d 0 1 = 0 := by
    change (h ≫ G.map (IN.ι.f 0)) ≫ G.map (IN.cocomplex.d 0 1) = 0
    rw [Category.assoc, ← G.map_comp, IN.ι_f_zero_comp_complex_d, G.map_zero,
      comp_zero]
  let aL := RingedPentagon.alpha S P L
  let aP := RingedPentagon.alpha S P H
  let l := RingedPentagon.totalMap S P b
  let s := RingedPentagon.totalMap S P lam
  let t := RingedPentagon.refineTotal u hX S T r a aTuple haTuple P' IN.cocomplex
  let delta := RingedPentagon.beta S P H i hi
  have haL : QuasiIso aL := by
    apply RingedPentagon.alpha_quasiIso hU S P L
    · intro n
      exact (L.X n).isSheaf
    · intro n p hp
      have := hL n
      exact injective_module_cech_cohomology_isZero J R (L.X n) U v hU S p hp
  have haP : QuasiIso aP := by
    apply RingedPentagon.alpha_quasiIso hU S P H
    · intro n
      exact (G.obj (IN.cocomplex.X n)).isSheaf
    · intro n p hp
      let Su := RingedPentagon.mappedCech u hX S
      have hcu : Presieve.ofArrows (fun j ↦ u.obj (U j))
          (fun j ↦ u.map (v j)) ∈ K (u.obj X) := by
        simpa only [Presieve.map_ofArrows] using hcover X _ hU
      exact injective_module_cech_cohomology_isZero K R' (IN.cocomplex.X n)
        (fun j ↦ u.obj (U j)) (fun j ↦ u.map (v j)) hcu Su p hp
  have hαM : dM.alpha = RingedPentagon.alpha S P IM.cocomplex := by
    apply HomologicalComplex.hom_ext
    intro n
    rw [dM.alpha_f]
    rfl
  have hβM : dM.beta = RingedPentagon.beta S P IM.cocomplex (IM.ι.f 0)
      IM.ι_f_zero_comp_complex_d := by
    apply HomologicalComplex.hom_ext
    intro n
    rw [dM.beta_f]
    rfl
  have hαN : dN.alpha = RingedPentagon.alpha T P' IN.cocomplex := by
    apply HomologicalComplex.hom_ext
    intro n
    rw [dN.alpha_f]
    rfl
  refine ⟨aL, aP, l, s, t, delta, haL, haP, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hβM]
    have hi' : (i ≫ lam.f 0) ≫ L.d 0 1 = 0 := by
      rw [Category.assoc, lam.comm, ← Category.assoc, hi, zero_comp]
    exact (RingedPentagon.beta_naturality S P b (IM.ι.f 0)
      IM.ι_f_zero_comp_complex_d (i ≫ lam.f 0) hi' hb).trans
        (RingedPentagon.beta_naturality S P lam i hi (i ≫ lam.f 0) hi' rfl).symm
  · apply HomologicalComplex.hom_ext
    intro n
    simp only [HomologicalComplex.comp_f, dN.beta_f, delta, RingedPentagon.beta,
      Category.assoc, t, RingedPentagon.refineTotal, HomologicalComplex₂.ιTotal_map]
    rw [← Category.assoc, ← Category.assoc]
    congr 1
    apply AddCommGrpCat.ext
    intro x
    funext j
    change ((IN.ι.f 0).val.app (op (T.W n j))) ((γ.f n x) j) =
      ((RingedPentagon.refineComplex u hX S T r a aTuple haTuple
        (P'.obj (IN.cocomplex.X 0))).f n (S.cochainsMap (P.map i) n x)) j
    rw [hγ, RingedPentagon.refineComplex_f]
    exact ConcreteCategory.congr_hom
      (((PresheafOfModules.toPresheaf R'.obj).map (IN.ι.f 0).val).naturality
        (aTuple n j).op) _
  · rw [hαM]
    exact RingedPentagon.alpha_naturality S P b
  · exact RingedPentagon.alpha_naturality S P lam
  · rw [hαN]
    exact RingedPentagon.refine_alpha u hX S T r a aTuple haTuple P' IN.cocomplex huX

end CategoryTheory
