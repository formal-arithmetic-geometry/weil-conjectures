/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q3
-/
module

public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.CechResolution
import Sheaf.CategoryTheory.SitePullbackAbelianExact

/-! # Abelian direct-image resolution roofs

The canonical map computed from a strict lift into a pushed-forward injective resolution.
Source: Stacks Project, Tags 01FB, 04JC, 013P and 013S.
(blueprint: lem-weil-pbc-ringed-site-cech-refinement-square-abelian-exists)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction

namespace CategoryTheory

attribute [local instance] Functor.additive_of_preserves_binary_products

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem lift_augmentation
    {A : Type*} [Category A] [Abelian A] {M : A}
    (I : InjectiveResolution M) (P : CochainComplex A ℕ)
    [∀ n, Injective (P.X n)] (f : M ⟶ P.X 0) (hf : f ≫ P.d 0 1 = 0) :
    ∃ b : I.cocomplex ⟶ P, I.ι.f 0 ≫ b.f 0 = f := by
  have hexact := I.exact₀
  let a₀ : I.cocomplex.X 0 ⟶ P.X 0 := Injective.factorThru f (I.ι.f 0)
  have ha₀ : I.ι.f 0 ≫ a₀ = f := Injective.comp_factorThru _ _
  let a₁ := hexact.descToInjective (a₀ ≫ P.d 0 1) (by
    rw [← Category.assoc, ha₀, hf])
  have ha₁ : I.cocomplex.d 0 1 ≫ a₁ = a₀ ≫ P.d 0 1 :=
    hexact.comp_descToInjective _ _
  let b := CochainComplex.mkHom I.cocomplex P a₀ a₁ ha₁.symm
    (fun n ⟨a, b, h⟩ ↦
      ⟨(I.exact_succ n).descToInjective (b ≫ P.d (n + 1) (n + 2)) (by
          rw [← Category.assoc, ← h, Category.assoc, P.d_comp_d, comp_zero]),
        ((I.exact_succ n).comp_descToInjective _ _).symm⟩)
  exact ⟨b, ha₀⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem compare_lifts
    {A B E : Type*} [Category A] [Category B] [Category E]
    [Abelian A] [Abelian B] [Abelian E]
    [HasInjectiveResolutions A] [HasInjectiveResolutions B]
    (T : B ⥤ A) [T.Additive] [T.PreservesInjectiveObjects]
    (H : A ⥤ E) [H.Additive]
    {M : A} {N : B} (h : M ⟶ T.obj N)
    (I₀ I : InjectiveResolution M) (J₀ J : InjectiveResolution N)
    (b₀ : I₀.cocomplex ⟶ (T.mapHomologicalComplex (.up ℕ)).obj J₀.cocomplex)
    (b : I.cocomplex ⟶ (T.mapHomologicalComplex (.up ℕ)).obj J.cocomplex)
    (hb₀ : I₀.ι.f 0 ≫ b₀.f 0 = h ≫ T.map (J₀.ι.f 0))
    (hb : I.ι.f 0 ≫ b.f 0 = h ≫ T.map (J.ι.f 0)) (q : ℕ) :
    (I₀.isoRightDerivedObj H q).hom ≫
        HomologicalComplex.homologyMap ((H.mapHomologicalComplex (.up ℕ)).map b₀) q ≫
        (J₀.isoRightDerivedObj (T ⋙ H) q).inv ≫
        (J.isoRightDerivedObj (T ⋙ H) q).hom =
      (I.isoRightDerivedObj H q).hom ≫
        HomologicalComplex.homologyMap ((H.mapHomologicalComplex (.up ℕ)).map b) q := by
  let s := InjectiveResolution.desc (𝟙 M) I I₀
  let t := InjectiveResolution.desc (𝟙 N) J J₀
  have hs : I₀.ι.f 0 ≫ s.f 0 = I.ι.f 0 := by
    simp [s]
  have ht : J₀.ι.f 0 ≫ t.f 0 = J.ι.f 0 := by
    simp [t]
  have hc : I₀.ι.f 0 ≫ (b₀ ≫ (T.mapHomologicalComplex (.up ℕ)).map t).f 0 =
      I₀.ι.f 0 ≫ (s ≫ b).f 0 := by
    simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
      ← Category.assoc, hb₀, hs]
    rw [Category.assoc, ← T.map_comp, ht, hb]
  have : ∀ n, Injective (((T.mapHomologicalComplex (.up ℕ)).obj J.cocomplex).X n) :=
    fun n ↦ T.injective_obj (J.cocomplex.X n)
  have hh := (H.mapHomotopy (CochainComplex.homotopyOfQuasiIso I₀.ι _ _ hc)).homologyMap_eq q
  simp only [Functor.map_comp, HomologicalComplex.homologyMap_comp] at hh
  have hsource := InjectiveResolution.isoRightDerivedObj_hom_naturality
    (𝟙 M) I₀ I s (by simpa using hs) H q
  have htarget := InjectiveResolution.isoRightDerivedObj_hom_naturality
    (𝟙 N) J₀ J t (by simpa using ht) (T ⋙ H) q
  simp only [Functor.map_id, Category.id_comp] at hsource htarget
  rw [htarget]
  simp only [← Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [Category.assoc]
  change (I₀.isoRightDerivedObj H q).hom ≫
      (HomologicalComplex.homologyMap ((H.mapHomologicalComplex (.up ℕ)).map b₀) q ≫
        HomologicalComplex.homologyMap
          ((H.mapHomologicalComplex (.up ℕ)).map
            ((T.mapHomologicalComplex (.up ℕ)).map t)) q) = _
  rw [hh, ← Category.assoc]
  exact congrArg (fun k ↦ k ≫
    HomologicalComplex.homologyMap ((H.mapHomologicalComplex (.up ℕ)).map b) q)
      hsource.symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem lift_pushforward
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    (T : B ⥤ A) [T.Additive] [T.PreservesInjectiveObjects]
    {M : A} {N : B} (h : M ⟶ T.obj N)
    (I : InjectiveResolution M) (J : InjectiveResolution N) :
    ∃ b : I.cocomplex ⟶ (T.mapHomologicalComplex (.up ℕ)).obj J.cocomplex,
      I.ι.f 0 ≫ b.f 0 = h ≫ T.map (J.ι.f 0) := by
  have : ∀ n, Injective (((T.mapHomologicalComplex (.up ℕ)).obj J.cocomplex).X n) :=
    fun n ↦ T.injective_obj (J.cocomplex.X n)
  apply lift_augmentation I ((T.mapHomologicalComplex (.up ℕ)).obj J.cocomplex)
    (h ≫ T.map (J.ι.f 0))
  change (h ≫ T.map (J.ι.f 0)) ≫ T.map (J.cocomplex.d 0 1) = 0
  rw [Category.assoc, ← T.map_comp]
  simp

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The abelian refinement-square roof exists and has its all-resolution normalizations.

Source: Stacks Project, Tags 01FB, 04JC, 013P and 013S
(blueprint: lem-weil-pbc-ringed-site-cech-refinement-square-abelian-exists).

Proof: Exactness of inverse image makes direct image preserve injectives. Extend the
coefficient map from the source augmentation into the pushed-forward target resolution,
using injectivity in degree zero and exactness recursively in subsequent degrees. Define
its cohomology map using the canonical injective resolutions. For arbitrary resolutions,
comparison maps and homotopy uniqueness identify this with any other strict lift. For an
arbitrary injective replacement, the replacement is a homotopy equivalence between
nonnegative injective complexes, so its image on section cohomology is invertible; another
augmentation homotopy gives the roof equation. Apply the same lifting to the adjunction
unit. Composing that lift with a resolution lift of the adjoint coefficient morphism has
augmentation h by the adjunction identity. Naturality of the derived-functor comparison
then gives the last formula. The identity replacement supplies the required existence
clause; no extra acyclicity or resolution hypothesis is assumed.
-/
theorem ringedSite_cech_refinement_square_abelian_exists
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
    [EnoughInjectives (Sheaf J.toGrothendieck AddCommGrpCat.{u})]
    [EnoughInjectives (Sheaf K.toGrothendieck AddCommGrpCat.{u})]
    (M : Sheaf J.toGrothendieck AddCommGrpCat.{u})
    (N : Sheaf K.toGrothendieck AddCommGrpCat.{u})
    (h : M ⟶ (u.sheafPushforwardContinuous AddCommGrpCat.{u} J.toGrothendieck K.toGrothendieck).obj
      N)
    (q : ℕ)
    {X : C} (_hX : IsTerminal X) (_huX : IsTerminal (u.obj X)) :
    ∃ hH : ((sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u} ⋙ (evaluation Cᵒᵖ
      AddCommGrpCat.{u}).obj (op X)).rightDerived q).obj M ⟶ ((sheafToPresheaf K.toGrothendieck
      AddCommGrpCat.{u} ⋙ (evaluation Dᵒᵖ AddCommGrpCat.{u}).obj (op (u.obj X))).rightDerived q).obj
      N,
      (∀ (IM : InjectiveResolution M) (IN : InjectiveResolution N),
        ∃ (L : CochainComplex (Sheaf J.toGrothendieck AddCommGrpCat.{u}) ℕ)
          (lam : ((u.sheafPushforwardContinuous AddCommGrpCat.{u} J.toGrothendieck
            K.toGrothendieck).mapHomologicalComplex (ComplexShape.up ℕ)).obj IN.cocomplex ⟶ L) (b :
            IM.cocomplex ⟶ L),
          (∀ n : ℕ, Injective (L.X n)) ∧ (∀ n : ℕ, Mono (lam.f n)) ∧ QuasiIso lam ∧
          IM.ι.f 0 ≫ b.f 0 = h ≫ (u.sheafPushforwardContinuous AddCommGrpCat.{u} J.toGrothendieck
            K.toGrothendieck).map (IN.ι.f 0) ≫ lam.f 0) ∧
      (∀ (IM : InjectiveResolution M) (IN : InjectiveResolution N)
        (L : CochainComplex (Sheaf J.toGrothendieck AddCommGrpCat.{u}) ℕ)
        (lam : ((u.sheafPushforwardContinuous AddCommGrpCat.{u} J.toGrothendieck
          K.toGrothendieck).mapHomologicalComplex (ComplexShape.up ℕ)).obj IN.cocomplex ⟶ L) (b :
          IM.cocomplex ⟶ L),
        (∀ n : ℕ, Injective (L.X n)) → (∀ n : ℕ, Mono (lam.f n)) → QuasiIso lam →
        IM.ι.f 0 ≫ b.f 0 = h ≫ (u.sheafPushforwardContinuous AddCommGrpCat.{u} J.toGrothendieck
          K.toGrothendieck).map (IN.ι.f 0) ≫ lam.f 0 →
        IsIso (HomologicalComplex.homologyMap (((sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u}
          ⋙ (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op X)).mapHomologicalComplex (ComplexShape.up
          ℕ)).map lam) q) ∧
        hH ≫ (IN.isoRightDerivedObj (sheafToPresheaf K.toGrothendieck AddCommGrpCat.{u} ⋙
          (evaluation Dᵒᵖ AddCommGrpCat.{u}).obj (op (u.obj X))) q).hom ≫
          HomologicalComplex.homologyMap (((sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u} ⋙
            (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op X)).mapHomologicalComplex (ComplexShape.up
            ℕ)).map lam) q =
        (IM.isoRightDerivedObj (sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u} ⋙ (evaluation Cᵒᵖ
          AddCommGrpCat.{u}).obj (op X)) q).hom ≫
          HomologicalComplex.homologyMap (((sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u} ⋙
            (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op X)).mapHomologicalComplex (ComplexShape.up
            ℕ)).map b) q) ∧
      (∀ (IM : InjectiveResolution M) (E : InjectiveResolution ((sheafPullback u AddCommGrpCat.{u}
        J.toGrothendieck K.toGrothendieck).obj M)),
        ∃ z : IM.cocomplex ⟶ ((u.sheafPushforwardContinuous AddCommGrpCat.{u} J.toGrothendieck
          K.toGrothendieck).mapHomologicalComplex (ComplexShape.up ℕ)).obj E.cocomplex,
          IM.ι.f 0 ≫ z.f 0 = (sheafAdjunctionContinuous u AddCommGrpCat.{u} J.toGrothendieck
            K.toGrothendieck).unit.app M ≫ (u.sheafPushforwardContinuous AddCommGrpCat.{u}
            J.toGrothendieck K.toGrothendieck).map (E.ι.f 0)) ∧
      (∀ (IM : InjectiveResolution M) (E : InjectiveResolution ((sheafPullback u AddCommGrpCat.{u}
        J.toGrothendieck K.toGrothendieck).obj M))
        (z : IM.cocomplex ⟶ ((u.sheafPushforwardContinuous AddCommGrpCat.{u} J.toGrothendieck
          K.toGrothendieck).mapHomologicalComplex (ComplexShape.up ℕ)).obj E.cocomplex),
        IM.ι.f 0 ≫ z.f 0 = (sheafAdjunctionContinuous u AddCommGrpCat.{u} J.toGrothendieck
          K.toGrothendieck).unit.app M ≫ (u.sheafPushforwardContinuous AddCommGrpCat.{u}
          J.toGrothendieck K.toGrothendieck).map (E.ι.f 0) →
        hH = (IM.isoRightDerivedObj (sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u} ⋙
          (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op X)) q).hom ≫
          HomologicalComplex.homologyMap (((sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u} ⋙
            (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op X)).mapHomologicalComplex (ComplexShape.up
            ℕ)).map z) q ≫
          (E.isoRightDerivedObj (sheafToPresheaf K.toGrothendieck AddCommGrpCat.{u} ⋙ (evaluation
            Dᵒᵖ AddCommGrpCat.{u}).obj (op (u.obj X))) q).inv ≫
          ((sheafToPresheaf K.toGrothendieck AddCommGrpCat.{u} ⋙ (evaluation Dᵒᵖ
            AddCommGrpCat.{u}).obj (op (u.obj X))).rightDerived q).map (((sheafAdjunctionContinuous
            u AddCommGrpCat.{u} J.toGrothendieck K.toGrothendieck).homEquiv M N).symm h)) := by
  classical
  let F := sheafPullback u AddCommGrpCat.{u} J.toGrothendieck K.toGrothendieck
  let G := u.sheafPushforwardContinuous AddCommGrpCat.{u} J.toGrothendieck K.toGrothendieck
  let adj := sheafAdjunctionContinuous u AddCommGrpCat.{u} J.toGrothendieck K.toGrothendieck
  obtain ⟨hadd, hlim, hcol, _, _⟩ := sitePullback_abelian_exact J K u hcover
    (by intros; infer_instance)
  have : F.Additive := hadd
  have : PreservesFiniteLimits F := hlim
  have : PreservesFiniteColimits F := hcol
  have : G.PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms adj
  have : G.Additive := ⟨by intros; ext; rfl⟩
  let H := sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u} ⋙
    (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op X)
  let H' := sheafToPresheaf K.toGrothendieck AddCommGrpCat.{u} ⋙
    (evaluation Dᵒᵖ AddCommGrpCat.{u}).obj (op (u.obj X))
  let I₀ := injectiveResolution M
  let J₀ := injectiveResolution N
  obtain ⟨b₀, hb₀⟩ := lift_pushforward G h I₀ J₀
  let hH := (I₀.isoRightDerivedObj H q).hom ≫
    HomologicalComplex.homologyMap ((H.mapHomologicalComplex (.up ℕ)).map b₀) q ≫
      (J₀.isoRightDerivedObj H' q).inv
  have formula (I : InjectiveResolution M) (J : InjectiveResolution N)
      (b : I.cocomplex ⟶ (G.mapHomologicalComplex (.up ℕ)).obj J.cocomplex)
      (hb : I.ι.f 0 ≫ b.f 0 = h ≫ G.map (J.ι.f 0)) :
      hH ≫ (J.isoRightDerivedObj H' q).hom =
        (I.isoRightDerivedObj H q).hom ≫
          HomologicalComplex.homologyMap ((H.mapHomologicalComplex (.up ℕ)).map b) q := by
    exact compare_lifts G H h I₀ I J₀ J b₀ b hb₀ hb q
  refine ⟨hH, ?_, ?_, ?_, ?_⟩
  · intro IM IN
    obtain ⟨b, hb⟩ := lift_pushforward G h IM IN
    refine ⟨(G.mapHomologicalComplex (.up ℕ)).obj IN.cocomplex, 𝟙 _, b,
      fun n ↦ G.injective_obj (IN.cocomplex.X n), ?_, inferInstance, ?_⟩
    · intro n
      change Mono (𝟙 _)
      infer_instance
    · change IM.ι.f 0 ≫ b.f 0 = h ≫ G.map (IN.ι.f 0) ≫ 𝟙 _
      simpa only [Category.comp_id] using hb
  · intro IM IN L lam b hL hmono hlam hb
    have : ∀ n, Injective (L.X n) := hL
    have : ∀ n, Injective (((G.mapHomologicalComplex (.up ℕ)).obj IN.cocomplex).X n) :=
      fun n ↦ G.injective_obj (IN.cocomplex.X n)
    have hmap : QuasiIso ((H.mapHomologicalComplex (.up ℕ)).map lam) := by
      obtain ⟨e, he⟩ := (CochainComplex.quasiIso_iff_of_injective lam).1 hlam
      rw [← he]
      exact (H.mapHomotopyEquiv e).quasiIso_hom
    obtain ⟨c, hc⟩ := lift_pushforward G h IM IN
    have heq := (H.mapHomotopy (CochainComplex.homotopyOfQuasiIso IM.ι
      (c ≫ lam) b (by
        simp only [HomologicalComplex.comp_f, ← Category.assoc]
        rw [hc, hb, Category.assoc]))).homologyMap_eq q
    simp only [Functor.map_comp, HomologicalComplex.homologyMap_comp] at heq
    refine ⟨inferInstance, ?_⟩
    change hH ≫ (IN.isoRightDerivedObj H' q).hom ≫
      HomologicalComplex.homologyMap ((H.mapHomologicalComplex (.up ℕ)).map lam) q = _
    rw [← Category.assoc, formula IM IN c hc, Category.assoc, heq]
  · intro IM E
    exact lift_pushforward G (adj.unit.app M) IM E
  · intro IM E z hz
    let k := (adj.homEquiv M N).symm h
    let t := InjectiveResolution.desc k J₀ E
    have ht : E.ι.f 0 ≫ t.f 0 = k ≫ J₀.ι.f 0 :=
      InjectiveResolution.desc_commutes_zero k J₀ E
    have hk : adj.unit.app M ≫ G.map k = h := by
      exact (adj.homEquiv M N).apply_symm_apply h
    let b := z ≫ (G.mapHomologicalComplex (.up ℕ)).map t
    have hb : IM.ι.f 0 ≫ b.f 0 = h ≫ G.map (J₀.ι.f 0) := by
      change IM.ι.f 0 ≫ z.f 0 ≫ G.map (t.f 0) = _
      rw [← Category.assoc, hz, Category.assoc, ← G.map_comp, ht,
        G.map_comp, ← Category.assoc, hk]
    have hf := formula IM J₀ b hb
    have hn := InjectiveResolution.isoRightDerivedObj_inv_naturality k E J₀ t ht H' q
    have hresult : hH = (IM.isoRightDerivedObj H q).hom ≫
        HomologicalComplex.homologyMap ((H.mapHomologicalComplex (.up ℕ)).map b) q ≫
          (J₀.isoRightDerivedObj H' q).inv := by
      rw [← Category.assoc, ← hf, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    change hH = (IM.isoRightDerivedObj H q).hom ≫
      HomologicalComplex.homologyMap ((H.mapHomologicalComplex (.up ℕ)).map z) q ≫
        (E.isoRightDerivedObj H' q).inv ≫ (H'.rightDerived q).map k
    rw [hn, hresult]
    simp only [b, Functor.map_comp, HomologicalComplex.homologyMap_comp, Category.assoc]
    rfl

end CategoryTheory
