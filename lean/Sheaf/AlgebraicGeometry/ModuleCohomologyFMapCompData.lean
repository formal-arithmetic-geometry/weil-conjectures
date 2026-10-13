/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups G2 and V1
-/
module

public import Sheaf.AlgebraicGeometry.ModuleCohomologyFMap
import all Sheaf.AlgebraicGeometry.ModuleCohomologyFMap
import all Sheaf.AlgebraicGeometry.ModuleCohomologyFMapComparison
import Sheaf.AlgebraicGeometry.SchemeModulesEnoughInjectives

/-! # Common-target diagram for composition of module cohomology maps

The statement concerns homology of section complexes before transport to derived
cohomology. Source: Stacks Project, Cohomology of Sheaves, Tags 01F8 and 01FB;
Derived Categories, Tags 013P and 013S.
-/

@[expose] public section

universe u

set_option autoImplicit false

open CategoryTheory

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency.types false in
private theorem sections_iso_naturality {X Y : Scheme.{u}} (h : X ⟶ Y)
    {A B : CochainComplex X.Modules ℕ} (f : A ⟶ B) :
    (pushforward_sections_iso h A).hom ≫
      (((RingedSpace.globalSectionsFunctor Y.toRingedSpace ⋙
        forget₂ _ AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.up ℕ)).map
        (((pushforward h).mapHomologicalComplex (ComplexShape.up ℕ)).map f)) =
      (((RingedSpace.globalSectionsFunctor X.toRingedSpace ⋙
        forget₂ _ AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.up ℕ)).map f) ≫
        (pushforward_sections_iso h B).hom := by
  rw [← cancel_mono (pushforward_sections_iso h B).inv,
    Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id,
    ← cancel_epi (pushforward_sections_iso h A).inv, Iso.inv_hom_id_assoc]
  ext1 n
  change ((SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).map (f.f n)).app _ ≫
      (presheaf (B.X n)).map _ =
    (presheaf (A.X n)).map _ ≫
      ((SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).map (f.f n)).app _
  exact ((SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).map
    (f.f n)).naturality _ |>.symm

private theorem data_sections_iso {X Y : Scheme.{u}} {h : X ⟶ Y}
    {G : Y.Modules} {F : X.Modules} {φ : G ⟶ (pushforward h).obj F}
    (C : ModuleCohomologyFMapData h G F φ) :
    C.a = pushforward_sections_iso h C.I.cocomplex := by
  apply Iso.ext_inv
  ext1 n
  exact C.sections n

set_option backward.isDefEq.respectTransparency.types false in
private theorem sections_iso_comp {X Y Z : Scheme.{u}} (h : X ⟶ Y) (k : Y ⟶ Z)
    (A : CochainComplex X.Modules ℕ) :
    (pushforward_sections_iso (h ≫ k) A).hom ≫
      (((RingedSpace.globalSectionsFunctor Z.toRingedSpace ⋙
        forget₂ _ AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.up ℕ)).map
        ((Functor.mapHomologicalComplexCompIso (pushforwardComp h k)
          (ComplexShape.up ℕ)).inv.app A)) =
    (pushforward_sections_iso h A).hom ≫
      (pushforward_sections_iso k
        (((pushforward h).mapHomologicalComplex (ComplexShape.up ℕ)).obj A)).hom := by
  rw [← cancel_mono
    (pushforward_sections_iso k
      (((pushforward h).mapHomologicalComplex (ComplexShape.up ℕ)).obj A)).inv,
    Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id,
    ← cancel_mono (pushforward_sections_iso h A).inv,
    Category.assoc, Category.assoc, Iso.hom_inv_id,
    ← cancel_epi (pushforward_sections_iso (h ≫ k) A).inv, Iso.inv_hom_id_assoc]
  ext1 n
  change (((pushforwardComp h k).inv.app (A.X n)).app (⊤ : Z.Opens)) ≫
      (presheaf ((pushforward h).obj (A.X n))).map
        (eqToHom (by simp) : (⊤ : Y.Opens) ⟶ k ⁻¹ᵁ (⊤ : Z.Opens)).op ≫
      (presheaf (A.X n)).map
        (eqToHom (by simp) : (⊤ : X.Opens) ⟶ h ⁻¹ᵁ (⊤ : Y.Opens)).op =
    (presheaf (A.X n)).map
      (eqToHom (by simp) : (⊤ : X.Opens) ⟶ (h ≫ k) ⁻¹ᵁ (⊤ : Z.Opens)).op
  simp only [pushforwardComp_inv_app_app, Category.id_comp,
    pushforward_obj_presheaf_map, ← Functor.map_comp]
  congr 1

set_option maxHeartbeats 1000000 in
-- Cross-scheme complex functors require extra elaboration during diagram rewrites.
set_option backward.isDefEq.respectTransparency.types false in
/-- The section-complex homology maps for two successive scheme maps admit a common
comparison target. This is the diagram step, before cancellation or transport through
`isoRightDerivedObj`, of composition.
Source: Stacks Project, Cohomology of Sheaves, Tags 01F8 and 01FB; Derived Categories,
Tags 013P and 013S (blueprint: lem-weil-pbc-module-cohomology-fmap-comp-data).

Proof: Z.Modules has enough injectives. Replace k_*Ch.K by a nonnegative
termwise injective complex L with a quasi-isomorphism mu. Since Ch.K is termwise
injective, the canonical sections comparison followed by Gamma(mu) induces an
isomorphism s on homology (01EZ).
Lift k_*(desc id from Ck.I to Ch.J) followed by k_*(Ch.beta) and mu across
Ck.lambda to obtain e : Ck.K -> L up to homotopy. Lift (kh)_*(desc id from
Ccomp.I to Ch.I), followed by the inverse successive-pushforward comparison at
Ch.I, k_*(Ch.lambda), and mu across Ccomp.lambda to obtain
f : Ccomp.K -> L up to homotopy.
Precomposing the beta square with Ccomp.J's augmentation gives homotopic maps:
the two beta compatibility equations, the augmentation equation for identity
descent, and naturality of pushforwardComp identify both routes. Uniqueness of
lifts into L gives the beta homotopy (013S). Apply additive global sections and
homology to these three homotopies. Canonical sections comparisons commute with
identity descents and with successive pushforwards, by naturality of restrictions
and h inverse k inverse top = (h followed by k) inverse top. Their three resulting
identities are precisely the displayed squares. Take Q = H^p(Gamma(Z,L)),
qk = H^p(Gamma(e)), qc = H^p(Gamma(f)), and s as above. No identification with
derived cohomology and no cancellation of the three squares occurs in this lemma.
-/
theorem moduleCohomologyFMap_comp_data {X Y Z : Scheme.{u}} (h : X ⟶ Y) (k : Y ⟶ Z)
    {H : Z.Modules} {G : Y.Modules} {F : X.Modules}
    (ψ : H ⟶ (pushforward k).obj G) (φ : G ⟶ (pushforward h).obj F)
    (Ck : ModuleCohomologyFMapData k H G ψ)
    (Ch : ModuleCohomologyFMapData h G F φ)
    (Cc : ModuleCohomologyFMapData (h ≫ k) H F
      (ψ ≫ (pushforward k).map φ ≫ (pushforwardComp h k).hom.app F)) (p : ℕ) :
    let HX := (RingedSpace.globalSectionsFunctor X.toRingedSpace ⋙
      forget₂ _ AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.up ℕ)
    let HY := (RingedSpace.globalSectionsFunctor Y.toRingedSpace ⋙
      forget₂ _ AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.up ℕ)
    let HZ := (RingedSpace.globalSectionsFunctor Z.toRingedSpace ⋙
      forget₂ _ AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.up ℕ)
    let Hp := HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) p
    ∃ (Q : AddCommGrpCat.{u}) (qk : Hp.obj (HZ.obj Ck.K) ⟶ Q)
      (qc : Hp.obj (HZ.obj Cc.K) ⟶ Q) (s : Hp.obj (HY.obj Ch.K) ⟶ Q),
      IsIso s ∧
      Hp.map (HZ.map Cc.β) ≫ qc =
        Hp.map (HZ.map (InjectiveResolution.desc (𝟙 H) Ck.J Cc.J)) ≫
          Hp.map (HZ.map Ck.β) ≫ qk ∧
      Hp.map (Cc.a.hom ≫ HZ.map Cc.lambda) ≫ qc =
        Hp.map (HX.map (InjectiveResolution.desc (𝟙 F) Ch.I Cc.I)) ≫
          Hp.map (Ch.a.hom ≫ HY.map Ch.lambda) ≫ s ∧
      Hp.map (Ck.a.hom ≫ HZ.map Ck.lambda) ≫ qk =
        Hp.map (HY.map (InjectiveResolution.desc (𝟙 G) Ch.J Ck.I)) ≫
          Hp.map (HY.map Ch.β) ≫ s := by
  dsimp only
  let PX := (pushforward h).mapHomologicalComplex (ComplexShape.up ℕ)
  let PY := (pushforward k).mapHomologicalComplex (ComplexShape.up ℕ)
  let PC := (pushforward (h ≫ k)).mapHomologicalComplex (ComplexShape.up ℕ)
  let HX := (RingedSpace.globalSectionsFunctor X.toRingedSpace ⋙
    forget₂ _ AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.up ℕ)
  let HY := (RingedSpace.globalSectionsFunctor Y.toRingedSpace ⋙
    forget₂ _ AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.up ℕ)
  let HZ := (RingedSpace.globalSectionsFunctor Z.toRingedSpace ⋙
    forget₂ _ AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.up ℕ)
  let Hp := HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) p
  let T := Functor.mapHomologicalComplexCompIso (pushforwardComp h k) (ComplexShape.up ℕ)
  have : EnoughInjectives Z.Modules := enoughInjectives Z
  obtain ⟨L, μ, hL, hμ⟩ := nat_complex_injective_resolution (PY.obj Ch.K)
  have : QuasiIso μ := hμ
  have : QuasiIso Ck.lambda := Ck.quasiIso
  have : QuasiIso Cc.lambda := Cc.quasiIso
  let αG := InjectiveResolution.desc (𝟙 G) Ch.J Ck.I
  let αF := InjectiveResolution.desc (𝟙 F) Ch.I Cc.I
  let αH := InjectiveResolution.desc (𝟙 H) Ck.J Cc.J
  let γ := PY.map (αG ≫ Ch.β) ≫ μ
  let δ := PC.map αF ≫ T.inv.app Ch.I.cocomplex ≫ PY.map Ch.lambda ≫ μ
  obtain ⟨e, he⟩ := lift_nat_quasiIso hL Ck.lambda γ
  obtain ⟨f, hf⟩ := lift_nat_quasiIso hL Cc.lambda δ
  have hb : Nonempty (Homotopy (Cc.β ≫ f) (αH ≫ Ck.β ≫ e)) := by
    let η₀ := ψ ≫ (pushforward k).map (Ck.I.ι.f 0)
    have hη₀ : η₀ ≫ (PY.obj Ck.I.cocomplex).d 0 1 = 0 := by
      change (ψ ≫ (pushforward k).map (Ck.I.ι.f 0)) ≫
        (pushforward k).map (Ck.I.cocomplex.d 0 1) = 0
      rw [Category.assoc, ← Functor.map_comp, Ck.I.ι_f_zero_comp_complex_d,
        Functor.map_zero, CategoryTheory.Limits.comp_zero]
    let η := (CochainComplex.fromSingle₀Equiv (PY.obj Ck.I.cocomplex) H).symm ⟨η₀, hη₀⟩
    have hη : η.f 0 = η₀ := CochainComplex.fromSingle₀Equiv_symm_apply_f_zero _ _
    let θ := ψ ≫ (pushforward k).map φ ≫ (pushforwardComp h k).hom.app F
    let ξ₀ := θ ≫ (pushforward (h ≫ k)).map (Cc.I.ι.f 0)
    have hξ₀ : ξ₀ ≫ (PC.obj Cc.I.cocomplex).d 0 1 = 0 := by
      change (θ ≫ (pushforward (h ≫ k)).map (Cc.I.ι.f 0)) ≫
        (pushforward (h ≫ k)).map (Cc.I.cocomplex.d 0 1) = 0
      rw [Category.assoc, ← Functor.map_comp, Cc.I.ι_f_zero_comp_complex_d,
        Functor.map_zero, CategoryTheory.Limits.comp_zero]
    let ξ := (CochainComplex.fromSingle₀Equiv (PC.obj Cc.I.cocomplex) H).symm ⟨ξ₀, hξ₀⟩
    have hξ : ξ.f 0 = ξ₀ := CochainComplex.fromSingle₀Equiv_symm_apply_f_zero _ _
    have hβk : Ck.J.ι ≫ Ck.β = η ≫ Ck.lambda := by
      apply HomologicalComplex.from_single_hom_ext
      rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, hη]
      exact Ck.compatible
    have hβc : Cc.J.ι ≫ Cc.β = ξ ≫ Cc.lambda := by
      apply HomologicalComplex.from_single_hom_ext
      rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, hξ]
      exact Cc.compatible
    have hJ : Cc.J.ι ≫ αH = Ck.J.ι := by simp [αH]
    have hleft : Cc.J.ι ≫ (Cc.β ≫ f) = ξ ≫ (Cc.lambda ≫ f) := by
      rw [← Category.assoc, hβc, Category.assoc]
    have hright : Cc.J.ι ≫ (αH ≫ Ck.β ≫ e) = η ≫ (Ck.lambda ≫ e) := by
      rw [← Category.assoc, hJ, ← Category.assoc, hβk, Category.assoc]
    have hmiddle : ξ ≫ δ = η ≫ γ := by
      apply HomologicalComplex.from_single_hom_ext
      simp only [δ, γ, HomologicalComplex.comp_f, hξ, hη]
      change ξ₀ ≫ (pushforward (h ≫ k)).map (αF.f 0) ≫
          (pushforwardComp h k).inv.app (Ch.I.cocomplex.X 0) ≫
          (pushforward k).map (Ch.lambda.f 0) ≫ μ.f 0 =
        η₀ ≫ (pushforward k).map ((αG ≫ Ch.β).f 0) ≫ μ.f 0
      dsimp only [ξ₀, η₀, θ]
      simp only [HomologicalComplex.comp_f, Category.assoc]
      rw [← Functor.map_comp_assoc, InjectiveResolution.desc_commutes_zero]
      simp only [Category.id_comp]
      have hG : Ck.I.ι.f 0 ≫ αG.f 0 = Ch.J.ι.f 0 := by
        simp [αG]
      rw [← Functor.map_comp_assoc]
      rw [← Category.assoc (Ck.I.ι.f 0) (αG.f 0) (Ch.β.f 0), hG, Ch.compatible]
      have hn := (pushforwardComp h k).hom.naturality
        (show F ⟶ Ch.I.cocomplex.X 0 from Ch.I.ι.f 0)
      change (pushforward k).map ((pushforward h).map (Ch.I.ι.f 0)) ≫
          (pushforwardComp h k).hom.app (Ch.I.cocomplex.X 0) =
        (pushforwardComp h k).hom.app F ≫
          (pushforward (h ≫ k)).map (Ch.I.ι.f 0) at hn
      rw [← reassoc_of% hn, Iso.hom_inv_id_app_assoc]
      simp only [Functor.map_comp, Category.assoc]
    apply unique_nat_quasiIso hL Cc.J.ι (Cc.β ≫ f) (αH ≫ Ck.β ≫ e)
    rw [hleft, hright]
    exact ⟨(hf.some.compLeft ξ).trans (hmiddle ▸ (he.some.compLeft η).symm)⟩
  let a := pushforward_sections_iso k Ch.K
  have hΓ : QuasiIso (HZ.map μ) :=
    nat_quasiIso_globalSections_pushforward_injectives k Ch.K L Ch.injective hL μ hμ
  have : IsIso (Hp.map (HZ.map μ)) := by
    change IsIso (HomologicalComplex.homologyMap _ p)
    infer_instance
  refine ⟨Hp.obj (HZ.obj L), Hp.map (HZ.map e), Hp.map (HZ.map f),
    Hp.map (a.hom ≫ HZ.map μ), ?_, ?_, ?_, ?_⟩
  · rw [Functor.map_comp]
    infer_instance
  · have hh := ((RingedSpace.globalSectionsFunctor Z.toRingedSpace ⋙
      forget₂ _ AddCommGrpCat.{u}).mapHomotopy hb.some).homologyMap_eq p
    change Hp.map (HZ.map (Cc.β ≫ f)) = Hp.map (HZ.map (αH ≫ Ck.β ≫ e)) at hh
    simpa only [Functor.map_comp, Category.assoc, αH, Hp, HZ] using hh
  · have hh := ((RingedSpace.globalSectionsFunctor Z.toRingedSpace ⋙
      forget₂ _ AddCommGrpCat.{u}).mapHomotopy hf.some).homologyMap_eq p
    change Hp.map (HZ.map (Cc.lambda ≫ f)) = Hp.map (HZ.map δ) at hh
    have hs : Cc.a.hom ≫ HZ.map δ =
        HX.map αF ≫ Ch.a.hom ≫ HY.map Ch.lambda ≫ a.hom ≫ HZ.map μ := by
      have h1 := sections_iso_naturality (h ≫ k) αF
      have h2 := sections_iso_comp h k Ch.I.cocomplex
      have h3 := sections_iso_naturality k Ch.lambda
      change (pushforward_sections_iso (h ≫ k) Cc.I.cocomplex).hom ≫
        HZ.map (PC.map αF) = HX.map αF ≫
          (pushforward_sections_iso (h ≫ k) Ch.I.cocomplex).hom at h1
      change (pushforward_sections_iso (h ≫ k) Ch.I.cocomplex).hom ≫
        HZ.map (T.inv.app Ch.I.cocomplex) =
          (pushforward_sections_iso h Ch.I.cocomplex).hom ≫
            (pushforward_sections_iso k (PX.obj Ch.I.cocomplex)).hom at h2
      change (pushforward_sections_iso k (PX.obj Ch.I.cocomplex)).hom ≫
        HZ.map (PY.map Ch.lambda) = HY.map Ch.lambda ≫ a.hom at h3
      dsimp only [δ]
      simp only [HZ.map_comp]
      rw [data_sections_iso Cc, reassoc_of% h1, reassoc_of% h2, reassoc_of% h3,
        ← data_sections_iso Ch]
    change Hp.map (Cc.a.hom ≫ HZ.map Cc.lambda) ≫ Hp.map (HZ.map f) = _
    rw [← Hp.map_comp, Category.assoc, ← HZ.map_comp]
    rw [Hp.map_comp, hh, ← Hp.map_comp, hs]
    simp only [Functor.map_comp, Category.assoc]
    rfl
  · have hh := ((RingedSpace.globalSectionsFunctor Z.toRingedSpace ⋙
      forget₂ _ AddCommGrpCat.{u}).mapHomotopy he.some).homologyMap_eq p
    change Hp.map (HZ.map (Ck.lambda ≫ e)) = Hp.map (HZ.map γ) at hh
    have hs : Ck.a.hom ≫ HZ.map γ =
        HY.map αG ≫ HY.map Ch.β ≫ a.hom ≫ HZ.map μ := by
      dsimp only [γ]
      rw [HZ.map_comp, ← Category.assoc, data_sections_iso Ck]
      have hn := sections_iso_naturality k (αG ≫ Ch.β)
      change (pushforward_sections_iso k Ck.I.cocomplex).hom ≫
        HZ.map (PY.map (αG ≫ Ch.β)) = HY.map (αG ≫ Ch.β) ≫ a.hom at hn
      rw [hn, HY.map_comp]
      simp only [Category.assoc]
    change Hp.map (Ck.a.hom ≫ HZ.map Ck.lambda) ≫ Hp.map (HZ.map e) = _
    rw [← Hp.map_comp, Category.assoc, ← HZ.map_comp]
    rw [Hp.map_comp, hh, ← Hp.map_comp, hs]
    simp only [Functor.map_comp]
    rfl

end AlgebraicGeometry.Scheme.Modules
