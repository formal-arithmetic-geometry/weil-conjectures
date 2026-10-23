/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.CohomologyContinuityDefs
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic
public import WeilConjectures.AlgebraicGeometry.Sites.CohomologyColimit
public import WeilConjectures.CategoryTheory.Sites.CechComplex
public import WeilConjectures.CategoryTheory.Sites.SheafCohomologyRightDerived
public import WeilConjectures.CategoryTheory.Sites.SheafComposeMonoidal
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

/-!
# Étale cohomology of sheaves of modules and of their underlying abelian sheaves

For a ring `Λ`, a quasi-compact quasi-separated scheme `X` and an étale sheaf `M` of
`Λ`-modules on `X`, the cohomology `Hᵠ(X, M)` computed with sheaves of `Λ`-modules vanishes
if and only if the cohomology of the underlying abelian sheaf of `M` vanishes
(`AlgebraicGeometry.Etale.isZero_rightDerived_sectionsFunctor_iff_forget₂`): the underlying
abelian sheaves of an injective resolution of `M` form an acyclic resolution of the underlying
abelian sheaf (`AlgebraicGeometry.Etale.subsingleton_H_forget₂_succ_of_injective`),
and forgetting the module structure is exact and faithful.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Etale

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- Taking underlying abelian groups preserves étale sheaves. -/
lemma hasSheafCompose_forget₂_moduleCat (X : Scheme.{u}) :
    X.smallEtaleTopology.HasSheafCompose (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) :=
  hasSheafCompose_of_preservesLimitsOfSize _

lemma preservesColimits_forget₂_moduleCat :
    PreservesColimits (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) :=
  ModuleCat.forget₂PreservesColimitsOfSize.{u + 1, u + 1, u + 1} Λ

attribute [local instance high] hasSheafCompose_forget₂_moduleCat
  preservesColimits_forget₂_moduleCat

section Acyclicity

open Presheaf Scheme

variable (Λ)
variable {C : Type (u + 1)} [Category.{u} C] (P : Cᵒᵖ ⥤ ModuleCat.{u + 1} Λ)

/-- The presheaf of `Λ`-modules `Y ↦ ∏_{W, g : W ⟶ Y} P(W)`, with restriction by precomposition:
the `Λ`-linear version of `CategoryTheory.Presheaf.cofree`. -/
noncomputable def cofreeModulePresheaf : Cᵒᵖ ⥤ ModuleCat.{u + 1} Λ where
  obj Y := ModuleCat.of Λ (∀ (W : C) (_ : W ⟶ Y.unop), P.obj (op W))
  map {Y Y'} h := ModuleCat.ofHom
    { toFun c W g := c W (g ≫ h.unop)
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  map_id _ := by
    ext
    simp
  map_comp _ _ := by
    ext
    simp

/-- The embedding of a presheaf of `Λ`-modules into its cofree presheaf, `p ↦ (g ↦ P(g) p)`. -/
noncomputable def toCofreeModulePresheaf : P ⟶ cofreeModulePresheaf Λ P where
  app Y := ModuleCat.ofHom
    { toFun p W g := P.map g.op p
      map_add' _ _ := funext fun _ ↦ funext fun _ ↦ map_add _ _ _
      map_smul' _ _ := funext fun _ ↦ funext fun _ ↦ map_smul _ _ _ }
  naturality Y Y' h := by
    refine ModuleCat.hom_ext (LinearMap.ext fun p ↦ funext fun W ↦ funext fun g ↦ ?_)
    change P.map g.op (P.map h p) = P.map (g ≫ h.unop).op p
    rw [op_comp, P.map_comp]
    rfl

instance : Mono (toCofreeModulePresheaf Λ P) := by
  have (Y : Cᵒᵖ) : Mono ((toCofreeModulePresheaf Λ P).app Y) :=
    (ModuleCat.mono_iff_injective _).2 fun p p' h ↦ by
      have := congrFun (congrFun h Y.unop) (𝟙 _)
      change P.map (𝟙 _).op p = P.map (𝟙 _).op p' at this
      simpa using this
  exact NatTrans.mono_of_mono_app _


/-- The Čech complexes of the underlying abelian presheaf of an injective presheaf of
`Λ`-modules are exact in positive degrees: it is a retract of the cofree abelian presheaf, as
the presheaf of `Λ`-modules is a retract of its `Λ`-linear cofree presheaf. -/
lemma exactAt_cechComplex_forget₂_of_injective_aux [Injective P] {V : C}
    [HasFiniteProducts (Over V)] {ι : Type*} (U : ι → Over V) (q : ℕ) :
    ((cechComplex U).obj (P ⋙ forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).ExactAt
      (q + 1) := by
  let r := Injective.factorThru (𝟙 P) (toCofreeModulePresheaf Λ P)
  have hr : toCofreeModulePresheaf Λ P ≫ r = 𝟙 P := Injective.comp_factorThru _ _
  let b : cofree (P ⋙ forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) ⟶
      P ⋙ forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1} :=
    { app Y := AddCommGrpCat.ofHom
        (show (∀ (W : C) (_ : W ⟶ Y.unop), P.obj (op W)) →+ P.obj Y from
          (r.app Y).hom.toAddMonoidHom)
      naturality Y Y' h := by
        ext c
        exact ConcreteCategory.congr_hom (r.naturality h) c }
  have hab : toCofree _ ≫ b = 𝟙 _ := by
    ext Y p
    exact ConcreteCategory.congr_hom (NatTrans.congr_app hr Y) p
  set ι' := (cechComplex U).map
    (toCofree (P ⋙ forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}))
  set ρ := (cechComplex U).map b
  have hιρ (k : ℕ) (c : ((cechComplex U).obj
      (P ⋙ forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).X k) : ρ.f k (ι'.f k c) = c := by
    rw [← ConcreteCategory.comp_apply, ← HomologicalComplex.comp_f, ← Functor.map_comp, hab,
      CategoryTheory.Functor.map_id, HomologicalComplex.id_f, ConcreteCategory.id_apply]
  rw [exactAt_cechComplex_iff]
  intro c hc
  obtain ⟨b', hb'⟩ := (exactAt_cechComplex_iff U _ q).1 (exactAt_cechComplex_cofree U _ q)
    (ι'.f (q + 1) c) ((ConcreteCategory.congr_hom (ι'.comm (q + 1) (q + 2)) c).trans
        ((congrArg (ι'.f (q + 2)) hc).trans (map_zero _)))
  exact ⟨ρ.f q b', (ConcreteCategory.congr_hom (ρ.comm q (q + 1)) b').trans
    ((congrArg (ρ.f (q + 1)) hb').trans (hιρ _ c))⟩

/-- On a quasi-compact quasi-separated scheme `Z`, the underlying abelian sheaf of an injective
sheaf of `Λ`-modules has no higher cohomology, by the Čech criterion
`CategoryTheory.Sheaf.subsingleton_H_succ_of_exactAt_cechComplex` and
`AlgebraicGeometry.exactAt_cechComplex_forget₂_of_injective_aux`. -/
theorem subsingleton_H_sheafCompose_forget₂_succ_of_injective (Z : Scheme.{u}) [CompactSpace Z]
    [QuasiSeparatedSpace Z] (I : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [Injective I]
    (q : ℕ) :
    Subsingleton (Sheaf.H ((sheafCompose Z.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj I) (q + 1)) := by
  have : Injective I.obj := (sheafificationAdjunction _ _).map_injective I inferInstance
  let B : Z.Etale → Prop := fun W ↦ CompactSpace W.left ∧ QuasiSeparatedSpace W.left
  have hcov (V : Z.Etale) (hV : B V) (R : Sieve V) (hR : R ∈ Z.smallEtaleTopology V) :
      ∃ (n : ℕ) (U : Fin n → Over V),
        (∀ (k : ℕ) (y : Fin (k + 1) → Fin n), B (cechNerveObj U y).left) ∧ (∀ a, R (U a).hom) ∧
        Sieve.ofArrows (fun a ↦ (U a).left) (fun a ↦ (U a).hom) ∈ Z.smallEtaleTopology V := by
    obtain ⟨_, _⟩ := hV
    obtain ⟨n, U, g, hRg, hU, hg⟩ := exists_finite_affine_of_mem_smallEtaleTopology hR
    refine ⟨n, fun a ↦ Over.mk (g a), fun k y ↦ ?_, hRg,
      (ofArrows_mem_smallEtaleTopology_iff g).2 hg⟩
    refine compactSpace_and_quasiSeparatedSpace_piObj _ fun l ↦ ?_
    have := hU (y l)
    exact ⟨inferInstanceAs (CompactSpace (U (y l)).left),
      inferInstanceAs (QuasiSeparatedSpace (U (y l)).left)⟩
  let T : Z.Etale := MorphismProperty.Over.mk ⊤ (𝟙 Z) (inferInstance : Etale (𝟙 Z))
  have hT : IsTerminal T :=
    MorphismProperty.Over.mkIdTerminal _ Z
  have key := Sheaf.subsingleton_H_succ_of_exactAt_cechComplex hT B
    ⟨‹CompactSpace Z›, ‹QuasiSeparatedSpace Z›⟩ hcov ((sheafCompose Z.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj I)
    (fun _ _ _ U _ _ q ↦ exactAt_cechComplex_forget₂_of_injective_aux Λ I.obj U q) q
  exact key

end Acyclicity

/-- The forgetful functor from `Λ`-modules to abelian groups is a left adjoint: restriction of
scalars along `ℤ → Λ` is left adjoint to coextension of scalars. -/
lemma isLeftAdjoint_forget₂_moduleCat :
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).IsLeftAdjoint := by
  let V := ModuleCat.restrictScalars.{u + 1} (algebraMap ℤ Λ) ⋙
    forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}
  let e : V ≅ forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1} :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ by rfl)
  have : (ModuleCat.restrictScalars.{u + 1} (algebraMap ℤ Λ)).IsLeftAdjoint :=
    (ModuleCat.restrictCoextendScalarsAdj.{0, 0, u + 1} (algebraMap ℤ Λ)).isLeftAdjoint
  exact Functor.isLeftAdjoint_of_iso e

/-- Taking underlying abelian sheaves is additive. -/
lemma additive_sheafCompose_forget₂' {X : Scheme.{u}} :
    (sheafCompose X.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).Additive where
  map_add := by
    intros
    rfl

/-- Taking underlying abelian sheaves preserves finite limits. -/
lemma preservesFiniteLimits_sheafCompose_forget₂' {X : Scheme.{u}} :
    PreservesFiniteLimits (sheafCompose X.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})) := by
  have : PreservesFiniteLimits (sheafCompose X.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) ⋙ sheafToPresheaf _ _) :=
    inferInstanceAs (PreservesFiniteLimits (sheafToPresheaf _ _ ⋙
      (Functor.whiskeringRight _ _ _).obj (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})))
  exact preservesFiniteLimits_of_reflects_of_preserves _ (sheafToPresheaf _ _)

/-- Taking underlying abelian sheaves preserves finite colimits. -/
lemma preservesFiniteColimits_sheafCompose_forget₂ {X : Scheme.{u}} :
    PreservesFiniteColimits (sheafCompose X.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})) := by
  have := isLeftAdjoint_forget₂_moduleCat (Λ := Λ)
  let hadj := Adjunction.ofIsLeftAdjoint (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
  have : PreservesLimitsOfSize.{u, u + 1}
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).rightAdjoint :=
    hadj.rightAdjoint_preservesLimits
  have : X.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).rightAdjoint :=
    hasSheafCompose_of_preservesLimitsOfSize _
  have := (Sheaf.adjunction X.smallEtaleTopology hadj).isLeftAdjoint
  exact preservesFiniteColimits_of_natIso
    (sheafToPresheafCompWhiskeringRightCompPresheafToSheafIso _ _)

attribute [local instance] additive_sheafCompose_forget₂'
  preservesFiniteLimits_sheafCompose_forget₂' preservesFiniteColimits_sheafCompose_forget₂

/-- The cohomology of an étale sheaf of `Λ`-modules vanishes if and only if the cohomology of its
underlying abelian sheaf vanishes. -/
lemma isZero_rightDerived_sectionsFunctor_iff_forget₂ {X : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X]
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ) :
    IsZero (((sectionsFunctor (ModuleCat.{u + 1} Λ) X).rightDerived q).obj M) ↔
      IsZero (((sectionsFunctor AddCommGrpCat.{u + 1} X).rightDerived q).obj
        ((sheafCompose X.smallEtaleTopology
          (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj M)) := by
  let G := sheafCompose X.smallEtaleTopology (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
  let J := injectiveResolution M
  have hacyc (n : ℕ) : (sectionsFunctor AddCommGrpCat.{u + 1} X).rightAcyclic
      (G.obj (J.cocomplex.X n)) := fun m ↦
    (Sheaf.subsingleton_H_iff_isZero_rightDerived X.smallEtaleTopology
      (MorphismProperty.Over.mkIdTerminal _ X) (m + 1) _).1
      (subsingleton_H_sheafCompose_forget₂_succ_of_injective Λ X (J.cocomplex.X n) m)
  let ι' : (CochainComplex.single₀ _).obj (G.obj M) ⟶
      (G.mapHomologicalComplex _).obj J.cocomplex :=
    (HomologicalComplex.singleMapHomologicalComplex G (ComplexShape.up ℕ) 0).inv.app M ≫
      (G.mapHomologicalComplex _).map J.ι
  have : QuasiIso ι' := by
    dsimp only [ι']
    infer_instance
  rw [(J.isoRightDerivedObj _ q).isZero_iff,
    ((sectionsFunctor AddCommGrpCat.{u + 1} X).rightDerivedObjIsoOfResolution
      ι' hacyc q).isZero_iff,
    HomologicalComplex.homologyFunctor_obj,
    ← HomologicalComplex.exactAt_iff_isZero_homology,
    ← HomologicalComplex.exactAt_iff_isZero_homology]
  exact ((((sectionsFunctor (ModuleCat.{u + 1} Λ) X).mapHomologicalComplex _).obj
    J.cocomplex).sc q |>.exact_map_iff_of_faithful
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).symm

end AlgebraicGeometry.Etale
