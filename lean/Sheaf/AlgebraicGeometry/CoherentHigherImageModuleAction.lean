/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.AffineCohomologyComparisonData
import Sheaf.AlgebraicGeometry.RawRestrictedClassNormalization
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Sheaf.AlgebraicGeometry.CoherentRawScalarRestriction
import Mathlib.Algebra.Module.TransferInstance
import Mathlib.Algebra.Category.Ring.Adjunctions
import WeilConjectures.AlgebraicGeometry.Sites.Gm

/-! # Canonical local scalar action on coherent higher images

Source: Stacks Project, Tags 03Q8 and 03CY.
-/

@[expose] public section
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
set_option autoImplicit false
set_option cleanup.letToHave false
set_option backward.defeqAttrib.useBackward false
attribute [local irreducible] affineRealizationRawEquiv affineRealizationClass
  Etale.normalizationKappa Etale.normalizationLift
  Etale.sheafHDerivedEquiv Etale.sheafHToDerived
  CategoryTheory.derivedExtEvaluation coherentEtaleRestrictionIso
  moduleAbelianCohomologyLarge coherentEtaleMap Sheaf.H.map
  moduleCohomologyFMap IsNormalizedCoherentEtaleComparison
  tensorPullback tensorPullbackObj tensorSectionsComp tensorSectionsUnit
  Etale.abelianHigherDirectImageClass Etale.rawRestrictedCohomologyComparison
  DerivedCategory.Plus.homologyFunctor
  Etale.lowerStar Etale.upperStar
  etaleTensorSectionsRestriction smulHom
attribute [local instance 50]
  instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensCarrierAbPresheaf
attribute [local instance] Etale.RawRestrictedComparison.etaleComposition
  Etale.RawRestrictedComparison.etaleIdentities Etale.RawRestrictedComparison.etalePullbacks
  Etale.RawRestrictedComparison.etaleBaseChange Etale.RawRestrictedComparison.sheafifyInstance
  Etale.RawRestrictedComparison.weakSheafifyInstance
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem etale_ext (Y : Scheme.{u}) :
    HasExt.{u + 1} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) := by
  infer_instance

attribute [local instance 3000] etale_ext

private theorem zariski_over_weak (Y : Scheme.{u}) :
    ∀ U : TopologicalSpace.Opens Y,
      HasWeakSheafify ((Opens.grothendieckTopology Y).over U) AddCommGrpCat.{u} := by
  intro U
  infer_instance

private theorem zariski_over_local (Y : Scheme.{u}) :
    ∀ U : TopologicalSpace.Opens Y,
      ((Opens.grothendieckTopology Y).over U).WEqualsLocallyBijective AddCommGrpCat.{u} := by
  intro U
  infer_instance

attribute [local instance 3000] zariski_over_weak zariski_over_local

private abbrev QC {Y : Scheme.{u}} (M : Y.Modules) := M.IsQuasicoherent

private noncomputable instance tensor_additive {Y Z : Scheme.{u}} (g : Y ⟶ Z) :
    (tensorPullback g).Additive := by
  exact (Classical.choose (exists_tensorPullbackAdjunction g)).left_adjoint_additive

private theorem coherent_map_app {Y : Scheme.{u}} (M N : Y.Modules)
    [QC M] [QC N] (φ : M ⟶ N) (V : Y.Etale) :
    (coherentEtaleMap M N φ).hom.app (op V) =
      AddCommGrpCat.uliftFunctor.map (((tensorPullback V.hom).map φ).app ⊤) := by
  unfold coherentEtaleMap
  exact congrArg AddCommGrpCat.uliftFunctor.map
    ((Classical.choose_spec (etale_zariski_qcoh_comparison Y)).1 M N φ V)



private theorem coherent_map_id {Y : Scheme.{u}} (M : Y.Modules)
    [QC M] : coherentEtaleMap M M (𝟙 M) = 𝟙 _ := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  rw [coherent_map_app, CategoryTheory.Functor.map_id, Hom.id_app,
    CategoryTheory.Functor.map_id]
  rfl

private theorem coherent_map_comp {Y : Scheme.{u}} (M N P : Y.Modules)
    [QC M] [QC N] [QC P]
    (φ : M ⟶ N) (ψ : N ⟶ P) :
    coherentEtaleMap M P (φ ≫ ψ) = coherentEtaleMap M N φ ≫ coherentEtaleMap N P ψ := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  change (coherentEtaleMap M P (φ ≫ ψ)).hom.app V =
    (coherentEtaleMap M N φ).hom.app V ≫ (coherentEtaleMap N P ψ).hom.app V
  rw [coherent_map_app, coherent_map_app, coherent_map_app,
    Functor.map_comp, Hom.comp_app, Functor.map_comp]

private theorem coherent_map_add {Y : Scheme.{u}} (M N : Y.Modules)
    [QC M] [QC N] (φ ψ : M ⟶ N) :
    coherentEtaleMap M N (φ + ψ) = coherentEtaleMap M N φ + coherentEtaleMap M N ψ := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  change (coherentEtaleMap M N (φ + ψ)).hom.app V =
    (coherentEtaleMap M N φ).hom.app V + (coherentEtaleMap M N ψ).hom.app V
  rw [coherent_map_app, coherent_map_app, coherent_map_app,
    Functor.map_add, Hom.add_app, Functor.map_add]

private theorem coherent_map_zero {Y : Scheme.{u}} (M N : Y.Modules)
    [QC M] [QC N] : coherentEtaleMap M N 0 = 0 := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  rw [coherent_map_app, Functor.map_zero, Hom.zero_app, Functor.map_zero]
  rfl



set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible] CoherentEtale.Coeff etaleTensorSectionsSheaf

@[instance_reducible] private def module_of_functor {C : Type*} [Category C] [Preadditive C]
    {R : Type*} [Semiring R] (T : C ⥤ AddCommGrpCat.{v}) [T.Additive] (M : C)
    (ρ : R → (M ⟶ M)) (h₁ : ρ 1 = 𝟙 M) (hzero : ρ 0 = 0)
    (hmul : ∀ a b, ρ (a * b) = ρ b ≫ ρ a)
    (hadd : ∀ a b, ρ (a + b) = ρ a + ρ b) : Module R (T.obj M) where
  smul a x := T.map (ρ a) x
  one_smul x := by
    change T.map (ρ 1) x = x
    rw [h₁, T.map_id]
    rfl
  mul_smul a b x := by
    change T.map (ρ (a * b)) x = T.map (ρ a) (T.map (ρ b) x)
    rw [hmul, T.map_comp]
    rfl
  smul_zero a := map_zero _
  smul_add a := map_add _
  add_smul a b x := by
    change T.map (ρ (a + b)) x = T.map (ρ a) x + T.map (ρ b) x
    rw [hadd, T.map_add]
    rfl
  zero_smul x := by
    change T.map (ρ 0) x = 0
    rw [hzero, T.map_zero]
    rfl


@[instance_reducible] private def coherent_cohomology_module {Y : Scheme.{u}} (M : Y.Modules)
    [QC M] (q : ℕ) :
    Module Γ(Y, ⊤) (Sheaf.H (liftedCoherentEtaleSheaf M) q) :=
  module_of_functor (Sheaf.functorH Y.smallEtaleTopology q) (liftedCoherentEtaleSheaf M)
    (fun a ↦ coherentEtaleMap M M (M.smulHom a))
    (by rw [smulHom_one, coherent_map_id])
    (by rw [smulHom_zero, coherent_map_zero])
    (by intro a b; rw [smulHom_mul, coherent_map_comp])
    (by intro a b; rw [smulHom_add, coherent_map_add])

private theorem coherent_cohomology_module_apply {Y : Scheme.{u}} (M : Y.Modules)
    [QC M] (q : ℕ) (a : Γ(Y, ⊤))
    (x : Sheaf.H (liftedCoherentEtaleSheaf M) q) :
    affineRealizationSmul (coherent_cohomology_module M q) a x =
      Sheaf.H.map (coherentEtaleMap M M (M.smulHom a)) q x := rfl




attribute [local irreducible] coherent_cohomology_module

private def lift_ring : CommRingCat.{u} ⥤ CommRingCat.{u + 1} where
  obj R := CommRingCat.of (ULift.{u + 1} R)
  map φ := CommRingCat.ofHom φ.hom.ulift

attribute [local irreducible] AlgebraicGeometry.Scheme.etaleStructurePresheaf

private def scalar_ring (S : Scheme.{u}) : Sheaf S.smallEtaleTopology RingCat.{u + 1} := by
  let : PreservesLimitsOfSize.{u, u + 1} (CategoryTheory.forget CommRingCat.{u}) :=
    CommRingCat.adj.rightAdjoint_preservesLimits
  let R := S.etaleStructurePresheaf ⋙ lift_ring
  have hR : Presheaf.IsSheaf S.smallEtaleTopology R := by
    apply Presheaf.isSheaf_of_isSheaf_forget_commRingCat
    change Presieve.IsSheaf S.smallEtaleTopology
      ((S.etaleStructurePresheaf ⋙ CategoryTheory.forget CommRingCat.{u}) ⋙ uliftFunctor.{u + 1, u})
    apply Presieve.isSheaf_comp_uliftFunctor
    exact (isSheaf_iff_isSheaf_of_type _ _).1
      (Presheaf.isSheaf_comp_of_isSheaf _ _ (CategoryTheory.forget CommRingCat.{u})
        S.isSheaf_etaleStructurePresheaf)
  exact ⟨R ⋙ forget₂ CommRingCat RingCat,
    Presheaf.isSheaf_comp_of_isSheaf _ _ _ hR⟩


attribute [local semireducible] AlgebraicGeometry.Scheme.etaleStructurePresheaf

private theorem kappa_locally_bijective {X S : Scheme.{u}} (f : X ⟶ S)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) :
    Presheaf.IsLocallyInjective S.smallEtaleTopology (Etale.normalizationKappa f q F) ∧
      Presheaf.IsLocallySurjective S.smallEtaleTopology (Etale.normalizationKappa f q F) := by
  have : IsIso (Etale.normalizationLift f q F) :=
    (Etale.rawRestrictedClassNormalization f q F).2.2.2.1
  have hfac : toSheafify S.smallEtaleTopology
      (Etale.abelianHigherDirectImageRawPresheaf f q F) ≫
      (Etale.normalizationLift f q F).hom = Etale.normalizationKappa f q F := by
    unfold Etale.normalizationLift
    exact toSheafify_sheafifyLift S.smallEtaleTopology
      (Etale.normalizationKappa f q F) _
  rw [← hfac]
  constructor <;> infer_instance


private theorem kappa_eq_class {X S : Scheme.{u}} (f : X ⟶ S)
    (G : X.Modules) [QC G] (q : ℕ) (V : S.Etale)
    (z : (Etale.abelianHigherDirectImageRawPresheaf f q
      (liftedCoherentEtaleSheaf G)).obj (op V)) :
    (Etale.normalizationKappa f q (liftedCoherentEtaleSheaf G)).app (op V) z =
      affineRealizationClass f G q V (affineRealizationRawEquiv f G q V z) := by
  exact ((Etale.rawRestrictedClassNormalization f q
    (liftedCoherentEtaleSheaf G)).2.2.1 V z).trans
      (affineRealizationClass_rawEvaluation f G q V z).symm




private theorem sheafify_action {C : Type*} [Category C]
    {J : GrothendieckTopology C} (R : Sheaf J RingCat.{v})
    (P : Cᵒᵖ ⥤ AddCommGrpCat.{w}) (H : Sheaf J AddCommGrpCat.{w})
    (E : Cᵒᵖ → Type w) [∀ V, AddCommGroup (E V)]
    (e : ∀ V, P.obj V ≃+ E V) (m : ∀ V, Module (R.obj.obj V) (E V))
    (hres : ∀ {V V'} (h : V ⟶ V') a z,
      P.map h ((e V).symm (affineRealizationSmul (m V) a (e V z))) =
        (e V').symm (affineRealizationSmul (m V') (R.obj.map h a) (e V' (P.map h z))))
    (φ : P ⟶ H.obj) [Presheaf.IsLocallyInjective J φ]
    [Presheaf.IsLocallySurjective J φ] :
    ∃ action : ∀ V, Module (R.obj.obj V) (H.obj.obj V),
      (∀ {V V'} (h : V ⟶ V') a x,
        H.obj.map h (affineRealizationSmul (action V) a x) =
          affineRealizationSmul (action V') (R.obj.map h a) (H.obj.map h x)) ∧
      (∀ V a x, affineRealizationSmul (action V) a (φ.app V ((e V).symm x)) =
        φ.app V ((e V).symm (affineRealizationSmul (m V) a x))) := by
  let (V : Cᵒᵖ) := m V
  let (V : Cᵒᵖ) := (e V).module (R.obj.obj V)
  let M₀ : _root_.PresheafOfModules.{w} R.obj :=
    _root_.PresheafOfModules.ofPresheaf P (by
      intro V V' h a z
      change P.map h ((e V).symm (a • e V z)) =
        (e V').symm (R.obj.map h a • e V' (P.map h z))
      exact hres h a z)
  let ψ : M₀.presheaf ⟶ H.obj := φ
  let : Presheaf.IsLocallyInjective J ψ := inferInstanceAs
    (Presheaf.IsLocallyInjective J φ)
  let : Presheaf.IsLocallySurjective J ψ := inferInstanceAs
    (Presheaf.IsLocallySurjective J φ)
  let action V := _root_.PresheafOfModules.Sheafify.module (𝟙 R.obj) ψ V
  refine ⟨action, ?_, ?_⟩
  · intro V V' h a x
    exact _root_.PresheafOfModules.Sheafify.map_smul (𝟙 R.obj) ψ V h a x
  · intro V a x
    have h := (((_root_.PresheafOfModules.toSheafify (𝟙 R.obj) ψ).app V).hom.map_smul
      a ((e V).symm x)).symm
    change affineRealizationSmul (action V) a (φ.app V ((e V).symm x)) =
      φ.app V ((e V).symm
        (affineRealizationSmul (m V) a (e V ((e V).symm x)))) at h
    exact h.trans (congrArg (fun y ↦ φ.app V ((e V).symm
      (affineRealizationSmul (m V) a y))) ((e V).apply_symm_apply x))


/-- Local multiplication induces a module action on the abelian higher image,
independently of any realization by another coefficient module.
Source: Stacks Project, Tag 03Q8, lemma-higher-direct-images, and Tag 03CY.
(blueprint: lem-weil-pbc-coherent-higher-image-module-action).

Proof: On an etale object V, multiply the restricted coefficient by the pullback
of a function on V, and apply cohomology. Additivity and functoriality carry the
identities for coefficient multiplication to the module identities on cohomology.
Cohomological restriction commutes with these endomorphisms by coefficient
naturality and the tensor pullback composition identity. This gives a presheaf
of modules over the lifted etale structure sheaf on the entire etale site.
Sheafify that presheaf as a module presheaf. Its underlying abelian sheaf is the
abelian sheafification of its underlying presheaf. The actual raw evaluation and
its canonical class normalization identify that sheafification with the abelian
higher direct image. Transfer the module structures by this fixed identification.
The sheafification unit is linear and restriction is semilinear; on each
cohomology class these facts give exactly the second displayed equality.
The zero coefficient, empty etale object and degree zero satisfy the same
identities, so no affine or quasi-compact hypothesis is needed here. -/
theorem exists_coherentHigherImageModuleAction {X S : Scheme.{u}} (f : X ⟶ S)
    (G : X.Modules) [G.IsQuasicoherent] (q : ℕ) :
    ∃ action : ∀ V : S.Etale,
        Module (ULift.{u + 1} Γ(V.left, ⊤))
          ((affineRealizationHigherImage f G q).obj.obj (op V)),
      (∀ (V V' : S.Etale) (h : V' ⟶ V) (a : ULift.{u + 1} Γ(V.left, ⊤))
        (x : (affineRealizationHigherImage f G q).obj.obj (op V)),
        (affineRealizationHigherImage f G q).obj.map h.op
          (affineRealizationSmul (action V) a x) =
        affineRealizationSmul (action V') (ULift.up (h.left.appTop a.down))
          ((affineRealizationHigherImage f G q).obj.map h.op x)) ∧
      (∀ (V : S.Etale) (a : Γ(V.left, ⊤))
        (x : Sheaf.H (liftedCoherentEtaleSheaf (affineRealizationCoefficient f G V)) q),
        affineRealizationSmul (action V) (ULift.up a) (affineRealizationClass f G q V x) =
          affineRealizationClass f G q V (Sheaf.H.map
            (coherentEtaleMap _ _
              ((affineRealizationCoefficient f G V).smulHom
                ((Limits.pullback.fst V.hom f).appTop a)))
            q x)) := by
  classical
  let R := scalar_ring S
  let P := Etale.abelianHigherDirectImageRawPresheaf f q (liftedCoherentEtaleSheaf G)
  let E (V : S.Etaleᵒᵖ) :=
    Sheaf.H (liftedCoherentEtaleSheaf (affineRealizationCoefficient f G V.unop)) q
  let e (V : S.Etaleᵒᵖ) : P.obj V ≃+ E V := affineRealizationRawEquiv f G q V.unop
  let m (V : S.Etaleᵒᵖ) : Module (R.obj.obj V) (E V) := by
    letI := coherent_cohomology_module (affineRealizationCoefficient f G V.unop) q
    exact Module.compHom (E V)
      ((Limits.pullback.fst V.unop.hom f).appTop.hom.comp ULift.ringEquiv.toRingHom)
  have hm (V : S.Etaleᵒᵖ) (a : R.obj.obj V) (x : E V) :
      affineRealizationSmul (m V) a x =
        Sheaf.H.map (coherentEtaleMap _ _
          ((affineRealizationCoefficient f G V.unop).smulHom
            ((Limits.pullback.fst V.unop.hom f).appTop a.down))) q x := by
    exact coherent_cohomology_module_apply _ q _ x
  have hres {V V' : S.Etaleᵒᵖ} (h : V ⟶ V') (a : R.obj.obj V) (z : P.obj V) :
      P.map h ((e V).symm (affineRealizationSmul (m V) a (e V z))) =
        (e V').symm (affineRealizationSmul (m V') (R.obj.map h a) (e V' (P.map h z))) := by
    simp only [hm]
    exact coherentRawScalarRestriction f G q h.unop a.down z
  let φ : P ⟶ (affineRealizationHigherImage f G q).obj :=
    Etale.normalizationKappa f q (liftedCoherentEtaleSheaf G)
  have hbij := kappa_locally_bijective f (liftedCoherentEtaleSheaf G) q
  let : Presheaf.IsLocallyInjective S.smallEtaleTopology φ := hbij.1
  let : Presheaf.IsLocallySurjective S.smallEtaleTopology φ := hbij.2
  obtain ⟨action, hrestrict, hlinear⟩ :=
    sheafify_action R P (affineRealizationHigherImage f G q) E e m hres φ
  refine ⟨fun V ↦ action (op V), ?_, ?_⟩
  · intro V V' h a x
    exact hrestrict h.op a x
  · intro V a x
    have hc (y : E (op V)) :
        φ.app (op V) ((e (op V)).symm y) = affineRealizationClass f G q V y := by
      exact (kappa_eq_class f G q V ((e (op V)).symm y)).trans
        (congrArg (affineRealizationClass f G q V)
          ((affineRealizationRawEquiv f G q V).apply_symm_apply y))
    have hl := hlinear (op V) (ULift.up a) x
    exact (congrArg (affineRealizationSmul (action (op V)) (ULift.up a)) (hc x).symm).trans
      (hl.trans ((hc _).trans
        (congrArg (affineRealizationClass f G q V) (hm (op V) (ULift.up a) x))))

end
end AlgebraicGeometry.Scheme.Modules
