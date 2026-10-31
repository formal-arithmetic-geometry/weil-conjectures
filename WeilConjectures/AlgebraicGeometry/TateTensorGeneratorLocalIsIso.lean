/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.TateTensorGeneratorMap
import all WeilConjectures.AlgebraicGeometry.FiniteTateLocalRootTensorsExt
import all WeilConjectures.AlgebraicGeometry.PurTwistRootLocalModels
import all WeilConjectures.AlgebraicGeometry.CompactSupportCoefficientModelsOrdinaryExistence
import all WeilConjectures.AlgebraicGeometry.FiniteRootSiteComparison
import all WeilConjectures.AlgebraicGeometry.ProEtaleSheafificationTensorComparison
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarExtensionConstraintCoherence
import all WeilConjectures.AlgebraicGeometry.ComparisonPureSections
import all WeilConjectures.Algebra.Homology.RingedTensorComplexConstraintsSupplement
import all WeilConjectures.AlgebraicGeometry.ScalarReductionTowerBalancing

/-! Pointwise local invertibility of the normalized Tate tensor map.

Source: smooth-purity transport, normalized Tate tower, Step 2.
(blueprint: lem-pur-tate-tensor-generator-local-isiso)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry.Etale.FiniteSmoothPurity
namespace AlgebraicGeometry.Scheme.PurityIntegralTower

private theorem component_isIso
    {C : Type*} [Category* C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u + 1}} {M N : SheafOfModules.{u + 1} R}
    (e : M ≅ N) (W : Cᵒᵖ) : IsIso (e.hom.val.app W) :=
  Functor.map_isIso (SheafOfModules.evaluation R W) e.hom

private theorem component_injective
    {C : Type*} [Category* C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u + 1}} {M N : SheafOfModules.{u + 1} R}
    (e : M ≅ N) (W : Cᵒᵖ) : Function.Injective (e.hom.val.app W) := by
  have := component_isIso e W
  exact (ModuleCat.mono_iff_injective _).mp inferInstance

private theorem component_hom_inv
    {C : Type*} [Category* C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u + 1}} {M N : SheafOfModules.{u + 1} R}
    (e : M ≅ N) (W : Cᵒᵖ) (x : M.val.obj W) :
    e.inv.val.app W (e.hom.val.app W x) = x := by
  exact congrArg (fun f ↦ f.val.app W x) e.hom_inv_id

private theorem component_inv_hom
    {C : Type*} [Category* C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u + 1}} {M N : SheafOfModules.{u + 1} R}
    (e : M ≅ N) (W : Cᵒᵖ) (x : N.val.obj W) :
    e.hom.val.app W (e.inv.val.app W x) = x := by
  exact congrArg (fun f ↦ f.val.app W x) e.inv_hom_id

private theorem compatible_unique
    (T : Scheme.{u}) [IsNoetherian T] (ell : ℕ) [Fact ell.Prime]
    (hT : IsUnit (ell : Γ(T, ⊤))) (n d : ℕ)
    (f g : (realization T ell n).obj (finiteSheaf T ell n d) ⟶ quotientLine T ell n d)
    (hf : GeneratorCompatible T ell n d f)
    (hg : GeneratorCompatible T ell n d g) : f = g := by
  let P := (PresheafOfModules.restrictScalars (scalars T ell n)).obj
    (quotientLine T ell n d).val
  let Q : Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (coefficient.{u} ell (n + 1))) :=
    ⟨{ obj := P.obj
       map := P.map
       map_id := fun U ↦ by ext x; exact ConcreteCategory.congr_hom (P.presheaf.map_id U) x
       map_comp := fun i j ↦ by
         ext x
         exact ConcreteCategory.congr_hom (P.presheaf.map_comp i j) x },
      Presheaf.isSheaf_of_isSheaf_comp _ _
        (forget₂ (ModuleCat.{u + 1} (coefficient.{u} ell (n + 1))) AddCommGrpCat.{u + 1})
        (quotientLine T ell n d).isSheaf⟩
  let lift (k : (realization T ell n).obj (finiteSheaf T ell n d) ⟶
      quotientLine T ell n d) : finiteSheaf T ell n d ⟶ Q :=
    { hom :=
      { app := (PresheafOfModules.sheafificationHomEquiv (scalars T ell n) k).app
        naturality := fun U V i ↦ by
          ext x
          exact ConcreteCategory.congr_hom
            ((PresheafOfModules.sheafificationHomEquiv (scalars T ell n) k).naturality i) x } }
  suffices he : lift f = lift g by
    apply (PresheafOfModules.sheafificationHomEquiv (scalars T ell n)).injective
    ext U x
    exact ConcreteCategory.congr_hom
      (congr_app (congrArg (fun q : finiteSheaf T ell n d ⟶ Q ↦ q.hom) he) U) x
  let adj := ProEtale.comparisonAdjunction
    (ModuleCat.{u + 1} (coefficient.{u} ell (n + 1))) T
  apply (adj.homEquiv _ _).injective
  apply finite_tate_generators_hom_ext
  intro U a z
  obtain ⟨S, hS, hlift⟩ := finite_roots_lift_cover ell T hT n d U z
  let t := (adj.unit.app (finiteEtaleTateTwist T (ell ^ (n + 1))
    (coefficient.{u} ell (n + 1)) (CharP.cast_eq_zero _ _) d)).hom.app U
      (finiteTateEtalePowerGenerator T _ (ell ^ (n + 1))
        (CharP.cast_eq_zero _ _) U a d z)
  change (lift f).hom.app (op ((toProEt T).obj U.unop)) t =
    (lift g).hom.app (op ((toProEt T).obj U.unop)) t
  apply (((isSheaf_iff_isSheaf_of_type _ _).mp
    ((sheafCompose (ProEt.topology T)
      (CategoryTheory.forget (ModuleCat.{u + 1} (coefficient.{u} ell (n + 1))))).obj
        Q).property).isSeparated _ hS).ext
  intro W v hv
  obtain ⟨x, hx⟩ := hlift W v hv
  have hfn := ConcreteCategory.congr_hom ((lift f).hom.naturality v.op) t
  have hgn := ConcreteCategory.congr_hom ((lift g).hom.naturality v.op) t
  apply hfn.symm.trans
  apply Eq.trans _ hgn
  have hfg := (hf U (op W) v a z x hx).trans (hg U (op W) v a z x hx).symm
  change ((PresheafOfModules.toPresheaf _).map
      (PresheafOfModules.sheafificationHomEquiv (scalars T ell n) f)).app (op W)
        ((finiteSheaf T ell n d).obj.map v.op t) =
    ((PresheafOfModules.toPresheaf _).map
      (PresheafOfModules.sheafificationHomEquiv (scalars T ell n) g)).app (op W)
        ((finiteSheaf T ell n d).obj.map v.op t)
  rw [PresheafOfModules.toPresheaf_map_sheafificationHomEquiv_def,
    PresheafOfModules.toPresheaf_map_sheafificationHomEquiv_def]
  simp only [one_smul, id_eq] at hfg
  exact hfg

private theorem root_reduction_isIso
    (T : Scheme.{u}) (ell : ℕ) [Fact ell.Prime]
    [∀ x : T, Invertible (ell : T.residueField x)] (n : ℕ) :
    IsIso (rootReductionMap T ell n) := by
  classical
  obtain ⟨I, U, f, hc, hq⟩ := localTowerCover T ell
  have hU : (ProEt.topology T).CoversTop U := by
    let hT : IsTerminal (ProEt.mk (𝟙 T)) := MorphismProperty.Over.mkIdTerminal _ _
    rw [GrothendieckTopology.coversTop_iff_of_isTerminal _ _ hT]
    rw [← Sieve.ofArrows_eq_ofObjects hT U f]
    exact Precoverage.generate_mem_toGrothendieck hc
  have : IsIso ((SheafOfModules.toSheaf _).map (rootReductionMap T ell n)) := by
    apply Sheaf.isIso_of_coversTop hU
    intro i
    have := rootReductionMap_local T ell (U i) (hq i).some n
    exact Functor.map_isIso (SheafOfModules.toSheaf _)
      ((rootReductionMap T ell n).over (U i))
  exact isIso_of_reflects_iso _ (SheafOfModules.toSheaf _)

private theorem extension_pure
    (T : Scheme.{u}) {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (M : pbcModules T R) (W : T.ProEtᵒᵖ)
    (s : S.obj.obj W) (x : M.val.obj W) :
    (eqToIso ((pbcExtensionExistence φ).choose_spec.choose M)).hom.val.app W
        (pbcTensorSection φ M W s x) =
      SheafOfModules.scalarExtensionConstraintTmul φ M W x s := by
  let h := (pbcExtensionExistence φ).choose_spec.choose M
  change (eqToHom h).val.app W ((eqToHom h.symm).val.app W _) = _
  have hi := congrArg (fun f ↦ f.val.app W
      (SheafOfModules.scalarExtensionConstraintTmul φ M W x s))
    (eqToIso h).inv_hom_id
  exact hi

set_option maxHeartbeats 2000000 in
-- Comparing the two transported coefficient actions requires substantial definitional reduction.
private theorem root_quotient_iso
    (T : Scheme.{u}) (ell : ℕ) [Fact ell.Prime]
    [∀ x : T, Invertible (ell : T.residueField x)] (n : ℕ) :
    ∃ e : (pbcExtend (pbcAdicProjection T (datum.{u} ell) n)).obj
        (integralRoot T ell) ≅
      (pbcRestrict (coefficientIso T ell n).hom).obj (purTwistRootsModule T ell n),
      ∀ (W : T.ProEtᵒᵖ)
        (s : ((pbcAdicRings T (datum.{u} ell)).obj (op n)).obj.obj W)
        (x : (purTwistZlOne T ell).obj.obj W),
        e.hom.val.app W
          (pbcTensorSection (pbcAdicProjection T (datum.{u} ell) n)
            (integralRoot T ell) W s x) =
          (coefficientIso T ell n).hom.hom.app W s •
            (show (purTwistRootsModule T ell n).val.obj W from
              (limit.π (proEtaleRootsOfUnityTower T ell (Fact.out : ell.Prime))
                (op n)).hom.app W x) := by
  let φ := pbcAdicProjection T (datum.{u} ell) n
  let ψ := purTwistZlProjection T ell n
  let c := completionIso T ell
  let b := coefficientIso T ell n
  have hsq : c.hom ≫ ψ = φ ≫ b.hom :=
    (completionIso_existsUnique T ell).exists.choose_spec n
  obtain ⟨a, ha⟩ := WeilConjectures.PurStrictScalar.tensorBalancingOfSectionPushouts T
    φ ψ ((adicLisseForget T).map c.hom) ((adicLisseForget T).map b.hom)
    (fun W ↦ by
      change IsPushout (φ.hom.app W) (c.hom.hom.app W)
        (b.hom.hom.app W) (ψ.hom.app W)
      have hc : IsIso (c.hom.hom.app W) := inferInstance
      have hb : IsIso (b.hom.hom.app W) := inferInstance
      apply IsPushout.of_vert_isIso
      exact ⟨congrArg (fun f ↦ f.hom.app W) hsq.symm⟩)
    (purTwistZlModule T ell)
  let hq := (pbcExtensionExistence ψ).choose_spec.choose (purTwistZlModule T ell)
  have := root_reduction_isIso T ell n
  let r : (pbcExtend ψ).obj (purTwistZlModule T ell) ≅ purTwistRootsModule T ell n :=
    eqToIso hq ≪≫ asIso (rootReductionMap T ell n)
  refine ⟨a ≪≫ (pbcRestrict b.hom).mapIso r, ?_⟩
  intro W s x
  change r.hom.val.app W (a.hom.val.app W _) = _
  have haa := ha W s (show (purTwistZlModule T ell).val.obj W from x)
  change r.hom.val.app W _ = _
  erw [haa]
  change (rootReductionMap T ell n).val.app W
    ((eqToIso hq).hom.val.app W
      (pbcTensorSection ψ (purTwistZlModule T ell) W
        (b.hom.hom.app W s) x)) = _
  rw [extension_pure]
  exact SheafOfModules.scalarExtensionLift_tmul.{u + 1, u, u + 1, u + 1}
    ψ (purTwistZlModule T ell) (purTwistRootsModule T ell n)
      (rootProjectionModule T ell n) W (b.hom.hom.app W s) x

private def fixedModule (T : Scheme.{u}) (ell : ℕ) [Fact ell.Prime] (n : ℕ)
    (M : pbcModules T ((pbcAdicRings T (datum.{u} ell)).obj (op n))) :
    Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (coefficient.{u} ell (n + 1))) :=
  let P := (PresheafOfModules.restrictScalars (scalars T ell n)).obj M.val
  ⟨{ obj := P.obj
     map := P.map
     map_id := fun U ↦ by ext x; exact ConcreteCategory.congr_hom (P.presheaf.map_id U) x
     map_comp := fun i j ↦ by
       ext x
       exact ConcreteCategory.congr_hom (P.presheaf.map_comp i j) x },
    Presheaf.isSheaf_of_isSheaf_comp _ _
      (forget₂ (ModuleCat.{u + 1} (coefficient.{u} ell (n + 1))) AddCommGrpCat.{u + 1})
      M.isSheaf⟩

private def rootFixed (T : Scheme.{u}) (ell : ℕ) [Fact ell.Prime] (n : ℕ) :=
  fixedModule T ell n ((pbcRestrict (coefficientIso T ell n).hom).obj
    (purTwistRootsModule T ell n))

private def rootFixedHomEquiv (T : Scheme.{u}) (ell : ℕ) [Fact ell.Prime] (n : ℕ)
    (Q : Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (coefficient.{u} ell (n + 1)))) :
    (rootFixed T ell n ⟶ Q) ≃
      (proEtaleRootsOfUnitySheaf T (ell ^ (n + 1)) ⟶
        (sheafCompose (ProEt.topology T)
          (forget₂ (ModuleCat.{u + 1} (coefficient.{u} ell (n + 1)))
            AddCommGrpCat.{u + 1})).obj Q) where
  toFun f := { hom := {
    app := fun W ↦ AddCommGrpCat.ofHom (f.hom.app W).hom.toAddMonoidHom
    naturality := by
      intro U V v
      ext x
      exact ConcreteCategory.congr_hom (f.hom.naturality v) x } }
  invFun f := { hom := {
    app := fun W ↦ ModuleCat.ofHom
      (X := (rootFixed T ell n).obj.obj W) (Y := Q.obj.obj W) {
      toFun := f.hom.app W
      map_add' := map_add _
      map_smul' := by
        intro a x
        obtain ⟨z, hz⟩ := ZMod.intCast_surjective a.down.down
        have ha : (z : coefficient.{u} ell (n + 1)) = a :=
          ULift.ext _ _ (ULift.ext _ _ hz)
        rw [← ha]
        exact map_intCast_smul
          (show (rootFixed T ell n).obj.obj W →+ Q.obj.obj W from (f.hom.app W).hom)
          (coefficient.{u} ell (n + 1)) (coefficient.{u} ell (n + 1)) z x }
    naturality := by
      intro U V v
      ext x
      exact ConcreteCategory.congr_hom (f.hom.naturality v) x } }
  left_inv f := by ext W x; rfl
  right_inv f := by ext W x; rfl

private def finiteRootToFixed (T : Scheme.{u}) (ell : ℕ) [Fact ell.Prime] (n : ℕ) :
    finiteRootProTensor (coefficient.{u} ell (n + 1)) (ell ^ (n + 1))
      (pow_pos (Fact.out : ell.Prime).pos _) (CharP.cast_eq_zero _ _) T ⟶
        rootFixed T ell n :=
  (proLineHomEquiv T _ (pow_pos (Fact.out : ell.Prime).pos _)
    (coefficient.{u} ell (n + 1)) (CharP.cast_eq_zero _ _) _).symm
      (rootFixedHomEquiv T ell n _ (𝟙 _))

private theorem finiteRootToFixed_isIso
    (T : Scheme.{u}) (ell : ℕ) [Fact ell.Prime] (n : ℕ) :
    IsIso (finiteRootToFixed T ell n) := by
  apply isIso_of_coyoneda_map_bijective
  intro Q
  let e := (proLineHomEquiv T _ (pow_pos (Fact.out : ell.Prime).pos _)
    (coefficient.{u} ell (n + 1)) (CharP.cast_eq_zero _ _) Q).trans
      (rootFixedHomEquiv T ell n Q).symm
  suffices he : (fun g ↦ finiteRootToFixed T ell n ≫ g) = e.symm by
    rw [he]
    exact e.symm.bijective
  funext g
  apply (proLineHomEquiv T _ (pow_pos (Fact.out : ell.Prime).pos _)
    (coefficient.{u} ell (n + 1)) (CharP.cast_eq_zero _ _) Q).injective
  rw [proLineHomEquiv_comp, finiteRootToFixed, Equiv.apply_symm_apply]
  change _ = (proLineHomEquiv T _ (pow_pos (Fact.out : ell.Prime).pos _)
    (coefficient.{u} ell (n + 1)) (CharP.cast_eq_zero _ _) Q)
      ((proLineHomEquiv T _ (pow_pos (Fact.out : ell.Prime).pos _)
        (coefficient.{u} ell (n + 1)) (CharP.cast_eq_zero _ _) Q).symm
          ((rootFixedHomEquiv T ell n Q) g))
  rw [Equiv.apply_symm_apply]
  ext W x
  rfl

private def realizationCounit (T : Scheme.{u}) (ell : ℕ) [Fact ell.Prime] (n : ℕ)
    (M : pbcModules T ((pbcAdicRings T (datum.{u} ell)).obj (op n))) :
    (realization T ell n).obj (fixedModule T ell n M) ≅ M :=
  asIso ((PresheafOfModules.sheafificationAdjunction (scalars T ell n)).counit.app M)

private theorem realizationCounit_unit
    (T : Scheme.{u}) (ell : ℕ) [Fact ell.Prime] (n : ℕ)
    (M : pbcModules T ((pbcAdicRings T (datum.{u} ell)).obj (op n)))
    (W : T.ProEtᵒᵖ) (x : M.val.obj W) :
    (realizationCounit T ell n M).hom.val.app W
      ((toSheafify (ProEt.topology T) M.val.presheaf).app W x) = x := by
  have h := (PresheafOfModules.sheafificationAdjunction (scalars T ell n)).right_triangle_components
    M
  exact congrArg (fun k ↦ k.app W x) h

private theorem finiteRootToFixed_generator
    (T : Scheme.{u}) (ell : ℕ) [Fact ell.Prime] (n : ℕ)
    (W : T.ProEtᵒᵖ) (a : coefficient.{u} ell (n + 1))
    (z : (proEtaleRootsOfUnitySheaf T (ell ^ (n + 1))).obj.obj W) :
    (finiteRootToFixed T ell n).hom.app W
      (finiteRootProGenerator (coefficient.{u} ell (n + 1)) (ell ^ (n + 1))
        (pow_pos (Fact.out : ell.Prime).pos _) (CharP.cast_eq_zero _ _) T W a z) =
      a • (show (rootFixed T ell n).obj.obj W from z) := by
  have h := congrArg (fun f ↦ f.hom.app W z)
    ((proLineHomEquiv T _ (pow_pos (Fact.out : ell.Prime).pos _)
      (coefficient.{u} ell (n + 1)) (CharP.cast_eq_zero _ _) _).apply_symm_apply
        (rootFixedHomEquiv T ell n _ (𝟙 _)))
  rw [proLineHomEquiv_generator] at h
  change (finiteRootToFixed T ell n).hom.app W
      (finiteRootProGenerator (coefficient.{u} ell (n + 1)) (ell ^ (n + 1))
        (pow_pos (Fact.out : ell.Prime).pos _) (CharP.cast_eq_zero _ _) T W 1 z) =
      (show (rootFixed T ell n).obj.obj W from z) at h
  rw [proGenerator_smul, map_smul, h]


private theorem module_forget_preserves (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    (ProEt.topology T).PreservesSheafification
      (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1}) where
  le := by
    intro P Q f hf
    change (ProEt.topology T).W
      (Functor.whiskerRight f (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1}))
    rw [(ProEt.topology T).W_iff_isLocallyBijective] at hf ⊢
    have := hf.1
    have := hf.2
    constructor
    · exact ⟨fun x y h ↦ Presheaf.equalizerSieve_mem (ProEt.topology T) f x y h⟩
    · exact ⟨fun x ↦ Presheaf.imageSieve_mem (ProEt.topology T) f x⟩

set_option maxHeartbeats 1000000 in
-- Tensor comparison crosses the fixed and variable coefficient module presentations.
private theorem realization_tensor
    (T : Scheme.{u}) (ell : ℕ) [Fact ell.Prime] (n : ℕ)
    (F G : Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (coefficient.{u} ell (n + 1)))) :
    ∃ e : (realization T ell n).obj (F ⊗ G) ≅
        (realization T ell n).obj F ⊗ (realization T ell n).obj G,
      ∀ (W : T.ProEtᵒᵖ) (x : F.obj.obj W) (y : G.obj.obj W),
        e.hom.val.app W
          ((toSheafify (ProEt.topology T)
            ((F ⊗ G).obj ⋙ forget₂ _ AddCommGrpCat.{u + 1})).app W
            ((Functor.LaxMonoidal.μ (sheafToPresheaf (ProEt.topology T)
              (ModuleCat.{u + 1} (coefficient.{u} ell (n + 1)))) F G).app W
                (x ⊗ₜ[coefficient.{u} ell (n + 1)] y))) =
        SheafOfModules.scalarExtensionConstraintPureTensor
          ((pbcAdicRings T (datum.{u} ell)).obj (op n))
          ((realization T ell n).obj F) ((realization T ell n).obj G) W
          ((toSheafify (ProEt.topology T)
            (F.obj ⋙ forget₂ _ AddCommGrpCat.{u + 1})).app W x)
          ((toSheafify (ProEt.topology T)
            (G.obj ⋙ forget₂ _ AddCommGrpCat.{u + 1})).app W y) := by
  let J := ProEt.topology T
  let A := coefficient.{u} ell (n + 1)
  let R := (pbcAdicRings T (datum.{u} ell)).obj (op n)
  let E := ProEtale.finiteCoefficientModulePresheaf T.ProEt A
  let S := PresheafOfModules.sheafification (scalars T ell n)
  let O := (Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of A)
  let : MonoidalCategory (_root_.PresheafOfModules.{u + 1}
      ((Functor.const T.ProEtᵒᵖ).obj (RingCat.of A))) :=
    PresheafOfModules.monoidalCategory (R := O)
  let : J.PreservesSheafification (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1}) :=
    module_forget_preserves T A
  let j := sheafToPresheaf J (ModuleCat.{u + 1} A)
  let L := presheafToSheaf J (ModuleCat.{u + 1} A)
  let μ := Functor.LaxMonoidal.μ j F G
  have hμ : J.W μ := by
    rw [J.W_iff]
    have h := (sheafificationAdjunction J (ModuleCat.{u + 1} A)).map_μ_comp_counit_app_tensor
      F G
    have : IsIso (L.map μ ≫
        (sheafificationAdjunction J (ModuleCat.{u + 1} A)).counit.app (F ⊗ G)) := by
      rw [h]
      infer_instance
    exact IsIso.of_isIso_comp_right _
      ((sheafificationAdjunction J (ModuleCat.{u + 1} A)).counit.app (F ⊗ G))
  have hS : IsIso (S.map (E.map μ)) := by
    have : IsIso ((SheafOfModules.toSheaf ((adicLisseForget T).obj R)).map
        (S.map (E.map μ))) := by
      change IsIso ((presheafToSheaf J AddCommGrpCat.{u + 1}).map
        (Functor.whiskerRight μ (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})))
      rw [← J.W_iff]
      exact J.W_of_preservesSheafification _ μ hμ
    exact isIso_of_reflects_iso _ (SheafOfModules.toSheaf ((adicLisseForget T).obj R))
  let q : E.obj (F.obj ⊗ G.obj) ≅ E.obj F.obj ⊗ E.obj G.obj :=
    PresheafOfModules.isoMk (fun W ↦ Iso.refl _) (by
      intro U V f
      apply ModuleCat.MonoidalCategory.tensor_ext
      intro x y
      rfl)
  obtain ⟨b, hb⟩ := PresheafOfModules.exists_sheafificationTensorIso_proEtaleUniverses
    (O := (Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of A)) (R := R) (scalars T ell n)
  have hcomp : IsIso (S.map (q.inv ≫ E.map μ)) := by
    rw [S.map_comp]
    infer_instance
  let a : S.obj (E.obj F.obj ⊗ E.obj G.obj) ≅ S.obj (E.obj (F ⊗ G).obj) :=
    asIso (S.map (q.inv ≫ E.map μ))
  refine ⟨a.symm ≪≫ (b.app (E.obj F.obj, E.obj G.obj)).symm, ?_⟩
  intro W x y
  have ha : a.hom.val.app W
      (((PresheafOfModules.sheafificationAdjunction (scalars T ell n)).unit.app
        (E.obj F.obj ⊗ E.obj G.obj)).app W (x ⊗ₜ[A] y)) =
      (toSheafify J ((F ⊗ G).obj ⋙ forget₂ _ AddCommGrpCat.{u + 1})).app W
        (μ.app W (x ⊗ₜ[A] y)) := by
    have hn := (PresheafOfModules.sheafificationAdjunction
      (scalars T ell n)).unit.naturality (q.inv ≫ E.map μ)
    exact (congrArg (fun k ↦ k.app W (x ⊗ₜ[A] y)) hn).symm
  change (b.inv.app (E.obj F.obj, E.obj G.obj)).val.app W (a.inv.val.app W _) = _
  have hi := (congrArg (a.inv.val.app W) ha.symm).trans
    (component_hom_inv a W
      (((PresheafOfModules.sheafificationAdjunction (scalars T ell n)).unit.app
        (E.obj F.obj ⊗ E.obj G.obj)).app W (x ⊗ₜ[A] y)))
  have hbb := hb (E.obj F.obj) (E.obj G.obj) W x y
  exact (congrArg ((b.inv.app (E.obj F.obj, E.obj G.obj)).val.app W) hi).trans hbb

private theorem quotient_tensor
    (T : Scheme.{u}) {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (M N : pbcModules T R) :
    ∃ e : (pbcExtend φ).obj M ⊗ (pbcExtend φ).obj N ≅
        (pbcExtend φ).obj (M ⊗ N),
      ∀ (W : T.ProEtᵒᵖ) (s t : S.obj.obj W) (x : M.val.obj W) (y : N.val.obj W),
        e.hom.val.app W
          (SheafOfModules.scalarExtensionConstraintPureTensor S
            ((pbcExtend φ).obj M) ((pbcExtend φ).obj N) W
            (pbcTensorSection φ M W s x) (pbcTensorSection φ N W t y)) =
        pbcTensorSection φ (M ⊗ N) W (s * t)
          (SheafOfModules.scalarExtensionConstraintPureTensor R M N W x y) := by
  let c := (SheafOfModules.scalarExtension_constraint_coherence R S φ).some
  let a (H : pbcModules T R) : (pbcExtend φ).obj H ≅
      SheafOfModules.changeOfRings.{u, u + 1, u + 1} φ H :=
    eqToIso ((pbcExtensionExistence φ).choose_spec.choose H)
  refine ⟨tensorIso (a M) (a N) ≪≫ (c.tensorIso M N).symm ≪≫ (a (M ⊗ N)).symm, ?_⟩
  intro W s t x y
  change (a (M ⊗ N)).inv.val.app W
    ((c.tensorIso M N).inv.val.app W
      (((a M).hom ⊗ₘ (a N).hom).val.app W _)) = _
  erw [SheafOfModules.pure_natural S (a M).hom (a N).hom W
    (pbcTensorSection φ M W s x) (pbcTensorSection φ N W t y)]
  erw [extension_pure T φ M W s x, extension_pure T φ N W t y,
    c.tensor_inv M N W x y s t]
  apply component_injective (a (M ⊗ N)) W
  change (a (M ⊗ N)).hom.val.app W ((a (M ⊗ N)).inv.val.app W _) = _
  rw [component_inv_hom]
  exact (extension_pure T φ (M ⊗ N) W (s * t) _).symm

private theorem quotient_unit
    (T : Scheme.{u}) {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (φ : R ⟶ S) :
    ∃ e : SheafOfModules.unit ((adicLisseForget T).obj S) ≅
        (pbcExtend φ).obj (SheafOfModules.unit ((adicLisseForget T).obj R)),
      ∀ (W : T.ProEtᵒᵖ) (s : S.obj.obj W),
        e.hom.val.app W s = pbcTensorSection φ _ W s (1 : R.obj.obj W) := by
  let c := (SheafOfModules.scalarExtension_constraint_coherence R S φ).some
  let a : (pbcExtend φ).obj (SheafOfModules.unit ((adicLisseForget T).obj R)) ≅
      SheafOfModules.changeOfRings.{u, u + 1, u + 1} φ
        (SheafOfModules.unit ((adicLisseForget T).obj R)) :=
    eqToIso ((pbcExtensionExistence φ).choose_spec.choose _)
  refine ⟨c.unitIso.symm ≪≫ a.symm, ?_⟩
  intro W s
  change a.inv.val.app W (c.unitIso.inv.val.app W s) = _
  rw [c.unit_inv]
  apply component_injective a W
  rw [component_inv_hom]
  exact (extension_pure T φ (SheafOfModules.unit ((adicLisseForget T).obj R))
    W s (1 : R.obj.obj W)).symm

private theorem realization_map_unit
    (T : Scheme.{u}) (ell : ℕ) [Fact ell.Prime] (n : ℕ)
    {F G : Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (coefficient.{u} ell (n + 1)))}
    (f : F ⟶ G) (W : T.ProEtᵒᵖ) (x : F.obj.obj W) :
    ((realization T ell n).map f).val.app W
        ((toSheafify (ProEt.topology T)
          (F.obj ⋙ forget₂ _ AddCommGrpCat.{u + 1})).app W x) =
      (toSheafify (ProEt.topology T)
        (G.obj ⋙ forget₂ _ AddCommGrpCat.{u + 1})).app W (f.hom.app W x) := by
  exact (congrArg (fun k ↦ k.app W x)
    ((PresheafOfModules.sheafificationAdjunction (scalars T ell n)).unit.naturality
      ((ProEtale.finiteCoefficientModulePresheaf T.ProEt
        (coefficient.{u} ell (n + 1))).map f.hom))).symm

private theorem realization_constant
    (T : Scheme.{u}) (ell : ℕ) [Fact ell.Prime] (n : ℕ) :
    ∃ e : (realization T ell n).obj
        ((constantSheaf (ProEt.topology T)
          (ModuleCat.{u + 1} (coefficient.{u} ell (n + 1)))).obj
            (ModuleCat.of (coefficient.{u} ell (n + 1)) (coefficient.{u} ell (n + 1)))) ≅
        SheafOfModules.unit ((adicLisseForget T).obj
          ((pbcAdicRings T (datum.{u} ell)).obj (op n))),
      ∀ (W : T.ProEtᵒᵖ) (a : coefficient.{u} ell (n + 1)),
        e.hom.val.app W
          ((toSheafify (ProEt.topology T)
            (((constantSheaf (ProEt.topology T)
              (ModuleCat.{u + 1} (coefficient.{u} ell (n + 1)))).obj
                (ModuleCat.of (coefficient.{u} ell (n + 1))
                  (coefficient.{u} ell (n + 1)))).obj ⋙ forget₂ _ AddCommGrpCat.{u + 1})).app W
            ((toSheafify (ProEt.topology T) ((Functor.const T.ProEtᵒᵖ).obj
              (ModuleCat.of (coefficient.{u} ell (n + 1))
                (coefficient.{u} ell (n + 1))))).app W a)) =
        (scalars T ell n).app W a := by
  let J := ProEt.topology T
  let A := coefficient.{u} ell (n + 1)
  let R := (adicLisseForget T).obj ((pbcAdicRings T (datum.{u} ell)).obj (op n))
  let α := scalars T ell n
  let : J.PreservesSheafification (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1}) :=
    module_forget_preserves T A
  let E := ProEtale.finiteCoefficientModulePresheaf T.ProEt A
  let S := PresheafOfModules.sheafification α
  let P := (Functor.const T.ProEtᵒᵖ).obj (ModuleCat.of A A)
  let M := SheafOfModules.unit R
  let q : E.obj P ⟶ (PresheafOfModules.restrictScalars α).obj M.val :=
    { app := fun W ↦ ModuleCat.ofHom
        (X := (E.obj P).obj W)
        (Y := ((PresheafOfModules.restrictScalars α).obj M.val).obj W) {
        toFun := α.app W
        map_add' := map_add _
        map_smul' := fun a b ↦ (α.app W).hom.map_mul a b }
      naturality := by
        intro U V f
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro a
        exact ConcreteCategory.congr_hom (α.naturality f) a }
  have hs : IsIso (S.map q) := by
    have : IsIso ((SheafOfModules.toSheaf R).map (S.map q)) := by
      change IsIso ((presheafToSheaf J AddCommGrpCat.{u + 1}).map
        (Functor.whiskerRight α (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})))
      rw [← J.W_iff, J.W_iff_isLocallyBijective]
      constructor
      · apply (Presheaf.isLocallyInjective_forget_iff J _).mp
        change Presheaf.IsLocallyInjective J
          (Functor.whiskerRight α (CategoryTheory.forget RingCat.{u + 1}))
        infer_instance
      · apply (Presheaf.isLocallySurjective_iff_whisker_forget J _).mpr
        change Presheaf.IsLocallySurjective J
          (Functor.whiskerRight α (CategoryTheory.forget RingCat.{u + 1}))
        infer_instance
    exact isIso_of_reflects_iso _ (SheafOfModules.toSheaf R)
  let b : S.obj (E.obj P) ≅ M :=
    asIso (S.map q) ≪≫ asIso ((PresheafOfModules.sheafificationAdjunction α).counit.app M)
  let v := E.map (toSheafify J P)
  have hv : IsIso (S.map v) := by
    have : IsIso ((SheafOfModules.toSheaf R).map (S.map v)) := by
      change IsIso ((presheafToSheaf J AddCommGrpCat.{u + 1}).map
        (Functor.whiskerRight (toSheafify J P)
          (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})))
      rw [← J.W_iff]
      exact J.W_of_preservesSheafification _ _ (J.W_toSheafify P)
    exact isIso_of_reflects_iso _ (SheafOfModules.toSheaf R)
  refine ⟨(asIso (S.map v)).symm ≪≫ b, ?_⟩
  intro W a
  have hvv := congrArg (fun k ↦ k.app W a)
    ((PresheafOfModules.sheafificationAdjunction α).unit.naturality v)
  change (toSheafify J ((sheafify J P) ⋙
      forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})).app W
      ((toSheafify J P).app W a) =
    (S.map v).val.app W
      (((PresheafOfModules.sheafificationAdjunction α).unit.app (E.obj P)).app W a) at hvv
  change b.hom.val.app W ((inv (S.map v)).val.app W
    ((toSheafify J ((sheafify J P) ⋙
      forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})).app W
        ((toSheafify J P).app W a))) = α.app W a
  rw [hvv]
  have hi := component_hom_inv (asIso (S.map v)) W
    (((PresheafOfModules.sheafificationAdjunction α).unit.app (E.obj P)).app W a)
  have hc : b.hom.val.app W
      (((PresheafOfModules.sheafificationAdjunction α).unit.app (E.obj P)).app W a) =
      α.app W a :=
    congrArg (fun f ↦ f.app W a)
      (((PresheafOfModules.sheafificationAdjunction α).homEquiv (E.obj P) M).apply_symm_apply q)
  exact (congrArg (b.hom.val.app W) hi).trans hc

private theorem canonical_zero
    (T : Scheme.{u}) [IsNoetherian T] (ell : ℕ) [Fact ell.Prime] (n : ℕ) :
    ∃ e : (realization T ell n).obj (finiteSheaf T ell n 0) ≅ quotientLine T ell n 0,
      GeneratorCompatible T ell n 0 e.hom := by
  obtain ⟨a, ha⟩ := realization_constant T ell n
  obtain ⟨b, hb⟩ := quotient_unit T (pbcAdicProjection T (datum.{u} ell) n)
  let c := Functor.Monoidal.εIso
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (coefficient.{u} ell (n + 1))) T)
  refine ⟨(realization T ell n).mapIso c.symm ≪≫ a ≪≫ b, ?_⟩
  intro U W v q z x hx
  simp only [one_smul, id_eq]
  change b.hom.val.app W (a.hom.val.app W
    (((realization T ell n).map c.inv).val.app W _)) = _
  erw [realization_map_unit]
  erw [(comparison_pure_sections (coefficient.{u} ell (n + 1)) T).2 U W v q]
  erw [ha W q, hb]
  rfl

set_option maxHeartbeats 2000000 in
-- Transporting the finite-root comparison through both realizations is definitionally expensive.
private theorem canonical_root
    (T : Scheme.{u}) [IsNoetherian T] (ell : ℕ) [Fact ell.Prime]
    (hT : IsUnit (ell : Γ(T, ⊤))) (n : ℕ)
    [∀ x : T, Invertible (ell : T.residueField x)] :
    ∃ e : (realization T ell n).obj (finiteSheaf T ell n 1) ≅
        (pbcExtend (pbcAdicProjection T (datum.{u} ell) n)).obj (integralRoot T ell),
      ∀ (U : T.Etaleᵒᵖ) (W : T.ProEtᵒᵖ)
        (v : W.unop ⟶ (toProEt T).obj U.unop) (a : coefficient.{u} ell (n + 1))
        (z : (T.rootsOfUnitySheaf (ell ^ (n + 1))).obj.obj U)
        (x : (purTwistZlOne T ell).obj.obj W),
        finiteTateLimitRootValue ell T n W x =
          Units.map v.left.appTop.hom.toMonoidHom
            (finiteTateEtaleRootValue T (ell ^ (n + 1)) U z) →
        e.hom.val.app W
          ((toSheafify (ProEt.topology T)
            ((finiteSheaf T ell n 1).obj ⋙ forget₂ _ AddCommGrpCat.{u + 1})).app W
              ((finiteSheaf T ell n 1).obj.map v.op
                (((ProEtale.comparisonAdjunction
                  (ModuleCat.{u + 1} (coefficient.{u} ell (n + 1))) T).unit.app
                    (finiteEtaleTateLine T (ell ^ (n + 1)) (coefficient.{u} ell (n + 1))
                      (CharP.cast_eq_zero _ _))).hom.app U
                        (finiteEtaleTateOneGenerator _ _ T (CharP.cast_eq_zero _ _)
                          U a z)))) =
          pbcTensorSection (pbcAdicProjection T (datum.{u} ell) n)
            (integralRoot T ell) W ((scalars T ell n).app W a) x := by
  let m := ell ^ (n + 1)
  have hm : 0 < m := pow_pos (Fact.out : ell.Prime).pos _
  have hTm : IsUnit (m : Γ(T, ⊤)) := by
    simpa only [m, Nat.cast_pow] using hT.pow (n + 1)
  obtain ⟨sigma, d, hs, hu, ht, hd⟩ := finiteRootSiteComparison (coefficient.{u} ell (n + 1))
  let σ := sigma m hm (CharP.cast_eq_zero _ _) T hTm
  have := finiteRootToFixed_isIso T ell n
  let N := (pbcRestrict (coefficientIso T ell n).hom).obj (purTwistRootsModule T ell n)
  let b := (realization T ell n).mapIso σ ≪≫
    (realization T ell n).mapIso (asIso (finiteRootToFixed T ell n)) ≪≫
      realizationCounit T ell n N
  obtain ⟨r, hr⟩ := root_quotient_iso T ell n
  refine ⟨b ≪≫ r.symm, ?_⟩
  intro U W v a z x hx
  apply component_injective r W
  change r.hom.val.app W (r.inv.val.app W (b.hom.val.app W _)) = _
  rw [component_inv_hom]
  change b.hom.val.app W _ = _
  change (realizationCounit T ell n N).hom.val.app W
    (((realization T ell n).map (finiteRootToFixed T ell n)).val.app W
      (((realization T ell n).map σ.hom).val.app W _)) = _
  erw [realization_map_unit T ell n σ.hom W,
    realization_map_unit T ell n (finiteRootToFixed T ell n) W]
  erw [ht m hm (CharP.cast_eq_zero _ _) T hTm U W v a z,
    finiteRootToFixed_generator T ell n W a,
    realizationCounit_unit T ell n N W,
    hr W ((scalars T ell n).app W a) x]
  congr 1
  have : Mono (proEtaleRootsOfUnityInclusion T m) := by
    dsimp [proEtaleRootsOfUnityInclusion]
    infer_instance
  have : Mono (proEtaleRootsOfUnityInclusion T m).hom :=
    (sheafToPresheaf _ _).map_mono _
  apply (AddCommGrpCat.mono_iff_injective
    ((proEtaleRootsOfUnityInclusion T m).hom.app W)).mp inferInstance
  apply ULift.ext
  apply Additive.toMul.injective
  exact (hu m hm T hTm U W v z).trans hx.symm

private theorem integral_left_unitor
    (T : Scheme.{u}) (ell : ℕ) [Fact ell.Prime] (W : T.ProEtᵒᵖ)
    (x : (purTwistZlOne T ell).obj.obj W) :
    (λ_ (integralRoot T ell)).hom.val.app W
      (integralGenerator T ell W 1 (fun _ ↦ x)) = x := by
  change (λ_ (integralRoot T ell)).hom.val.app W
    (integralPure T ell _ _ W
      (1 : (pbcAdicCompletion T (datum.{u} ell)).obj.obj W) x) = x
  exact (CategoryTheory.RingedDerivedNative.pureTensor_leftUnitor.{u + 1, u, u + 1}
    (ProEt.topology T) (pbcAdicCompletion T (datum.{u} ell))
      (integralRoot T ell) W
      (1 : (pbcAdicCompletion T (datum.{u} ell)).obj.obj W) x).trans (one_smul _ _)

private theorem canonical_one
    (T : Scheme.{u}) [IsNoetherian T] (ell : ℕ) [Fact ell.Prime]
    (hT : IsUnit (ell : Γ(T, ⊤))) (n : ℕ)
    [∀ x : T, Invertible (ell : T.residueField x)] :
    ∃ e : (realization T ell n).obj (finiteSheaf T ell n 1) ≅ quotientLine T ell n 1,
      GeneratorCompatible T ell n 1 e.hom := by
  obtain ⟨a, ha⟩ := canonical_root T ell hT n
  let φ := pbcAdicProjection T (datum.{u} ell) n
  let b : (pbcExtend φ).obj (integralLine T ell 1) ≅
      (pbcExtend φ).obj (integralRoot T ell) :=
    (pbcExtend φ).mapIso (λ_ (integralRoot T ell))
  refine ⟨a ≪≫ b.symm, ?_⟩
  intro U W v q z x hx
  simp only [one_smul, id_eq]
  apply component_injective b W
  change b.hom.val.app W (b.inv.val.app W (a.hom.val.app W _)) = _
  rw [component_inv_hom]
  change a.hom.val.app W _ = _
  erw [ha U W v q (z 0) (x 0) (hx 0)]
  erw [WeilConjectures.PurStrictScalar.tensorSection_map]
  congr 1
  exact (integral_left_unitor T ell W (x 0)).symm

private theorem canonical_step
    (T : Scheme.{u}) [IsNoetherian T] (ell : ℕ) [Fact ell.Prime]
    (hT : IsUnit (ell : Γ(T, ⊤))) (n d : ℕ)
    [∀ x : T, Invertible (ell : T.residueField x)]
    (e : (realization T ell n).obj (finiteSheaf T ell n (d + 1)) ≅
      quotientLine T ell n (d + 1))
    (he : GeneratorCompatible T ell n (d + 1) e.hom) :
    ∃ e : (realization T ell n).obj (finiteSheaf T ell n (d + 2)) ≅
        quotientLine T ell n (d + 2),
      GeneratorCompatible T ell n (d + 2) e.hom := by
  obtain ⟨g, hg⟩ := canonical_root T ell hT n
  let A := coefficient.{u} ell (n + 1)
  let F := finiteEtaleTateTwist T (ell ^ (n + 1)) A (CharP.cast_eq_zero _ _) (d + 1)
  let G := finiteEtaleTateLine T (ell ^ (n + 1)) A (CharP.cast_eq_zero _ _)
  let c := (Functor.Monoidal.μIso (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T)
    F G).symm
  obtain ⟨b, hb⟩ := realization_tensor T ell n
    (finiteSheaf T ell n (d + 1)) (finiteSheaf T ell n 1)
  obtain ⟨q, hq⟩ := quotient_tensor T (pbcAdicProjection T (datum.{u} ell) n)
    (integralLine T ell (d + 1)) (integralRoot T ell)
  refine ⟨(realization T ell n).mapIso c ≪≫ b ≪≫ tensorIso e g ≪≫ q, ?_⟩
  intro U W v a z x hx
  simp only [one_smul, id_eq]
  change q.hom.val.app W ((e.hom ⊗ₘ g.hom).val.app W
    (b.hom.val.app W (((realization T ell n).map c.hom).val.app W _))) = _
  erw [realization_map_unit]
  erw [(comparison_pure_sections A T).1 F G U W v
    (finiteTateEtalePowerGenerator T A (ell ^ (n + 1)) (CharP.cast_eq_zero _ _) U a
      (d + 1) (fun i ↦ z i.castSucc))
    (finiteEtaleTateOneGenerator A (ell ^ (n + 1)) T (CharP.cast_eq_zero _ _)
      U 1 (z (Fin.last (d + 1))))]
  erw [hb W]
  erw [SheafOfModules.pure_natural
    ((pbcAdicRings T (datum.{u} ell)).obj (op n)) e.hom g.hom W]
  have he' := he U W v a (fun i ↦ z i.castSucc) (fun i ↦ x i.castSucc)
    (fun i ↦ hx i.castSucc)
  simp only [one_smul, id_eq] at he'
  erw [he', hg U W v 1 (z (Fin.last (d + 1))) (x (Fin.last (d + 1)))
    (hx (Fin.last (d + 1))), hq]
  rw [map_one, mul_one]
  rfl

private theorem canonical_iso
    (T : Scheme.{u}) [IsNoetherian T] (ell : ℕ) [Fact ell.Prime]
    (hT : IsUnit (ell : Γ(T, ⊤))) (n d : ℕ)
    [∀ x : T, Invertible (ell : T.residueField x)] :
    ∃ e : (realization T ell n).obj (finiteSheaf T ell n d) ≅ quotientLine T ell n d,
      GeneratorCompatible T ell n d e.hom := by
  induction d with
  | zero => exact canonical_zero T ell n
  | succ d ih =>
    cases d with
    | zero => exact canonical_one T ell hT n
    | succ d =>
      obtain ⟨e, he⟩ := ih
      exact canonical_step T ell hT n d e he

/-- The compatible root formula gives an isomorphism on every pro-etale section.

Source: current blueprint, sec-smooth-purity/sk-thm-purity-transport, Step 2,
local rank-one argument in the ordinary quotient comparison.
(blueprint: lem-pur-tate-tensor-generator-local-isiso)

Proof: choose the common pro-etale covering with compatible primitive roots.
On each member, scalar coordinates identify the inverse-limit root line with the
coefficient unit, and reduction identifies its ordered tensor with the finite
root tensor. The displayed GeneratorCompatible formula then says that the
section map is the identity between the two rank-one coordinate modules. The
local inverse is multiplication by the inverse coordinate, and compatibility
with restriction makes it the inverse on every pro-etale section. Degree zero
uses the coefficient unit; an empty scheme has the unique section map.
-/
theorem tateTensorQuotient_generator_local_isIso
    (T : Scheme.{u}) [IsNoetherian T] (ell : ℕ) [Fact ell.Prime]
    (hT : IsUnit (ell : Γ(T, ⊤))) (n d : ℕ)
    (f : (realization T ell n).obj (finiteSheaf T ell n d) ⟶ quotientLine T ell n d)
    (hf : GeneratorCompatible T ell n d f) :
    ∀ W, IsIso (f.val.app W) := by
  let (x : T) : Invertible (ell : T.residueField x) :=
    (show IsUnit (ell : T.residueField x) by
      simpa only [map_natCast] using hT.map (T.Γevaluation x).hom).invertible
  obtain ⟨e, he⟩ := canonical_iso T ell hT n d
  have h := compatible_unique T ell hT n d f e.hom hf he
  subst f
  intro W
  exact component_isIso e W

end AlgebraicGeometry.Scheme.PurityIntegralTower
