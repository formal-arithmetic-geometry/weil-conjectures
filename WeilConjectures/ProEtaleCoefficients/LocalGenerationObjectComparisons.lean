/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ProEtaleCoefficients.LocalGenerationSectionFunctor

/-! # Object comparisons for local generation transport

This records the finite-free and constant-module comparison isomorphisms after the
localized internal-to-sectionwise functor has been constructed.
(blueprint: lem-sfb-local-generation-object-comparisons)
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option maxRecDepth 2048

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  AlgebraicGeometry Opposite
open scoped TensorProduct
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] sectionRingRestrictionIso sectionScalarIso
  localSectionRingIso proEtaleObjectCompositeRestrictionIso

/-- Scalar evaluation with the bundled module specified explicitly.
(blueprint: lem-sfb-local-generation-object-comparisons) -/
abbrev localGenerationSMul {A : Type (u + 1)} [Ring A]
    (M : ModuleCat.{u + 1} A) (r : A) (x : M) : M := r • x

/-- The canonical pullback comparison is semilinear on the reconstructed section modules.
This is the module action equation of the monoidal pullback comparison, evaluated on
a pure tensor after passing to presheaves.
(blueprint: lem-sfb-local-generation-object-comparisons) -/
theorem localGenerationPullbackSectionSemilinear
    {Y Z W : Scheme.{u}} (g : Z ⟶ Y) (f : W ⟶ Z)
    [WeaklyEtale f] [WeaklyEtale (f ≫ g)]
    (B : Type (u + 1)) [CommRing B]
    (M : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology Y) AddCommGrpCat.{u + 1})
      (Sheaf.constRingSheaf (Scheme.ProEt.topology Y) B))
    (U : W.ProEtᵒᵖ)
    (r : (localPullbackRing g f B).obj.obj U)
    (x : ((upperStar AddCommGrpCat.{u + 1} f).obj
      ((upperStar AddCommGrpCat.{u + 1} g).obj M.X)).obj.obj U) :
    let L := (InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
      (Scheme.ProEt.topology W) (localPullbackRing g f B)).functor.obj
        (((upperStar AddCommGrpCat.{u + 1} f).mapMod
          ((upperStar AddCommGrpCat.{u + 1} g).obj
            (Sheaf.constRingSheaf (Scheme.ProEt.topology Y) B))).obj
              (((upperStar AddCommGrpCat.{u + 1} g).mapMod _).obj M))
    let L₀ := (InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
      (Scheme.ProEt.topology Y) (Sheaf.constRingSheaf (Scheme.ProEt.topology Y) B)).functor.obj M
    let θ := proEtaleObjectCompositeRestrictionIso g (Scheme.ProEt.mk f)
      (show WeaklyEtale ((Scheme.ProEt.mk f).hom ≫ g) from ‹WeaklyEtale (f ≫ g)›)
    ((θ.hom.app M.X).hom.app U) (localGenerationSMul (L.val.obj U) r x) =
      localGenerationSMul (L₀.val.obj ((localizationSite g f).op.obj U))
        ((localPullbackRingIso g f B).hom.hom.app U r) ((θ.hom.app M.X).hom.app U x) := by
  have := localizationSite_continuous g f
  let R := Sheaf.constRingSheaf (Scheme.ProEt.topology Y) B
  let F := upperStar AddCommGrpCat.{u + 1} g
  let G := upperStar AddCommGrpCat.{u + 1} f
  let T := sheafToPresheaf (Scheme.ProEt.topology W) AddCommGrpCat.{u + 1}
  let θ := proEtaleObjectCompositeRestrictionIso g (Scheme.ProEt.mk f)
    (show WeaklyEtale ((Scheme.ProEt.mk f).hom ≫ g) from ‹WeaklyEtale (f ≫ g)›)
  have : NatTrans.IsMonoidal θ.hom :=
    (proEtaleObjectPullbackCompMonoidal g (Scheme.ProEt.mk f)
      (show WeaklyEtale ((Scheme.ProEt.mk f).hom ≫ g) from ‹WeaklyEtale (f ≫ g)›)).2
  let α := sectionRestrictionPresheafIso (Scheme.ProEt.topology W)
    (Scheme.ProEt.topology Y) (localizationSite g f)
  let τ := (Functor.associator F G T).symm ≪≫ Functor.isoWhiskerRight θ T ≪≫ α.symm
  have : NatTrans.IsMonoidal α.hom :=
    sectionRestrictionPresheafIso_monoidal _ _ _
  have : NatTrans.IsMonoidal τ.hom := by
    dsimp only [τ, Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom]
    infer_instance
  let c := Functor.mapModCompIso F (G ⋙ T) τ.hom R
  have h := ConcreteCategory.congr_hom (congr_app (Mod.act_hom (c.hom.app M)) U)
    (r ⊗ₜ[ℤ] x)
  exact h

/-- The fixed comparison sends the internal regular module to the sectionwise unit.
The two maps are the inverse coefficient-ring isomorphisms. Their linearity follows
from multiplication preservation and their inverse identities.
(blueprint: lem-sfb-local-generation-object-comparisons) -/
def localGenerationRegularComparison
    {Y Z W : Scheme.{u}} (g : Z ⟶ Y) (f : W ⟶ Z)
    [WeaklyEtale f] [WeaklyEtale (f ≫ g)]
    (B : Type (u + 1)) [CommRing B] :
    (localGenerationSectionFunctor g f B).obj (Mod.regular (localPullbackRing g f B)) ≅
      SheafOfModules.unit (((constantSheaf (Scheme.ProEt.topology Y) RingCat.{u + 1}).obj
        (RingCat.of B)).over (Scheme.ProEt.mk (f ≫ g))) := by
  let S := ((constantSheaf (Scheme.ProEt.topology Y) RingCat.{u + 1}).obj
    (RingCat.of B)).over (Scheme.ProEt.mk (f ≫ g))
  let T := ((Scheme.ProEt.sliceTo Y (Scheme.ProEt.mk (f ≫ g))).sheafPushforwardContinuous
    RingCat.{u + 1} ((Scheme.ProEt.topology Y).over (Scheme.ProEt.mk (f ≫ g)))
      (Scheme.ProEt.topology W)).obj
    ((sheafCompose (Scheme.ProEt.topology W) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
        (Scheme.ProEt.topology W) (localPullbackRing g f B)))
  let φ : S ≅ T := localSectionRingIso g f B
  let h : (localGenerationSectionFunctor g f B).obj
      (Mod.regular (localPullbackRing g f B)) ⟶ SheafOfModules.unit _ :=
    ⟨PresheafOfModules.homMk
      (Functor.whiskerRight φ.inv.hom (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1}))
      (by
        intro U r x
        change φ.inv.hom.app U
          (φ.hom.hom.app U r * (show T.obj.obj U from x)) = r * φ.inv.hom.app U x
        rw [(φ.inv.hom.app U).hom.map_mul]
        have hi := ConcreteCategory.congr_hom (C := RingCat.{u + 1})
          (congr_app (congrArg (fun t ↦ t.hom) φ.hom_inv_id) U) r
        change φ.inv.hom.app U (φ.hom.hom.app U r) = r at hi
        rw [hi])⟩
  let k : SheafOfModules.unit _ ⟶ (localGenerationSectionFunctor g f B).obj
      (Mod.regular (localPullbackRing g f B)) :=
    ⟨PresheafOfModules.homMk
      (Functor.whiskerRight φ.hom.hom (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1}))
      (by
        intro U r x
        change φ.hom.hom.app U (r * (show S.obj.obj U from x)) =
          φ.hom.hom.app U r * φ.hom.hom.app U x
        exact (φ.hom.hom.app U).hom.map_mul _ _)⟩
  refine ⟨h, k, ?_, ?_⟩
  · apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact ConcreteCategory.congr_hom (C := RingCat.{u + 1})
      (congr_app (congrArg (fun t ↦ t.hom) φ.inv_hom_id) U) x
  · apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact ConcreteCategory.congr_hom (C := RingCat.{u + 1})
      (congr_app (congrArg (fun t ↦ t.hom) φ.hom_inv_id) U) x

/-- Finite free modules compare by preservation of coproducts and the regular-module
comparison, with the finite index set transported through `ULift`.
(blueprint: lem-sfb-local-generation-object-comparisons) -/
def localGenerationFiniteFreeComparison
    {Y Z W : Scheme.{u}} (g : Z ⟶ Y) (f : W ⟶ Z)
    [WeaklyEtale f] [WeaklyEtale (f ≫ g)]
    (B : Type (u + 1)) [CommRing B] (n : ℕ) :
    (localGenerationSectionFunctor g f B).obj (Mod.finiteFree (localPullbackRing g f B) n) ≅
      SheafOfModules.free (R :=
        ((constantSheaf (Scheme.ProEt.topology Y) RingCat.{u + 1}).obj
          (RingCat.of B)).over (Scheme.ProEt.mk (f ≫ g))) (ULift.{u + 1} (Fin n)) := by
  let F := localGenerationSectionFunctor g f B
  have := localGenerationSectionFunctor_isEquivalence g f B
  exact F.mapIso (biproduct.isoCoproduct _) ≪≫ PreservesCoproduct.iso F _ ≪≫
    Sigma.whiskerEquiv Equiv.ulift.symm (fun _ ↦ (localGenerationRegularComparison g f B).symm)

set_option maxHeartbeats 2000000 in
-- Checking scalar compatibility traverses several reconstructed module structures.
/-- The fixed comparison identifies the pulled-back constant internal module with
its sectionwise constant module restricted to the slice. The comparison of successive
pullbacks with restriction and the normalized constant-action comparison give the
underlying additive isomorphism; their scalar compatibility gives its linearity.
(blueprint: lem-sfb-local-generation-object-comparisons) -/
theorem localGenerationConstantModuleComparison
    {Y Z W : Scheme.{u}} (g : Z ⟶ Y) (f : W ⟶ Z)
    [WeaklyEtale f] [WeaklyEtale (f ≫ g)]
    (B : Type (u + 1)) [CommRing B]
    (P : Type (u + 1)) [AddCommGroup P] [Module B P] :
    Nonempty ((localGenerationSectionFunctor g f B).obj
      (((upperStar AddCommGrpCat.{u + 1} f).mapMod
        ((upperStar AddCommGrpCat.{u + 1} g).obj
          (Sheaf.constRingSheaf (Scheme.ProEt.topology Y) B))).obj
        (((upperStar AddCommGrpCat.{u + 1} g).mapMod
          (Sheaf.constRingSheaf (Scheme.ProEt.topology Y) B)).obj
            (localGenerationConstantModule Y B P))) ≅
      localGenerationRestrictedModule Y (Scheme.ProEt.mk (f ≫ g)) B P) := by
  let V := Scheme.ProEt.mk (f ≫ g)
  let R := Sheaf.constRingSheaf (Scheme.ProEt.topology Y) B
  let M := localGenerationConstantModule Y B P
  let E := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
    (Scheme.ProEt.topology Y) R
  let N := (siteConstantModuleFunctorGeneral (Scheme.ProEt.topology Y) B).obj
    (ModuleCat.of B P)
  let ψ := (sheafCompose (Scheme.ProEt.topology Y)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso (localConstantRingIso Y B) ≪≫
      (constantModuleHomRingIso (Scheme.ProEt.topology Y) B).symm
  obtain ⟨eP, heP, _⟩ :=
    (sfbInternalConstantModule_sectionwise (Scheme.ProEt.topology Y) B).choose_spec.2.2
      (ModuleCat.of B P)
  have hact (T : Y.ProEtᵒᵖ)
      (s : (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
        (Scheme.ProEt.topology Y) R).obj.obj T) (y : (E.functor.obj M).val.obj T) :
      localGenerationSMul ((E.functor.obj M).val.obj T) s y =
        localGenerationSMul (N.val.obj T) (ψ.hom.hom.app T s) y := by
    have h := (eP.hom.val.app T).hom.map_smul s y
    change eP.hom.val.app T (localGenerationSMul ((E.functor.obj M).val.obj T) s y) =
      localGenerationSMul (N.val.obj T) (ψ.hom.hom.app T s) (eP.hom.val.app T y) at h
    rw [heP T _, heP T _] at h
    exact h
  let θ := proEtaleObjectCompositeRestrictionIso g (Scheme.ProEt.mk f)
    (show WeaklyEtale ((Scheme.ProEt.mk f).hom ≫ g) from ‹WeaklyEtale (f ≫ g)›)
  let A := ((localGenerationSectionFunctor g f B).obj
      (((upperStar AddCommGrpCat.{u + 1} f).mapMod
        ((upperStar AddCommGrpCat.{u + 1} g).obj R)).obj
          (((upperStar AddCommGrpCat.{u + 1} g).mapMod R).obj M)))
  let Q := localGenerationRestrictedModule Y V B P
  let L := (InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
    (Scheme.ProEt.topology W) (localPullbackRing g f B)).functor.obj
      (((upperStar AddCommGrpCat.{u + 1} f).mapMod
        ((upperStar AddCommGrpCat.{u + 1} g).obj R)).obj
          (((upperStar AddCommGrpCat.{u + 1} g).mapMod R).obj M))
  let α : A.val.presheaf ≅ Q.val.presheaf :=
    Functor.isoWhiskerLeft (Scheme.ProEt.sliceTo Y V).op
      ((sheafToPresheaf (Scheme.ProEt.topology W) AddCommGrpCat.{u + 1}).mapIso
        (θ.app M.X)) ≪≫
      Functor.isoWhiskerRight (Scheme.ProEt.sliceEquiv Y V).op.unitIso.symm
        ((Over.forget V).op ⋙ M.X.obj)
  have hlinear (U : (Over V)ᵒᵖ)
      (r : (((constantSheaf (Scheme.ProEt.topology Y) RingCat.{u + 1}).obj
        (RingCat.of B)).over V).obj.obj U) (x : A.val.obj U) :
      α.hom.app U (localGenerationSMul (A.val.obj U) r x) =
        localGenerationSMul (Q.val.obj U) r (α.hom.app U x) := by
    let T := (Scheme.ProEt.sliceTo Y V).op.obj U
    let U₀ := (Over.forget V).op.obj U
    let k := (Over.forget V).op.map ((Scheme.ProEt.sliceEquiv Y V).op.unitIso.inv.app U)
    let s := (localSectionRingIso g f B).hom.hom.app U r
    have hs := localGenerationPullbackSectionSemilinear g f B M T s x
    have hm := (E.functor.obj M).val.map_smul k
      ((localPullbackRingIso g f B).hom.hom.app T s) ((θ.hom.app M.X).hom.app T x)
    have ha := hact U₀
      ((InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
        (Scheme.ProEt.topology Y) R).obj.map k
          ((localPullbackRingIso g f B).hom.hom.app T s))
      ((E.functor.obj M).val.map k ((θ.hom.app M.X).hom.app T x))
    have hr := localGenerationCoefficientFormula g f B U r
    change (E.functor.obj M).val.map k
      (localGenerationSMul ((E.functor.obj M).val.obj ((localizationSite g f).op.obj T))
        ((localPullbackRingIso g f B).hom.hom.app T s)
        ((θ.hom.app M.X).hom.app T x)) =
      localGenerationSMul ((E.functor.obj M).val.obj U₀)
        ((InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
          (Scheme.ProEt.topology Y) R).obj.map k
            ((localPullbackRingIso g f B).hom.hom.app T s))
        ((E.functor.obj M).val.map k ((θ.hom.app M.X).hom.app T x)) at hm
    have hstep := congrArg (fun z ↦ M.X.obj.map k z) hs
    have hlast := congrArg (fun b ↦ localGenerationSMul (N.val.obj U₀) b
      ((E.functor.obj M).val.map k ((θ.hom.app M.X).hom.app T x))) hr
    change M.X.obj.map k ((θ.hom.app M.X).hom.app T (localGenerationSMul (L.val.obj T) s x)) =
      localGenerationSMul (Q.val.obj U) r (M.X.obj.map k ((θ.hom.app M.X).hom.app T x))
    exact hstep.trans (hm.trans (ha.trans hlast))
  change Nonempty (A ≅ Q)
  refine ⟨(SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (M₁ := A.val) (M₂ := Q.val) (fun U ↦
      ModuleCat.isoMk (M := A.val.obj U) (N := Q.val.obj U) (α.app U) (by
        intro r
        apply AddCommGrpCat.hom_ext
        apply AddMonoidHom.ext
        intro x
        exact (hlinear U r x).symm)) ?_)⟩
  intro U U' a
  ext x
  exact ConcreteCategory.congr_hom (α.hom.naturality a) x

end AlgebraicGeometry.ProEtale
