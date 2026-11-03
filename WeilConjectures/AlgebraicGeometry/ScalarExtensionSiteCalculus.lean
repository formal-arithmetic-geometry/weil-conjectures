/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import WeilConjectures.AlgebraicGeometry.Picard.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.SmoothPurity.SheafRingCoefficientOrdinaryAdjunction
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Algebra.Homology.ChangeOfRingsComplex
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import WeilConjectures.AlgebraicGeometry.Picard.KFlatResolutionIndependentCoefficients
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlat
import WeilConjectures.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Adjunction.Whiskering

/-! # Universal scalar extension for arbitrary ring sheaves

Source: current blueprint, scalar extension clauses (1) and (4); Stacks 06YY.
The ordinary objects are sheafified sectionwise tensors. The universal left-derived
pair fixes the functor and all comparisons; there is no completed coefficient datum.
(blueprint: lem-sp-scalar-extension-site-calculus).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe t u v w u' v' w' u₁ v₁ w₁ u₂ v₂ w₂ u₃ v₃ w₃
open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct ChangeOfRings
namespace AlgebraicGeometry.Scheme

/-- The underlying ordinary ring sheaf, with commutativity forgotten.
Source: Stacks 06YY; scalar-extension clauses (1), (4)
(blueprint: lem-sp-scalar-extension-site-calculus). -/
noncomputable abbrev siteScalarModuleRing (T : Scheme.{t})
    (R : Sheaf (ProEt.topology T) CommRingCat.{t + 1}) :=
  (sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R


/-- The ordinary category of modules over the given ring sheaf.
Source: Stacks 06YY; scalar-extension clauses (1), (4)
(blueprint: lem-sp-scalar-extension-site-calculus). -/
noncomputable abbrev siteScalarModules (T : Scheme.{t})
    (R : Sheaf (ProEt.topology T) CommRingCat.{t + 1}) :=
  ringedSiteModules.{t + 1} (siteScalarModuleRing T R)


/-- Use the standard derived category of ordinary sheaf modules.
Source: Stacks 06YY; scalar-extension clauses (1), (4)
(blueprint: lem-sp-scalar-extension-site-calculus). -/
noncomputable instance siteScalarModulesHasDerivedCategory (T : Scheme.{t})
    (R : Sheaf (ProEt.topology T) CommRingCat.{t + 1}) :
    HasDerivedCategory (siteScalarModules T R) := HasDerivedCategory.standard _


/-- The ordinary unbounded derived category of ring-sheaf modules.
Source: Stacks 06YY; scalar-extension clauses (1), (4)
(blueprint: lem-sp-scalar-extension-site-calculus). -/
noncomputable abbrev siteScalarDerivedCategory (T : Scheme.{t})
    (R : Sheaf (ProEt.topology T) CommRingCat.{t + 1}) :=
  DerivedCategory (siteScalarModules T R)


/-- The universal tensor and its left-derived pair for an arbitrary ring-sheaf map.
Source: Stacks 06YY (blueprint: lem-sp-scalar-extension-site-calculus).
The existence theorem specifies tensor objects and maps and the derived universal
property, so all selected data are unique up to the normalized isomorphisms. -/
def scalarSiteChangeData (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S) :=
  letI := HasDerivedCategory.standard (SheafOfModules.{t + 1}
    (SheafOfModules.derivedChangeRingIndependentCoefficients.{t + 1, t + 1, t}
      (ProEt.topology T) R))
  letI := HasDerivedCategory.standard (SheafOfModules.{t + 1}
    (SheafOfModules.derivedChangeRingIndependentCoefficients.{t + 1, t + 1, t}
      (ProEt.topology T) S))
  SheafOfModules.derivedChangeOfRingsIndependentCoefficients.{t + 2, t + 1, t + 1, t} φ


/-- Ordinary sheafified extension of scalars from the universal tensor pair.
Source: Stacks 06YY; scalar-extension clauses (1), (4)
(blueprint: lem-sp-scalar-extension-site-calculus). -/
def scalarSiteChange (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S) :=
  (scalarSiteChangeData T φ).choose


/-- The ordinary extension of scalars is additive.
Source: Stacks 06YY; scalar-extension clauses (1), (4)
(blueprint: lem-sp-scalar-extension-site-calculus). -/
instance scalarSiteChange_additive (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S) :
    (scalarSiteChange T φ).Additive :=
  (scalarSiteChangeData T φ).choose_spec.choose_spec.choose_spec.choose


/-- The universal left-derived extension of scalars.
Source: Stacks 06YY; scalar-extension clauses (1), (4)
(blueprint: lem-sp-scalar-extension-site-calculus). -/
def scalarSiteDerivedChange (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S) :=
  (scalarSiteChangeData T φ).choose_spec.choose_spec.choose_spec.choose_spec.2.2.choose


/-- The normalized sectionwise tensor map into ordinary scalar extension.
Source: Stacks 06YY; scalar-extension clauses (1), (4)
(blueprint: lem-sp-scalar-extension-site-calculus). -/
def scalarSiteChangeTensor (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S)
    (M : SheafOfModules.{t + 1}
      (SheafOfModules.derivedChangeRingIndependentCoefficients.{t + 1, t + 1, t}
        (ProEt.topology T) R)) (U : T.ProEtᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U) :
    ((scalarSiteChange T φ).obj M).val.obj U :=
  (eqToHom ((scalarSiteChangeData T φ).choose_spec.choose M).symm).val.app U
    ((toSheafify (ProEt.topology T)
      (SheafOfModules.changeOfRingsPresheaf φ M).presheaf).app U
        (s ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x))

/-- The ordinary restriction-of-scalars functor.
Source: Stacks 06YY; scalar-extension clauses (1), (4)
(blueprint: lem-sp-scalar-extension-site-calculus). -/
abbrev scalarSiteRestriction (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S) :=
  SheafOfModules.restrictScalars.{t + 1}
    ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map φ)

/-- The normalized tensor-restriction adjunction sends a map to its value on 1 tensor x.
Source: Stacks 06YY; scalar-extension clauses (1), (4)
(blueprint: lem-sp-scalar-extension-site-calculus). -/
theorem scalarSiteAdjunction (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S) :
    ∃ a : scalarSiteChange T φ ⊣ scalarSiteRestriction T φ,
      ∀ (M : SheafOfModules.{t + 1}
        ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R))
        (N : SheafOfModules.{t + 1}
        ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj S))
        (f : (scalarSiteChange T φ).obj M ⟶ N) (U : T.ProEtᵒᵖ) (x : M.val.obj U),
        (a.homEquiv M N f).val.app U x =
          f.val.app U (scalarSiteChangeTensor T φ M U 1 x) := by
  let h := (scalarSiteChangeData T φ).choose_spec.choose
  obtain ⟨_, _, ha⟩ := SheafOfModules.sheafRingCoefficientOrdinaryAdjunction φ
  obtain ⟨a, hnorm⟩ := ha (scalarSiteChange T φ) h
    (fun f ↦ (scalarSiteChangeData T φ).choose_spec.choose_spec.choose f)
  refine ⟨a, ?_⟩
  intro M N f U x
  have he := hnorm M N (eqToHom (h M).symm ≫ f) U x
  have hh : eqToHom (h M) ≫ (eqToHom (h M).symm ≫ f) = f := by simp
  rw [hh] at he
  exact he

/-- A normalized tensor adjunction determines scalar multiplication on pure tensors.
Source: Stacks 06YY; scalar-extension clauses (1), (4)
(blueprint: lem-sp-scalar-extension-site-calculus). -/
theorem normalizedTensor_smul (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S)
    (M : SheafOfModules.{t + 1}
      ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R))
    (N : SheafOfModules.{t + 1}
      ((sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj S))
    (h : N = SheafOfModules.changeOfRings φ M)
    (U : T.ProEtᵒᵖ) (s z : S.obj.obj U) (x : M.val.obj U) :
    (eqToHom h.symm).val.app U
      ((toSheafify (ProEt.topology T)
        (SheafOfModules.changeOfRingsPresheaf φ M).presheaf).app U
          ((s * z) ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x)) =
      s • (eqToHom h.symm).val.app U
        ((toSheafify (ProEt.topology T)
          (SheafOfModules.changeOfRingsPresheaf φ M).presheaf).app U
            (z ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x)) := by
  let η := ((PresheafOfModules.sheafificationAdjunction.{t + 1}
    (R := (sheafCompose (ProEt.topology T)
      (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj S)
    (𝟙 _)).unit.app (SheafOfModules.changeOfRingsPresheaf.{t, t + 1, t + 1} φ M)).app U
  let e := eqToHom h.symm
  change e.val.app U (η ((s * z) ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x)) =
    s • e.val.app U (η (z ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x))
  clear_value e η
  have ht := ModuleCat.ExtendScalars.smul_tmul (φ.hom.app U).hom s z x
  have hη := η.hom.map_smul s (z ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x)
  have he := (e.val.app U).hom.map_smul s
    (η (z ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x))
  exact (congrArg (fun w ↦ e.val.app U (η w)) ht.symm).trans
    ((congrArg (fun w ↦ e.val.app U w) hη).trans he)


/-- The chosen scalar tensor section is linear in its scalar factor.
Source: Stacks 06YY; scalar-extension clauses (1), (4)
(blueprint: lem-sp-scalar-extension-site-calculus). -/
theorem scalarSiteTensor_smul (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S)
    (M : SheafOfModules.{t + 1}
      ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R))
    (U : T.ProEtᵒᵖ) (s z : S.obj.obj U) (x : M.val.obj U) :
    scalarSiteChangeTensor T φ M U (s * z) x =
      s • scalarSiteChangeTensor T φ M U z x := by
  exact normalizedTensor_smul T φ M _
    ((scalarSiteChangeData T φ).choose_spec.choose M) U s z x

/-- Successive ordinary restriction agrees with direct restriction.
Source: Stacks 06YY; scalar-extension clauses (1), (4)
(blueprint: lem-sp-scalar-extension-site-calculus). -/
def scalarSiteRestrictCompIso (T : Scheme.{t})
    {R S V : Sheaf (ProEt.topology T) CommRingCat.{t + 1}}
    (φ : R ⟶ S) (ψ : S ⟶ V) :
    scalarSiteRestriction T (φ ≫ ψ) ≅ scalarSiteRestriction T ψ ⋙ scalarSiteRestriction T φ :=
  NatIso.ofComponents (fun N ↦
    { hom.val.app U := (ModuleCat.restrictScalarsComp'App _ _ _ rfl (N.val.obj U)).hom
      hom.val.naturality i := by ext m; rfl
      inv.val.app U := (ModuleCat.restrictScalarsComp'App _ _ _ rfl (N.val.obj U)).inv
      inv.val.naturality i := by ext m; rfl }) (by intro M N f; ext U x; rfl)

/-- Normalized tensor adjunctions determine the ordinary balancing isomorphism.
Source: Stacks 06YY; scalar-extension clauses (1), (4)
(blueprint: lem-sp-scalar-extension-site-calculus). -/
theorem balancing_from_adjunctions (T : Scheme.{t})
    {R S V : Sheaf (ProEt.topology T) CommRingCat.{t + 1}}
    (φ : R ⟶ S) (ψ : S ⟶ V)
    (E1 : SheafOfModules.{t + 1}
      ((sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R) ⥤ SheafOfModules.{t + 1}
      ((sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj S))
    [E1.Additive]
    (τ1 : ∀ (M : SheafOfModules.{t + 1}
      ((sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R)) (U : T.ProEtᵒᵖ),
      S.obj.obj U → M.val.obj U → (E1.obj M).val.obj U)
    (a1 : E1 ⊣ scalarSiteRestriction T φ)
    (h1 : ∀ (M : SheafOfModules.{t + 1}
      ((sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R)) (N : SheafOfModules.{t + 1}
      ((sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj S))
      (f : E1.obj M ⟶ N) (U : T.ProEtᵒᵖ) (x : M.val.obj U),
      (a1.homEquiv M N f).val.app U x = f.val.app U (τ1 M U 1 x))
    (hs1 : ∀ (M : SheafOfModules.{t + 1}
      ((sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R)) (U : T.ProEtᵒᵖ) (s z : S.obj.obj U)
      (x : M.val.obj U), τ1 M U (s * z) x = s • τ1 M U z x)
    (E2 : SheafOfModules.{t + 1}
      ((sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj S) ⥤ SheafOfModules.{t + 1}
      ((sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj V))
    [E2.Additive]
    (τ2 : ∀ (M : SheafOfModules.{t + 1}
      ((sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj S)) (U : T.ProEtᵒᵖ),
      V.obj.obj U → M.val.obj U → (E2.obj M).val.obj U)
    (a2 : E2 ⊣ scalarSiteRestriction T ψ)
    (h2 : ∀ (M : SheafOfModules.{t + 1}
      ((sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj S)) (N : SheafOfModules.{t + 1}
      ((sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj V))
      (f : E2.obj M ⟶ N) (U : T.ProEtᵒᵖ) (x : M.val.obj U),
      (a2.homEquiv M N f).val.app U x = f.val.app U (τ2 M U 1 x))
    (hs2 : ∀ (M : SheafOfModules.{t + 1}
      ((sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj S)) (U : T.ProEtᵒᵖ) (s z : V.obj.obj U)
      (x : M.val.obj U), τ2 M U (s * z) x = s • τ2 M U z x)
    (E3 : SheafOfModules.{t + 1}
      ((sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R) ⥤ SheafOfModules.{t + 1}
      ((sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj V))
    [E3.Additive]
    (τ3 : ∀ (M : SheafOfModules.{t + 1}
      ((sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R)) (U : T.ProEtᵒᵖ),
      V.obj.obj U → M.val.obj U → (E3.obj M).val.obj U)
    (a3 : E3 ⊣ scalarSiteRestriction T (φ ≫ ψ))
    (h3 : ∀ (M : SheafOfModules.{t + 1}
      ((sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R)) (N : SheafOfModules.{t + 1}
      ((sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj V))
      (f : E3.obj M ⟶ N) (U : T.ProEtᵒᵖ) (x : M.val.obj U),
      (a3.homEquiv M N f).val.app U x = f.val.app U (τ3 M U 1 x))
    (hs3 : ∀ (M : SheafOfModules.{t + 1}
      ((sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R)) (U : T.ProEtᵒᵖ) (s z : V.obj.obj U)
      (x : M.val.obj U), τ3 M U (s * z) x = s • τ3 M U z x)
    (P : CochainComplex (SheafOfModules.{t + 1}
      (SheafOfModules.derivedChangeRingIndependentCoefficients.{t + 1, t + 1, t}
        (ProEt.topology T) R)) ℤ) :
    ∃! f : ((E2).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((E1).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ⟶
      ((E3).mapHomologicalComplex (ComplexShape.up ℤ)).obj P,
      IsIso f ∧ ∀ (p : ℤ) (U : T.ProEtᵒᵖ) (s : V.obj.obj U) (z : S.obj.obj U)
        (x : (P.X p).val.obj U),
        (f.f p).val.app U
          (τ2 _ U s (τ1 _ U z x)) =
        τ3 _ U (s * (ψ.hom.app U z)) x := by
  let a := (a1.comp a2).ofNatIsoRight (scalarSiteRestrictCompIso T φ ψ).symm
  let e := a.leftAdjointUniq a3
  have hcomp (M : SheafOfModules.{t + 1}
      ((sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R))
      (N : SheafOfModules.{t + 1}
      ((sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj V))
      (f : ((E1) ⋙ E2).obj M ⟶ N)
      (U : T.ProEtᵒᵖ) (x : M.val.obj U) :
      (a.homEquiv M N f).val.app U x =
        f.val.app U (τ2 _ U 1
          (τ1 M U 1 x)) := by
    dsimp only [a]
    rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv]
    change (a1.homEquiv M _ (a2.homEquiv _ N f)).val.app U x = _
    exact (h1 M _ (a2.homEquiv _ N f) U x).trans
      (h2 _ N f U (τ1 M U 1 x))
  clear_value a
  have hunit (M : SheafOfModules.{t + 1}
      ((sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R))
      (U : T.ProEtᵒᵖ) (x : M.val.obj U) :
      (e.hom.app M).val.app U (τ2 _ U 1
        (τ1 M U 1 x)) =
      τ3 M U 1 x := by
    have he := congrArg (fun f ↦ f.val.app U x)
      (Adjunction.homEquiv_leftAdjointUniq_hom_app a a3 M)
    rw [hcomp] at he
    rw [← a3.homEquiv_id M, h3] at he
    exact he
  clear_value e
  have hformula (M : SheafOfModules.{t + 1}
      ((sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R))
      (U : T.ProEtᵒᵖ) (s : V.obj.obj U) (z : S.obj.obj U) (x : M.val.obj U) :
      (e.hom.app M).val.app U (τ2 _ U s
        (τ1 M U z x)) =
      τ3 M U (s * ψ.hom.app U z) x := by
    have hz := hs1 M U z 1 x
    rw [mul_one] at hz
    have hs := hs2 ((E1).obj M) U s 1
      (τ1 M U z x)
    rw [mul_one] at hs
    erw [hs, map_smul, ← h2, hz, map_smul]
    change s • (ψ.hom.app U z •
      (show (E3.obj M).val.obj U from
        (a2.homEquiv _ _ (e.hom.app M)).val.app U (τ1 M U 1 x))) = _
    erw [h2, hunit, ← mul_smul]
    have ht := hs3 M U (s * ψ.hom.app U z) 1 x
    simpa only [mul_one] using ht.symm
  let f := ((Functor.mapHomologicalComplexCompIso e (.up ℤ)).hom.app P)
  refine ⟨f, ⟨by dsimp [f]; infer_instance, ?_⟩, ?_⟩
  · intro p U s z x
    exact hformula (P.X p) U s z x
  · intro g hg
    apply HomologicalComplex.Hom.ext
    funext p
    apply (a.homEquiv _ _).injective
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    ext x
    rw [hcomp, hcomp]
    exact (hg.2 p U 1 1 x).trans (hformula (P.X p) U 1 1 x).symm



/-- Ordinary successive extension admits the pure-tensor balancing comparison.
Source: Stacks 06YY; scalar-extension clauses (1), (4)
(blueprint: lem-sp-scalar-extension-site-calculus). -/
theorem scalarSiteBalance_exists (T : Scheme.{t})
    {R S V : Sheaf (ProEt.topology T) CommRingCat.{t + 1}}
    (φ : R ⟶ S) (ψ : S ⟶ V) (χ : R ⟶ V) (_h : φ ≫ ψ = χ)
    (P : CochainComplex (SheafOfModules.{t + 1}
      (SheafOfModules.derivedChangeRingIndependentCoefficients.{t + 1, t + 1, t}
        (ProEt.topology T) R)) ℤ) :
    ∃! f : ((scalarSiteChange T ψ).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((scalarSiteChange T φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ⟶
      ((scalarSiteChange T χ).mapHomologicalComplex (ComplexShape.up ℤ)).obj P,
      IsIso f ∧ ∀ (p : ℤ) (U : T.ProEtᵒᵖ) (s : V.obj.obj U) (z : S.obj.obj U)
        (x : (P.X p).val.obj U),
        (f.f p).val.app U
          (scalarSiteChangeTensor T ψ _ U s (scalarSiteChangeTensor T φ _ U z x)) =
        scalarSiteChangeTensor T χ _ U (s * (ψ.hom.app U z)) x := by
  subst χ
  obtain ⟨a1, h1⟩ := scalarSiteAdjunction T φ
  obtain ⟨a2, h2⟩ := scalarSiteAdjunction T ψ
  obtain ⟨a3, h3⟩ := scalarSiteAdjunction T (φ ≫ ψ)
  exact balancing_from_adjunctions T φ ψ _ (scalarSiteChangeTensor T φ) a1 h1
    (scalarSiteTensor_smul T φ) _ (scalarSiteChangeTensor T ψ) a2 h2
    (scalarSiteTensor_smul T ψ) _ (scalarSiteChangeTensor T (φ ≫ ψ)) a3 h3
    (scalarSiteTensor_smul T (φ ≫ ψ)) P

/-- The specified ordinary tensor objects and morphisms of scalar extension.
Source: Stacks 06YY; scalar-extension clauses (1), (4)
(blueprint: lem-sp-scalar-extension-site-calculus). -/
def siteScalarChangeSpec (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S) :
    (siteScalarModules T R ⥤ siteScalarModules T S) → Prop :=
  (fun {B : Type (t + 2)} {P : B → Prop} (_ : ∃ x, P x) ↦ P)
    (scalarSiteChangeData T φ)


/-- The generic change-of-rings theorem supplies the specified ordinary tensor.
Source: Stacks 06YY; scalar-extension clauses (1), (4)
(blueprint: lem-sp-scalar-extension-site-calculus). -/
theorem siteScalarChangeExistence (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S) :
    ∃ E, siteScalarChangeSpec T φ E := scalarSiteChangeData T φ


/-- The ordinary tensor functor selected with its explicit tensor specification.
Source: Stacks 06YY; scalar-extension clauses (1), (4)
(blueprint: lem-sp-scalar-extension-site-calculus). -/
noncomputable def siteScalarChange (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S) :
    siteScalarModules T R ⥤ siteScalarModules T S := scalarSiteChange T φ


/-- The specified ordinary extension of scalars is additive.
Source: Stacks 06YY (blueprint: lem-sp-scalar-extension-site-calculus). -/
noncomputable instance siteScalarChangeAdditive (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S) :
    (siteScalarChange T φ).Additive :=
  (siteScalarChangeExistence T φ).choose_spec.choose_spec.choose_spec.choose


/-- The universal left-derived pair and its K-flat counit specification.
Source: Stacks 06YY; scalar-extension clauses (1), (4)
(blueprint: lem-sp-scalar-extension-site-calculus). -/
def siteScalarDerivedSpec (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S)
    (LF : siteScalarDerivedCategory T R ⥤ siteScalarDerivedCategory T S) : Prop :=
    ∃ (ε : DerivedCategory.Qh ⋙ LF ⟶
        (siteScalarChange T φ).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh),
      LF.IsLeftDerivedFunctor ε
          (HomotopyCategory.quasiIso (siteScalarModules T R) (.up ℤ)) ∧
        (∃ (_ : LF.CommShift ℤ), LF.IsTriangulated) ∧
        ∀ P : CochainComplex (siteScalarModules T R) ℤ,
          CochainComplex.IsKFlatIndependentCoefficients (R := R) P →
          IsIso (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P))


/-- The ordinary tensor admits the specified universal left-derived pair.
Source: Stacks 06YY; scalar-extension clauses (1), (4)
(blueprint: lem-sp-scalar-extension-site-calculus). -/
theorem siteScalarDerivedExistence (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S) :
    ∃ LF, siteScalarDerivedSpec T φ LF :=
  (siteScalarChangeExistence T φ).choose_spec.choose_spec.choose_spec.choose_spec.2.2


/-- The derived tensor functor selected from its universal left-derived pair.
Source: Stacks 06YY; scalar-extension clauses (1), (4)
(blueprint: lem-sp-scalar-extension-site-calculus). -/
noncomputable def siteScalarDerivedChange (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S) :
    siteScalarDerivedCategory T R ⥤ siteScalarDerivedCategory T S :=
  scalarSiteDerivedChange T φ


/-- The counit from derived extension to ordinary extension on homotopy classes.
Source: Stacks 06YY; scalar-extension clauses (1), (4)
(blueprint: lem-sp-scalar-extension-site-calculus). -/
noncomputable def siteScalarDerivedCounit (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S) :
    DerivedCategory.Qh ⋙ siteScalarDerivedChange T φ ⟶
      (siteScalarChange T φ).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh :=
  (siteScalarDerivedExistence T φ).choose_spec.choose


/-- The chosen counit has the universal left-derived functor property.
Source: Stacks 06YY (blueprint: lem-sp-scalar-extension-site-calculus). -/
noncomputable instance siteScalarDerivedUniversal (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S) :
    (siteScalarDerivedChange T φ).IsLeftDerivedFunctor (siteScalarDerivedCounit T φ)
      (HomotopyCategory.quasiIso (siteScalarModules T R) (ComplexShape.up ℤ)) :=
  (siteScalarDerivedExistence T φ).choose_spec.choose_spec.1

attribute [local instance] siteScalarModulesHasDerivedCategory


/-- The sectionwise pure tensor in the specified ordinary extension.
Source: Stacks 06YY; scalar-extension clauses (1), (4)
(blueprint: lem-sp-scalar-extension-site-calculus). -/
noncomputable def siteScalarTensorSection (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S)
    (M : siteScalarModules T R) (U : T.ProEtᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U) :
    ((siteScalarChange T φ).obj M).val.obj U :=
  scalarSiteChangeTensor T φ M U s x

/-- Restriction of ordinary ring-sheaf modules along a coefficient map.
Source: Stacks 06YY; scalar-extension clauses (1), (4)
(blueprint: lem-sp-scalar-extension-site-calculus). -/
noncomputable def siteScalarRestrict (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S) :=
  SheafOfModules.restrictScalars.{t + 1}
    ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map φ)


/-- Restriction of scalars is additive on the ordinary module categories.
Source: Stacks 06YY; scalar-extension clause (1)
(blueprint: lem-sp-scalar-extension-site-calculus). -/
instance siteScalarRestrict_additive (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S) :
    (siteScalarRestrict T φ).Additive :=
  inferInstanceAs ((SheafOfModules.restrictScalars.{t + 1}
    ((sheafCompose (ProEt.topology T)
      (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map φ)).Additive)


/-- Restriction preserves finite limits, since it leaves underlying abelian sheaves unchanged.
Source: Stacks 06YY and 0DVC; scalar-extension clause (1)
(blueprint: lem-sp-scalar-extension-site-calculus). -/
instance siteScalarRestrict_preservesFiniteLimits (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S) :
    PreservesFiniteLimits (siteScalarRestrict T φ) := by
  obtain ⟨hl, _, _⟩ := SheafOfModules.sheafRingDerivedCoefficientAdjunction
    (J := ProEt.topology T) φ
  exact hl

/-- Restriction preserves finite colimits, since cokernels have the unchanged underlying sheaf.
Source: Stacks 06YY and 0DVC; scalar-extension clause (1)
(blueprint: lem-sp-scalar-extension-site-calculus). -/
instance siteScalarRestrict_preservesFiniteColimits (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S) :
    PreservesFiniteColimits (siteScalarRestrict T φ) := by
  obtain ⟨_, hc, _⟩ := SheafOfModules.sheafRingDerivedCoefficientAdjunction
    (J := ProEt.topology T) φ
  exact hc


/-- Ordinary extension has the specified sheafified tensor object.
Source: Stacks 06YY; scalar-extension clauses (1), (4)
(blueprint: lem-sp-scalar-extension-site-calculus). -/
theorem siteScalarChange_obj_eq (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S)
    (M : siteScalarModules T R) :
    (siteScalarChange T φ).obj M = SheafOfModules.changeOfRings.{t, t + 1, t + 1} φ M :=
  (siteScalarChangeExistence T φ).choose_spec.choose M

/-- Ordinary extension maps arrows by tensoring with the identity scalar.
Source: Stacks 06YY; scalar-extension clauses (1), (4)
(blueprint: lem-sp-scalar-extension-site-calculus). -/
theorem siteScalarChange_map_eq (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S)
    {M N : siteScalarModules T R} (f : M ⟶ N) :
    (siteScalarChange T φ).map f = eqToHom (siteScalarChange_obj_eq T φ M) ≫
      SheafOfModules.changeOfRingsHom φ M f ≫
        eqToHom (siteScalarChange_obj_eq T φ N).symm :=
  (siteScalarChangeExistence T φ).choose_spec.choose_spec.choose f

/-- Scalar extension preserves quasi-isomorphisms between K-flat complexes.
Source: Stacks 06YY; scalar-extension clauses (1), (4)
(blueprint: lem-sp-scalar-extension-site-calculus). -/
theorem siteScalarChange_quasiIso (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S)
    {P Q : CochainComplex (siteScalarModules T R) ℤ} (f : P ⟶ Q)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := R) P)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients (R := R) Q) (hf : QuasiIso f) :
    QuasiIso (((siteScalarChange T φ).mapHomologicalComplex (.up ℤ)).map f) :=
  (siteScalarChangeExistence T φ).choose_spec.choose_spec.choose_spec.choose_spec.1
    f hP hQ hf

/-- The derived counit is invertible at each K-flat homotopy object.
Source: Stacks 06YY; scalar-extension clauses (1), (4)
(blueprint: lem-sp-scalar-extension-site-calculus). -/
theorem siteScalarDerivedCounit_isIso (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S)
    (P : CochainComplex (siteScalarModules T R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := R) P) :
    IsIso ((siteScalarDerivedCounit T φ).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) :=
  (siteScalarDerivedExistence T φ).choose_spec.choose_spec.2.2 P hP

attribute [local irreducible] siteScalarChange siteScalarDerivedChange

/-- Tensoring a module arrow acts on the module factor of pure tensors.
Source: Stacks 06YY; scalar-extension clauses (1), (4)
(blueprint: lem-sp-scalar-extension-site-calculus). -/
theorem siteScalarTensor_map (X : Scheme.{u})
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (φ : R ⟶ S)
    {M N : siteScalarModules X R} (a : M ⟶ N) (U : X.ProEtᵒᵖ)
    (s : S.obj.obj U) (x : M.val.obj U) :
    ((siteScalarChange X φ).map a).val.app U
        (siteScalarTensorSection X φ M U s x) =
      siteScalarTensorSection X φ N U s (a.val.app U x) := by
  let : HasWeakSheafify (ProEt.topology X) AddCommGrpCat.{u + 1} := inferInstance
  let : (ProEt.topology X).HasSheafCompose
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) := inferInstance
  let : (ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    inferInstance
  let h : ∀ M : siteScalarModules X R, (siteScalarChange X φ).obj M =
      SheafOfModules.changeOfRings.{u, u + 1, u + 1} φ M :=
    (siteScalarChange_obj_eq X φ)
  have ha := siteScalarChange_map_eq X φ a
  change (siteScalarChange X φ).map a = _ at ha
  let b : SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} φ M ⟶
      SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} φ N :=
    { app := fun V ↦ (ModuleCat.extendScalars (φ.hom.app V).hom).map (a.val.app V)
      naturality := SheafOfModules.changeOfRingsHom_naturality.{u, u + 1, u + 1} φ M a }
  let adjS := PresheafOfModules.sheafificationAdjunction.{u + 1}
    (𝟙 (siteScalarModuleRing X S).obj)
  have hn := congrArg (fun t ↦ t.app U
    (s ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x))
      (adjS.unit.naturality b)
  have hc : eqToHom (h M).symm ≫ (siteScalarChange X φ).map a =
      SheafOfModules.changeOfRingsHom.{u, u + 1, u + 1} φ M a ≫ eqToHom (h N).symm := by
    rw [ha]
    simp
  have hc' := congrArg (fun t : SheafOfModules.changeOfRings.{u, u + 1, u + 1} φ M ⟶
      (siteScalarChange X φ).obj N ↦ t.val.app U
        ((toSheafify (ProEt.topology X)
          (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} φ M).presheaf).app U
            (s ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x))) hc
  change _ = _ at hn
  change _ = _ at hc'
  dsimp only [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply] at hc'
  with_unfolding_all
    exact hc'.trans (congrArg ((eqToHom (h N).symm).val.app U) hn.symm)

/-- Morphisms out of scalar extension are determined on pure tensors.
Source: Stacks 06YY; scalar-extension clauses (1), (4)
(blueprint: lem-sp-scalar-extension-site-calculus). -/
theorem siteScalarTensor_hom_ext (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S)
    (M : siteScalarModules T R) (N : Sheaf (ProEt.topology T) AddCommGrpCat.{t + 1})
    (f g : (SheafOfModules.toSheaf (siteScalarModuleRing T S)).obj
      ((siteScalarChange T φ).obj M) ⟶ N)
    (h : ∀ V s x, f.hom.app V (siteScalarTensorSection T φ M V s x) =
      g.hom.app V (siteScalarTensorSection T φ M V s x)) : f = g := by
  let : HasWeakSheafify (ProEt.topology T) AddCommGrpCat.{t + 1} := inferInstance
  let : (ProEt.topology T).HasSheafCompose
      (forget₂ CommRingCat.{t + 1} RingCat.{t + 1}) := inferInstance
  let : (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{t + 1} :=
    inferInstance
  let e := eqToHom ((siteScalarChange_obj_eq T φ) M).symm
  apply (cancel_epi ((SheafOfModules.toSheaf (siteScalarModuleRing T S)).map e)).1
  apply Sheaf.hom_ext
  apply sheafify_hom_ext (ProEt.topology T) _ _ N.property
  ext V z
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  | tmul s x => with_unfolding_all exact h V s x

/-- The explicit ordinary tensor admits its multiplication-normalized adjunction.
Source: Stacks 06YY; scalar-extension clauses (1), (4)
(blueprint: lem-sp-scalar-extension-site-calculus). -/
theorem ordinaryAdjunction_exists (X : Scheme.{u})
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (φ : R ⟶ S) :
    ∃ a : siteScalarChange X φ ⊣ siteScalarRestrict X φ,
      ∀ (M : siteScalarModules X R) (N : siteScalarModules X S)
        (f : (siteScalarChange X φ).obj M ⟶ N) (U : X.ProEtᵒᵖ) (x : M.val.obj U),
        HEq ((a.homEquiv M N f).val.app U x)
          (f.val.app U (siteScalarTensorSection X φ M U 1 x)) := by
  let h := siteScalarChange_obj_eq X φ
  obtain ⟨_, _, ho⟩ := SheafOfModules.sheafRingCoefficientOrdinaryAdjunction
    (J := ProEt.topology X) φ
  obtain ⟨a, ha⟩ := ho (siteScalarChange X φ) h (siteScalarChange_map_eq X φ)
  refine ⟨a, ?_⟩
  intro M N f U x
  have hh := ha M N (eqToHom (h M).symm ≫ f) U x
  have hi : eqToHom (h M) ≫ (eqToHom (h M).symm ≫ f) = f := by simp
  rw [hi] at hh
  dsimp only [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply] at hh
  with_unfolding_all exact heq_of_eq hh

/-- The unit of the normalized ordinary tensor-restriction adjunction.
Source: Stacks 06YY; scalar-extension clauses (1), (4)
(blueprint: lem-sp-scalar-extension-site-calculus). -/
def siteScalarUnit (X : Scheme.{u})
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (φ : R ⟶ S)
    (M : siteScalarModules X R) :
    M ⟶ (siteScalarRestrict X φ).obj ((siteScalarChange X φ).obj M) := by
  have h := (ordinaryAdjunction_exists X φ).choose.unit.app M
  exact h

/-- The ordinary adjunction unit sends a section x to 1 tensor x.
Source: Stacks 06YY; scalar-extension clauses (1), (4)
(blueprint: lem-sp-scalar-extension-site-calculus). -/
theorem siteScalarUnit_apply (X : Scheme.{u})
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (φ : R ⟶ S)
    (M : siteScalarModules X R) (U : X.ProEtᵒᵖ) (x : M.val.obj U) :
    (siteScalarUnit X φ M).val.app U x = siteScalarTensorSection X φ M U 1 x := by
  have hh := (ordinaryAdjunction_exists X φ).choose_spec M
    ((siteScalarChange X φ).obj M) (𝟙 _) U x
  let adj := (ordinaryAdjunction_exists X φ).choose
  have hi : adj.homEquiv M ((siteScalarChange X φ).obj M) (𝟙 _) = adj.unit.app M := by
    rw [Adjunction.homEquiv_unit, CategoryTheory.Functor.map_id]
    exact Category.comp_id _
  have hv := congrArg (fun f : M ⟶ (siteScalarRestrict X φ).obj
    ((siteScalarChange X φ).obj M) ↦ f.val.app U x) hi
  exact hv.symm.trans (eq_of_heq hh)


/-- The adjunction unit determines every map out of ordinary scalar extension.
Source: Stacks 06YY; scalar-extension clauses (1), (4)
(blueprint: lem-sp-scalar-extension-site-calculus). -/
theorem level_hom_ext (X : Scheme.{u})
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (M N : siteScalarModules X R)
    (f g : (siteScalarRestrict X φ).obj ((siteScalarChange X φ).obj M) ⟶ N)
    (h : ∀ (U : X.ProEtᵒᵖ)
      (s : S.obj.obj U) (x : M.val.obj U),
      f.val.app U (siteScalarTensorSection X φ M U s x) =
        g.val.app U (siteScalarTensorSection X φ M U s x)) : f = g := by
  let : HasWeakSheafify (ProEt.topology X) AddCommGrpCat.{u + 1} := inferInstance
  let : (ProEt.topology X).HasSheafCompose
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) := inferInstance
  let : (ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    inferInstance
  let hM := (siteScalarChange_obj_eq X φ) M
  apply (SheafOfModules.toSheaf (siteScalarModuleRing X R)).map_injective
  let adjS := sheafificationAdjunction (ProEt.topology X) AddCommGrpCat.{u + 1}
  let j := (SheafOfModules.toSheaf _).map (eqToHom hM.symm)
  apply (cancel_epi j).mp
  apply (adjS.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  ext U t
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add t t' ht ht' => simp only [map_add, ht, ht']
  | tmul s x => with_unfolding_all exact h U s x

open scoped ChangeOfRings in
/-- Scalar multiplication on pure tensor sections multiplies the scalar factor.
Source: Stacks 06YY; scalar-extension clauses (1), (4)
(blueprint: lem-sp-scalar-extension-site-calculus). -/
theorem tensorSection_smul (X : Scheme.{u})
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (M : siteScalarModules X R)
    (U : X.ProEtᵒᵖ) (s t : S.obj.obj U)
    (x : M.val.obj U) :
    s • siteScalarTensorSection X φ M U t x =
      siteScalarTensorSection X φ M U (s * t) x := by
  let : HasWeakSheafify (ProEt.topology X) AddCommGrpCat.{u + 1} := inferInstance
  let : (ProEt.topology X).HasSheafCompose
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) := inferInstance
  let : (ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    inferInstance
  let T := SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} φ M
  let b : T ⟶ ((siteScalarChange X φ).obj M).val :=
    (PresheafOfModules.sheafificationAdjunction.{u + 1}
      (𝟙 (siteScalarModuleRing X S).obj)).unit.app T ≫
      (eqToHom ((siteScalarChange_obj_eq X φ) M).symm).val
  with_unfolding_all change s • b.app U (t ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x) = _
  rw [← map_smul]
  with_unfolding_all rfl


/-- Apply ordinary scalar extension termwise to cochain complexes.
Source: Stacks 06YY; scalar-extension clauses (1), (4)
(blueprint: lem-sp-scalar-extension-site-calculus). -/
noncomputable def siteScalarChangeComplex (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S) :
    CochainComplex (siteScalarModules T R) ℤ ⥤ CochainComplex (siteScalarModules T S) ℤ :=
  (siteScalarChange T φ).mapHomologicalComplex (ComplexShape.up ℤ)


/-- The specified ordinary tensor has the normalized balancing isomorphism.
Source: Stacks 06YY; scalar-extension clauses (1), (4)
(blueprint: lem-sp-scalar-extension-site-calculus). -/
theorem siteScalarBalance_exists (T : Scheme.{t})
    {R S U : Sheaf (ProEt.topology T) CommRingCat.{t + 1}}
    (φ : R ⟶ S) (ψ : S ⟶ U) (χ : R ⟶ U) (_h : φ ≫ ψ = χ)
    (P : CochainComplex (siteScalarModules T R) ℤ) :
    ∃! f : (siteScalarChangeComplex T ψ).obj ((siteScalarChangeComplex T φ).obj P) ⟶
        (siteScalarChangeComplex T χ).obj P,
      IsIso f ∧ ∀ (p : ℤ) (V : T.ProEtᵒᵖ) (s : U.obj.obj V) (r : S.obj.obj V)
        (x : (P.X p).val.obj V),
        (f.f p).val.app V
          (siteScalarTensorSection T ψ ((siteScalarChange T φ).obj (P.X p)) V s
            (siteScalarTensorSection T φ (P.X p) V r x)) =
          siteScalarTensorSection T χ (P.X p) V (s * ψ.hom.app V r) x := by
  unfold siteScalarChangeComplex siteScalarChange siteScalarTensorSection
  exact scalarSiteBalance_exists T φ ψ χ _h P


/-- The uniquely normalized ordinary balancing isomorphism.
Source: Stacks 06YY; scalar-extension clauses (1), (4)
(blueprint: lem-sp-scalar-extension-site-calculus). -/
noncomputable def siteScalarBalance (T : Scheme.{t})
    {R S U : Sheaf (ProEt.topology T) CommRingCat.{t + 1}}
    (φ : R ⟶ S) (ψ : S ⟶ U) (χ : R ⟶ U) (h : φ ≫ ψ = χ)
    (P : CochainComplex (siteScalarModules T R) ℤ) :
    (siteScalarChangeComplex T ψ).obj ((siteScalarChangeComplex T φ).obj P) ⟶
      (siteScalarChangeComplex T χ).obj P :=
  (siteScalarBalance_exists T φ ψ χ h P).exists.choose


/-- The ordinary balancing map is an isomorphism.
Source: Stacks 06YY (blueprint: lem-sp-scalar-extension-site-calculus). -/
noncomputable instance siteScalarBalance_isIso (T : Scheme.{t})
    {R S U : Sheaf (ProEt.topology T) CommRingCat.{t + 1}}
    (φ : R ⟶ S) (ψ : S ⟶ U) (χ : R ⟶ U) (h : φ ≫ ψ = χ)
    (P : CochainComplex (siteScalarModules T R) ℤ) : IsIso (siteScalarBalance T φ ψ χ h P) :=
  (siteScalarBalance_exists T φ ψ χ h P).exists.choose_spec.1


/-- Balancing multiplies the two scalar factors on pure tensor sections.
Source: Stacks 06YY; scalar-extension clauses (1), (4)
(blueprint: lem-sp-scalar-extension-site-calculus). -/
theorem siteScalarBalance_tmul (T : Scheme.{t})
    {R S U : Sheaf (ProEt.topology T) CommRingCat.{t + 1}}
    (φ : R ⟶ S) (ψ : S ⟶ U) (χ : R ⟶ U) (h : φ ≫ ψ = χ)
    (P : CochainComplex (siteScalarModules T R) ℤ)
    (p : ℤ) (V : T.ProEtᵒᵖ) (s : U.obj.obj V) (r : S.obj.obj V)
    (x : (P.X p).val.obj V) :
    ((siteScalarBalance T φ ψ χ h P).f p).val.app V
      (siteScalarTensorSection T ψ ((siteScalarChange T φ).obj (P.X p)) V s
        (siteScalarTensorSection T φ (P.X p) V r x)) =
      siteScalarTensorSection T χ (P.X p) V (s * ψ.hom.app V r) x :=
  (siteScalarBalance_exists T φ ψ χ h P).exists.choose_spec.2 p V s r x

/-- Maps from a twice-extended module are determined on nested pure tensors.
Source: Stacks 06YY; scalar-extension clauses (1), (4)
(blueprint: lem-sp-scalar-extension-site-calculus). -/
theorem siteScalarBalance_hom_ext (T : Scheme.{t})
    {R S U : Sheaf (ProEt.topology T) CommRingCat.{t + 1}}
    (φ : R ⟶ S) (ψ : S ⟶ U) (χ : R ⟶ U) (h : φ ≫ ψ = χ)
    (P : CochainComplex (siteScalarModules T R) ℤ)
    {Q : CochainComplex (siteScalarModules T U) ℤ}
    (f g : (siteScalarChangeComplex T ψ).obj ((siteScalarChangeComplex T φ).obj P) ⟶ Q)
    (hf : ∀ p V s r x, (f.f p).val.app V
        (siteScalarTensorSection T ψ ((siteScalarChange T φ).obj (P.X p)) V s
          (siteScalarTensorSection T φ (P.X p) V r x)) =
      (g.f p).val.app V (siteScalarTensorSection T ψ
        ((siteScalarChange T φ).obj (P.X p)) V s
          (siteScalarTensorSection T φ (P.X p) V r x))) : f = g := by
  let : HasWeakSheafify (ProEt.topology T) AddCommGrpCat.{t + 1} := inferInstance
  let : (ProEt.topology T).HasSheafCompose
      (forget₂ CommRingCat.{t + 1} RingCat.{t + 1}) := inferInstance
  let : (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{t + 1} :=
    inferInstance
  let β := siteScalarBalance T φ ψ χ h P
  apply (cancel_epi (inv β)).1
  apply HomologicalComplex.Hom.ext
  funext p
  apply (SheafOfModules.toSheaf (siteScalarModuleRing T U)).map_injective
  apply siteScalarTensor_hom_ext T χ (P.X p)
  intro V s x
  have hb := siteScalarBalance_tmul T φ ψ χ h P p V s 1 x
  simp only [map_one, mul_one] at hb
  have hc := congrArg (fun k ↦ (k.f p).val.app V
    (siteScalarTensorSection T ψ ((siteScalarChange T φ).obj (P.X p)) V s
      (siteScalarTensorSection T φ (P.X p) V 1 x))) (IsIso.hom_inv_id β)
  dsimp only [HomologicalComplex.comp_f, HomologicalComplex.id_f,
    SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply,
    SheafOfModules.id_val, PresheafOfModules.id_app, ModuleCat.id_apply] at hc
  change ((inv β).f p).val.app V
    (((siteScalarBalance T φ ψ χ h P).f p).val.app V _) = _ at hc
  rw [hb] at hc
  change (f.f p).val.app V (((inv β).f p).val.app V _) =
    (g.f p).val.app V (((inv β).f p).val.app V _)
  rw [hc]
  exact hf p V s 1 x


/-- Ordinary balancing commutes with each module arrow.
Source: Stacks 06YY; scalar-extension clauses (1), (4)
(blueprint: lem-sp-scalar-extension-site-calculus). -/
theorem siteScalarBalance_naturality (T : Scheme.{t})
    {R S U : Sheaf (ProEt.topology T) CommRingCat.{t + 1}}
    (φ : R ⟶ S) (ψ : S ⟶ U) (χ : R ⟶ U) (h : φ ≫ ψ = χ)
    {P Q : CochainComplex (siteScalarModules T R) ℤ} (f : P ⟶ Q) :
    (siteScalarChangeComplex T ψ).map ((siteScalarChangeComplex T φ).map f) ≫
        siteScalarBalance T φ ψ χ h Q =
      siteScalarBalance T φ ψ χ h P ≫ (siteScalarChangeComplex T χ).map f := by
  apply siteScalarBalance_hom_ext T φ ψ χ h P
  intro p V s r x
  change ((siteScalarBalance T φ ψ χ h Q).f p).val.app V
      (((siteScalarChange T ψ).map ((siteScalarChange T φ).map (f.f p))).val.app V
        (siteScalarTensorSection T ψ ((siteScalarChange T φ).obj (P.X p)) V s
          (siteScalarTensorSection T φ (P.X p) V r x))) =
    ((siteScalarChange T χ).map (f.f p)).val.app V
      (((siteScalarBalance T φ ψ χ h P).f p).val.app V
        (siteScalarTensorSection T ψ ((siteScalarChange T φ).obj (P.X p)) V s
          (siteScalarTensorSection T φ (P.X p) V r x)))
  rw [siteScalarTensor_map, siteScalarTensor_map, siteScalarBalance_tmul,
    siteScalarBalance_tmul, siteScalarTensor_map]

/-- The first composite balancing route multiplies three scalar factors.
Source: Stacks 06YY; scalar-extension clauses (1), (4)
(blueprint: lem-sp-scalar-extension-site-calculus). -/
theorem siteScalarBalance_left_tmul (T : Scheme.{t})
    {R S U V : Sheaf (ProEt.topology T) CommRingCat.{t + 1}}
    (φ : R ⟶ S) (ψ : S ⟶ U) (θ : U ⟶ V)
    (P : CochainComplex (siteScalarModules T R) ℤ) (p : ℤ) (W : T.ProEtᵒᵖ)
    (s : V.obj.obj W) (r : U.obj.obj W) (q : S.obj.obj W) (x : (P.X p).val.obj W) :
    ((((siteScalarChangeComplex T θ).map (siteScalarBalance T φ ψ (φ ≫ ψ) rfl P) ≫
      siteScalarBalance T (φ ≫ ψ) θ ((φ ≫ ψ) ≫ θ) rfl P).f p).val.app W)
        (siteScalarTensorSection T θ _ W s (siteScalarTensorSection T ψ _ W r
          (siteScalarTensorSection T φ (P.X p) W q x))) =
      siteScalarTensorSection T ((φ ≫ ψ) ≫ θ) (P.X p) W
        (s * θ.hom.app W (r * ψ.hom.app W q)) x := by
  let : HasWeakSheafify (ProEt.topology T) AddCommGrpCat.{t + 1} := inferInstance
  let : (ProEt.topology T).HasSheafCompose
      (forget₂ CommRingCat.{t + 1} RingCat.{t + 1}) := inferInstance
  let : (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{t + 1} :=
    inferInstance
  let f := (siteScalarBalance T φ ψ (φ ≫ ψ) rfl P).f p
  let g := (siteScalarBalance T (φ ≫ ψ) θ ((φ ≫ ψ) ≫ θ) rfl P).f p
  change g.val.app W (((siteScalarChange T θ).map f).val.app W _) = _
  have hmap := siteScalarTensor_map T θ f W s
    (siteScalarTensorSection T ψ _ W r (siteScalarTensorSection T φ (P.X p) W q x))
  apply (congrArg (g.val.app W) hmap).trans
  have hb := siteScalarBalance_tmul T φ ψ (φ ≫ ψ) rfl P p W r q x
  apply (congrArg (fun z ↦ g.val.app W
    (siteScalarTensorSection T θ ((siteScalarChange T (φ ≫ ψ)).obj (P.X p)) W s z)) hb).trans
  exact siteScalarBalance_tmul T (φ ≫ ψ) θ ((φ ≫ ψ) ≫ θ) rfl P p W s
    (r * ψ.hom.app W q) x

/-- The second composite balancing route multiplies three scalar factors.
Source: Stacks 06YY; scalar-extension clauses (1), (4)
(blueprint: lem-sp-scalar-extension-site-calculus). -/
theorem siteScalarBalance_right_tmul (T : Scheme.{t})
    {R S U V : Sheaf (ProEt.topology T) CommRingCat.{t + 1}}
    (φ : R ⟶ S) (ψ : S ⟶ U) (θ : U ⟶ V)
    (P : CochainComplex (siteScalarModules T R) ℤ) (p : ℤ) (W : T.ProEtᵒᵖ)
    (s : V.obj.obj W) (r : U.obj.obj W) (q : S.obj.obj W) (x : (P.X p).val.obj W) :
    (((siteScalarBalance T ψ θ (ψ ≫ θ) rfl ((siteScalarChangeComplex T φ).obj P) ≫
      siteScalarBalance T φ (ψ ≫ θ) ((φ ≫ ψ) ≫ θ) (Category.assoc φ ψ θ).symm P).f p).val.app W)
        (siteScalarTensorSection T θ _ W s (siteScalarTensorSection T ψ _ W r
          (siteScalarTensorSection T φ (P.X p) W q x))) =
      siteScalarTensorSection T ((φ ≫ ψ) ≫ θ) (P.X p) W
        ((s * θ.hom.app W r) * θ.hom.app W (ψ.hom.app W q)) x := by
  let : HasWeakSheafify (ProEt.topology T) AddCommGrpCat.{t + 1} := inferInstance
  let : (ProEt.topology T).HasSheafCompose
      (forget₂ CommRingCat.{t + 1} RingCat.{t + 1}) := inferInstance
  let : (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{t + 1} :=
    inferInstance
  let g := (siteScalarBalance T φ (ψ ≫ θ) ((φ ≫ ψ) ≫ θ)
    (Category.assoc φ ψ θ).symm P).f p
  change g.val.app W _ = _
  have hb := siteScalarBalance_tmul T ψ θ (ψ ≫ θ) rfl
    ((siteScalarChangeComplex T φ).obj P) p W s r
      (siteScalarTensorSection T φ (P.X p) W q x)
  apply (congrArg (g.val.app W) hb).trans
  exact siteScalarBalance_tmul T φ (ψ ≫ θ) ((φ ≫ ψ) ≫ θ)
    (Category.assoc φ ψ θ).symm P p W (s * θ.hom.app W r) q x

/-- Maps from a thrice-extended module are determined on triple tensors.
Source: Stacks 06YY; scalar-extension clauses (1), (4)
(blueprint: lem-sp-scalar-extension-site-calculus). -/
theorem siteScalarBalance_triple_hom_ext (T : Scheme.{t})
    {R S U V : Sheaf (ProEt.topology T) CommRingCat.{t + 1}}
    (φ : R ⟶ S) (ψ : S ⟶ U) (θ : U ⟶ V)
    (P : CochainComplex (siteScalarModules T R) ℤ)
    {Q : CochainComplex (siteScalarModules T V) ℤ}
    (f g : (siteScalarChangeComplex T θ).obj ((siteScalarChangeComplex T ψ).obj
      ((siteScalarChangeComplex T φ).obj P)) ⟶ Q)
    (hf : ∀ p W s r q x, (f.f p).val.app W
        (siteScalarTensorSection T θ _ W s (siteScalarTensorSection T ψ _ W r
          (siteScalarTensorSection T φ (P.X p) W q x))) =
      (g.f p).val.app W (siteScalarTensorSection T θ _ W s
        (siteScalarTensorSection T ψ _ W r
          (siteScalarTensorSection T φ (P.X p) W q x)))) : f = g := by
  let : HasWeakSheafify (ProEt.topology T) AddCommGrpCat.{t + 1} := inferInstance
  let : (ProEt.topology T).HasSheafCompose
      (forget₂ CommRingCat.{t + 1} RingCat.{t + 1}) := inferInstance
  let : (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{t + 1} :=
    inferInstance
  let β := (siteScalarChangeComplex T θ).map (siteScalarBalance T φ ψ (φ ≫ ψ) rfl P) ≫
    siteScalarBalance T (φ ≫ ψ) θ ((φ ≫ ψ) ≫ θ) rfl P
  have : IsIso β := by dsimp [β]; infer_instance
  apply (cancel_epi (inv β)).1
  apply HomologicalComplex.Hom.ext
  funext p
  apply (SheafOfModules.toSheaf (siteScalarModuleRing T V)).map_injective
  apply siteScalarTensor_hom_ext T ((φ ≫ ψ) ≫ θ) (P.X p)
  intro W s x
  have hb : (β.f p).val.app W (siteScalarTensorSection T θ _ W s
      (siteScalarTensorSection T ψ _ W 1
        (siteScalarTensorSection T φ (P.X p) W 1 x))) =
      siteScalarTensorSection T ((φ ≫ ψ) ≫ θ) (P.X p) W s x := by
    have ht := siteScalarBalance_left_tmul T φ ψ θ P p W s 1 1 x
    simpa only [map_one, mul_one] using ht
  have hc := congrArg (fun k ↦ (k.f p).val.app W
    (siteScalarTensorSection T θ _ W s (siteScalarTensorSection T ψ _ W 1
      (siteScalarTensorSection T φ (P.X p) W 1 x)))) (IsIso.hom_inv_id β)
  dsimp only [HomologicalComplex.comp_f, HomologicalComplex.id_f,
    SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply,
    SheafOfModules.id_val, PresheafOfModules.id_app, ModuleCat.id_apply] at hc
  change ((inv β).f p).val.app W ((β.f p).val.app W _) = _ at hc
  rw [hb] at hc
  change (f.f p).val.app W (((inv β).f p).val.app W _) =
    (g.f p).val.app W (((inv β).f p).val.app W _)
  rw [hc]
  exact hf p W s 1 1 x


/-- The two routes through three ordinary scalar extensions agree.
Source: Stacks 06YY; scalar-extension clauses (1), (4)
(blueprint: lem-sp-scalar-extension-site-calculus). -/
theorem siteScalarBalance_cocycle (T : Scheme.{t})
    {R S U V : Sheaf (ProEt.topology T) CommRingCat.{t + 1}}
    (φ : R ⟶ S) (ψ : S ⟶ U) (θ : U ⟶ V)
    (P : CochainComplex (siteScalarModules T R) ℤ) :
    (siteScalarChangeComplex T θ).map (siteScalarBalance T φ ψ (φ ≫ ψ) rfl P) ≫
        siteScalarBalance T (φ ≫ ψ) θ ((φ ≫ ψ) ≫ θ) rfl P =
      siteScalarBalance T ψ θ (ψ ≫ θ) rfl ((siteScalarChangeComplex T φ).obj P) ≫
        siteScalarBalance T φ (ψ ≫ θ) ((φ ≫ ψ) ≫ θ) (Category.assoc φ ψ θ).symm P := by
  apply siteScalarBalance_triple_hom_ext T φ ψ θ P
  intro p W s r q x
  have hl := siteScalarBalance_left_tmul T φ ψ θ P p W s r q x
  have hr := siteScalarBalance_right_tmul T φ ψ θ P p W s r q x
  apply hl.trans
  apply Eq.trans _ hr.symm
  congr 1
  rw [map_mul, mul_assoc]

/-- Turn a homotopy derived counit into a map on a complex representative.
Source: Stacks 06YY; scalar-extension clauses (1), (4)
(blueprint: lem-sp-scalar-extension-site-calculus). -/
noncomputable def siteScalarComplexCounit
    {B : Type u₁} [Category.{v₁} B] [Abelian B] [HasDerivedCategory.{w₁} B]
    {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasDerivedCategory.{w₂} D]
    (E : B ⥤ D) [E.Additive] (L : DerivedCategory B ⥤ DerivedCategory D)
    (ε : DerivedCategory.Qh ⋙ L ⟶
      E.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    (P : CochainComplex B ℤ) :
    L.obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) :=
  L.map ((DerivedCategory.quotientCompQhIso B).inv.app P) ≫
    ε.app ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj P) ≫
    DerivedCategory.Qh.map ((E.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app P) ≫
    (DerivedCategory.quotientCompQhIso D).hom.app
      ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)



/-- The complex-representative counit for the specified scalar extension.
Source: Stacks 06YY; scalar-extension clauses (1), (4)
(blueprint: lem-sp-scalar-extension-site-calculus). -/
noncomputable abbrev siteScalarScalarComplexCounit (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S)
    (P : CochainComplex (siteScalarModules T R) ℤ) :=
  siteScalarComplexCounit (siteScalarChange T φ) (siteScalarDerivedChange T φ)
    (siteScalarDerivedCounit T φ) P


open CategoryTheory.Functor

/-- Transport a left Kan extension across a specified isomorphism of source functors.
Source: Stacks 06YY; scalar-extension clauses (1), (4)
(blueprint: lem-sp-scalar-extension-site-calculus). -/
theorem kan_change_iso
    {C D H : Type*} [Category C] [Category D] [Category H]
    {Q Q' : C ⥤ D} {G G' : C ⥤ H} (F : D ⥤ H)
    (i : Q ≅ Q') (j : G ≅ G') (α : Q ⋙ F ⟶ G)
    [F.IsRightKanExtension α] :
    F.IsRightKanExtension (whiskerRight i.inv F ≫ α ≫ j.hom) := by
  let P := (rightExtensionEquivalenceOfIso₁ i G).functor ⋙
    (rightExtensionEquivalenceOfIso₂ Q' j).functor
  constructor
  refine ⟨IsTerminal.ofIso
    (IsTerminal.isTerminalObj P _ (F.isUniversalOfIsRightKanExtension α)) ?_⟩
  exact CostructuredArrow.isoMk (Iso.refl _) (by
    ext X
    simp [P, rightExtensionEquivalenceOfIso₁, rightExtensionEquivalenceOfIso₂]
    rfl)


/-- Compose the homotopy counit with complex localization to obtain its Kan property.
Source: Stacks 06YY; scalar-extension clauses (1), (4)
(blueprint: lem-sp-scalar-extension-site-calculus). -/
theorem kan_precomp_quotient
    {A B D H : Type*} [Category A] [Category B] [Category D] [Category H]
    (q : A ⥤ B) [((whiskeringLeft A B H).obj q).Full]
    [((whiskeringLeft A B H).obj q).Faithful]
    (L : B ⥤ D) (G : B ⥤ H) (F : D ⥤ H)
    (α : L ⋙ F ⟶ G) [F.IsRightKanExtension α] :
    F.IsRightKanExtension ((Functor.associator q L F).hom ≫ whiskerLeft q α) := by
  let P := RightExtension.precomp L G q
  have : P.IsEquivalence := by
    dsimp only [P, RightExtension.precomp]
    apply CostructuredArrow.isEquivalenceMap₂
  let β := (Functor.associator q L F).hom ≫ whiskerLeft q α
  let e : P.obj (RightExtension.mk F α) ≅ RightExtension.mk F β :=
    CostructuredArrow.isoMk (Iso.refl _)
  exact ⟨⟨IsTerminal.ofIso
    (IsTerminal.isTerminalObj P _ (F.isUniversalOfIsRightKanExtension α)) e⟩⟩

/-- The natural counit on cochain representatives.
Source: Stacks 06YY; scalar-extension clauses (1), (4)
(blueprint: lem-sp-scalar-extension-site-calculus). -/
noncomputable def complexCounitNat
    {B : Type u₁} [Category.{v₁} B] [Abelian B] [HasDerivedCategory.{w₁} B]
    {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasDerivedCategory.{w₂} D]
    (E : B ⥤ D) [E.Additive] (L : DerivedCategory B ⥤ DerivedCategory D)
    (ε : DerivedCategory.Qh ⋙ L ⟶
      E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) :
    DerivedCategory.Q ⋙ L ⟶ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
  let q := HomotopyCategory.quotient B (.up ℤ)
  let j : q ⋙ (E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) ≅
      E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (E.mapHomotopyCategoryFactors (.up ℤ)) _ ≪≫
        Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso D)
  whiskerRight (DerivedCategory.quotientCompQhIso B).inv L ≫
    (Functor.associator q DerivedCategory.Qh L).hom ≫ whiskerLeft q ε ≫ j.hom

/-- The natural complex counit has the specified component at each representative.
Source: Stacks 06YY; scalar-extension clauses (1), (4)
(blueprint: lem-sp-scalar-extension-site-calculus). -/
theorem complexCounitNat_app
    {B : Type u₁} [Category.{v₁} B] [Abelian B] [HasDerivedCategory.{w₁} B]
    {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasDerivedCategory.{w₂} D]
    (E : B ⥤ D) [E.Additive] (L : DerivedCategory B ⥤ DerivedCategory D)
    (ε : DerivedCategory.Qh ⋙ L ⟶
      E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) (P : CochainComplex B ℤ) :
    (complexCounitNat E L ε).app P = siteScalarComplexCounit E L ε P := by
  simp [complexCounitNat, siteScalarComplexCounit]

/-- The complex counit presents the universal left-derived functor.
Source: Stacks 06YY; scalar-extension clauses (1), (4)
(blueprint: lem-sp-scalar-extension-site-calculus). -/
theorem complexCounitNat_kan
    {B : Type u₁} [Category.{v₁} B] [Abelian B] [HasDerivedCategory.{w₁} B]
    {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasDerivedCategory.{w₂} D]
    (E : B ⥤ D) [E.Additive] (L : DerivedCategory B ⥤ DerivedCategory D)
    (ε : DerivedCategory.Qh ⋙ L ⟶
      E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    [L.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso B (.up ℤ))] :
    L.IsLeftDerivedFunctor (complexCounitNat E L ε)
      (HomologicalComplex.quasiIso B (.up ℤ)) := by
  have : L.IsRightKanExtension ε :=
    Functor.IsLeftDerivedFunctor.isRightKanExtension L ε
      (HomotopyCategory.quasiIso B (.up ℤ))
  have := kan_precomp_quotient (HomotopyCategory.quotient B (.up ℤ))
    DerivedCategory.Qh
    (E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) L ε
  let q := HomotopyCategory.quotient B (.up ℤ)
  let j : q ⋙ (E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) ≅
      E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (E.mapHomotopyCategoryFactors (.up ℤ)) _ ≪≫
        Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso D)
  let α := (Functor.associator q DerivedCategory.Qh L).hom ≫ whiskerLeft q ε
  have hh := kan_change_iso L (DerivedCategory.quotientCompQhIso B) j α
  constructor
  simpa only [complexCounitNat, α, j, Category.assoc] using hh



/-- Derived natural transformations agree if they agree on K-flat counit representatives.
Source: Stacks 06YY; scalar-extension clauses (1), (4)
(blueprint: lem-sp-scalar-extension-site-calculus). -/
theorem derived_natTrans_ext
    {B : Type u} [Category.{v} B] [Abelian B] [HasDerivedCategory.{w} B]
    {D : Type u'} [Category.{v'} D] (F G : DerivedCategory B ⥤ D)
    (S : CochainComplex B ℤ → Prop)
    (hres : ∀ X : CochainComplex B ℤ, ∃ (P : CochainComplex B ℤ) (p : P ⟶ X),
      S P ∧ QuasiIso p)
    (α β : F ⟶ G) (h : ∀ P, S P → α.app (DerivedCategory.Q.obj P) =
      β.app (DerivedCategory.Q.obj P)) : α = β := by
  apply NatTrans.ext
  funext X
  obtain ⟨K, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage DerivedCategory.Q X
  obtain ⟨P, p, hP, hp⟩ := hres K
  have : IsIso (DerivedCategory.Q.map p) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso B p).2 hp
  let i : DerivedCategory.Q.obj P ≅ X := asIso (DerivedCategory.Q.map p) ≪≫ e
  apply (cancel_epi (F.map i.hom)).1
  rw [α.naturality, β.naturality, h P hP]

/-- A derived transformation is invertible when its K-flat components are invertible.
Source: Stacks 06YY; scalar-extension clauses (1), (4)
(blueprint: lem-sp-scalar-extension-site-calculus). -/
theorem derived_natTrans_isIso
    {B : Type u} [Category.{v} B] [Abelian B] [HasDerivedCategory.{w} B]
    {D : Type u'} [Category.{v'} D] (F G : DerivedCategory B ⥤ D)
    (S : CochainComplex B ℤ → Prop)
    (hres : ∀ X : CochainComplex B ℤ, ∃ (P : CochainComplex B ℤ) (p : P ⟶ X),
      S P ∧ QuasiIso p)
    (α : F ⟶ G) (h : ∀ P, S P → IsIso (α.app (DerivedCategory.Q.obj P))) :
    IsIso α := by
  have hi (X : DerivedCategory B) : IsIso (α.app X) := by
    obtain ⟨K, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage DerivedCategory.Q X
    obtain ⟨P, p, hP, hp⟩ := hres K
    have : IsIso (DerivedCategory.Q.map p) :=
      (DerivedCategory.isIso_Q_map_iff_quasiIso B p).2 hp
    have := h P hP
    let i : DerivedCategory.Q.obj P ≅ X := asIso (DerivedCategory.Q.map p) ≪≫ e
    have eq : α.app X = inv (F.map i.hom) ≫ α.app (DerivedCategory.Q.obj P) ≫
        G.map i.hom := by
      rw [← α.naturality, IsIso.inv_hom_id_assoc]
    rw [eq]
    infer_instance
  exact NatIso.isIso_of_isIso_app α

/-- Ordinary balancing applied degreewise gives a cochain-complex isomorphism.
Source: Stacks 06YY; scalar-extension clauses (1), (4)
(blueprint: lem-sp-scalar-extension-site-calculus). -/
def siteScalarRawComplexIso (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S)
    (P : CochainComplex (siteScalarModules T R) ℤ) :
    (siteScalarChangeComplex T φ).obj P ≅ SheafOfModules.changeOfRingsComplex.{t + 1, t} φ P := by
  let h : ∀ M : siteScalarModules T R, (siteScalarChange T φ).obj M =
      SheafOfModules.changeOfRings.{t, t + 1, t + 1} φ M :=
    siteScalarChange_obj_eq T φ
  refine HomologicalComplex.Hom.isoOfComponents (fun p ↦ eqToIso (h (P.X p))) ?_
  intro p q hpq
  have hd := siteScalarChange_map_eq T φ (P.d p q)
  change (siteScalarChange T φ).map (P.d p q) = _ at hd
  change eqToHom (h (P.X p)) ≫
      SheafOfModules.changeOfRingsHom φ (P.X p) (P.d p q) =
    (siteScalarChange T φ).map (P.d p q) ≫ eqToHom (h (P.X q))
  rw [hd]
  simp

/-- Ordinary scalar extension carries K-flat complexes to K-flat complexes.
Source: Stacks 06YY; scalar-extension clauses (1), (4)
(blueprint: lem-sp-scalar-extension-site-calculus). -/
theorem siteScalarChange_isKFlat (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S)
    (P : CochainComplex (siteScalarModules T R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := R) P)
    (hflat : ∀ i : ℤ, exactFunctor _ _
      (@MonoidalCategory.tensorRight _ _ (SheafOfModules.monoidalCategory R) (P.X i))) :
    CochainComplex.IsKFlatIndependentCoefficients (R := S)
      ((siteScalarChangeComplex T φ).obj P) := by
  let _ := SheafOfModules.monoidalCategory S
  have hflat' (i : ℤ) : exactFunctor _ _
      (@MonoidalCategory.tensorRight _ _ (SheafOfModules.monoidalCategory R) (P.X i)) := by
    exact hflat i
  have hk := (SheafOfModules.changeOfRings_isKFlat_of_flat_terms.{t + 1, t} φ P hP hflat').1
  intro F hF i
  have e := (((MonoidalCategory.curriedTensor _).mapBifunctorHomologicalComplex (.up ℤ)
    (.up ℤ)).obj F).mapIso (siteScalarRawComplexIso T φ P)
  exact (hk F hF i).of_iso (HomologicalComplex₂.total.mapIso e (.up ℤ)).symm

/-- The complex counit is invertible on a K-flat representative.
Source: Stacks 06YY; scalar-extension clauses (1), (4)
(blueprint: lem-sp-scalar-extension-site-calculus). -/
theorem scalarCounit_isIso (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S)
    (P : CochainComplex (siteScalarModules T R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := R) P) :
    IsIso (siteScalarScalarComplexCounit T φ P) := by
  have : IsIso ((siteScalarDerivedCounit T φ).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) :=
    siteScalarDerivedCounit_isIso T φ P hP
  dsimp only [siteScalarScalarComplexCounit, siteScalarComplexCounit]
  infer_instance

/-- The natural complex balancing comparison after localization.
Source: Stacks 06YY; scalar-extension clauses (1), (4)
(blueprint: lem-sp-scalar-extension-site-calculus). -/
def balanceNat (T : Scheme.{t})
    {R S U : Sheaf (ProEt.topology T) CommRingCat.{t + 1}}
    (φ : R ⟶ S) (ψ : S ⟶ U) (χ : R ⟶ U) (h : φ ≫ ψ = χ) :
    siteScalarChangeComplex T φ ⋙ siteScalarChangeComplex T ψ ⟶ siteScalarChangeComplex T χ where
  app P := siteScalarBalance T φ ψ χ h P
  naturality _ _ f := siteScalarBalance_naturality T φ ψ χ h f

/-- Successive derived extension is canonically isomorphic to direct extension.
Source: Stacks 06YY; scalar-extension clauses (1), (4)
(blueprint: lem-sp-scalar-extension-site-calculus). -/
theorem derivedReductionComposition (T : Scheme.{t})
    {R S U : Sheaf (ProEt.topology T) CommRingCat.{t + 1}}
    (φ : R ⟶ S) (ψ : S ⟶ U) (χ : R ⟶ U) (h : φ ≫ ψ = χ) :
    ∃! τ : siteScalarDerivedChange T φ ⋙ siteScalarDerivedChange T ψ ⟶ siteScalarDerivedChange T χ,
      IsIso τ ∧ ∀ P : CochainComplex (siteScalarModules T R) ℤ,
        CochainComplex.IsKFlatIndependentCoefficients (R := R) P →
        τ.app (DerivedCategory.Q.obj P) ≫ siteScalarScalarComplexCounit T χ P =
          (siteScalarDerivedChange T ψ).map (siteScalarScalarComplexCounit T φ P) ≫
          siteScalarScalarComplexCounit T ψ ((siteScalarChangeComplex T φ).obj P) ≫
          DerivedCategory.Q.map (siteScalarBalance T φ ψ χ h P) := by
  let eφ := complexCounitNat (siteScalarChange T φ) (siteScalarDerivedChange T φ)
    (siteScalarDerivedCounit T φ)
  let eψ := complexCounitNat (siteScalarChange T ψ) (siteScalarDerivedChange T ψ)
    (siteScalarDerivedCounit T ψ)
  let eχ := complexCounitNat (siteScalarChange T χ) (siteScalarDerivedChange T χ)
    (siteScalarDerivedCounit T χ)
  have := complexCounitNat_kan (siteScalarChange T χ) (siteScalarDerivedChange T χ)
    (siteScalarDerivedCounit T χ)
  let L := siteScalarDerivedChange T φ ⋙ siteScalarDerivedChange T ψ
  let β : DerivedCategory.Q ⋙ L ⟶ siteScalarChangeComplex T χ ⋙ DerivedCategory.Q :=
    (Functor.associator _ _ _).inv ≫ whiskerRight eφ (siteScalarDerivedChange T ψ) ≫
      (Functor.associator _ _ _).hom ≫ whiskerLeft (siteScalarChangeComplex T φ) eψ ≫
      (Functor.associator _ _ _).inv ≫ whiskerRight (balanceNat T φ ψ χ h) DerivedCategory.Q
  let τ := (siteScalarDerivedChange T χ).leftDerivedLift eχ
    (HomologicalComplex.quasiIso (siteScalarModules T R) (.up ℤ)) L β
  have ht (P : CochainComplex (siteScalarModules T R) ℤ) :
      τ.app (DerivedCategory.Q.obj P) ≫ siteScalarScalarComplexCounit T χ P =
        (siteScalarDerivedChange T ψ).map (siteScalarScalarComplexCounit T φ P) ≫
        siteScalarScalarComplexCounit T ψ ((siteScalarChangeComplex T φ).obj P) ≫
        DerivedCategory.Q.map (siteScalarBalance T φ ψ χ h P) := by
    have hf := (siteScalarDerivedChange T χ).leftDerived_fac_app eχ
      (HomologicalComplex.quasiIso (siteScalarModules T R) (.up ℤ)) L β P
    change τ.app (DerivedCategory.Q.obj P) ≫ eχ.app P = β.app P at hf
    have hb : β.app P =
        (siteScalarDerivedChange T ψ).map (siteScalarScalarComplexCounit T φ P) ≫
        siteScalarScalarComplexCounit T ψ ((siteScalarChangeComplex T φ).obj P) ≫
        DerivedCategory.Q.map (siteScalarBalance T φ ψ χ h P) := by
      change (𝟙 _ ≫ (siteScalarDerivedChange T ψ).map (eφ.app P) ≫
        𝟙 _ ≫ eψ.app ((siteScalarChangeComplex T φ).obj P) ≫
        𝟙 _ ≫ DerivedCategory.Q.map (siteScalarBalance T φ ψ χ h P)) = _
      simp only [Category.id_comp, eφ, eψ, complexCounitNat_app]
    have hc : eχ.app P = siteScalarScalarComplexCounit T χ P :=
      complexCounitNat_app _ _ _ _
    rw [hc] at hf
    exact hf.trans hb
  let S₀ (P : CochainComplex (siteScalarModules T R) ℤ) :=
    CochainComplex.IsKFlatIndependentCoefficients (R := R) P ∧
      ∀ i : ℤ, exactFunctor _ _
        (@MonoidalCategory.tensorRight _ _ (SheafOfModules.monoidalCategory R) (P.X i))
  have hres (X : CochainComplex (siteScalarModules T R) ℤ) :
      ∃ (P : CochainComplex (siteScalarModules T R) ℤ) (p : P ⟶ X), S₀ P ∧ QuasiIso p := by
    obtain ⟨P, p, hk, hf, hp, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := R) X
    exact ⟨P, p, ⟨hk, hf⟩, hp⟩
  refine ⟨τ, ⟨?_, fun P _ ↦ ht P⟩, ?_⟩
  · apply derived_natTrans_isIso L (siteScalarDerivedChange T χ) S₀ hres τ
    intro P hP
    have := scalarCounit_isIso T φ P hP.1
    have := scalarCounit_isIso T χ P hP.1
    have := scalarCounit_isIso T ψ ((siteScalarChangeComplex T φ).obj P)
      (siteScalarChange_isKFlat T φ P hP.1 hP.2)
    have : IsIso (τ.app (DerivedCategory.Q.obj P) ≫ siteScalarScalarComplexCounit T χ P) := by
      rw [ht P]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (siteScalarScalarComplexCounit T χ P)
  · intro τ' hτ'
    apply derived_natTrans_ext L (siteScalarDerivedChange T χ) S₀ hres
    intro P hP
    have := scalarCounit_isIso T χ P hP.1
    apply (cancel_mono (siteScalarScalarComplexCounit T χ P)).1
    exact (hτ'.2 P hP.1).trans (ht P).symm


/-- Derived tensor is left adjoint to exact derived restriction for arbitrary ring sheaves.
Source: Stacks 06YY and 0DVC; scalar-extension clause (1)
(blueprint: lem-sp-scalar-extension-site-calculus).
Proof: the ordinary object and map equations identify the chosen tensor presentation.
Apply the normalized derived coefficient adjunction to that presentation and its
specified universal left-derived pair. This proves existence, without choosing or
publishing a new adjunction datum. -/
theorem siteScalarDerivedAdjunction_exists (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S) :
    Nonempty (siteScalarDerivedChange T φ ⊣ (siteScalarRestrict T φ).mapDerivedCategory) := by
  let h := siteScalarChange_obj_eq T φ
  have hm {M N : siteScalarModules T R} (f : M ⟶ N) :
      (siteScalarChange T φ).map f = eqToHom (h M) ≫
        SheafOfModules.changeOfRingsHom φ M f ≫ eqToHom (h N).symm :=
    siteScalarChange_map_eq T φ f
  obtain ⟨_, _, hex⟩ := SheafOfModules.sheafRingDerivedCoefficientAdjunction
    (J := ProEt.topology T) φ
  obtain ⟨_, _, hder⟩ := hex (siteScalarChange T φ) h hm
  obtain ⟨adj, _⟩ := hder (siteScalarDerivedChange T φ) (siteScalarDerivedCounit T φ)
    (siteScalarDerivedUniversal T φ)
  exact ⟨adj⟩

end AlgebraicGeometry.Scheme
