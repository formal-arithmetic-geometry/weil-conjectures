/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Field.ULift
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.ProEtaleCoefficients.DerivedNakayamaResolution
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedOrdinaryCompactCohomology
public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
import WeilConjectures.AlgebraicGeometry.CondensedGeometricPoint.CondensedCoefficientPoint
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.FinitePointSectionsExact
import Mathlib.CategoryTheory.ObjectProperty.Equivalence
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientIsoConstructible
import all WeilConjectures.AlgebraicGeometry.Integral.IntegralCoefficientExtComparison
import all WeilConjectures.ProEtaleCoefficients.DerivedNakayamaResolution
import Mathlib.Algebra.CharP.CharAndCard
import WeilConjectures.CategoryTheory.ModuleObjects.FinitelyPresentedComap
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Evaluation.ContractibleRealizationOrdinaryUnit
import WeilConjectures.CategoryTheory.ModuleObjects.RegularEndBijective
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Reflective
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful

/-! # Coefficient and scalar realization at the geometric point
Source: latest blueprint sk-lem-finite, first proof paragraph
(blueprint: lem-sf-finite-point-scalar-realization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [instance 20000] HasDerivedCategory.ofIsGrothendieckAbelian
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open CategoryTheory.MonObj
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The restriction of the actual
terminal-sections functor to constructible finite-Tor objects.
Source: sk-lem-finite, point identification
(blueprint: lem-sf-finite-point-scalar-realization). -/
def FinitePointScalarRealizationData
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (k : Type u) [Field k] : Prop :=
  ∃ h : ∀ K : ConstantModelConstructibleFiniteTor Λ (Spec (.of k)),
      DerivedCategory.IsPerfectRingComplex.{u + 1, u + 1}
        ((condensedRingCoefficientSections Λ (Spec (.of k))).rightDerivedFunctor.obj K.obj),
    (ObjectProperty.lift
      (DerivedCategory.IsPerfectRingComplex.{u + 1, u + 1} (R := MonObj.Γ Λ) :
        ObjectProperty (DerivedCategory.{u + 1} (ModuleCat.{u + 1} (MonObj.Γ Λ))))
      ((constantModelBoundedConstructible Λ (Spec (.of k)) ⊓
          DerivedCategory.finiteTorAmplitude _).ι ⋙
        (condensedRingCoefficientSections Λ (Spec (.of k))).rightDerivedFunctor) h
      ).IsEquivalence

private def regularSectionIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] :
    (InternalAbelianSheafModule.sectionModuleEquivalence
      (coherentTopology Profinite.{u}) Λ).functor.obj (Mod.regular Λ) ≅
      SheafOfModules.unit ((sheafCompose (coherentTopology Profinite.{u})
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (condensedSectionRing Λ)) := by
  apply (SheafOfModules.fullyFaithfulForget _).preimageIso
  refine PresheafOfModules.isoMk (fun Z ↦ ?_) ?_
  · refine ModuleCat.isoMk (Iso.refl _) ?_
    intro r
    apply ConcreteCategory.hom_ext
    intro m
    rfl
  · intro Z W f
    ext
    rfl

private def regularSectionEquiv
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (M : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ) :
    (Mod.regular Λ ⟶ M) ≃
      (Evaluation.sections (coherentTopology Profinite.{u}) Λ (⊤_ Profinite.{u})).obj M :=
  let e := InternalAbelianSheafModule.sectionModuleEquivalence
    (coherentTopology Profinite.{u}) Λ
  e.fullyFaithfulFunctor.homEquiv.trans
    ((Iso.homCongr (regularSectionIso Λ) (Iso.refl _)).trans
      ((SheafOfModules.unitHomEquiv (e.functor.obj M)).trans
        (Evaluation.terminalSectionsEquiv (⊤_ Profinite.{u}) terminalIsTerminal
          (e.functor.obj M))))

private theorem regularSectionEquiv_apply
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (M : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ)
    (f : Mod.regular Λ ⟶ M) :
    regularSectionEquiv Λ M f =
      (Evaluation.sections (coherentTopology Profinite.{u}) Λ
        (⊤_ Profinite.{u})).map f (1 : condensedScalarRing Λ) := by
  rfl

private def scalarSectionHom
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] : MonObj.Γ Λ →+* condensedScalarRing Λ where
  toFun s := regularSectionEquiv Λ (Mod.regular Λ) (Mod.regularEndRingHom s)
  map_one' := by
    rw [map_one, regularSectionEquiv_apply]
    change (Evaluation.sections (coherentTopology Profinite.{u}) Λ
      (⊤_ Profinite.{u})).map (𝟙 (Mod.regular Λ)) (1 : condensedScalarRing Λ) =
        (1 : condensedScalarRing Λ)
    rfl
  map_mul' s t := by
    let S := Evaluation.sections (coherentTopology Profinite.{u}) Λ (⊤_ Profinite.{u})
    let ms : condensedScalarRing Λ →ₗ[condensedScalarRing Λ] condensedScalarRing Λ :=
      (S.map (Mod.regularEndRingHom s)).hom
    let mt : condensedScalarRing Λ →ₗ[condensedScalarRing Λ] condensedScalarRing Λ :=
      (S.map (Mod.regularEndRingHom t)).hom
    rw [map_mul]
    change S.map (Mod.regularEndRingHom t ≫ Mod.regularEndRingHom s)
      (1 : condensedScalarRing Λ) = _
    rw [S.map_comp]
    change ms (mt 1) = ms 1 * mt 1
    calc
      ms (mt 1) = mt 1 * ms 1 := by
        simpa only [smul_eq_mul, _root_.mul_one] using ms.map_smul (mt 1) 1
      _ = ms 1 * mt 1 := mul_comm _ _
  map_zero' := by
    rw [map_zero, regularSectionEquiv_apply, Functor.map_zero]
    rfl
  map_add' s t := by
    simp only [regularSectionEquiv_apply, map_add]
    rfl

private def scalarSectionEquiv
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] : MonObj.Γ Λ ≃+* condensedScalarRing Λ :=
  RingEquiv.ofBijective (scalarSectionHom Λ)
    ((regularSectionEquiv Λ (Mod.regular Λ)).bijective.comp Mod.regularEndRingHom_bijective)

private def pointCoyoneda
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] :=
  coyonedaSections ((Mod.regularEndRingHom.op).comp
    (RingEquiv.toOpposite (MonObj.Γ Λ)).toRingHom)

private def pointCoyonedaIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] :
    pointCoyoneda Λ ≅ Evaluation.sections (coherentTopology Profinite.{u}) Λ
      (⊤_ Profinite.{u}) ⋙ ModuleCat.restrictScalars.{u + 1} (scalarSectionEquiv Λ).toRingHom := by
  let S := Evaluation.sections (coherentTopology Profinite.{u}) Λ (⊤_ Profinite.{u})
  refine NatIso.ofComponents (fun M ↦ ?_) ?_
  · apply LinearEquiv.toModuleIso (X₁ := (pointCoyoneda Λ).obj M)
      (X₂ := (S ⋙ ModuleCat.restrictScalars.{u + 1}
        (scalarSectionEquiv Λ).toRingHom).obj M)
    refine
      { toEquiv := regularSectionEquiv Λ M
        map_add' := fun f g ↦ by
          change S.map (f + g) (1 : condensedScalarRing Λ) =
            S.map f (1 : condensedScalarRing Λ) + S.map g (1 : condensedScalarRing Λ)
          rw [S.map_add]
          rfl
        map_smul' := fun s f ↦ by
          change S.map (Mod.regularEndRingHom s ≫ f) (1 : condensedScalarRing Λ) =
            scalarSectionHom Λ s • S.map f (1 : condensedScalarRing Λ)
          rw [S.map_comp]
          let lf : condensedScalarRing Λ →ₗ[condensedScalarRing Λ] S.obj M := (S.map f).hom
          change lf (scalarSectionHom Λ s) = scalarSectionHom Λ s • lf 1
          simpa only [smul_eq_mul, _root_.mul_one] using
            lf.map_smul (scalarSectionHom Λ s) 1 }
  · intro M N f
    ext g
    change S.map (g ≫ f) (1 : condensedScalarRing Λ) =
      S.map f (S.map g (1 : condensedScalarRing Λ))
    rw [S.map_comp]
    rfl

private def sectionsPullbackIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (k : Type u) [Field k] [IsAlgClosed k] :
    pointCoyoneda Λ ≅ ((upperStarFromPoint (Spec (.of k))).mapMod Λ) ⋙
      condensedRingCoefficientSections Λ (Spec (.of k)) := by
  let H := (upperStarFromPoint (Spec (.of k))).mapMod Λ
  let c₁ := (Mod.regularEndRingHom.op).comp
    (RingEquiv.toOpposite (MonObj.Γ Λ)).toRingHom
  let c₂ := (Mod.regularEndRingHom.op).comp
    ((RingEquiv.toOpposite _).toRingHom.comp
      (condensedRingScalarSections Λ (Spec (.of k))))
  have h (a : MonObj.Γ Λ) : (Iso.refl (H.obj (Mod.regular Λ))).inv ≫
      H.map (c₁ a).unop = (c₂ ((RingHom.id _) a)).unop ≫
        (Iso.refl (H.obj (Mod.regular Λ))).inv := by
    simp only [Iso.refl_inv, Category.id_comp]
    exact Functor.mapMod_map_regularEndRingHom (upperStarFromPoint (Spec (.of k))) Λ a
  let τ := coyonedaSectionsMap (RingHom.id _) c₁ c₂ H (Iso.refl _) h
  have (M : _) : IsIso (τ.app M) := by
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    change Function.Bijective (fun f ↦ 𝟙 _ ≫ H.map f)
    simpa only [Category.id_comp] using
      (Functor.FullyFaithful.ofFullyFaithful H).map_bijective (Mod.regular Λ) M
  have : IsIso τ := NatIso.isIso_of_isIso_app _
  exact asIso τ

private def actualSectionsHeartIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (k : Type u) [Field k] [IsAlgClosed k] :
    condensedRingCoefficientSections Λ (Spec (.of k)) ≅
      CondensedGeometricPoint.heartFiber Λ k ⋙
        ModuleCat.restrictScalars.{u + 1} (scalarSectionEquiv Λ).toRingHom := by
  let e := ((upperStarFromPoint (Spec (.of k))).mapMod Λ).asEquivalence
  let F := condensedRingCoefficientSections Λ (Spec (.of k))
  exact (Functor.leftUnitor F).symm ≪≫
    Functor.isoWhiskerRight e.counitIso.symm F ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft e.inverse (sectionsPullbackIso Λ k).symm ≪≫
    Functor.isoWhiskerLeft e.inverse (pointCoyonedaIso Λ) ≪≫
    (Functor.associator _ _ _).symm

private def local_heartFiberDerivedIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (k : Type u) [Field k] [IsAlgClosed k] :
    (CondensedGeometricPoint.heartFiber Λ k).mapDerivedCategory ≅
      CondensedGeometricPoint.fiber Λ k := by
  let e := ((upperStarFromPoint (Spec (.of k))).mapMod Λ).asEquivalence
  let S := CondensedRing.Evaluation.sections (coherentTopology Profinite.{u}) Λ
    (⊤_ Profinite.{u})
  let := Functor.additive_of_preserves_binary_products e.inverse
  exact Functor.mapDerivedCategoryCompIso e.inverse S ≪≫
    Functor.isoWhiskerLeft e.inverse.mapDerivedCategory
      S.rightDerivedFunctorIsoMapDerivedCategory.symm

private def actualSectionsDerivedIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (k : Type u) [Field k] [IsAlgClosed k] :
    (condensedRingCoefficientSections Λ (Spec (.of k))).rightDerivedFunctor ≅
      CondensedGeometricPoint.fiber Λ k ⋙
        (ModuleCat.restrictScalars.{u + 1}
          (scalarSectionEquiv Λ).toRingHom).mapDerivedCategory := by
  have := (finite_point_sections_exact Λ k).1
  have := (finite_point_sections_exact Λ k).2
  exact Functor.rightDerivedFunctorIsoMapDerivedCategory _ ≪≫
    Functor.mapDerivedCategoryNatIso (actualSectionsHeartIso Λ k) ≪≫
    Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.isoWhiskerRight (local_heartFiberDerivedIso Λ k) _

private theorem perfect_restrictScalars
    {R S : Type (u + 1)} [CommRing R] [CommRing S] (e : R ≃+* S)
    (K : DerivedCategory.{u + 1} (ModuleCat.{u + 1} S))
    (hK : DerivedCategory.IsPerfectRingComplex K) :
    DerivedCategory.IsPerfectRingComplex
      ((ModuleCat.restrictScalars.{u + 1} e.toRingHom).mapDerivedCategory.obj K) := by
  let F := ModuleCat.restrictScalars.{u + 1} e.toRingHom
  obtain ⟨P, a, b, hge, hle, hfin, ⟨i⟩⟩ := hK
  let Q := (F.mapHomologicalComplex (.up ℤ)).obj P
  refine ⟨Q, a, b, inferInstance, inferInstance, ?_,
    ⟨F.mapDerivedCategory.mapIso i ≪≫ F.mapDerivedCategoryFactors.app P⟩⟩
  intro j
  let M := P.X j
  let N := F.obj M
  let : RingHomInvPair e.toRingHom e.symm.toRingHom :=
    ⟨e.symm_toRingHom_comp_toRingHom, e.toRingHom_comp_symm_toRingHom⟩
  let : RingHomInvPair e.symm.toRingHom e.toRingHom :=
    ⟨e.toRingHom_comp_symm_toRingHom, e.symm_toRingHom_comp_toRingHom⟩
  let : RingHomSurjective e.toRingHom := ⟨e.surjective⟩
  let f : N ≃ₛₗ[e.toRingHom] M :=
    { toEquiv := Equiv.refl _
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  have := (hfin j).1
  have := (hfin j).2
  exact ⟨Module.Projective.of_equiv f.symm,
    (f.toLinearMap.finite_iff_of_bijective f.bijective).mpr inferInstance⟩

private theorem perfect_of_iso
    {R : Type (u + 1)} [CommRing R]
    {K L : DerivedCategory.{u + 1} (ModuleCat.{u + 1} R)} (i : K ≅ L)
    (hK : DerivedCategory.IsPerfectRingComplex K) :
    DerivedCategory.IsPerfectRingComplex L := by
  obtain ⟨P, a, b, ha, hb, hP, ⟨e⟩⟩ := hK
  exact ⟨P, a, b, ha, hb, hP, ⟨i.symm ≪≫ e⟩⟩

private theorem perfect_restrictScalars_iff
    {R S : Type (u + 1)} [CommRing R] [CommRing S] (e : R ≃+* S)
    (K : DerivedCategory.{u + 1} (ModuleCat.{u + 1} S)) :
    DerivedCategory.IsPerfectRingComplex K ↔
      DerivedCategory.IsPerfectRingComplex
        ((ModuleCat.restrictScalars.{u + 1} e.toRingHom).mapDerivedCategory.obj K) := by
  constructor
  · exact perfect_restrictScalars e K
  · intro h
    let d := (ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{u + 1} e).mapDerivedCategory
    exact perfect_of_iso (d.unitIso.app K).symm (perfect_restrictScalars e.symm _ h)

private theorem restrict_equivalence_transport
    {C D E : Type*} [Category C] [Category D] [Category E]
    (P : ObjectProperty C) (Q : ObjectProperty D) (R : ObjectProperty E)
    [R.IsClosedUnderIsomorphisms]
    (F : C ⥤ D) (G : C ⥤ E) (H : D ≌ E) (i : F ⋙ H.functor ≅ G)
    (hQR : ∀ X, Q X ↔ R (H.functor.obj X))
    (hF : ∀ X : P.FullSubcategory, Q (F.obj X.obj))
    [hf : (Q.lift (P.ι ⋙ F) hF).IsEquivalence] :
    ∃ hG : ∀ X : P.FullSubcategory, R (G.obj X.obj),
      (R.lift (P.ι ⋙ G) hG).IsEquivalence := by
  let e := H.congrFullSubcategory (P := Q) (Q := R) (by
    funext X
    exact propext (hQR X).symm)
  have hG (X : P.FullSubcategory) : R (G.obj X.obj) :=
    R.prop_of_iso (i.app X.obj) ((hQR _).mp (hF X))
  refine ⟨hG, ?_⟩
  let j : Q.lift (P.ι ⋙ F) hF ⋙ e.functor ≅ R.lift (P.ι ⋙ G) hG :=
    (R.fullyFaithfulι.whiskeringRight _).preimageIso (P.ι.isoWhiskerLeft i)
  exact Functor.isEquivalence_of_iso j

private theorem scalarRealization_of_statement
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (k : Type u) [Field k] [IsAlgClosed k]
    (hΛ : CondensedGeometricPoint.Statement Λ k) : FinitePointScalarRealizationData Λ k := by
  obtain ⟨hc, hp, hch, hph, hct, hpt, hF, hres⟩ := hΛ
  obtain ⟨m, hequiv, htri, hhom, hev, hdual⟩ := hres
  let P := CondensedGeometricPoint.ctf Λ k
  let Q := CondensedGeometricPoint.perfect Λ
  have : (Q.lift (P.ι ⋙ CondensedGeometricPoint.fiber Λ k) hF).IsEquivalence := hequiv
  let R : ObjectProperty (DerivedCategory.{u + 1} (ModuleCat.{u + 1} (MonObj.Γ Λ))) :=
    DerivedCategory.IsPerfectRingComplex
  let e := (ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{u + 1}
    (scalarSectionEquiv Λ)).mapDerivedCategory
  have : R.IsClosedUnderIsomorphisms := ⟨fun i h ↦ perfect_of_iso i h⟩
  exact restrict_equivalence_transport P Q R (CondensedGeometricPoint.fiber Λ k)
    (condensedRingCoefficientSections Λ (Spec (.of k))).rightDerivedFunctor e
    (actualSectionsDerivedIso Λ k).symm
    (fun K ↦ perfect_restrictScalars_iff (scalarSectionEquiv Λ) K) hF

private def globalScalarEquiv
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [MonObj Λ'] (e : Mon.mk Λ ≅ Mon.mk Λ') :
    MonObj.Γ Λ ≃+* MonObj.Γ Λ' :=
  { MonObj.Γ.map e.hom.hom with
    invFun := MonObj.Γ.map e.inv.hom
    left_inv := fun s ↦ by
      ext1
      simp only [MonObj.Γ.map_hom]
      exact congrArg (s.hom ≫ ·) (congrArg Mon.Hom.hom e.hom_inv_id)
    right_inv := fun s ↦ by
      ext1
      exact congrArg (s.hom ≫ ·) (congrArg Mon.Hom.hom e.inv_hom_id) }

private theorem comapRegularEnd
    {C : Type*} [Category C] [MonoidalCategory C] [Preadditive C]
    [MonoidalPreadditive C] [BraidedCategory C]
    {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (e : Mon.mk R ≅ Mon.mk S) (s : MonObj.Γ R) :
    (Mod.regularIsoComapRegular e.inv.hom).hom ≫
        (Mod.comap e.inv.hom).map (Mod.regularEndRingHom s) =
      Mod.regularEndRingHom (MonObj.Γ.map e.hom.hom s) ≫
        (Mod.regularIsoComapRegular e.inv.hom).hom := by
  apply Mod.regular_hom_ext
  change η[S] ≫ (e.inv.hom ≫ (Mod.regularEndRingHom s).hom) =
    η[S] ≫ ((Mod.regularEndRingHom (MonObj.Γ.map e.hom.hom s)).hom ≫ e.inv.hom)
  simp only [Mod.regularEndRingHom_apply]
  erw [← Category.assoc, IsMonHom.one_hom, Mod.one_comp_regularLift_regular,
    ← Category.assoc, Mod.one_comp_regularLift_regular, MonObj.Γ.map_hom,
    Category.assoc]
  have he : e.hom.hom ≫ e.inv.hom = 𝟙 R :=
    congrArg Mon.Hom.hom e.hom_inv_id
  erw [he, Category.comp_id]

private def coefficientEquivalence
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [MonObj Λ'] (e : Mon.mk Λ ≅ Mon.mk Λ') (X : Scheme.{u}) :=
  let q : condensedRingObj Λ X ≅ condensedRingObj Λ' X :=
    (upperStarFromPoint X).mapIso ((Mon.forget _).mapIso e)
  letI : IsMonHom q.hom := inferInstanceAs
    (IsMonHom ((upperStarFromPoint X).map e.hom.hom))
  letI : IsMonHom q.inv := inferInstanceAs
    (IsMonHom ((upperStarFromPoint X).map e.inv.hom))
  CategoryTheory.Equivalence.mk (Mod.comap q.inv) (Mod.comap q.hom)
    ((Mod.comapId _).symm ≪≫ Mod.comapCongr q.hom_inv_id.symm ≪≫
      Mod.comapComp q.hom q.inv)
    ((Mod.comapComp q.inv q.hom).symm ≪≫ Mod.comapCongr q.inv_hom_id ≪≫ Mod.comapId _)

private def coefficientSectionsIso
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [MonObj Λ'] [IsCommMonObj Λ] [IsCommMonObj Λ']
    (e : Mon.mk Λ ≅ Mon.mk Λ') (X : Scheme.{u}) :
    condensedRingCoefficientSections Λ X ≅ (coefficientEquivalence e X).functor ⋙
      condensedRingCoefficientSections Λ' X ⋙
        ModuleCat.restrictScalars.{u + 1} (globalScalarEquiv e).toRingHom := by
  let q : condensedRingObj Λ X ≅ condensedRingObj Λ' X :=
    (upperStarFromPoint X).mapIso ((Mon.forget _).mapIso e)
  letI : IsMonHom q.hom := inferInstanceAs
    (IsMonHom ((upperStarFromPoint X).map e.hom.hom))
  letI : IsMonHom q.inv := inferInstanceAs
    (IsMonHom ((upperStarFromPoint X).map e.inv.hom))
  let qM : Mon.mk (condensedRingObj Λ X) ≅ Mon.mk (condensedRingObj Λ' X) :=
    Mon.mkIso' q
  let H := (coefficientEquivalence e X).functor
  let i := (Mod.regularIsoComapRegular q.inv).symm
  let c₁ := (Mod.regularEndRingHom.op).comp
    ((RingEquiv.toOpposite _).toRingHom.comp (condensedRingScalarSections Λ X))
  let c₂ := (Mod.regularEndRingHom.op).comp
    ((RingEquiv.toOpposite _).toRingHom.comp (condensedRingScalarSections Λ' X))
  have h (s : MonObj.Γ Λ) : i.inv ≫ H.map (c₁ s).unop =
      (c₂ ((globalScalarEquiv e).toRingHom s)).unop ≫ i.inv := by
    have hs : MonObj.Γ.map q.hom (condensedRingScalarSections Λ X s) =
        condensedRingScalarSections Λ' X (MonObj.Γ.map e.hom.hom s) := by
      ext1
      simp only [MonObj.Γ.map_hom, condensedRingScalarSections,
        MonObj.Γ.mapFunctor_hom, Functor.map_comp, Category.assoc]
      rfl
    calc
      i.inv ≫ H.map (c₁ s).unop =
          Mod.regularEndRingHom
            (MonObj.Γ.map q.hom (condensedRingScalarSections Λ X s)) ≫ i.inv :=
        comapRegularEnd qM (condensedRingScalarSections Λ X s)
      _ = (c₂ ((globalScalarEquiv e).toRingHom s)).unop ≫ i.inv := by
        change Mod.regularEndRingHom
            (MonObj.Γ.map q.hom (condensedRingScalarSections Λ X s)) ≫ i.inv =
          Mod.regularEndRingHom
            (condensedRingScalarSections Λ' X (MonObj.Γ.map e.hom.hom s)) ≫ i.inv
        rw [hs]
  have : H.Additive := by
    change (Mod.comap q.inv).Additive
    infer_instance
  let τ := coyonedaSectionsMap (globalScalarEquiv e).toRingHom c₁ c₂ H i h
  have (M : _) : IsIso (τ.app M) := by
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    change Function.Bijective (fun f ↦ i.inv ≫ H.map f)
    constructor
    · intro f g hfg
      apply H.map_injective
      exact (cancel_epi i.inv).mp hfg
    · intro y
      obtain ⟨f, hf⟩ := H.map_surjective (i.hom ≫ y)
      refine ⟨f, ?_⟩
      change i.inv ≫ H.map f = y
      erw [hf, Iso.inv_hom_id_assoc]
  have : IsIso τ := NatIso.isIso_of_isIso_app _
  exact asIso τ

private theorem scalarRealization_coefficientIso
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [MonObj Λ'] [IsCommMonObj Λ] [IsCommMonObj Λ']
    (e : Mon.mk Λ ≅ Mon.mk Λ') (k : Type u) [Field k] [IsAlgClosed k]
    (hΛ' : FinitePointScalarRealizationData Λ' k) : FinitePointScalarRealizationData Λ k := by
  let X := Spec (.of k)
  let H := coefficientEquivalence e X
  have : H.functor.Additive := by
    change (Mod.comap ((upperStarFromPoint X).map e.inv.hom)).Additive
    infer_instance
  have : H.inverse.Additive := by
    change (Mod.comap ((upperStarFromPoint X).map e.hom.hom)).Additive
    infer_instance
  let d := H.mapDerivedCategory
  let P := constantModelBoundedConstructible Λ X ⊓ DerivedCategory.finiteTorAmplitude _
  let P' := constantModelBoundedConstructible Λ' X ⊓ DerivedCategory.finiteTorAmplitude _
  have : P.IsClosedUnderIsomorphisms := by
    have := (constantModelConstructibleFiniteTor_wellDefined Λ X).2.1
    have := (constantModelConstructibleFiniteTor_wellDefined Λ X).2.2.2.1
    infer_instance
  have : P'.IsClosedUnderIsomorphisms := by
    have := (constantModelConstructibleFiniteTor_wellDefined Λ' X).2.1
    have := (constantModelConstructibleFiniteTor_wellDefined Λ' X).2.2.2.1
    infer_instance
  have hp : P'.inverseImage d.functor = P := by
    funext K
    apply propext
    constructor
    · intro h
      exact P.prop_of_iso (d.unitIso.app K).symm
        (constantModelCtf_coefficientIso e.symm X ⟨_, h⟩)
    · intro h
      exact constantModelCtf_coefficientIso e X ⟨_, h⟩
  let t := d.congrFullSubcategory hp
  let A := (condensedRingCoefficientSections Λ X)
  let B := (condensedRingCoefficientSections Λ' X)
  let V := ModuleCat.restrictScalars.{u + 1} (globalScalarEquiv e).toRingHom
  have := (finite_point_sections_exact Λ k).1
  have := (finite_point_sections_exact Λ k).2
  have := (finite_point_sections_exact Λ' k).1
  have := (finite_point_sections_exact Λ' k).2
  let i : A.rightDerivedFunctor ≅
      d.functor ⋙ (B.rightDerivedFunctor ⋙ V.mapDerivedCategory) :=
    A.rightDerivedFunctorIsoMapDerivedCategory ≪≫
      Functor.mapDerivedCategoryNatIso (coefficientSectionsIso e X) ≪≫
      Functor.mapDerivedCategoryCompIso _ _ ≪≫
      Functor.isoWhiskerLeft H.functor.mapDerivedCategory
        (Functor.mapDerivedCategoryCompIso _ _ ≪≫
          Functor.isoWhiskerRight B.rightDerivedFunctorIsoMapDerivedCategory.symm _)
  let Q : ObjectProperty (DerivedCategory.{u + 1} (ModuleCat.{u + 1} (MonObj.Γ Λ))) :=
    DerivedCategory.IsPerfectRingComplex
  let Q' : ObjectProperty (DerivedCategory.{u + 1} (ModuleCat.{u + 1} (MonObj.Γ Λ'))) :=
    DerivedCategory.IsPerfectRingComplex
  have : Q.IsClosedUnderIsomorphisms := ⟨fun i h ↦ perfect_of_iso i h⟩
  obtain ⟨hF, hEq⟩ := hΛ'
  have := hEq
  obtain ⟨hG, hGEq⟩ := restrict_equivalence_transport P' Q' Q B.rightDerivedFunctor
    (B.rightDerivedFunctor ⋙ V.mapDerivedCategory)
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{u + 1}
      (globalScalarEquiv e)).mapDerivedCategory
    (Iso.refl _) (fun K ↦ perfect_restrictScalars_iff (globalScalarEquiv e) K) hF
  have := hGEq
  have hA (K : P.FullSubcategory) : Q (A.rightDerivedFunctor.obj K.obj) :=
    Q.prop_of_iso (i.app K.obj).symm (hG (t.functor.obj K))
  refine ⟨hA, ?_⟩
  let j : t.functor ⋙
      Q.lift (P'.ι ⋙ (B.rightDerivedFunctor ⋙ V.mapDerivedCategory)) hG ≅
      Q.lift (P.ι ⋙ A.rightDerivedFunctor) hA :=
    (Q.fullyFaithfulι.whiskeringRight _).preimageIso (P.ι.isoWhiskerLeft i.symm)
  exact Functor.isEquivalence_of_iso j

private def discreteCoefficientSheafIso
    (A : Type) [CommRing A] [TopologicalSpace A] [DiscreteTopology A] [IsTopologicalRing A]
    (B : Type u) [CommRing B] [TopologicalSpace B] [DiscreteTopology B] [IsTopologicalRing B]
    (e : A ≃+* B) :
    Profinite.continuousMapRingSheaf.{u} A ≅ Profinite.continuousCoefficientRingSheaf B := by
  let forward (S : Profinite.{u}ᵒᵖ) : ULift.{u + 1} C(S.unop, A) →+*
      ULift.{u + 1} C(S.unop, B) :=
    ULift.ringEquiv.symm.toRingHom.comp
      ((e.toRingHom.compLeftContinuous S.unop continuous_of_discreteTopology).comp
        ULift.ringEquiv.toRingHom)
  let backward (S : Profinite.{u}ᵒᵖ) : ULift.{u + 1} C(S.unop, B) →+*
      ULift.{u + 1} C(S.unop, A) :=
    ULift.ringEquiv.symm.toRingHom.comp
      ((e.symm.toRingHom.compLeftContinuous S.unop continuous_of_discreteTopology).comp
        ULift.ringEquiv.toRingHom)
  refine
    { hom := ⟨{ app := fun S ↦ RingCat.ofHom (forward S)
                naturality := by intros; rfl }⟩
      inv := ⟨{ app := fun S ↦ RingCat.ofHom (backward S)
                naturality := by intros; rfl }⟩
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · ext S f
    apply ULift.ext
    apply ContinuousMap.ext
    intro x
    exact e.symm_apply_apply _
  · ext S f
    apply ULift.ext
    apply ContinuousMap.ext
    intro x
    exact e.apply_symm_apply _

set_option maxHeartbeats 2000000 in
-- Comparing the spectral and embedded integer presentations unfolds large coefficient types.
private def quotientCoefficientIso
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (π : PadicAlgCl.integers ℓ E)
    (hπ : Ideal.span ({π} : Set _) = IsLocalRing.maximalIdeal _) (n : ℕ) :
    Mon.mk (CondensedGeometricPoint.residueRingObj.{u} ℓ E π n) ≅
      Mon.mk (DerivedNakayama.quotientRing ℓ (ULift.{u} E) n) := by
  let O := Padic.coefficientExtensionIntegers ℓ (ULift.{u} E)
  let e := integerLiftEquiv.{u} ℓ ⟨E.val, E.property⟩
  have hd := (Padic.extension_integers_dvr ℓ (ULift.{u} E)
    (Padic.coefficientExtensionAbsoluteValue ℓ (ULift.{u} E))
    (spectralNorm_extends (K := Padic ℓ) (L := ULift.{u} E))).choose_spec.choose_spec
  let : IsLocalRing O := hd.2.2.2.1
  have hm : Padic.coefficientExtensionMaximalIdeal ℓ (ULift.{u} E) =
      IsLocalRing.maximalIdeal O := IsLocalRing.eq_maximalIdeal hd.2.2.2.2.1
  have hg : Ideal.span ({Padic.coefficientExtensionUniformizer ℓ (ULift.{u} E)} : Set O) =
      Padic.coefficientExtensionMaximalIdeal ℓ (ULift.{u} E) :=
    hd.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hi : Padic.coefficientExtensionIdeal ℓ (ULift.{u} E) n =
      Ideal.map e.toRingHom ((Ideal.span ({π} : Set _)) ^ n) := by
    rw [Padic.coefficientExtensionIdeal, hg, hm, Ideal.map_pow, hπ]
    exact congrArg (fun I : Ideal O ↦ I ^ n)
      (IsLocalRing.map_ringEquiv_maximalIdeal e).symm
  let eq := Ideal.quotientEquiv _ _ e hi
  let A := PadicAlgCl.integers ℓ E ⧸ (Ideal.span ({π} : Set _)) ^ n
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := ⟨rfl⟩
  let nf := (Padic.coefficientExtensionAbsoluteValue ℓ (ULift.{u} E)).toNormedField
  letI : NormedField (ULift.{u} E) := nf
  letI : TopologicalSpace (ULift.{u} E) :=
    nf.toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  letI := DerivedNakayama.quotientDiscrete ℓ (ULift.{u} E) n
  let eR : CondensedGeometricPoint.residueRingSheaf.{u} ℓ E π n ≅
      DerivedNakayama.quotientRingSheaf ℓ (ULift.{u} E) n :=
    discreteCoefficientSheafIso A (Padic.coefficientExtensionRing ℓ (ULift.{u} E) n) eq
  let eA := (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso eR
  have : IsMonHom eA.hom := Sheaf.isMonHom_sheafCompose_map _ eR.hom
  exact Mon.mkIso' eA

/-- The point comparison in the precise coefficient coordinates used for ordinary
cohomology. This assertion has no scheme X, no direct-image claim and no cohomological
bound.

Source: latest blueprint sec-six-functors/sk-lem-finite/sk-lem-finite.proof.md,
first paragraph (blueprint: lem-sf-finite-point-scalar-realization).

Proof: identify the valuation ring chosen from the spectral absolute value with the
norm-at-most-one subring of E, using uniqueness of the extending absolute value. The
same identification after ULift respects the chosen uniformizer ideal, hence induces
the finite quotient isomorphisms. The quotient topology is discrete since the
uniformizer ideal powers are open. These continuous ring isomorphisms induce
isomorphisms of condensed rings. Admissibility is proved separately.
Terminal evaluation identifies Γ Λ with the section ring, including the coefficient
universe lift.
The equivalence induced by upperStarFromPoint identifies constructible finite-Tor
objects at Spec k with perfect condensed scalar complexes by
condensed_geometric_point_perfect. A section of an internal module is a module map
from the regular module, determined by its value on 1. This identifies the actual
coyoneda sections, with their Γ Λ action, with sectionwise terminal evaluation after
the inverse point equivalence. Exactness gives the comparison on ordinary derived
categories. Restrict the comparison to the full subcategories and transport through
the coefficient ring isomorphisms; full faithfulness and essential surjectivity are
preserved. No equivalence on ambient module categories with scalar modules is used.
-/
theorem finite_point_scalar_realization
    (D : WeilConjectures.FiniteFieldDatum.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (hℓ : ℓ ≠ D.p) (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    (∀ n : ℕ, 1 ≤ n → FinitePointScalarRealizationData
      (DerivedNakayama.quotientRing ℓ (ULift.{u} E) n) D.k) ∧
    FinitePointScalarRealizationData (DerivedNakayama.integerRing ℓ (ULift.{u} E)) D.k ∧
    FinitePointScalarRealizationData (Profinite.continuousMapRingObj.{u} E) D.k ∧
    FinitePointScalarRealizationData (Profinite.padicAlgClRingObj.{u} ℓ) D.k := by
  let : Fintype D.k₀ := Fintype.ofFinite D.k₀
  let : Fact D.p.Prime := ⟨D.prime⟩
  let : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
    ((Nat.card_eq_fintype_card (α := D.k₀)).symm.trans
      (D.card_base.trans D.cardinality_eq))
  let : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
  obtain ⟨π, hπ⟩ := PadicAlgCl.isPrincipal_maximalIdeal_integers ℓ E.val
  have hπ' : Ideal.span ({π} : Set _) = IsLocalRing.maximalIdeal _ := by
    simpa only [Ideal.submodule_span_eq] using hπ.symm
  have hp (n : ℕ) (hn : 1 ≤ n) :=
    CondensedGeometricPoint.condensed_geometric_point_perfect D.k D.p ℓ hℓ.symm E π hπ' n hn
  refine ⟨?_, ?_, scalarRealization_of_statement _ _ (hp 1 le_rfl).2.2.1,
    scalarRealization_of_statement _ _ (hp 1 le_rfl).2.2.2⟩
  · intro n hn
    exact scalarRealization_coefficientIso (quotientCoefficientIso ℓ E π hπ' n).symm D.k
      (scalarRealization_of_statement _ _ (hp n hn).1)
  · let eR := integerRingSheafIso.{u} ℓ ⟨E.val, E.property⟩
    let eA := (sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso eR
    have : IsMonHom eA.hom := Sheaf.isMonHom_sheafCompose_map _ eR.hom
    exact scalarRealization_coefficientIso (Mon.mkIso' eA).symm D.k
      (scalarRealization_of_statement _ _ (hp 1 le_rfl).2.1)

end AlgebraicGeometry.ProEtale.CondensedRing
