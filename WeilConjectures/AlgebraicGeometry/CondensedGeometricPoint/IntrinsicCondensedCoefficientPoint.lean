/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedGeometricPoint.CondensedCoefficientPoint
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.FlatCondensedScalarRealization
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicFiniteTorsionConstructibility
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatExtendScalars
public import WeilConjectures.SixFunctors.Etale.Derived.PointFiber
import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientDescentTwoColimit
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
public import Mathlib.RingTheory.Finiteness.Cardinality
public import WeilConjectures.AlgebraicGeometry.FiniteCoefficientDescentTwoColimitStatement
public import WeilConjectures.WeilObject.Sheaf.StalkFiniteFree

/-! # The ordinary coefficient categories at a geometric point

Source: current blueprint, `def-weil-finite-coefficient-point`, all paragraphs
(blueprint: def-weil-finite-coefficient-point).

The source category is the recorded internal-module bounded constructible category.
The target categories are full subcategories of ordinary derived module categories.
Universe lifts implement the size convention and do not alter the coefficient rings.
The final descent assertion is a consequence, separate from their definitions.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedGeometricPoint

/-- The single point of the terminal profinite set, specified without an arbitrary choice.
Source: blueprint, evaluation at the point (blueprint: def-weil-finite-coefficient-point). -/
def coefficientPoint : (⊤_ Profinite.{u}) :=
  (terminalIsTerminal.from (Profinite.of PUnit.{u + 1})) PUnit.unit

/-- Evaluation followed by the scalar identification, on the unbounded derived category.
Source: blueprint, Fib_s in the display (blueprint: def-weil-finite-coefficient-point). -/
def ordinaryPointFiber {R : Type (u + 1)} [CommRing R]
    (e : R ≃+* condensedScalarRing Λ) :
    Complexes Λ k ⥤ DerivedCategory (ModuleCat.{u + 1} R) :=
  fiber Λ k ⋙ (ModuleCat.restrictScalars e.toRingHom).mapDerivedCategory

/-- Scalar realization after changing the ordinary ring to its identified section ring.
This is the existing derived constant scalar realization, with its actual tensor maps.
Source: blueprint, specified quasi-inverse (blueprint: def-weil-finite-coefficient-point). -/
def ordinaryPointRealization {R : Type (u + 1)} [CommRing R]
    (e : R ≃+* condensedScalarRing Λ) :
    DerivedCategory (ModuleCat.{u + 1} R) ⥤ Complexes Λ k :=
  (ModuleCat.restrictScalars e.symm.toRingHom).mapDerivedCategory ⋙
    condensedScalarRealization Λ (Spec (.of k))

/-- The exact heart adjunction, flatness of coefficient sections, and the global finite
presentation classification. Both recorded constructibility notions agree at this point.
Source: blueprint, third paragraph (blueprint: def-weil-finite-coefficient-point). -/
def IntrinsicPointHeart : Prop :=
  (∀ S : Profinite.{u},
    (CondensedRing.scalarSectionMap (Mon.mk Λ) S).Flat) ∧
  PreservesFiniteLimits (heartFiber Λ k) ∧
  PreservesFiniteColimits (heartFiber Λ k) ∧
  PreservesFiniteLimits (CondensedRing.ordinaryScalarRealization (Mon.mk Λ) (Spec (.of k))) ∧
  PreservesFiniteColimits (CondensedRing.ordinaryScalarRealization (Mon.mk Λ) (Spec (.of k))) ∧
  (∃ adj : CondensedRing.ordinaryScalarRealization (Mon.mk Λ) (Spec (.of k)) ⊣ heartFiber Λ k,
    IsIso adj.unit) ∧
  (∀ M : Mod (Sheaf (Scheme.ProEt.topology (Spec (.of k))) Ab.{u + 1})
      (condensedRingObj Λ (Spec (.of k))),
    (IsConstructibleModuleObject (condensedRingObj Λ (Spec (.of k))) M ↔
      IsConstantModelConstructible Λ (Spec (.of k)) M) ∧
    (IsConstructibleModuleObject (condensedRingObj Λ (Spec (.of k))) M ↔
      ∃ P : ModuleCat.{u + 1} (condensedScalarRing Λ),
        Module.FinitePresentation (condensedScalarRing Λ) P ∧
          Nonempty ((CondensedRing.ordinaryScalarRealization (Mon.mk Λ)
            (Spec (.of k))).obj P ≅ M)))

private theorem constructible_of_finitelyPresented
    {X : Scheme.{u}} (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R)
    (hM : Mod.IsFinitelyPresented R M) : IsConstructibleModuleObject R M := by
  refine ⟨Scheme.Stratification.trivial X, fun a ↦ ?_⟩
  let F := upperStar Ab.{u + 1} ((Scheme.Stratification.trivial X).immersion a)
  have h₁ := hM.map (F.mapMod R) (Mod.isoMk (Iso.refl _) (by simp))
  refine ⟨.singleton (𝟙 _) (Precoverage.mem_coverings_of_isIso _), fun i ↦ ?_⟩
  let G := upperStar Ab.{u + 1} (𝟙 X)
  exact h₁.map (G.mapMod (F.obj R)) (Mod.isoMk (Iso.refl _) (by simp))

private theorem intrinsic_iff_constantModel
    (M : Mod (Sheaf (Scheme.ProEt.topology (Spec (.of k))) Ab.{u + 1})
      (condensedRingObj Λ (Spec (.of k)))) :
    IsConstructibleModuleObject (condensedRingObj Λ (Spec (.of k))) M ↔
      IsConstantModelConstructible Λ (Spec (.of k)) M := by
  let e := ((upperStarFromPoint (Spec (.of k))).mapMod Λ).asEquivalence
  let r : e.functor.obj (Mod.regular Λ) ≅
      Mod.regular (condensedRingObj Λ (Spec (.of k))) :=
    Mod.isoMk (Iso.refl _) (by simp)
  let := Functor.additive_of_preserves_binary_products e.functor
  rw [point_global_model]
  constructor
  · intro hM
    exact ⟨e.inverse.obj M, pointInverse_finitelyPresented_of_constructible Λ k M hM,
      ⟨e.counitIso.app M⟩⟩
  · rintro ⟨P, hp, ⟨i⟩⟩
    exact constructible_of_finitelyPresented _ M ((hp.map e.functor r).of_iso i)

private theorem intrinsic_heart_of_flat
    [IsNoetherianRing (condensedScalarRing Λ)]
    (hflat : ∀ S : Profinite.{u},
      (CondensedRing.scalarSectionMap (Mon.mk Λ) S).Flat) :
    IntrinsicPointHeart Λ k := by
  obtain ⟨ha, hl, hc, _⟩ := CondensedRing.flat_ordinaryScalarRealization
    (Mon.mk Λ) (fun S _ ↦ hflat S) (Spec (.of k))
  let := ha
  let := hl
  let := hc
  let adj := ordinary_adjunction Λ k
  have := heart_adjunction_unit Λ k _ adj
  refine ⟨hflat, inferInstance, inferInstance, hl, hc, ⟨adj, inferInstance⟩, fun M ↦ ?_⟩
  refine ⟨intrinsic_iff_constantModel Λ k M, ?_⟩
  rw [intrinsic_iff_constantModel Λ k M, heart_classification Λ k _ adj M]
  exact exists_congr fun P ↦ and_congr (Module.finitePresentation_iff_finite _ _).symm Iff.rfl

/-- The displayed equivalence with the ordinary coefficient category, with scalar
coordinates normalized by evaluation. Both functors are specified before their
membership witnesses, so the adjunction cannot select unrelated equivalence data.
Source: blueprint, four displayed equivalences and their inverse
(blueprint: def-weil-finite-coefficient-point). -/
def IntrinsicPointEquivalence (R : Type (u + 1)) [CommRing R]
    (Q : ObjectProperty (DerivedCategory (ModuleCat.{u + 1} R)))
    (value : condensedScalarRing Λ → R) : Prop :=
  ∃ e : R ≃+* condensedScalarRing Λ,
    (∀ a, e.symm a = value a) ∧
    ∃ (hF : ∀ K : (boundedConstructible (condensedRingObj Λ (Spec (.of k)))).FullSubcategory,
        Q ((ordinaryPointFiber Λ k e).obj K.obj))
      (hJ : ∀ P : Q.FullSubcategory,
        boundedConstructible (condensedRingObj Λ (Spec (.of k)))
          ((ordinaryPointRealization Λ k e).obj P.obj))
      (adj : (boundedConstructible (condensedRingObj Λ (Spec (.of k)))).lift
          (Q.ι ⋙ ordinaryPointRealization Λ k e) hJ ⊣
        Q.lift ((boundedConstructible (condensedRingObj Λ (Spec (.of k)))).ι ⋙
          ordinaryPointFiber Λ k e) hF),
      IsIso adj.unit ∧ IsIso adj.counit

private theorem finite_restrict {R S : Type (u + 1)} [CommRing R] [CommRing S]
    (e : R ≃+* S) (M : ModuleCat.{u + 1} S) [Module.Finite S M] :
    Module.Finite R ((ModuleCat.restrictScalars e.toRingHom).obj M) := by
  let : RingHomSurjective e.toRingHom := ⟨e.surjective⟩
  let f : ((ModuleCat.restrictScalars e.toRingHom).obj M) →ₛₗ[e.toRingHom] M :=
    { toFun := fun x ↦ x
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  exact (f.finite_iff_of_bijective Function.bijective_id).mpr inferInstance

private theorem bounded_finite_restrict {R S : Type (u + 1)} [CommRing R] [CommRing S]
    (e : R ≃+* S) (K : DerivedCategory (ModuleCat.{u + 1} S))
    (hK : _root_.DerivedCategory.boundedFiniteCohomology S K) :
    _root_.DerivedCategory.boundedFiniteCohomology R
      ((ModuleCat.restrictScalars e.toRingHom).mapDerivedCategory.obj K) := by
  let F := ModuleCat.restrictScalars e.toRingHom
  refine ⟨F.bounded_mapDerivedCategory_obj hK.1, fun i ↦ ?_⟩
  have := hK.2 i
  exact (Module.Finite.equiv_iff (R := R)
    (((F.mapDerivedCategoryHomologyFunctorIso i).app K).toLinearEquiv)).mp
      (finite_restrict e ((DerivedCategory.homologyFunctor _ i).obj K))

private theorem intrinsic_equivalence_at_coordinates
    (h : scalar_properties Λ)
    {R : Type (u + 1)} [CommRing R]
    (Q : ObjectProperty (DerivedCategory (ModuleCat.{u + 1} R)))
    (hQ : ∀ K, Q K ↔ _root_.DerivedCategory.boundedFiniteCohomology R K)
    (e : R ≃+* condensedScalarRing Λ) :
    ∃ (hF : ∀ K : (boundedConstructible (condensedRingObj Λ (Spec (.of k)))).FullSubcategory,
        Q ((ordinaryPointFiber Λ k e).obj K.obj))
      (hJ : ∀ P : Q.FullSubcategory, boundedConstructible
        (condensedRingObj Λ (Spec (.of k))) ((ordinaryPointRealization Λ k e).obj P.obj))
      (a : (boundedConstructible (condensedRingObj Λ (Spec (.of k)))).lift
          (Q.ι ⋙ ordinaryPointRealization Λ k e) hJ ⊣
        Q.lift ((boundedConstructible (condensedRingObj Λ (Spec (.of k)))).ι ⋙
          ordinaryPointFiber Λ k e) hF), IsIso a.unit ∧ IsIso a.counit := by
  obtain ⟨hl, hc, J, adj, hJl, hJc, hu, ⟨ha, ⟨eJ⟩⟩, hF, hJ, b, hbu, hbc⟩ :=
    direct_of_scalar_properties Λ k h
  let := hl
  let := hc
  let := hJl
  let := hJc
  let := ha
  let := hu
  let := hbc
  let H := ModuleCat.restrictScalars e.toRingHom
  let I := ModuleCat.restrictScalars e.symm.toRingHom
  let se := ModuleCat.restrictScalarsEquivalenceOfRingEquiv e
  let ae : I ⊣ H := se.symm.toAdjunction
  let de := ae.mapDerivedCategoryAdjunction
  let da := (adj.mapDerivedCategoryAdjunction.ofNatIsoLeft eJ).ofNatIsoRight
    (heartFiberDerivedIso Λ k)
  have : IsIso da.unit := by
    let ff := adj.mapDerivedCategoryAdjunction.fullyFaithfulLOfIsIsoUnit
    let := ff.full
    let := ff.faithful
    have : (condensedScalarRealization Λ (Spec (.of k))).Full := Functor.Full.of_iso eJ
    have : (condensedScalarRealization Λ (Spec (.of k))).Faithful :=
      Functor.Faithful.of_iso eJ
    infer_instance
  let a := de.comp da
  have : IsIso a.unit := by
    let ff := de.fullyFaithfulLOfIsIsoUnit
    let := ff.full
    let := ff.faithful
    let gg := da.fullyFaithfulLOfIsIsoUnit
    let := gg.full
    let := gg.faithful
    infer_instance
  have hP (K) : boundedConstructible (condensedRingObj Λ (Spec (.of k))) K ↔
      constantModelBoundedConstructible Λ (Spec (.of k)) K := by
    exact and_congr Iff.rfl (forall_congr' fun _i ↦ intrinsic_iff_constantModel Λ k _)
  have hF' (K : (boundedConstructible
      (condensedRingObj Λ (Spec (.of k)))).FullSubcategory) :
      Q ((ordinaryPointFiber Λ k e).obj K.obj) := by
    have hh := hF ⟨K.obj, (hP K.obj).mp K.property⟩
    exact (hQ _).mpr (bounded_finite_restrict e _
      ⟨(finite_support_iff_bounded _).mp hh.1, hh.2⟩)
  have hJ' (N : Q.FullSubcategory) : boundedConstructible
      (condensedRingObj Λ (Spec (.of k))) ((ordinaryPointRealization Λ k e).obj N.obj) := by
    have hh := bounded_finite_restrict e.symm N.obj ((hQ _).mp N.property)
    exact (hP _).mpr (hJ ⟨I.mapDerivedCategory.obj N.obj,
      (finite_support_iff_bounded _).mpr hh.1, hh.2⟩)
  have hEss (K : (boundedConstructible
      (condensedRingObj Λ (Spec (.of k)))).FullSubcategory) :
      (ordinaryPointRealization Λ k e).essImage K.obj := by
    let K' : (constantModelBoundedConstructible Λ (Spec (.of k))).FullSubcategory :=
      ⟨K.obj, (hP K.obj).mp K.property⟩
    let N := (boundedFiber Λ k hF).obj K'
    let c := asIso (b.counit.app K')
    refine ⟨H.mapDerivedCategory.obj N.obj, ⟨?_⟩⟩
    exact (condensedScalarRealization Λ (Spec (.of k))).mapIso
      (asIso (de.counit.app N.obj)) ≪≫
      (constantModelBoundedConstructible Λ (Spec (.of k))).ι.mapIso c
  obtain ⟨c, hcu, hcc⟩ := restrict_adjunction a Q
    (boundedConstructible (condensedRingObj Λ (Spec (.of k)))) hJ' hF' hEss
  exact ⟨hF', hJ', c, hcu, hcc⟩

private theorem intrinsic_equivalence_of_coordinates
    (h : scalar_properties Λ)
    {R : Type (u + 1)} [CommRing R]
    (Q : ObjectProperty (DerivedCategory (ModuleCat.{u + 1} R)))
    (hQ : ∀ K, Q K ↔ _root_.DerivedCategory.boundedFiniteCohomology R K)
    (e : R ≃+* condensedScalarRing Λ) (value : condensedScalarRing Λ → R)
    (he : ∀ a, e.symm a = value a) : IntrinsicPointEquivalence Λ k R Q value := by
  obtain ⟨hF, hJ, a, hu, hc⟩ := intrinsic_equivalence_at_coordinates Λ k h Q hQ e
  exact ⟨e, he, hF, hJ, a, hu, hc⟩

/-- The usual inclusion of a finite coefficient field into the fixed algebraic closure,
acting by derived extension of scalars on ordinary modules.
Source: blueprint, last paragraph (blueprint: def-weil-finite-coefficient-point). -/
def ordinaryPointToAlgCl (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    DerivedCategory (ModuleCat.{u + 1} (ULift.{u + 1} E)) ⥤
      DerivedCategory (ModuleCat.{u + 1} (ULift.{u + 1} (PadicAlgCl ℓ))) :=
  let f : ULift.{u + 1} E →+* ULift.{u + 1} (PadicAlgCl ℓ) :=
    ULift.ringEquiv.symm.toRingHom.comp (E.1.val.toRingHom.comp ULift.ringEquiv.toRingHom)
  ModuleCat.derivedExtendScalars f (RingHom.Flat.of_isField (Field.toIsField _) f)

/-- Objects and arrows in the ordinary bounded finite-dimensional category descend.
No colimit enters its definition: the witnesses are ordinary complexes and their
ordinary scalar extensions, with the given arrow conjugated by the displayed isomorphisms.
Source: blueprint, final consequence (blueprint: def-weil-finite-coefficient-point). -/
def OrdinaryPointFiniteDescent (ℓ : ℕ) [Fact ℓ.Prime] : Prop :=
  (∀ K : (DerivedCategory.pointFiniteDimensional (ULift.{u + 1} (PadicAlgCl ℓ))).FullSubcategory,
    ∃ (E : PadicAlgCl.FiniteIntermediateField ℓ)
      (P : (DerivedCategory.pointFiniteDimensional (ULift.{u + 1} E)).FullSubcategory),
      Nonempty ((ordinaryPointToAlgCl ℓ E).obj P.obj ≅ K.obj)) ∧
  (∀ C D : (DerivedCategory.pointFiniteDimensional
      (ULift.{u + 1} (PadicAlgCl ℓ))).FullSubcategory, ∀ f : C.obj ⟶ D.obj,
    ∃ (E : PadicAlgCl.FiniteIntermediateField ℓ)
      (P Q : (DerivedCategory.pointFiniteDimensional (ULift.{u + 1} E)).FullSubcategory)
      (eC : (ordinaryPointToAlgCl ℓ E).obj P.obj ≅ C.obj)
      (eD : (ordinaryPointToAlgCl ℓ E).obj Q.obj ≅ D.obj)
      (g : P.obj ⟶ Q.obj),
      eC.inv ≫ (ordinaryPointToAlgCl ℓ E).map g ≫ eD.hom = f)

private theorem fd_iff_bounded {F : Type (u + 1)} [Field F]
    (K : DerivedCategory (ModuleCat.{u + 1} F)) :
    DerivedCategory.pointFiniteDimensional F K ↔
      _root_.DerivedCategory.boundedFiniteCohomology F K := by
  exact and_congr (finite_support_iff_bounded K) Iff.rfl

private def scalarCoefficientMap (φ : Λ ⟶ Λ') [IsMonHom φ] :
    condensedScalarRing Λ →+* condensedScalarRing Λ' := by
  let G := sheafToPresheaf (coherentTopology Profinite.{u}) Ab.{u + 1}
  let t := (Monoidal.monFunctorCategoryEquivalence Profinite.{u}ᵒᵖ Ab.{u + 1}).functor.map
    (G.mapMon.map (show Mon.mk Λ ⟶ Mon.mk Λ' from ⟨φ⟩))
  exact InternalAbelianSheafModule.ringHom (t.app (op (⊤_ Profinite.{u}))).hom

private def sectionsComapIso (φ : Λ ⟶ Λ') [IsMonHom φ] :
    Mod.comap φ ⋙ CondensedRing.Evaluation.sections (coherentTopology Profinite.{u})
      Λ (⊤_ Profinite.{u}) ≅
    CondensedRing.Evaluation.sections (coherentTopology Profinite.{u}) Λ'
      (⊤_ Profinite.{u}) ⋙ ModuleCat.restrictScalars (scalarCoefficientMap φ) := by
  refine NatIso.ofComponents (fun M ↦ ModuleCat.isoMk (Iso.refl _) ?_) ?_
  · intro a
    ext m
    let G := sheafToPresheaf (coherentTopology Profinite.{u}) Ab.{u + 1}
    have h := ConcreteCategory.congr_hom
      (congr_app (Mod.act_hom ((G.mapModComapIso φ).hom.app M))
        (op (⊤_ Profinite.{u}))) (TensorProduct.tmul ℤ a m)
    exact h.symm
  · intro M N f
    ext m
    rfl

private def heartComapIso (k : Type u) [Field k] [IsAlgClosed k]
    (φ : Λ ⟶ Λ') [IsMonHom φ] :
    Mod.comap (coefficientMap φ (Spec (.of k))) ⋙ heartFiber Λ k ≅
      heartFiber Λ' k ⋙ ModuleCat.restrictScalars (scalarCoefficientMap φ) := by
  let F := upperStarFromPoint (Spec (.of k))
  let e := (F.mapMod Λ).asEquivalence
  let e' := (F.mapMod Λ').asEquivalence
  let c := F.mapModComapIso φ
  let ci : Mod.comap (coefficientMap φ (Spec (.of k))) ⋙ e.inverse ≅
      e'.inverse ⋙ Mod.comap φ :=
    Iso.isoInverseComp ((Functor.associator _ _ _).symm ≪≫
      (Iso.isoCompInverse (H := e) c).symm)
  exact (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight ci _ ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft e'.inverse (sectionsComapIso φ) ≪≫
    (Functor.associator _ _ _).symm

private def coordinateHeartComapIso (k : Type u) [Field k] [IsAlgClosed k]
    (φ : Λ ⟶ Λ') [IsMonHom φ]
    {R S : Type (u + 1)} [CommRing R] [CommRing S]
    (e : R ≃+* condensedScalarRing Λ) (e' : S ≃+* condensedScalarRing Λ')
    (f : R →+* S) (hf : (scalarCoefficientMap φ).comp e.toRingHom =
      e'.toRingHom.comp f) :
    Mod.comap (coefficientMap φ (Spec (.of k))) ⋙
        (heartFiber Λ k ⋙ ModuleCat.restrictScalars e.toRingHom) ≅
      (heartFiber Λ' k ⋙ ModuleCat.restrictScalars e'.toRingHom) ⋙
        ModuleCat.restrictScalars f :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (heartComapIso k φ) _ ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _
      ((ModuleCat.restrictScalarsComp _ _).symm ≪≫ ModuleCat.restrictScalarsCongr hf ≪≫
        ModuleCat.restrictScalarsComp _ _) ≪≫ (Functor.associator _ _ _).symm

private theorem ordinaryPointAdjunction_exists
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (k : Type u) [Field k] [IsAlgClosed k]
    (h : scalar_properties Λ) {R : Type (u + 1)} [CommRing R]
    (e : R ≃+* condensedScalarRing Λ) :
    ∃ a : ordinaryPointRealization Λ k e ⊣ ordinaryPointFiber Λ k e,
      IsIso a.unit := by
  obtain ⟨ha, hl, hc, ⟨eJ⟩⟩ := CondensedRing.flat_ordinaryScalarRealization
    (Mon.mk Λ) h.2 (Spec (.of k))
  let := ha
  let := hl
  let := hc
  let adj := ordinary_adjunction Λ k
  have : IsIso adj.unit := heart_adjunction_unit Λ k _ adj
  let da := (adj.mapDerivedCategoryAdjunction.ofNatIsoLeft eJ).ofNatIsoRight
    (heartFiberDerivedIso Λ k)
  have : IsIso da.unit := by
    let ff := adj.mapDerivedCategoryAdjunction.fullyFaithfulLOfIsIsoUnit
    let := ff.full
    let := ff.faithful
    have : (condensedScalarRealization Λ (Spec (.of k))).Full := Functor.Full.of_iso eJ
    have : (condensedScalarRealization Λ (Spec (.of k))).Faithful :=
      Functor.Faithful.of_iso eJ
    infer_instance
  let ae : ModuleCat.restrictScalars e.symm.toRingHom ⊣
      ModuleCat.restrictScalars e.toRingHom :=
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e).symm.toAdjunction
  let de := ae.mapDerivedCategoryAdjunction
  let a := de.comp da
  have : IsIso a.unit := by
    let ff := de.fullyFaithfulLOfIsIsoUnit
    let := ff.full
    let := ff.faithful
    let gg := da.fullyFaithfulLOfIsIsoUnit
    let := gg.full
    let := gg.faithful
    infer_instance
  exact ⟨a, inferInstance⟩

/-- Scalar realization commutes naturally with coefficient extension at the point.
Source: def-weil-finite-coefficient-point, the specified scalar quasi-inverse and its
exact adjunction (blueprint: def-weil-finite-coefficient-point).
The restriction square is the identity on sections. Derive it and take the unique
adjunction-compatible comparison of the two left adjoints. This is tensor
associativity for Λ'_s ⊗ (Λ_s ⊗ P), including its naturality in P. -/
private def ordinaryPointScalarRealizationIso (k : Type u) [Field k] [IsAlgClosed k]
    (h : scalar_properties Λ) (h' : scalar_properties Λ')
    (φ : Λ ⟶ Λ') [IsMonHom φ]
    {R S : Type (u + 1)} [CommRing R] [CommRing S]
    (e : R ≃+* condensedScalarRing Λ) (e' : S ≃+* condensedScalarRing Λ')
    (f : R →+* S) (hf : f.Flat)
    (he : (scalarCoefficientMap φ).comp e.toRingHom = e'.toRingHom.comp f) :
    ordinaryPointRealization Λ k e ⋙
        (Mod.extendScalars (coefficientMap φ (Spec (.of k)))).leftDerivedFunctor ≅
      ModuleCat.derivedExtendScalars f hf ⋙ ordinaryPointRealization Λ' k e' := by
  let HR := heartFiber Λ k ⋙ ModuleCat.restrictScalars e.toRingHom
  let HS := heartFiber Λ' k ⋙ ModuleCat.restrictScalars e'.toRingHom
  let cR : HR.mapDerivedCategory ≅ ordinaryPointFiber Λ k e :=
    Functor.mapDerivedCategoryCompIso _ _ ≪≫
      Functor.isoWhiskerRight (heartFiberDerivedIso Λ k) _
  let cS : HS.mapDerivedCategory ≅ ordinaryPointFiber Λ' k e' :=
    Functor.mapDerivedCategoryCompIso _ _ ≪≫
      Functor.isoWhiskerRight (heartFiberDerivedIso Λ' k) _
  let U : Mod (Sheaf (Scheme.ProEt.topology (Spec (.of k))) Ab.{u + 1})
      (condensedRingObj Λ' (Spec (.of k))) ⥤
      Mod (Sheaf (Scheme.ProEt.topology (Spec (.of k))) Ab.{u + 1})
        (condensedRingObj Λ (Spec (.of k))) :=
    Mod.comap (coefficientMap φ (Spec (.of k)))
  let V := ModuleCat.restrictScalars f
  let d : U.mapDerivedCategory ⋙ ordinaryPointFiber Λ k e ≅
      ordinaryPointFiber Λ' k e' ⋙ V.mapDerivedCategory :=
    Functor.isoWhiskerLeft _ cR.symm ≪≫ (Functor.mapDerivedCategoryCompIso U HR).symm ≪≫
      Functor.mapDerivedCategoryNatIso (coordinateHeartComapIso k φ e e' f he) ≪≫
      Functor.mapDerivedCategoryCompIso HS V ≪≫ Functor.isoWhiskerRight cS _
  let a := (ordinaryPointAdjunction_exists Λ k h e).choose
  let b := (ordinaryPointAdjunction_exists Λ' k h' e').choose
  have : PreservesFiniteLimits (ModuleCat.extendScalars.{u + 1} f) :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf
  let c :=
    (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} f).mapDerivedCategoryAdjunction
  exact (a.comp (Mod.derivedExtendMapDerivedCategoryAdjunction
    (coefficientMap φ (Spec (.of k))))).leftAdjointUniq
      ((c.comp b).ofNatIsoRight d.symm)

private theorem intrinsic_bounded_iff_constantModel
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (k : Type u) [Field k] [IsAlgClosed k]
    (K : Complexes Λ k) :
    boundedConstructible (condensedRingObj Λ (Spec (.of k))) K ↔
      constantModelBoundedConstructible Λ (Spec (.of k)) K :=
  and_congr Iff.rfl (forall_congr' fun _i ↦ intrinsic_iff_constantModel Λ k _)

/-- Simultaneous finite models for an arrow over the geometric point.
Source: def-weil-finite-coefficient-point, final paragraph, using precisely
sk-thm-sfb-qlbar-two-colimit (blueprint: def-weil-finite-coefficient-point).
Descend the endpoints, enlarge to a common field, and use its Hom assertion at
shift zero. Tensor transitivity supplies both endpoint identifications. -/
private theorem point_sheaf_arrow_descent (D : WeilConjectures.FiniteFieldDatum.{u})
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ D.p)
    (C B : PadicAlgClConstructible (Spec (.of D.k)) ℓ) (f : C.obj ⟶ B.obj) :
    ∃ (E : PadicAlgCl.FiniteIntermediateField ℓ)
      (P Q : PadicSubfieldConstructible (Spec (.of D.k)) ℓ E)
      (eC : (derivedExtendScalarsToPadicAlgCl (Spec (.of D.k)) ℓ E).obj P.obj ≅ C.obj)
      (eB : (derivedExtendScalarsToPadicAlgCl (Spec (.of D.k)) ℓ E).obj Q.obj ≅ B.obj)
      (g : P.obj ⟶ Q.obj),
      eC.inv ≫ (derivedExtendScalarsToPadicAlgCl (Spec (.of D.k)) ℓ E).map g ≫
        eB.hom = f := by
  let X := Spec (.of D.k)
  let : X.Over X := ⟨𝟙 X⟩
  let := Fintype.ofFinite D.k₀
  have : Fact D.p.Prime := ⟨D.prime⟩
  have : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
    ((Nat.card_eq_fintype_card (α := D.k₀)).symm.trans
      (D.card_base.trans D.cardinality_eq))
  have : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
  have hchar : ringChar D.k ≠ ℓ := (ringChar.eq D.k D.p).symm ▸ hℓ.symm
  have hd := finiteCoefficientDescentTwoColimitStatement ℓ D.k hchar
    (Or.inr inferInstance) X
  obtain ⟨E, P₀, ⟨i₀⟩⟩ := hd.2
    ⟨C.obj, (intrinsic_bounded_iff_constantModel _ D.k _).mp C.property⟩
  obtain ⟨F, Q₀, ⟨j₀⟩⟩ := hd.2
    ⟨B.obj, (intrinsic_bounded_iff_constantModel _ D.k _).mp B.property⟩
  obtain ⟨G, hE, hF⟩ := exists_ge_ge E F
  let P₁ : PadicSubfieldConstructible X ℓ E :=
    ⟨P₀.obj, (intrinsic_bounded_iff_constantModel _ D.k _).mpr P₀.property⟩
  let Q₁ : PadicSubfieldConstructible X ℓ F :=
    ⟨Q₀.obj, (intrinsic_bounded_iff_constantModel _ D.k _).mpr Q₀.property⟩
  let P : ConstantModelBoundedConstructible (Profinite.continuousMapRingObj G) X :=
    ⟨(derivedExtendScalarsSubfield X ℓ hE).obj P₁.obj,
      (intrinsic_bounded_iff_constantModel _ D.k _).mp
        (boundedConstructible_derivedExtendScalarsSubfield_obj X ℓ hE P₁)⟩
  let Q : ConstantModelBoundedConstructible (Profinite.continuousMapRingObj G) X :=
    ⟨(derivedExtendScalarsSubfield X ℓ hF).obj Q₁.obj,
      (intrinsic_bounded_iff_constantModel _ D.k _).mp
        (boundedConstructible_derivedExtendScalarsSubfield_obj X ℓ hF Q₁)⟩
  let i : (derivedExtendScalarsToPadicAlgCl X ℓ G).obj P.obj ≅ C.obj :=
    (derivedExtendScalarsCompIso X ℓ hE).app P₁.obj ≪≫ i₀
  let j : (derivedExtendScalarsToPadicAlgCl X ℓ G).obj (Q.obj⟦(0 : ℤ)⟧) ≅ B.obj :=
    (derivedExtendScalarsToPadicAlgCl X ℓ G).mapIso
      ((shiftFunctorZero _ ℤ).app Q.obj) ≪≫
      (derivedExtendScalarsCompIso X ℓ hF).app Q₁.obj ≪≫ j₀
  let ψ := i.hom ≫ f ≫ j.inv
  obtain ⟨H, hG, g, hg⟩ := (hd.1 G P Q 0).1 ψ
  let P' : PadicSubfieldConstructible X ℓ G :=
    ⟨P.obj, (intrinsic_bounded_iff_constantModel _ D.k _).mpr P.property⟩
  let Q' : PadicSubfieldConstructible X ℓ G :=
    ⟨Q.obj⟦(0 : ℤ)⟧, (boundedConstructible _).prop_of_iso
      ((shiftFunctorZero _ ℤ).app Q.obj).symm
      ((intrinsic_bounded_iff_constantModel _ D.k _).mpr Q.property)⟩
  let i' := (derivedExtendScalarsCompIso X ℓ hG).app P.obj ≪≫ i
  let j' := (derivedExtendScalarsCompIso X ℓ hG).app (Q.obj⟦(0 : ℤ)⟧) ≪≫ j
  refine ⟨H, (constructibleExtendScalars X ℓ hG).obj P',
    (constructibleExtendScalars X ℓ hG).obj Q', i', j', g, ?_⟩
  calc
    _ = i.inv ≫ finiteDescentDerivedHomToAlgCl X ℓ hG g ≫ j.hom := by
      simp only [i', j', finiteDescentDerivedHomToAlgCl, Iso.trans_inv, Iso.trans_hom,
        Iso.app_hom, Iso.app_inv, Category.assoc]
      rfl
    _ = i.inv ≫ ψ ≫ j.hom := by rw [hg]
    _ = f := by simp only [ψ, Category.assoc, Iso.inv_hom_id_assoc,
      Iso.inv_hom_id, Category.comp_id]

private def fieldPointCoordinates (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    ULift.{u + 1} E ≃+* condensedScalarRing (Profinite.continuousMapRingObj.{u} E) :=
  ULift.ringEquiv.trans (continuous_scalar_coordinates E).symm

private def algClPointCoordinates (ℓ : ℕ) [Fact ℓ.Prime] :
    ULift.{u + 1} (PadicAlgCl ℓ) ≃+*
      condensedScalarRing (Profinite.padicAlgClRingObj.{u} ℓ) :=
  ULift.ringEquiv.trans (algClosure_scalar_coordinates ℓ).symm

private def fieldPointScalarIso (k : Type u) [Field k] [IsAlgClosed k]
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    ordinaryPointRealization (Profinite.continuousMapRingObj.{u} E) k
        (fieldPointCoordinates ℓ E) ⋙ derivedExtendScalarsToPadicAlgCl (Spec (.of k)) ℓ E ≅
      ordinaryPointToAlgCl ℓ E ⋙ ordinaryPointRealization
        (Profinite.padicAlgClRingObj.{u} ℓ) k (algClPointCoordinates ℓ) := by
  let f : ULift.{u + 1} E →+* ULift.{u + 1} (PadicAlgCl ℓ) :=
    ULift.ringEquiv.symm.toRingHom.comp (E.1.val.toRingHom.comp ULift.ringEquiv.toRingHom)
  exact ordinaryPointScalarRealizationIso k (field_scalar_properties E)
    (algClosure_scalar_properties ℓ) (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E)
    (fieldPointCoordinates ℓ E) (algClPointCoordinates ℓ) f
    (RingHom.Flat.of_isField (Field.toIsField _) f) (by
      ext a
      rfl)

private theorem coordinate_models
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (k : Type u) [Field k] [IsAlgClosed k]
    (h : scalar_properties Λ) {R : Type (u + 1)} [CommRing R]
    (Q : ObjectProperty (DerivedCategory (ModuleCat.{u + 1} R)))
    (hQ : ∀ K, Q K ↔ _root_.DerivedCategory.boundedFiniteCohomology R K)
    (e : R ≃+* condensedScalarRing Λ) :
    (∀ K : (boundedConstructible (condensedRingObj Λ (Spec (.of k)))).FullSubcategory,
      Q ((ordinaryPointFiber Λ k e).obj K.obj)) ∧
    (∀ P : Q.FullSubcategory, boundedConstructible (condensedRingObj Λ (Spec (.of k)))
      ((ordinaryPointRealization Λ k e).obj P.obj)) ∧
    (∀ K : (boundedConstructible (condensedRingObj Λ (Spec (.of k)))).FullSubcategory,
      Nonempty ((ordinaryPointRealization Λ k e).obj
        ((ordinaryPointFiber Λ k e).obj K.obj) ≅ K.obj)) := by
  obtain ⟨hF, hJ, a, hu, hc⟩ := intrinsic_equivalence_at_coordinates Λ k h Q hQ e
  let := hc
  exact ⟨hF, hJ, fun K ↦
    ⟨(boundedConstructible _).ι.mapIso (asIso (a.counit.app K))⟩⟩

private theorem point_ordinary_arrow_descent (D : WeilConjectures.FiniteFieldDatum.{u})
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ D.p)
    (C B : (DerivedCategory.pointFiniteDimensional
      (ULift.{u + 1} (PadicAlgCl ℓ))).FullSubcategory) (f : C.obj ⟶ B.obj) :
    ∃ (E : PadicAlgCl.FiniteIntermediateField ℓ)
      (P Q : (DerivedCategory.pointFiniteDimensional (ULift.{u + 1} E)).FullSubcategory)
      (eC : (ordinaryPointToAlgCl ℓ E).obj P.obj ≅ C.obj)
      (eB : (ordinaryPointToAlgCl ℓ E).obj Q.obj ≅ B.obj) (g : P.obj ⟶ Q.obj),
      eC.inv ≫ (ordinaryPointToAlgCl ℓ E).map g ≫ eB.hom = f := by
  let Ω := Profinite.padicAlgClRingObj.{u} ℓ
  let eΩ := algClPointCoordinates.{u} ℓ
  let JΩ := ordinaryPointRealization Ω D.k eΩ
  obtain ⟨aΩ, huΩ⟩ := ordinaryPointAdjunction_exists Ω D.k
    (algClosure_scalar_properties ℓ) eΩ
  let := huΩ
  let ffΩ := aΩ.fullyFaithfulLOfIsIsoUnit
  let : JΩ.Full := ffΩ.full
  let : JΩ.Faithful := ffΩ.faithful
  have hmΩ := coordinate_models Ω D.k (algClosure_scalar_properties ℓ)
    (DerivedCategory.pointFiniteDimensional _) fd_iff_bounded eΩ
  let C' : PadicAlgClConstructible (Spec (.of D.k)) ℓ := ⟨JΩ.obj C.obj, hmΩ.2.1 C⟩
  let B' : PadicAlgClConstructible (Spec (.of D.k)) ℓ := ⟨JΩ.obj B.obj, hmΩ.2.1 B⟩
  obtain ⟨E, P', Q', i, j, g', hg⟩ := point_sheaf_arrow_descent D ℓ hℓ C' B' (JΩ.map f)
  let Λ := Profinite.continuousMapRingObj.{u} E
  let e := fieldPointCoordinates.{u} ℓ E
  let J := ordinaryPointRealization Λ D.k e
  let F := ordinaryPointFiber Λ D.k e
  let T := derivedExtendScalarsToPadicAlgCl (Spec (.of D.k)) ℓ E
  let O := ordinaryPointToAlgCl.{u} ℓ E
  obtain ⟨a, hu⟩ := ordinaryPointAdjunction_exists Λ D.k (field_scalar_properties E) e
  let := hu
  let ff := a.fullyFaithfulLOfIsIsoUnit
  let : J.Full := ff.full
  let : J.Faithful := ff.faithful
  have hm := coordinate_models Λ D.k (field_scalar_properties E)
    (DerivedCategory.pointFiniteDimensional _) fd_iff_bounded e
  let P : (DerivedCategory.pointFiniteDimensional (ULift.{u + 1} E)).FullSubcategory :=
    ⟨F.obj P'.obj, hm.1 P'⟩
  let Q : (DerivedCategory.pointFiniteDimensional (ULift.{u + 1} E)).FullSubcategory :=
    ⟨F.obj Q'.obj, hm.1 Q'⟩
  obtain ⟨cP⟩ := hm.2.2 P'
  obtain ⟨cQ⟩ := hm.2.2 Q'
  let χ : J ⋙ T ≅ O ⋙ JΩ := fieldPointScalarIso D.k ℓ E
  let i' : JΩ.obj (O.obj P.obj) ≅ JΩ.obj C.obj :=
    (χ.app P.obj).symm ≪≫ T.mapIso cP ≪≫ i
  let j' : JΩ.obj (O.obj Q.obj) ≅ JΩ.obj B.obj :=
    (χ.app Q.obj).symm ≪≫ T.mapIso cQ ≪≫ j
  let g : P.obj ⟶ Q.obj := J.preimage (cP.hom ≫ g' ≫ cQ.inv)
  refine ⟨E, P, Q, JΩ.preimageIso i', JΩ.preimageIso j', g, ?_⟩
  apply JΩ.map_injective
  simp only [Functor.map_comp, Functor.preimageIso_inv, Functor.preimageIso_hom,
    Functor.map_preimage]
  change i'.inv ≫ JΩ.map (O.map g) ≫ j'.hom = JΩ.map f
  calc
    _ = i.inv ≫ T.map cP.inv ≫
        (χ.hom.app P.obj ≫ JΩ.map (O.map g)) ≫
        χ.inv.app Q.obj ≫ T.map cQ.hom ≫ j.hom := by
      simp only [i', j', Iso.trans_inv, Iso.trans_hom, Iso.symm_inv, Iso.symm_hom,
        Functor.mapIso_inv, Functor.mapIso_hom, Iso.app_hom, Iso.app_inv, Category.assoc]
    _ = i.inv ≫ T.map cP.inv ≫ T.map (J.map g) ≫ T.map cQ.hom ≫ j.hom := by
      have hn := χ.hom.naturality g
      change T.map (J.map g) ≫ χ.hom.app Q.obj =
        χ.hom.app P.obj ≫ JΩ.map (O.map g) at hn
      rw [← hn]
      simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
    _ = i.inv ≫ T.map g' ≫ j.hom := by
      have hmap : T.map cP.inv ≫ T.map (J.map g) ≫ T.map cQ.hom = T.map g' := by
        rw [show J.map g = cP.hom ≫ g' ≫ cQ.inv from J.map_preimage _]
        rw [← T.map_comp, ← T.map_comp]
        simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
      simpa only [Category.assoc] using congrArg (fun z ↦ i.inv ≫ z ≫ j.hom) hmap
    _ = JΩ.map f := hg

private theorem ordinary_finite_descent (D : WeilConjectures.FiniteFieldDatum.{u})
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ D.p) :
    OrdinaryPointFiniteDescent.{u} ℓ := by
  constructor
  · intro K
    obtain ⟨E, P, Q, eK, eQ, g, hg⟩ := point_ordinary_arrow_descent D ℓ hℓ K K (𝟙 K.obj)
    exact ⟨E, P, ⟨eK⟩⟩
  · exact point_ordinary_arrow_descent D ℓ hℓ

/-- The four ordinary coefficient targets and the intrinsic bounded constructible point
categories, together with exact evaluation, exact scalar realization, and final descent.
Source: current blueprint, def-weil-finite-coefficient-point, entire definition
(blueprint: def-weil-finite-coefficient-point).

Proof: (1) The profinite description of the point site makes covers of its final object
split. Local lifting across a sheaf epimorphism then makes evaluation exact; the affine
weakly contractible evaluation theorem also gives preservation of colimits.
(2) Sections are continuous functions. They are flat over the scalar ring: locally
constant flatness for the finite quotient, torsion-freeness over the valuation ring for
integral coefficients, and field flatness for the two rational coefficients. Evaluation
on the singleton identifies the section rings with the specified ordinary rings.
(3) Transport the terminal scalar adjunction through the point-module equivalence.
Its left adjoint is the actual scalar realization; flatness makes it exact and
colimit-preserving singleton evaluation makes its constant-section unit invertible.
(4) Split the local trivializing cover to obtain a global finite scalar presentation.
This identifies both constructibility conventions. The rings are Noetherian, so finite
presentation is finite generation; for the finite ring this is finite cardinality and
for fields it is finite dimension. Discrete realization recovers finite torsion sheaves.
(5) Derive the exact adjunction and use its cohomology comparison. Both functors preserve
the stated full subcategories. The unit is invertible. The triangulated essential image
contains the constructible heart by (4). Bounded Postnikov induction makes its counit
invertible there. Restrict the adjunction to obtain the four equivalences with the
specified scalar quasi-inverse.
(6) Apply sk-thm-sfb-qlbar-two-colimit at Spec k and transport its object and Hom descent
through the field equivalences. Scalar extension commutes with their specified scalar
realizations by the adjunction-compatible comparison.
-/
theorem intrinsic_coefficient_point (D : WeilConjectures.FiniteFieldDatum.{u})
    (ℓ : ℕ) [Fact ℓ.Prime] (_hℓ : ℓ ≠ D.p)
    (E : PadicAlgCl.FiniteIntermediateField ℓ) (π : PadicAlgCl.integers ℓ E)
    (_hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E))
    (n : ℕ) (_hn : 1 ≤ n) :
    (∀ M : Mod (Sheaf (Scheme.ProEt.topology (Spec (.of D.k))) Ab.{u + 1})
        (condensedRingObj (residueRingObj.{u} ℓ E π n) (Spec (.of D.k))),
      IsConstructibleModuleObject
          (condensedRingObj (residueRingObj.{u} ℓ E π n) (Spec (.of D.k))) M ↔
        ∃ P : ModuleCat.{u + 1} (condensedScalarRing (residueRingObj.{u} ℓ E π n)),
          Finite P ∧ Nonempty ((CondensedRing.ordinaryScalarRealization
            (Mon.mk (residueRingObj.{u} ℓ E π n)) (Spec (.of D.k))).obj P ≅ M)) ∧
    IntrinsicPointHeart (residueRingObj.{u} ℓ E π n) D.k ∧
    IntrinsicPointHeart (Profinite.padicIntegersRingObj.{u} ℓ E) D.k ∧
    IntrinsicPointHeart (Profinite.continuousMapRingObj.{u} E) D.k ∧
    IntrinsicPointHeart (Profinite.padicAlgClRingObj.{u} ℓ) D.k ∧
    IntrinsicPointEquivalence (residueRingObj.{u} ℓ E π n) D.k
      (ULift.{u + 1} (PadicAlgCl.integers ℓ E ⧸ (Ideal.span {π}) ^ n))
      (DerivedCategory.pointFiniteCohomology _)
      (fun a ↦ ULift.up (a.down coefficientPoint)) ∧
    IntrinsicPointEquivalence (Profinite.padicIntegersRingObj.{u} ℓ E) D.k
      (ULift.{u + 1} (PadicAlgCl.integers ℓ E)) (_root_.DerivedCategory.boundedFiniteCohomology _)
      (fun a ↦ ULift.up (a.down coefficientPoint)) ∧
    IntrinsicPointEquivalence (Profinite.continuousMapRingObj.{u} E) D.k
      (ULift.{u + 1} E) (DerivedCategory.pointFiniteDimensional _)
      (fun a ↦ ULift.up (a.down coefficientPoint)) ∧
    IntrinsicPointEquivalence (Profinite.padicAlgClRingObj.{u} ℓ) D.k
      (ULift.{u + 1} (PadicAlgCl ℓ)) (DerivedCategory.pointFiniteDimensional _)
      (fun a ↦ ULift.up (a.down.val coefficientPoint)) ∧
    OrdinaryPointFiniteDescent.{u} ℓ := by
  let A := PadicAlgCl.integers ℓ E ⧸ (Ideal.span ({π} : Set _)) ^ n
  let : TopologicalSpace A := ⊥
  let : DiscreteTopology A := ⟨rfl⟩
  have hA : Finite A := by
    change Finite (PadicAlgCl.integers ℓ E ⧸ (Ideal.span {π}) ^ n)
    rw [_hπ]
    infer_instance
  let := hA
  let er := continuous_scalar_coordinates.{u} A
  let ei := continuous_scalar_coordinates.{u} (PadicAlgCl.integers ℓ E)
  let ef := continuous_scalar_coordinates.{u} E
  let ea := algClosure_scalar_coordinates.{u} ℓ
  have hr := residue_scalar_properties.{u} ℓ E π n
  have hi := integers_scalar_properties.{u} ℓ E
  have hf := field_scalar_properties.{u} E
  have ha := algClosure_scalar_properties.{u} ℓ
  let := hr.1
  let := hi.1
  let := hf.1
  let := ha.1
  have hrf : ∀ S : Profinite.{u},
      (CondensedRing.scalarSectionMap (Mon.mk (residueRingObj.{u} ℓ E π n)) S).Flat := by
    apply continuous_scalar_flat A
    intro S
    rw [show ContinuousMap.C (α := S) (R := A) (A := A) = algebraMap A C(S, A)
      from rfl, RingHom.flat_algebraMap_iff]
    apply Module.Flat.of_linearEquiv
      (LinearEquiv.ofBijective (LocallyConstant.toContinuousMapLinearMap A) ?_).symm
    exact ⟨LocallyConstant.toContinuousMap_injective,
      fun f ↦ ⟨⟨f, (IsLocallyConstant.iff_continuous _).2 f.continuous⟩, rfl⟩⟩
  have hif : ∀ S : Profinite.{u}, (CondensedRing.scalarSectionMap
      (Mon.mk (Profinite.padicIntegersRingObj.{u} ℓ E)) S).Flat := by
    let := PadicAlgCl.normedFieldOfAlgebra ℓ E
    apply continuous_scalar_flat (PadicAlgCl.integers ℓ E)
    intro S
    rw [show ContinuousMap.C (α := S) (R := PadicAlgCl.integers ℓ E)
      (A := PadicAlgCl.integers ℓ E) = algebraMap _ C(S, PadicAlgCl.integers ℓ E)
      from rfl, RingHom.flat_algebraMap_iff]
    let : Module.IsTorsionFree (PadicAlgCl.integers ℓ E)
        C(S, PadicAlgCl.integers ℓ E) := by
      constructor
      intro a ha f g hfg
      apply ContinuousMap.ext
      intro x
      exact ha.left (ContinuousMap.congr_fun hfg x)
    infer_instance
  have hff : ∀ S : Profinite.{u}, (CondensedRing.scalarSectionMap
      (Mon.mk (Profinite.continuousMapRingObj.{u} E)) S).Flat :=
    continuous_scalar_flat E (fun S ↦ RingHom.Flat.of_isField (Field.toIsField E) _)
  have haf : ∀ S : Profinite.{u}, (CondensedRing.scalarSectionMap
      (Mon.mk (Profinite.padicAlgClRingObj.{u} ℓ)) S).Flat := by
    have hh : IsField (condensedScalarRing (Profinite.padicAlgClRingObj.{u} ℓ)) :=
      MulEquiv.isField (Field.toIsField (PadicAlgCl ℓ)) ea.toMulEquiv
    exact fun S ↦ RingHom.Flat.of_isField hh _
  have hheart := intrinsic_heart_of_flat (residueRingObj.{u} ℓ E π n) D.k hrf
  have hscalar : Finite (condensedScalarRing (residueRingObj.{u} ℓ E π n)) :=
    Finite.of_equiv A er.symm.toEquiv
  let := hscalar
  refine ⟨?_, hheart,
    intrinsic_heart_of_flat _ D.k hif, intrinsic_heart_of_flat _ D.k hff,
    intrinsic_heart_of_flat _ D.k haf, ?_, ?_, ?_, ?_, ordinary_finite_descent D ℓ _hℓ⟩
  · intro M
    rw [(hheart.2.2.2.2.2.2 M).2]
    exact exists_congr fun P ↦ and_congr
      ((Module.finitePresentation_iff_finite _ _).trans
        (Module.finite_iff_finite (R := condensedScalarRing (residueRingObj.{u} ℓ E π n))
          (M := P))) Iff.rfl
  · refine intrinsic_equivalence_of_coordinates _ D.k hr _ ?_
      (er.trans ULift.ringEquiv.symm).symm _ ?_
    · intro K
      exact and_congr (finite_support_iff_bounded K)
        (forall_congr' fun i ↦ (Module.finite_iff_finite).symm)
    · intro a
      change ULift.up (a.down default) = ULift.up (a.down coefficientPoint)
      exact congrArg (fun x ↦ ULift.up (a.down x)) (Subsingleton.elim _ _)
  · apply intrinsic_equivalence_of_coordinates _ D.k hi _ (fun K ↦ Iff.rfl)
      (ei.trans ULift.ringEquiv.symm).symm _
    intro a
    change ULift.up (a.down default) = ULift.up (a.down coefficientPoint)
    exact congrArg (fun x ↦ ULift.up (a.down x)) (Subsingleton.elim _ _)
  · apply intrinsic_equivalence_of_coordinates _ D.k hf _ fd_iff_bounded
      (ef.trans ULift.ringEquiv.symm).symm _
    intro a
    change ULift.up (a.down default) = ULift.up (a.down coefficientPoint)
    exact congrArg (fun x ↦ ULift.up (a.down x)) (Subsingleton.elim _ _)
  · apply intrinsic_equivalence_of_coordinates _ D.k ha _ fd_iff_bounded
      (ea.trans ULift.ringEquiv.symm).symm _
    intro a
    change ULift.up (a.down.val default) = ULift.up (a.down.val coefficientPoint)
    exact congrArg (fun x ↦ ULift.up (a.down.val x)) (Subsingleton.elim _ _)

/-- Singleton evaluation identifies discrete finite coefficient scalars with A itself.
This is the existing section-coordinate map followed by evaluation at the specified point.
Source: latest blueprint def-weil-finite-coefficient-point, finite-coefficient display
(blueprint: def-weil-finite-coefficient-point). -/
def finiteDiscreteScalarCoordinates (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] :
    condensedScalarRing (Profinite.continuousCoefficientRingObj A) ≃+*
      ULift.{u + 1, u} A :=
  by
    have : Subsingleton (⊤_ Profinite.{u}) := by
      constructor
      intro x y
      let c : (⊤_ Profinite.{u}) ⟶ (⊤_ Profinite.{u}) :=
        ConcreteCategory.ofHom ⟨fun _ ↦ x, continuous_const⟩
      exact ConcreteCategory.congr_hom (terminalIsTerminal.hom_ext c (𝟙 _)) y
    let ev : C((⊤_ Profinite.{u}), A) ≃+* A :=
      { toFun := fun f ↦ f coefficientPoint
        invFun := ContinuousMap.const _
        left_inv := fun f ↦ ContinuousMap.ext fun _x ↦
          congrArg f (Subsingleton.elim _ _)
        right_inv := fun _ ↦ rfl
        map_add' := fun _ _ ↦ rfl
        map_mul' := fun _ _ ↦ rfl }
    exact ((ringSheafSectionCoordinates (Profinite.continuousCoefficientRingSheaf A)
      (⊤_ Profinite.{u})).trans (ULift.ringEquiv.trans ev)).trans ULift.ringEquiv.symm

private theorem pointInverse_finitelyPresented_of_constructible
    (M : Mod (Sheaf (Scheme.ProEt.topology (Spec (.of k))) Ab.{u + 1})
      (condensedRingObj Λ (Spec (.of k))))
    (hM : IsConstructibleModuleObject (condensedRingObj Λ (Spec (.of k))) M) :
    Mod.IsFinitelyPresented Λ
      ((((upperStarFromPoint (Spec (.of k))).mapMod Λ).asEquivalence).inverse.obj M) := by
  let e := ((upperStarFromPoint (Spec (.of k))).mapMod Λ).asEquivalence
  have hfp := CondensedRing.isFinitelyPresented_upperStar_of_isConstructibleModuleObject
    Λ (Field.toIsField k) IsField.isSepClosed_toField hM (𝟙 _)
  have hfp' := hfp.of_iso ((CondensedRing.upperStarId Λ _).app M)
  let r : e.functor.obj (Mod.regular Λ) ≅
      Mod.regular (condensedRingObj Λ (Spec (.of k))) :=
    Mod.isoMk (Iso.refl _) (by simp)
  let r' : e.inverse.obj (Mod.regular (condensedRingObj Λ (Spec (.of k)))) ≅
      Mod.regular Λ :=
    e.inverse.mapIso r.symm ≪≫ (e.unitIso.app (Mod.regular Λ)).symm
  let := Functor.additive_of_preserves_binary_products e.inverse
  exact hfp'.map e.inverse r'

private theorem heartFiber_finite_of_constructible [Finite (condensedScalarRing Λ)]
    (M : Mod (Sheaf (Scheme.ProEt.topology (Spec (.of k))) Ab.{u + 1})
      (condensedRingObj Λ (Spec (.of k))))
    (hM : IsConstructibleModuleObject (condensedRingObj Λ (Spec (.of k))) M) :
    Finite ((heartFiber Λ k).obj M) := by
  let e := ((upperStarFromPoint (Spec (.of k))).mapMod Λ).asEquivalence
  let S := CondensedRing.Evaluation.sections (coherentTopology Profinite.{u}) Λ
    (⊤_ Profinite.{u})
  have hp := pointInverse_finitelyPresented_of_constructible Λ k M hM
  obtain ⟨n, m, f, ⟨ef⟩⟩ := hp
  have hreg : Finite (S.obj (Mod.regular Λ)) :=
    Finite.of_equiv (condensedScalarRing Λ) (Equiv.refl _)
  let := hreg
  let b := S.mapBiproduct (fun _ : Fin n ↦ Mod.regular Λ) ≪≫
    ModuleCat.biproductIsoPi (fun _ : Fin n ↦ S.obj (Mod.regular Λ))
  have : Module.Finite (condensedScalarRing Λ) (S.obj (Mod.finiteFree Λ n)) :=
    Module.Finite.equiv b.toLinearEquiv.symm
  have : Module.Finite (condensedScalarRing Λ)
      (cokernel (S.map f) : ModuleCat (condensedScalarRing Λ)) :=
    Module.Finite.equiv (ModuleCat.cokernelIsoRangeQuotient (S.map f)).toLinearEquiv.symm
  have : Module.Finite (condensedScalarRing Λ) (S.obj (e.inverse.obj M)) :=
    Module.Finite.equiv (S.mapIso ef ≪≫ PreservesCokernel.iso S f).toLinearEquiv.symm
  change Finite (S.obj (e.inverse.obj M))
  exact Module.finite_of_finite (condensedScalarRing Λ)

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] (k : Type u) [Field k] [IsAlgClosed k]

omit Λ k in
omit Λ k in
end AlgebraicGeometry.ProEtale.CondensedGeometricPoint
