/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteNativeTensor.FiniteNativeTensorComparisonData
import all WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteCtfInternalEtaleRealization
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteEncodingConstructibility
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteEncodingTensorTor
import WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion

/-! # Finite native domain comparison

Source: the finite native tensor comparison argument.
(blueprint: lem-pur-finite-native-domain-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u u₁ u₂ u₃ u₄ u₅ u₆ v₁ v₂ v₃ v₄ v₅ v₆
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

namespace AlgebraicGeometry.ProEtale.FiniteNativeTensor
open FiniteDiscreteOrdinary
-- Discard the imported instance with a free coefficient universe.
attribute [-instance] WeilConjectures.scalarReductionSiteSmall
attribute [local instance 20000] sheafBraidedCategory sheafSymmetricCategory
  sheafMonoidalCategory sheafMonoidalClosed
  preservesColimitsOfSize_tensorLeft_sheaf preservesColimitsOfSize_tensorRight_sheaf
attribute [local instance 2000] Mod.monoidalCategory Mod.monoidalClosed
attribute [local irreducible] Mod.monoidalClosed
attribute [local irreducible] Sheaf.monoidalCategory SheafOfModules.monoidalCategory

variable (A : Type u) [CommRing A] [Finite A]
  [TopologicalSpace A] [DiscreteTopology A] [IsTopologicalRing A]

omit [TopologicalSpace A] [DiscreteTopology A] [IsTopologicalRing A] in
private theorem etaleDomain_iff (T : Scheme.{u})
    (K : Etale.DerivedCategoryModule (ULift.{u + 1} A) T) :
    etaleDomain A T K ↔ Etale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} (ULift.{u + 1} A)) T K := by
  constructor
  · rintro ⟨hb, a, b, _, ht⟩
    exact ⟨(etaleBC_iff A T K).mp hb, a, b,
      Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.mp ht⟩
  · rintro ⟨hb, a, b, ht⟩
    exact ⟨(etaleBC_iff A T K).mpr hb, min a b, max a b, min_le_max,
      Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.mpr
        (ht.mono (min_le_left _ _) (le_max_right _ _))⟩

omit [TopologicalSpace A] [DiscreteTopology A] [IsTopologicalRing A] in
private theorem etaleDomain_monoidal (T : Scheme.{u}) :
    (etaleDomain A T).IsMonoidal where
  prop_unit := by
    apply (etaleDomain_iff A T _).mpr
    exact ⟨(Etale.DerivedCategory.boundedConstructible _ T).prop_of_iso
      (_root_.DerivedCategory.singleFunctorObjUnitIso _)
      (Etale.DerivedCategory.boundedConstructible_singleFunctor_obj _ 0), 0, 0,
      (Etale.DerivedCategory.torAmplitudeIn _ T 0 0).prop_of_iso
        (_root_.DerivedCategory.singleFunctorObjUnitIso _)
        (_root_.DerivedCategory.torAmplitudeIn_singleFunctor_obj_of_flat
          (ObjectProperty.flat_of_isDualizable isDualizable_unit))⟩
  prop_tensor _K _L hK hL := (etaleDomain_iff A T _).mpr
    (Etale.constructibleFiniteTor_tensor (ULift.{u + 1} A) T
      ((etaleDomain_iff A T _).mp hK) ((etaleDomain_iff A T _).mp hL))

private def restrictedCore {C : Type u₁} {D : Type u₂}
    [Category.{v₁} C] [Category.{v₂} D] [MonoidalCategory C] [MonoidalCategory D]
    (P : ObjectProperty C) (Q : ObjectProperty D) [P.IsMonoidal] [Q.IsMonoidal]
    (F : C ⥤ D) [F.Monoidal] (h : ∀ M : P.FullSubcategory, Q (F.obj M.obj)) :
    (Q.lift (P.ι ⋙ F) h).CoreMonoidal where
  εIso := Q.isoMk (Functor.Monoidal.εIso F)
  μIso M N := Q.isoMk (Functor.Monoidal.μIso F M.obj N.obj)
  μIso_hom_natural_left f N := by
    apply ObjectProperty.hom_ext
    exact Functor.LaxMonoidal.μ_natural_left F f.hom N.obj
  μIso_hom_natural_right M f := by
    apply ObjectProperty.hom_ext
    exact Functor.LaxMonoidal.μ_natural_right F M.obj f.hom
  associativity M N L := by
    apply ObjectProperty.hom_ext
    exact Functor.LaxMonoidal.associativity F M.obj N.obj L.obj
  left_unitality M := by
    apply ObjectProperty.hom_ext
    exact Functor.LaxMonoidal.left_unitality F M.obj
  right_unitality M := by
    apply ObjectProperty.hom_ext
    exact Functor.LaxMonoidal.right_unitality F M.obj

private theorem monoidalImage {C : Type u₁} {D : Type u₂}
    [Category.{v₁} C] [Category.{v₂} D] [MonoidalCategory C] [MonoidalCategory D]
    (P : ObjectProperty C) (Q : ObjectProperty D) [P.IsMonoidal]
    [Q.IsClosedUnderIsomorphisms] (F : C ⥤ D) [F.Monoidal]
    (h : ∀ M : P.FullSubcategory, Q (F.obj M.obj))
    (hs : ∀ N : Q.FullSubcategory,
      ∃ M : P.FullSubcategory, Nonempty (F.obj M.obj ≅ N.obj)) : Q.IsMonoidal where
  prop_unit := Q.prop_of_iso (Functor.Monoidal.εIso F).symm (h (𝟙_ P.FullSubcategory))
  prop_tensor K L hK hL := by
    obtain ⟨M, ⟨e⟩⟩ := hs ⟨K, hK⟩
    obtain ⟨N, ⟨j⟩⟩ := hs ⟨L, hL⟩
    exact Q.prop_of_iso ((Functor.Monoidal.μIso F M.obj N.obj).symm ≪≫ tensorIso e j)
      (h (M ⊗ N))

omit [DiscreteTopology A] in
private theorem buildDomainComparison (ordinary : Bool)
    (E : ∀ T : Scheme.{u}, Encoding A T) (T : Scheme.{u})
    [hQ : (nativeDomain A ordinary T).IsClosedUnderIsomorphisms]
    (h : ∀ M : (etaleDomain A T).FullSubcategory,
      nativeDomain A ordinary T ((realization A ordinary E T).obj M.obj))
    (hs : ∀ N : (nativeDomain A ordinary T).FullSubcategory,
      ∃ M : (etaleDomain A T).FullSubcategory,
        Nonempty ((realization A ordinary E T).obj M.obj ≅ N.obj))
    [((etaleDomain A T).ι ⋙ realization A ordinary E T).Full]
    [((etaleDomain A T).ι ⋙ realization A ordinary E T).Faithful] :
    Nonempty (DomainComparison A ordinary E T) := by
  let := etaleDomain_monoidal A T
  let := nativeRealizationMonoidal A ordinary E T
  let := monoidalImage (etaleDomain A T) (nativeDomain A ordinary T)
    (realization A ordinary E T) h hs
  let R := restrictRealization A ordinary E T h
  let : R.Monoidal := (restrictedCore _ _ (realization A ordinary E T) h).toMonoidal
  have : R.Full := by dsimp [R, restrictRealization]; infer_instance
  have : R.Faithful := by dsimp [R, restrictRealization]; infer_instance
  have : R.EssSurj := ⟨fun N ↦ by
    obtain ⟨M, ⟨e⟩⟩ := hs N
    exact ⟨M, ⟨ObjectProperty.isoMk _ e⟩⟩⟩
  have : R.IsEquivalence := {}
  exact ⟨{
    mem := h
    tensor_normalization := fun _ _ ↦ rfl
    unit_normalization := rfl }⟩

omit [DiscreteTopology A] in
private theorem ordinaryDomainComparison (E : ∀ T : Scheme.{u}, Encoding A T)
    (T : Scheme.{u}) [CompactSpace T] [QuasiSeparatedSpace T] :
    Nonempty (DomainComparison A true E T) := by
  let C := comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) T
  let P := etaleDomain A T
  let Q := ordinaryDomain A T
  let F := P.ι ⋙ C.mapDerivedCategory
  have htC (K : Etale.DerivedCategoryModule (ULift.{u + 1} A) T) (a b : ℤ) :
      Etale.DerivedCategory.hasTorAmplitudeIn (ULift.{u + 1} A) T a b K ↔
        _root_.DerivedCategory.torAmplitudeIn _ a b (C.mapDerivedCategory.obj K) :=
    Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.trans
      (DerivedCategory.torAmplitudeIn_mapDerivedCategory_iff a b K).symm
  have hplus (K : P.FullSubcategory) : DerivedCategory.TStructure.t.plus K.obj := by
    obtain ⟨a, b, _, hv⟩ := K.property.1.2
    exact ⟨a, (DerivedCategory.isGE_iff K.obj a).2 fun i hi ↦ hv i (Or.inl hi)⟩
  have : F.Full := ⟨fun {K L} f ↦ by
    obtain ⟨g, hg⟩ := (bijective_comparisonUpperStar_mapDerivedCategory_map
      K.obj L.obj (hplus L)).2 f
    exact ⟨ObjectProperty.homMk g, hg⟩⟩
  have : F.Faithful := ⟨fun {K L} f g h ↦ ObjectProperty.hom_ext _
    ((bijective_comparisonUpperStar_mapDerivedCategory_map
      K.obj L.obj (hplus L)).1 h)⟩
  have hQ : Q.IsClosedUnderIsomorphisms := ⟨fun e h ↦ by
    exact ⟨(ordinaryBC_iff A T _).mpr
      ((DerivedCategory.boundedConstructible _ _).prop_of_iso e
        ((ordinaryBC_iff A T _).mp h.1)),
      (_root_.DerivedCategory.finiteTorAmplitude _).prop_of_iso e h.2⟩⟩
  have hm (K : P.FullSubcategory) : Q (C.mapDerivedCategory.obj K.obj) := by
    obtain ⟨a, b, hab, ht⟩ := K.property.2
    exact ⟨(ordinaryBC_iff A T _).mpr
      (DerivedCategory.boundedConstructible_comparisonUpperStar_mapDerivedCategory_obj
        ((etaleBC_iff A T _).mp K.property.1)), a, b, (htC K.obj a b).mp ht⟩
  have : (nativeDomain A true T).IsClosedUnderIsomorphisms := hQ
  have : (P.ι ⋙ realization A true E T).Full := by
    change F.Full
    infer_instance
  have : (P.ι ⋙ realization A true E T).Faithful := by
    change F.Faithful
    infer_instance
  apply buildDomainComparison A true E T hm
  intro K
  obtain ⟨L, hL, ⟨j⟩⟩ := (ordinaryBC_iff A T _).mp K.property.1
  obtain ⟨a, b, ht⟩ := K.property.2
  have htor := (_root_.DerivedCategory.torAmplitudeIn _ a b).prop_of_iso j.symm ht
  let L' : P.FullSubcategory := ⟨L, (etaleBC_iff A T L).mpr hL,
    min a b, max a b, min_le_max, (htC L _ _).mpr
      (htor.mono (min_le_left _ _) (le_max_right _ _))⟩
  exact ⟨L', ⟨j⟩⟩

private theorem internalDomainComparison (E : ∀ T : Scheme.{u}, Encoding A T)
    (T : Scheme.{u}) [CompactSpace T] [QuasiSeparatedSpace T] :
    Nonempty (DomainComparison A false E T) := by
  let : EssentiallySmall.{u + 1} T.ProEt := WeilConjectures.scalarReductionSiteSmall.{u, u} T
  let C := comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) T
  let e := (E T).fixedDerived
  let P := etaleDomain A T
  let Q := internalDomain A T
  let F := P.ι ⋙ C.mapDerivedCategory
  have hb := (encoding_constructibility A T (E T)).2
  have ht := (encoding_tensor_tor A T (E T)).2.2
  have htC (K : Etale.DerivedCategoryModule (ULift.{u + 1} A) T) (a b : ℤ) :
      Etale.DerivedCategory.hasTorAmplitudeIn (ULift.{u + 1} A) T a b K ↔
        _root_.DerivedCategory.torAmplitudeIn _ a b (C.mapDerivedCategory.obj K) :=
    Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.trans
      (DerivedCategory.torAmplitudeIn_mapDerivedCategory_iff a b K).symm
  have hplus (K : P.FullSubcategory) : DerivedCategory.TStructure.t.plus K.obj := by
    obtain ⟨a, b, _, hv⟩ := K.property.1.2
    exact ⟨a, (DerivedCategory.isGE_iff K.obj a).2 fun i hi ↦ hv i (Or.inl hi)⟩
  have : F.Full := ⟨fun {K L} f ↦ by
    obtain ⟨g, hg⟩ := (bijective_comparisonUpperStar_mapDerivedCategory_map
      K.obj L.obj (hplus L)).2 f
    exact ⟨ObjectProperty.homMk g, hg⟩⟩
  have : F.Faithful := ⟨fun {K L} f g h ↦ ObjectProperty.hom_ext _
    ((bijective_comparisonUpperStar_mapDerivedCategory_map
      K.obj L.obj (hplus L)).1 h)⟩
  let := (constantModelConstructibleFiniteTor_wellDefined (coefficient A) T).2.1
  have hQ : Q.IsClosedUnderIsomorphisms := ⟨fun j h ↦
    ⟨(constantModelBoundedConstructible (coefficient A) T).prop_of_iso j h.1,
      (_root_.DerivedCategory.finiteTorAmplitude _).prop_of_iso j h.2⟩⟩
  have hm (K : P.FullSubcategory) : Q ((F ⋙ e.inverse).obj K) := by
    obtain ⟨a, b, hab, htor⟩ := K.property.2
    have hbc := DerivedCategory.boundedConstructible_comparisonUpperStar_mapDerivedCategory_obj
      ((etaleBC_iff A T _).mp K.property.1)
    have he := e.counitIso.app (C.mapDerivedCategory.obj K.obj)
    exact ⟨(hb _).mpr ((ordinaryBC_iff A T _).mpr
      ((DerivedCategory.boundedConstructible _ _).prop_of_iso he.symm hbc)),
      a, b, (ht _ a b hab).mpr
        ((_root_.DerivedCategory.torAmplitudeIn _ a b).prop_of_iso he.symm
          ((htC K.obj a b).mp htor))⟩
  have : (P.ι ⋙ realization A false E T).Full := by
    change (F ⋙ e.inverse).Full
    infer_instance
  have : (P.ι ⋙ realization A false E T).Faithful := by
    change (F ⋙ e.inverse).Faithful
    infer_instance
  have : (nativeDomain A false T).IsClosedUnderIsomorphisms := hQ
  apply buildDomainComparison A false E T hm
  intro K
  obtain ⟨L, hL, ⟨j⟩⟩ := (ordinaryBC_iff A T _).mp ((hb K.obj).mp K.property.1)
  obtain ⟨a, b, htor⟩ := K.property.2
  have hab : min a b ≤ max a b := min_le_max
  have htK := htor.mono (min_le_left a b) (le_max_right a b)
  have htL := (_root_.DerivedCategory.torAmplitudeIn _ (min a b) (max a b)).prop_of_iso
    j.symm ((ht K.obj _ _ hab).mp htK)
  let L' : P.FullSubcategory := ⟨L, (etaleBC_iff A T L).mpr hL,
    min a b, max a b, hab, (htC L _ _).mpr htL⟩
  exact ⟨L', ⟨e.inverse.mapIso j ≪≫ (e.unitIso.app K.obj).symm⟩⟩

/-- The normalized realization restricts to a strong monoidal equivalence on the
finite-Tor bounded constructible domains, in both the internal and ordinary presentations.
Source: finite native tensor comparison, Step 1; Stacks 09AL.
(blueprint: lem-pur-finite-native-domain-comparison).

Proof: Bounded constructibility gives a bounded-below witness. Derived site-comparison
Hom bijectivity therefore supplies full faithfulness on the source domain. Bounded
constructible descent gives each target an etale origin, and Tor comparison preserves
and reflects every interval. In the internal presentation use encoding_constructibility,
encoding_tensor_tor and the encoding's unit and counit to make these identifications.
Enlarge unordered witness intervals to [min a b,max a b]. The etale constructible finite-Tor
subcategory contains the unit and is tensor closed. Transfer these properties along the
ambient normalized strong monoidal realization, using essential surjectivity and closure
under isomorphism. Restrict the ambient unit isomorphism and tensorator to the full
subcategories; the inclusions are faithful, so all coherence equations follow from the
ambient equations. Their underlying maps are definitionally the prescribed ones. -/
theorem finiteNativeDomainComparison_exists
    (E : ∀ T : Scheme.{u}, Encoding A T)
    (T : Scheme.{u}) [CompactSpace T] [QuasiSeparatedSpace T] (ordinary : Bool) :
    Nonempty (DomainComparison A ordinary E T) := by
  cases ordinary
  · exact internalDomainComparison A E T
  · exact ordinaryDomainComparison A E T


end AlgebraicGeometry.ProEtale.FiniteNativeTensor
