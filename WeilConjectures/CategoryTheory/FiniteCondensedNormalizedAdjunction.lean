/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteCtfInternalEtaleRealization
public import WeilConjectures.AlgebraicGeometry.FiniteNativeTensor.FiniteNativeTensorComparison
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriek
public import WeilConjectures.Compactification.NagataCompactification
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.SixFunctors.Etale.Derived.VerdierBiduality
import WeilConjectures.AlgebraicGeometry.FiniteCondensedCtfEquivalence
import WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek
import WeilConjectures.SixFunctors.Etale.Derived.WeilComplexDual
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import Mathlib.CategoryTheory.Adjunction.Restrict

/-! # Normalized finite constructible exceptional adjunction

Source: latest blueprint, `det-pd-biduality-coefficients.proof.md`, paragraph (i).
This is the compact-support and dualizing-object part of the finite comparison.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] WeilConjectures.scalarReductionSiteSmall
universe u v w v₀ w₀ c d c₀ d₀ b
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj
open AlgebraicGeometry

namespace CategoryTheory

/-- A right adjoint on the full constructible categories and the counit-normalized
comparison at the unit. The source dualizing object remains the ambient etale one.
Source: finite-coefficient comparison, compact-support and right-adjoint clauses
(blueprint: lem-sf-finite-condensed-normalized-adjunction). -/
structure FiniteCondensedNormalizedAdjunctionData
    {C : Type c} [Category.{v} C] {D : Type d} [Category.{w} D]
    {C₀ : Type c₀} [Category.{v₀} C₀] [MonoidalCategory C₀]
    {D₀ : Type d₀} [Category.{w₀} D₀] [MonoidalCategory D₀]
    (F : C ⥤ D) (F₀ : C₀ ⥤ D₀) [baseMonoidal : F₀.Monoidal]
    (Le : C ⥤ C₀) (Lp : D ⥤ D₀) (Ge : C₀ ⥤ C) (adje : Le ⊣ Ge)
    (P : ObjectProperty C) (Q : ObjectProperty D) (Q₀ : ObjectProperty D₀)
    (B : Type b) [Category B] (iB : B ⥤ C)
    (alpha : iB ⋙ Le ⋙ F₀ ≅ iB ⋙ F ⋙ Lp) where
  unit_constructible : Q₀ (𝟙_ D₀)
  support_preserves : ∀ K : Q.FullSubcategory, Q₀ (Lp.obj K.obj)
  Gp : Q₀.FullSubcategory ⥤ Q.FullSubcategory
  adjp : Q₀.lift (Q.ι ⋙ Lp) support_preserves ⊣ Gp
  dualizing_constructible : P (Ge.obj (𝟙_ C₀))
  dualizing_bounded : B
  dualizing_bounded_spec : iB.obj dualizing_bounded = Ge.obj (𝟙_ C₀)
  w : F.obj (Ge.obj (𝟙_ C₀)) ≅ (Gp.obj ⟨𝟙_ D₀, unit_constructible⟩).obj
  normalization :
    Lp.map (F.map (eqToHom dualizing_bounded_spec) ≫ w.hom) ≫
        (adjp.counit.app ⟨𝟙_ D₀, unit_constructible⟩).hom =
      alpha.inv.app dualizing_bounded ≫
        F₀.map (Le.map (eqToHom dualizing_bounded_spec) ≫ adje.counit.app (𝟙_ C₀)) ≫
          (Functor.Monoidal.εIso F₀).inv

private theorem finiteCondensedAdjunctionTransport
    {C : Type c} [Category.{v} C] {D : Type d} [Category.{w} D]
    {C₀ : Type c₀} [Category.{v₀} C₀] {D₀ : Type d₀} [Category.{w₀} D₀]
    (e : C ≌ D) (e₀ : C₀ ≌ D₀)
    (Le : C ⥤ C₀) (Lp : D ⥤ D₀) (Ge : C₀ ⥤ C) (adje : Le ⊣ Ge)
    (α : Le ⋙ e₀.functor ≅ e.functor ⋙ Lp) :
    ∃ adjp : Lp ⊣ e₀.inverse ⋙ Ge ⋙ e.functor,
      ∀ (U : C₀) (V : D₀) (v : e₀.functor.obj U ≅ V),
        Lp.map (e.functor.map (Ge.map
            ((e₀.unitIso.app U).hom ≫ e₀.inverse.map v.hom))) ≫
            adjp.counit.app V =
          α.inv.app (Ge.obj U) ≫ e₀.functor.map (adje.counit.app U) ≫ v.hom := by
  let q : e.inverse ⋙ Le ⋙ e₀.functor ≅ Lp :=
    Functor.isoWhiskerLeft e.inverse α ≪≫
      (Functor.associator e.inverse e.functor Lp).symm ≪≫
      Functor.isoWhiskerRight e.counitIso Lp ≪≫ Functor.leftUnitor Lp
  let adj := (e.symm.toAdjunction.comp (adje.comp e₀.toAdjunction)).ofNatIsoLeft q
  refine ⟨adj, ?_⟩
  intro U V v
  dsimp only [adj]
  simp only [Adjunction.ofNatIsoLeft_counit, Adjunction.comp_counit_app,
    Equivalence.toAdjunction_counit,
    Functor.whiskerLeft_app, NatTrans.comp_app]
  dsimp [q]
  simp only [Functor.map_comp, Category.id_comp, Category.comp_id,
    Category.assoc]
  have hn {X Y : C} (f : X ⟶ Y) :
      Lp.map (e.functor.map f) ≫ α.inv.app Y =
        α.inv.app X ≫ e₀.functor.map (Le.map f) := α.inv.naturality f
  rw [← reassoc_of% (hn (e.unitInv.app (Ge.obj (e₀.inverse.obj V))))]
  simp only [← Functor.map_comp_assoc, Equivalence.counitInv_functor_comp,
    Functor.map_id, Category.id_comp]
  rw [← e.functor.map_comp, ← Ge.map_comp]
  rw [reassoc_of% (hn (Ge.map
    (e₀.unitIso.hom.app U ≫ e₀.inverse.map v.hom)))]
  simp only [← Functor.map_comp_assoc]
  erw [adje.counit_naturality]
  simp only [Functor.map_comp, Category.assoc]
  have h₀ : e₀.functor.map (e₀.inverse.map v.hom) ≫ e₀.counit.app V =
      e₀.counit.app (e₀.functor.obj U) ≫ v.hom := e₀.counit_naturality v.hom
  rw [h₀]
  simp only [Equivalence.functor_unit_comp_assoc]


end CategoryTheory

namespace AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary

private theorem boundedConstructible_iff_source
    (A : Type (u + 1)) [CommRing A] [Finite A] (X : Scheme.{u})
    (K : Etale.DerivedCategoryModule A X) :
    Etale.DerivedCategory.isBoundedConstructible A X K ↔
      Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) X K := by
  constructor
  · rintro ⟨hc, a, b, -, hz⟩
    refine ⟨⟨⟨a, ?_⟩, ⟨b, ?_⟩⟩, fun i ↦
      (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).1 (hc i)⟩
    · exact (_root_.DerivedCategory.isGE_iff K a).2 (fun i hi ↦ hz i (.inl hi))
    · exact (_root_.DerivedCategory.isLE_iff K b).2 (fun i hi ↦ hz i (.inr hi))
  · rintro ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hc⟩
    refine ⟨fun i ↦
      (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).2 (hc i),
      min a b, b, min_le_right _ _, fun i hi ↦ ?_⟩
    rcases hi with hi | hi
    · exact (_root_.DerivedCategory.isGE_iff K a).1 ha i
        (hi.trans_le (min_le_left _ _))
    · exact (_root_.DerivedCategory.isLE_iff K b).1 hb i hi

/-- The normalized exceptional adjunction comparison, without any internal-Hom assertion.

Source: latest blueprint, `det-pd-biduality-coefficients.proof.md`, paragraph (i),
compatibility with compact support and its right adjoint
(blueprint: lem-sf-finite-condensed-normalized-adjunction).

Proof:
1. Finite etale/pro-etale constructible descent and the section-action encoding identify
   the full finite-Tor constructible subcategories on T and on Spec k. The equivalences
   retain their natural isomorphisms with the ambient realization functors.
2. The constant coefficient complex is constructible and has Tor amplitude [0,0].
   Finite-ring etale six-operation stability makes compact support preserve the source
   domain and its ambient right adjoint preserve the base domain. In particular the
   ambient right adjoint of the unit is constructible finite-Tor and bounded below.
3. Restrict the etale adjunction along these full inclusions. For a condensed input,
   take its etale preimage under the base equivalence, apply the restricted etale right
   adjoint, and then realize on T. The given alpha identifies the corresponding left
   adjoint with the actual condensed compact-support restriction. This constructs Gp,
   adjp, and support preservation. The unit belongs to the target base domain because
   the specified monoidal unit isomorphism identifies it with the realized source unit.
4. Apply this transported adjunction to the base unit. The unit of the base equivalence
   and the inverse monoidal unit isomorphism identify the resulting object with the
   realization of the ambient etale dualizing object. Their composite is w.
5. The counit of a composite adjunction is the composite of the two counits; transporting
   a left adjoint along alpha precomposes its counit with alpha inverse. Naturality of
   the base equivalence unit and its triangle identity therefore give the displayed
   normalization. Use the actual bounded-below lift of the dualizing object, so that
   dualizing_bounded_spec is reflexive. This argument works for every supplied alpha;
   no change of the specified compact-support arrow is required. -/
theorem finiteCondensedNormalizedAdjunction
    (p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime] (hpℓ : p ≠ ℓ)
    (k : Type u) [Field k] [IsAlgClosed k] [CharP k p]
    (A : Type u) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A] [IsTopologicalRing A]
    [HasInvertibleExponent (ULift.{u + 1} A) (Spec (.of k))]
    (enc : ∀ X : Scheme.{u}, Encoding A X)
    (T : Scheme.{u}) (a : T ⟶ Spec (.of k))
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
    (alpha : _root_.DerivedCategory.Plus.ι ⋙
        Etale.rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} (ULift.{u + 1} A)) (NagataCompactification a) ⋙
            internalEtaleRealization A (Spec (.of k)) (enc (Spec (.of k))) ≅
      _root_.DerivedCategory.Plus.ι ⋙ internalEtaleRealization A T (enc T) ⋙
        CondensedRing.rightDerivedLowerShriekOfCompactification
          (coefficient A) (NagataCompactification a)) :
    Nonempty (CategoryTheory.FiniteCondensedNormalizedAdjunctionData
      (baseMonoidal := FiniteNativeTensor.realizationMonoidal
        A (Spec (.of k)) (enc (Spec (.of k))))
      (internalEtaleRealization A T (enc T))
      (internalEtaleRealization A (Spec (.of k)) (enc (Spec (.of k))))
      (Etale.rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} (ULift.{u + 1} A)) (NagataCompactification a))
      (CondensedRing.rightDerivedLowerShriekOfCompactification
        (coefficient A) (NagataCompactification a))
      (Etale.rightDerivedUpperShriekOfCompactification
        (ULift.{u + 1} A) (NagataCompactification a))
      (Etale.rightDerivedUpperShriekOfCompactificationAdjunction
        (ULift.{u + 1} A) (NagataCompactification a))
      (Etale.DerivedCategory.isBoundedConstructible (ULift.{u + 1} A) T ⊓
        _root_.DerivedCategory.finiteTorAmplitude _)
      (constantModelBoundedConstructible (coefficient A) T ⊓
        _root_.DerivedCategory.finiteTorAmplitude _)
      (constantModelBoundedConstructible (coefficient A) (Spec (.of k)) ⊓
        _root_.DerivedCategory.finiteTorAmplitude _)
      (_root_.DerivedCategory.Plus
        (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} A))))
      _root_.DerivedCategory.Plus.ι alpha) := by
  let P (X : Scheme.{u}) :=
    Etale.DerivedCategory.isBoundedConstructible (ULift.{u + 1} A) X ⊓
      _root_.DerivedCategory.finiteTorAmplitude _
  let Q (X : Scheme.{u}) := constantModelBoundedConstructible (coefficient A) X ⊓
    _root_.DerivedCategory.finiteTorAmplitude _
  let s := Spec (.of k)
  let F := internalEtaleRealization A T (enc T)
  let F₀ := internalEtaleRealization A s (enc s)
  let Le := Etale.rightDerivedLowerShriekOfCompactification
    (ModuleCat.{u + 1} (ULift.{u + 1} A)) (NagataCompactification a)
  let Lp := CondensedRing.rightDerivedLowerShriekOfCompactification
    (coefficient A) (NagataCompactification a)
  let Ge := Etale.rightDerivedUpperShriekOfCompactification
    (ULift.{u + 1} A) (NagataCompactification a)
  let adje := Etale.rightDerivedUpperShriekOfCompactificationAdjunction
    (ULift.{u + 1} A) (NagataCompactification a)
  let : IsNoetherian T := isNoetherian_of_locallyOfFiniteType a
  have hP (X : Scheme.{u}) (K : Etale.DerivedCategoryModule (ULift.{u + 1} A) X) :
      P X K ↔ Etale.DerivedCategory.constructibleFiniteTor
        (ModuleCat.{u + 1} (ULift.{u + 1} A)) X K :=
    and_congr (boundedConstructible_iff_source (ULift.{u + 1} A) X K) Iff.rfl
  have hunit : P s (𝟙_ _) :=
    (hP s _).mpr (Etale.constructibleFiniteTor_unit (ULift.{u + 1} A))
  have hLe : ∀ K : (P T).FullSubcategory, P s (Le.obj K.obj) := by
    intro K
    let : HasCompactification a := (NagataCompactification a).hasCompactification
    have h := Etale.constructibleFiniteTor_rightDerivedLowerShriek
      (ULift.{u + 1} A) (𝟙 s) a ((hP T K.obj).mp K.property)
    exact (hP s _).mpr ((Etale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} (ULift.{u + 1} A)) s).prop_of_iso
        ((Etale.rightDerivedLowerShriekIso (ULift.{u + 1} A)
          (NagataCompactification a)).app K.obj) h)
  have hGe : ∀ K : (P s).FullSubcategory, P T (Ge.obj K.obj) := by
    intro K
    let : HasCompactification a := (NagataCompactification a).hasCompactification
    let adj := (Etale.rightDerivedUpperShriekAdjunction (ULift.{u + 1} A) a).ofNatIsoLeft
      (Etale.rightDerivedLowerShriekIso (ULift.{u + 1} A) (NagataCompactification a)).symm
    exact (hP T _).mpr ((Etale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} (ULift.{u + 1} A)) T).prop_of_iso
        (((adje.rightAdjointUniq adj).app K.obj).symm)
          (Etale.constructibleFiniteTor_rightDerivedUpperShriek
            (ULift.{u + 1} A) (𝟙 s) a ((hP s K.obj).mp K.property)))
  obtain ⟨hF, hR⟩ := finiteCondensedCtfEquivalence p ℓ hpℓ k A enc T a
  obtain ⟨hF₀, hR₀⟩ := finiteCondensedCtfEquivalence p ℓ hpℓ k A enc s (𝟙 s)
  let R := (Q T).lift ((P T).ι ⋙ F) hF
  let R₀ := (Q s).lift ((P s).ι ⋙ F₀) hF₀
  have : R.IsEquivalence := hR
  have : R₀.IsEquivalence := hR₀
  let e := R.asEquivalence
  let e₀ := R₀.asEquivalence
  have hplus (K : (P T).FullSubcategory) :
      _root_.DerivedCategory.TStructure.t.plus K.obj := by
    obtain ⟨_, c, d, _, hv⟩ := K.property.1
    exact ⟨c, (_root_.DerivedCategory.isGE_iff K.obj c).mpr
      (fun i hi ↦ hv i (Or.inl hi))⟩
  let b : (P T).FullSubcategory ⥤ _root_.DerivedCategory.Plus
      (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} A))) :=
    { obj := fun K ↦ ⟨K.obj, hplus K⟩
      map := fun f ↦ ObjectProperty.homMk f.hom }
  have : (constantModelBoundedConstructible (coefficient A) s).IsClosedUnderIsomorphisms :=
    (constantModelConstructibleFiniteTor_wellDefined (coefficient A) s).2.1
  have : (Q s).IsClosedUnderIsomorphisms := by dsimp [Q]; infer_instance
  let : F₀.Monoidal := FiniteNativeTensor.realizationMonoidal A s (enc s)
  have huQ : Q s (𝟙_ _) :=
    (Q s).prop_of_iso (Functor.Monoidal.εIso F₀).symm (hF₀ ⟨𝟙_ _, hunit⟩)
  have hLp : ∀ K : (Q T).FullSubcategory, Q s (Lp.obj K.obj) := by
    intro K
    let L := e.inverse.obj K
    exact (Q s).prop_of_iso
      (alpha.app (b.obj L) ≪≫ Lp.mapIso ((Q T).ι.mapIso (e.counitIso.app K)))
      (hF₀ ⟨Le.obj L.obj, hLe L⟩)
  let Ler := (P s).lift ((P T).ι ⋙ Le) hLe
  let Ger := (P T).lift ((P s).ι ⋙ Ge) hGe
  let Lpr := (Q s).lift ((Q T).ι ⋙ Lp) hLp
  let adjer : Ler ⊣ Ger := adje.restrictFullyFaithful
    (ObjectProperty.fullyFaithfulι (P T)) (ObjectProperty.fullyFaithfulι (P s))
      (Iso.refl _) (Iso.refl _)
  let αr : Ler ⋙ e₀.functor ≅ e.functor ⋙ Lpr := NatIso.ofComponents
    (fun K ↦ (Q s).isoMk (alpha.app (b.obj K))) (by
      intro K L f
      apply ObjectProperty.hom_ext
      exact alpha.hom.naturality (b.map f))
  obtain ⟨adjp, hn⟩ := CategoryTheory.finiteCondensedAdjunctionTransport
    e e₀ Ler Lpr Ger adjer αr
  let U : (P s).FullSubcategory := ⟨𝟙_ _, hunit⟩
  let V : (Q s).FullSubcategory := ⟨𝟙_ _, huQ⟩
  let v : e₀.functor.obj U ≅ V := (Q s).isoMk (Functor.Monoidal.εIso F₀).symm
  let Gp := e₀.inverse ⋙ Ger ⋙ e.functor
  let w := (Q T).ι.mapIso (e.functor.mapIso
    (Ger.mapIso (e₀.unitIso.app U ≪≫ e₀.inverse.mapIso v)))
  have hc : (adjer.counit.app U).hom = adje.counit.app (𝟙_ _) := by
    change (P s).ι.map (adjer.counit.app U) = _
    dsimp only [adjer]
    rw [Adjunction.map_restrictFullyFaithful_counit_app]
    change (𝟙 _) ≫ Le.map (𝟙 _) ≫ adje.counit.app U.obj = adje.counit.app U.obj
    erw [Le.map_id, Category.id_comp, Category.id_comp]
  refine ⟨{ unit_constructible := huQ
            support_preserves := hLp
            Gp := Gp
            adjp := adjp
            dualizing_constructible := hGe U
            dualizing_bounded := b.obj (Ger.obj U)
            dualizing_bounded_spec := rfl
            w := w
            normalization := ?_ }⟩
  have h := congrArg (fun f ↦ f.hom) (hn U V v)
  change Lp.map w.hom ≫ (adjp.counit.app V).hom =
    alpha.inv.app (b.obj (Ger.obj U)) ≫
      F₀.map (adjer.counit.app U).hom ≫ (Functor.Monoidal.εIso F₀).inv at h
  change Lp.map (F.map (𝟙 _) ≫ w.hom) ≫ (adjp.counit.app V).hom =
    alpha.inv.app (b.obj (Ger.obj U)) ≫
      F₀.map (Le.map (𝟙 _) ≫ adje.counit.app (𝟙_ _)) ≫
        (Functor.Monoidal.εIso F₀).inv
  erw [F.map_id, Le.map_id, Category.id_comp, Category.id_comp]
  rw [hc] at h
  exact h

end AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary
