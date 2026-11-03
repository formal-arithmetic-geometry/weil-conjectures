/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constructible.ProEtaleConstructibleSheaf
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import WeilConjectures.SixFunctors.ProEtale.ConstructibleSheaf
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.AlgebraicGeometry.Compact.CompactSupportComparisonUnit
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleEncoding
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.AlgebraicGeometry.ProEtaleConstructibleOrigin
public import WeilConjectures.AlgebraicGeometry.Compact.CompactSupportComparisonUnit

/-!
# Constructible pro-etale coefficients are of etale origin

Source: Weil blueprint, smooth purity, `lem-sf-proetale-constructible-origin`;
Stacks Project, Tags 09AK and 09AL (blueprint: lem-sf-proetale-constructible-origin).

The scalar conversion below is induced by constant scalar sections and sheafification.
It retains the recorded intrinsic constructibility predicate and the recorded category
of finite coefficient modules. Discrete topology is fixed canonically on lifted coefficients.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

variable (T : Scheme.{u}) (B : Type u) [CommRing B] [Finite B]

/-- The recorded finite coefficient ring sheaf with discrete lifted coefficients.
Source: blueprint, finite coefficient convention
(blueprint: lem-sf-proetale-constructible-origin). -/
noncomputable abbrev originCoefficientRing : Sheaf (Scheme.ProEt.topology T) RingCat.{u + 1} :=
  @finiteCoefficientRingSheaf.{u} T (ULift.{u + 1, u} B) _ _ ⊥
    (discreteTopology_bot _)

/-- The recorded module category with the discrete coefficient topology fixed.
Source: blueprint, finite coefficient convention
(blueprint: lem-sf-proetale-constructible-origin). -/
noncomputable abbrev OriginModules :=
  ringedSiteModules.{u + 1} (originCoefficientRing T B)

/-- The recorded derived category with the discrete coefficient topology fixed.
Source: blueprint, finite coefficient convention
(blueprint: lem-sf-proetale-constructible-origin). -/
noncomputable abbrev OriginDerivedCategory :=
  @FiniteCoefficientDerivedCategory.{u} T (ULift.{u + 1, u} B) _ _ ⊥
    (discreteTopology_bot _)

/-- The canonical comparison from sheafification in rings to sheafification in
commutative rings followed by forgetting commutativity. It is adjoint to the
commutative-ring sheafification unit, so its data involve no choice.
Source: Stacks, sheafification of algebraic structures
(blueprint: lem-sf-proetale-constructible-origin). -/
noncomputable def originConstantRingComparison :
    (constantSheaf (Scheme.ProEt.topology T) RingCat.{u + 1}).obj
      (RingCat.of (ULift.{u + 1, u} B)) ⟶
    (sheafCompose (Scheme.ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (Scheme.proEtaleConstantRing T B) :=
  (sheafComposeNatTrans (Scheme.ProEt.topology T)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
    (sheafificationAdjunction (Scheme.ProEt.topology T) CommRingCat.{u + 1})
    (sheafificationAdjunction (Scheme.ProEt.topology T) RingCat.{u + 1})).app
      ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} B)))

/-- Constant scalars induce the canonical map from the constant ring sheaf to the
continuous-function coefficient sheaf. The second arrow is adjoint to the recorded
constant scalar map. Source: Stacks, constant sheaves and Tag 09AK
(blueprint: lem-sf-proetale-constructible-origin). -/
noncomputable def originCoefficientMap :
    (sheafCompose (Scheme.ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (Scheme.proEtaleConstantRing T B) ⟶ originCoefficientRing T B :=
  (asIso (originConstantRingComparison T B)).inv ≫
    ((sheafificationAdjunction (Scheme.ProEt.topology T) RingCat.{u + 1}).homEquiv _ _).symm
      (@finiteCoefficientScalarMap.{u} T (ULift.{u + 1, u} B) _ _ ⊥ (discreteTopology_bot _))

/-- Restrict scalars along the canonical coefficient map; the underlying additive sheaf
is unchanged. This is the identification used to read intrinsic constructibility.
Source: Stacks, Tag 09AK (blueprint: lem-sf-proetale-constructible-origin). -/
noncomputable def originConstantModules :
    OriginModules T B ⥤ Scheme.proEtaleRingModules T (Scheme.proEtaleConstantRing T B) :=
  SheafOfModules.restrictScalars.{u + 1} (originCoefficientMap T B)

private theorem originScalar_fac :
    Scheme.proEtaleModuleScalarUnit T B ≫ (originCoefficientMap T B).hom =
      @finiteCoefficientScalarMap.{u} T (ULift.{u + 1, u} B) _ _ ⊥
        (discreteTopology_bot _) := by
  have hc := sheafComposeNatTrans_fac (Scheme.ProEt.topology T)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
    (sheafificationAdjunction (Scheme.ProEt.topology T) CommRingCat.{u + 1})
    (sheafificationAdjunction (Scheme.ProEt.topology T) RingCat.{u + 1})
    ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} B)))
  change toSheafify (Scheme.ProEt.topology T)
      ((Functor.const T.ProEtᵒᵖ).obj (RingCat.of (ULift.{u + 1, u} B))) ≫
    (originConstantRingComparison T B).hom = Scheme.proEtaleModuleScalarUnit T B at hc
  have hm : originConstantRingComparison T B ≫ originCoefficientMap T B =
      ((sheafificationAdjunction (Scheme.ProEt.topology T) RingCat.{u + 1}).homEquiv
        _ _).symm (@finiteCoefficientScalarMap.{u} T (ULift.{u + 1, u} B)
          _ _ ⊥ (discreteTopology_bot _)) := by
    change (asIso (originConstantRingComparison T B)).hom ≫
      ((asIso (originConstantRingComparison T B)).inv ≫ _) = _
    rw [Iso.hom_inv_id_assoc]
  rw [← hc, Category.assoc, ← ObjectProperty.FullSubcategory.comp_hom, hm]
  exact ((sheafificationAdjunction (Scheme.ProEt.topology T) RingCat.{u + 1}).homEquiv
    _ _).apply_symm_apply _

set_option linter.unusedSectionVars false in
attribute [instance] isIso_originConstantRingComparison

set_option backward.isDefEq.respectTransparency false in
/-- The recorded canonical inverse image on module sheaves.
Source: blueprint, site comparison (blueprint: lem-sf-proetale-constructible-origin). -/
noncomputable abbrev originComparison :
    Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) ⥤ OriginModules T B :=
  @finiteCoefficientComparison.{u} T (ULift.{u + 1, u} B) _ _ ⊥ (discreteTopology_bot _)

private theorem fixedDerivedOrigin (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} Λ)))
    (hc : ∀ q : ℤ, IsConstructible Λ
      ((DerivedCategory.homologyFunctor _ q).obj K))
    (a b : ℤ) (hz : ∀ q : ℤ, (q < a ∨ b < q) →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj K)) :
    ∃ L : Etale.DerivedCategoryModule Λ T,
      Etale.DerivedCategory.isBoundedConstructible Λ T L ∧
      Nonempty ((comparisonUpperStar (ModuleCat.{u + 1} Λ) T).mapDerivedCategory.obj L ≅ K) := by
  let ν := comparisonUpperStar (ModuleCat.{u + 1} Λ) T
  have : IsIso (derivedComparisonAdjunctionPlus (ModuleCat.{u + 1} Λ) T).unit :=
    isIso_compactSupportComparisonUnit T Λ
  have : ν.mapDerivedCategoryPlus.Full :=
    (derivedComparisonAdjunctionPlus (ModuleCat.{u + 1} Λ) T).fullyFaithfulLOfIsIsoUnit.full
  let F := ν.mapDerivedCategoryPlus ⋙ DerivedCategory.Plus.ι
  let P := ν.essImage
  have hP (G : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} Λ)) (hG : P G) :
      F.essImage ((DerivedCategory.singleFunctor _ 0).obj G) := by
    obtain ⟨H, ⟨e⟩⟩ := hG
    refine ⟨(DerivedCategory.Plus.singleFunctor _ 0).obj H, ⟨?_⟩⟩
    exact (ν.mapDerivedCategoryPlusCompatibility.app _) ≪≫
      ν.mapDerivedCategory.mapIso ((DerivedCategory.Plus.singleFunctorιIso _ 0).app H) ≪≫
      (ν.mapDerivedCategorySingleFunctor 0).app H ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso e
  have hGE : K.IsGE a := (DerivedCategory.isGE_iff K a).mpr
    (fun q hq ↦ hz q (Or.inl hq))
  have hLE : K.IsLE b := (DerivedCategory.isLE_iff K b).mpr
    (fun q hq ↦ hz q (Or.inr hq))
  have hK : F.essImage K := DerivedCategory.prop_of_bounded F.essImage P hP K
    ⟨⟨a, hGE⟩, ⟨b, hLE⟩⟩ (fun q ↦ by
      obtain ⟨G, _, he⟩ := exists_isConstructibleSheaf_iso_comparisonUpperStar_obj Λ (hc q)
      exact ⟨G, he⟩)
  obtain ⟨L, ⟨e⟩⟩ := hK
  let e' : ν.mapDerivedCategory.obj L.obj ≅ K :=
    (ν.mapDerivedCategoryPlusCompatibility.app L).symm ≪≫ e
  refine ⟨L.obj, ⟨?_, ?_⟩, ⟨e'⟩⟩
  · intro q
    have hq := isConstructible_of_iso
      ((DerivedCategory.homologyFunctor _ q).mapIso e'.symm) (hc q)
    have hν := isConstructible_of_iso
      ((ν.mapDerivedCategoryHomologyFunctorIso q).symm.app L.obj) hq
    obtain ⟨G, hG, ⟨eG⟩⟩ :=
      exists_isConstructibleSheaf_iso_comparisonUpperStar_obj Λ hν
    have : Scheme.IsConstructibleSheaf G := hG
    exact (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr
      (Scheme.IsConstructibleSheaf.of_iso (ν.preimageIso eG))
  · refine ⟨min a b, b, min_le_right _ _, fun q hq ↦ ?_⟩
    apply ν.isZero_homologyFunctor_of_isZero_homologyFunctor_mapDerivedCategory_obj
    exact (hz q (hq.imp (fun h ↦ lt_of_lt_of_le h (min_le_left _ _)) id)).of_iso
      ((DerivedCategory.homologyFunctor _ q).mapIso e')

set_option backward.isDefEq.respectTransparency false in
private noncomputable def originRealizationUnit :
    𝟭 (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1, u} B))) ⟶
      @finiteCoefficientRealization.{u} T (ULift.{u + 1, u} B) _ _ ⊥
        (discreteTopology_bot _) ⋙ originConstantModules T B ⋙
          Scheme.proEtaleModuleRestriction T B where
  app F := by
    let P : PresheafOfModules.{u + 1}
        ((Functor.const T.ProEtᵒᵖ).obj (RingCat.of (ULift.{u + 1, u} B))) :=
      (finiteCoefficientModulePresheaf T.ProEt (ULift.{u + 1, u} B)).obj F.obj
    let τ := (PresheafOfModules.sheafificationAdjunction.{u + 1}
      (@finiteCoefficientScalarMap.{u} T (ULift.{u + 1, u} B) _ _ ⊥
        (discreteTopology_bot _))).unit.app P
    refine ⟨{ app := ?_, naturality := ?_ }⟩
    · intro U
      refine ModuleCat.ofHom (X := F.obj.obj U)
        (Y := ((Scheme.proEtaleModuleRestriction T B).obj
          ((originConstantModules T B).obj
            ((@finiteCoefficientRealization.{u} T (ULift.{u + 1, u} B) _ _ ⊥
              (discreteTopology_bot _)).obj F))).obj.obj U)
        { toFun := τ.app U
          map_add' := map_add _
          map_smul' := ?_ }
      intro b m
      have hs := ConcreteCategory.congr_hom
        (congr_app (originScalar_fac T B).symm U) b
      change (@finiteCoefficientScalarMap.{u} T (ULift.{u + 1, u} B) _ _ ⊥
        (discreteTopology_bot _)).app U b =
        (originCoefficientMap T B).hom.app U
          ((Scheme.proEtaleModuleScalarUnit T B).app U b) at hs
      let N := ((@finiteCoefficientRealization.{u} T (ULift.{u + 1, u} B)
        _ _ ⊥ (discreteTopology_bot _)).obj F).val.obj U
      change τ.app U (b • m) =
        (originCoefficientMap T B).hom.app U
          ((Scheme.proEtaleModuleScalarUnit T B).app U b) • (show N from τ.app U m)
      calc
        _ = (@finiteCoefficientScalarMap.{u} T (ULift.{u + 1, u} B) _ _ ⊥
            (discreteTopology_bot _)).app U b • (show N from τ.app U m) :=
          (τ.app U).hom.map_smul b m
        _ = _ := by rw [hs]
    · intro U V f
      ext m
      exact ConcreteCategory.congr_hom (τ.naturality f) m
  naturality {F G} f := by
    ext U m
    exact ConcreteCategory.congr_hom
      (congr_app (toSheafify_naturality (Scheme.ProEt.topology T)
        (Functor.whiskerRight f.hom
          (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1, u} B))
            AddCommGrpCat.{u + 1}))) U) m

private theorem originRealizationUnit_isIso : IsIso (originRealizationUnit T B) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro F
  rw [← isIso_iff_of_reflects_iso _ (sheafCompose (Scheme.ProEt.topology T)
    (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) AddCommGrpCat.{u + 1}))]
  rw [← isIso_iff_of_reflects_iso _
    (sheafToPresheaf (Scheme.ProEt.topology T) AddCommGrpCat)]
  have he : (sheafToPresheaf (Scheme.ProEt.topology T) AddCommGrpCat).map
      ((sheafCompose (Scheme.ProEt.topology T)
        (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) AddCommGrpCat.{u + 1})).map
          ((originRealizationUnit T B).app F)) =
      toSheafify (Scheme.ProEt.topology T)
        (F.obj ⋙ forget₂ (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) AddCommGrpCat.{u + 1}) := by
    ext U m
    rfl
  rw [he]
  exact isIso_toSheafify (Scheme.ProEt.topology T)
    ((sheafCompose (Scheme.ProEt.topology T)
      (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) AddCommGrpCat.{u + 1})).obj F).property

private noncomputable def originFixedModules :
    OriginModules T B ⥤
      Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) :=
  originConstantModules T B ⋙ Scheme.proEtaleModuleRestriction T B

private noncomputable def originFixedComparisonIso :
    originComparison T B ⋙ originFixedModules T B ≅
      comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) T :=
  have := originRealizationUnit_isIso T B
  Functor.isoWhiskerLeft
    (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) T)
    (asIso (originRealizationUnit T B)).symm

/-- The recorded canonical derived inverse image.
Source: blueprint, site comparison (blueprint: lem-sf-proetale-constructible-origin). -/
noncomputable abbrev originDerivedComparison :
    Etale.DerivedCategoryModule (ULift.{u + 1, u} B) T ⥤ OriginDerivedCategory T B :=
  @finiteCoefficientDerivedComparison.{u} T (ULift.{u + 1, u} B) _ _ ⊥ (discreteTopology_bot _)

/-- Intrinsic bounded constructibility: every cohomology sheaf is intrinsically
constructible, and cohomology vanishes outside a finite interval.
Source: blueprint clause (ii), Stacks Tag 09AL
(blueprint: lem-sf-proetale-constructible-origin). -/
noncomputable def intrinsicOriginBoundedConstructible :
    ObjectProperty (OriginDerivedCategory T B) :=
  fun K ↦
    (∀ q : ℤ, Scheme.IsConstructibleProEtaleModuleSheaf T B
      ((originConstantModules T B).obj
        ((_root_.DerivedCategory.homologyFunctor (OriginModules T B) q).obj K))) ∧
    ∃ a b : ℤ, a ≤ b ∧ ∀ q : ℤ, (q < a ∨ b < q) →
      IsZero ((_root_.DerivedCategory.homologyFunctor (OriginModules T B) q).obj K)

/-- The recorded etale-origin object class, with discrete lifted coefficients.
Source: blueprint, final clause (blueprint: lem-sf-proetale-constructible-origin). -/
noncomputable abbrev etaleOriginBoundedConstructible : ObjectProperty (OriginDerivedCategory T B) :=
  @isBoundedConstructibleFiniteCoefficient.{u} T (ULift.{u + 1, u} B) _ _ ⊥
    (discreteTopology_bot _)

private noncomputable def originFixedDerivedIso :
    originDerivedComparison T B ⋙ (originFixedModules T B).mapDerivedCategory ≅
      (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) T).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso (originComparison T B)
    (originFixedModules T B)).symm ≪≫
    Functor.mapDerivedCategoryNatIso (originFixedComparisonIso T B)

private theorem intrinsicOrigin_iso {K L : OriginDerivedCategory T B} (e : K ≅ L)
    (hK : intrinsicOriginBoundedConstructible T B K) :
    intrinsicOriginBoundedConstructible T B L := by
  constructor
  · intro q
    apply (Scheme.proEtaleModuleRestriction_constructible_iff T B _).mpr
    exact isConstructible_of_iso
      ((originFixedModules T B).mapIso ((DerivedCategory.homologyFunctor _ q).mapIso e))
      ((Scheme.proEtaleModuleRestriction_constructible_iff T B _).mp (hK.1 q))
  · obtain ⟨a, b, hab, hz⟩ := hK.2
    exact ⟨a, b, hab, fun q hq ↦ (hz q hq).of_iso
      ((DerivedCategory.homologyFunctor _ q).mapIso e.symm)⟩

private theorem intrinsicOrigin_image
    (L : Etale.DerivedCategoryModule (ULift.{u + 1, u} B) T)
    (hL : Etale.DerivedCategory.isBoundedConstructible (ULift.{u + 1, u} B) T L) :
    intrinsicOriginBoundedConstructible T B ((originDerivedComparison T B).obj L) := by
  let E := originFixedModules T B
  let ν := comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) T
  let e := originFixedDerivedIso T B
  constructor
  · intro q
    apply (Scheme.proEtaleModuleRestriction_constructible_iff T B _).mpr
    have : Scheme.IsConstructibleSheaf ((DerivedCategory.homologyFunctor _ q).obj L) :=
      (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp (hL.1 q)
    have hc := isConstructible_comparisonUpperStar_obj
      ((DerivedCategory.homologyFunctor _ q).obj L)
    exact isConstructible_of_iso
      ((ν.mapDerivedCategoryHomologyFunctorIso q).app L ≪≫
        (DerivedCategory.homologyFunctor _ q).mapIso (e.app L).symm ≪≫
        (E.mapDerivedCategoryHomologyFunctorIso q).symm.app _) hc
  · obtain ⟨a, b, hab, hz⟩ := hL.2
    exact ⟨a, b, hab, fun q hq ↦
      (originComparison T B).isZero_homologyFunctor_mapDerivedCategory_obj (hz q hq)⟩

private theorem intrinsicOrigin_preimage (K : OriginDerivedCategory T B)
    (hK : intrinsicOriginBoundedConstructible T B K) :
    ∃ L : Etale.DerivedCategoryModule (ULift.{u + 1, u} B) T,
      Etale.DerivedCategory.isBoundedConstructible (ULift.{u + 1, u} B) T L ∧
        Nonempty ((originDerivedComparison T B).obj L ≅ K) := by
  let E := originFixedModules T B
  obtain ⟨a, b, _, hz⟩ := hK.2
  have hc (q : ℤ) : IsConstructible (ULift.{u + 1, u} B)
      ((DerivedCategory.homologyFunctor _ q).obj (E.mapDerivedCategory.obj K)) := by
    exact isConstructible_of_iso ((E.mapDerivedCategoryHomologyFunctorIso q).app K)
      ((Scheme.proEtaleModuleRestriction_constructible_iff T B _).mp (hK.1 q))
  obtain ⟨L, hL, ⟨e⟩⟩ := fixedDerivedOrigin T (ULift.{u + 1, u} B)
    (E.mapDerivedCategory.obj K) hc a b
    (fun q hq ↦ E.isZero_homologyFunctor_mapDerivedCategory_obj (hz q hq))
  exact ⟨L, hL, ⟨E.mapDerivedCategory.preimageIso
    ((originFixedDerivedIso T B).app L ≪≫ e)⟩⟩

private theorem etaleOrigin_iff (K : OriginDerivedCategory T B) :
    etaleOriginBoundedConstructible T B K ↔
      ∃ L : Etale.DerivedCategoryModule (ULift.{u + 1, u} B) T,
        Etale.DerivedCategory.isBoundedConstructible (ULift.{u + 1, u} B) T L ∧
          Nonempty ((originDerivedComparison T B).obj L ≅ K) := by
  constructor
  · rintro ⟨L, ⟨hc, hb⟩, he⟩
    refine ⟨L, ⟨?_, hb⟩, he⟩
    intro q
    obtain ⟨S, _, hS⟩ := hc q
    exact ⟨S, hS⟩
  · rintro ⟨L, ⟨hc, hb⟩, he⟩
    refine ⟨L, ⟨?_, hb⟩, he⟩
    intro q
    obtain ⟨S, hS⟩ := hc q
    exact ⟨S, S.isConstructible_stratum, hS⟩

/-- Both equivalences are induced by the specified comparison, expressed by natural
isomorphisms after the full inclusions. The last equality compares object properties
on exactly the same ambient derived category.
Source: blueprint clauses (i), (ii), and the final sentence; Stacks Tags 09AK, 09AL
(blueprint: lem-sf-proetale-constructible-origin). -/
noncomputable def ConstructibleOriginComparison : Prop :=
  (∃ e :
    ObjectProperty.FullSubcategory (Scheme.IsConstructibleEtaleModuleSheaf (T := T)
      (Λ := ULift.{u + 1, u} B)) ≌
    ObjectProperty.FullSubcategory (Scheme.IsConstructibleProEtaleModuleSheaf T B),
    Nonempty
      (ObjectProperty.ι (Scheme.IsConstructibleEtaleModuleSheaf (T := T)
          (Λ := ULift.{u + 1, u} B)) ⋙ originComparison T B ⋙ originConstantModules T B ≅
        e.functor ⋙ ObjectProperty.ι (Scheme.IsConstructibleProEtaleModuleSheaf T B))) ∧
  (∃ e :
    (Etale.DerivedCategory.isBoundedConstructible (ULift.{u + 1, u} B) T).FullSubcategory ≌
    (intrinsicOriginBoundedConstructible T B).FullSubcategory,
    Nonempty
      ((Etale.DerivedCategory.isBoundedConstructible (ULift.{u + 1, u} B) T).ι ⋙
        originDerivedComparison T B ≅ e.functor ⋙ (intrinsicOriginBoundedConstructible T B).ι)) ∧
  intrinsicOriginBoundedConstructible T B = etaleOriginBoundedConstructible T B

/-- For a finite commutative ring on any scheme, the specified comparison induces
both constructible equivalences and identifies the intrinsic and etale-origin classes.
Source: Stacks Tags 09AK and 09AL; the finite-ring subargument of the blueprint comparison.
(blueprint: lem-sf-proetale-constructible-origin-finite-ring).

Proof: identify the canonical coefficient realization with fixed module sheaves using
originFixedComparisonIso. Restrict comparison to constructible sheaves: fullness and
faithfulness come from fixed-module comparison, and essential surjectivity comes from
the fixed-module constructible-origin theorem. On derived categories, transport the
bounded-below Hom bijection through originFixedDerivedIso; intrinsicOrigin_image and
intrinsicOrigin_preimage supply preservation and essential surjectivity. These latter
lemmas use finite amplitude induction and truncation, with boundary maps lifted by
bounded-below full faithfulness. Finally use intrinsicOrigin_iso and etaleOrigin_iff
to identify the two object properties by propositional and function extensionality. -/
theorem constructible_proEtale_origin_finite_ring : ConstructibleOriginComparison T B := by
  classical
  let A := ULift.{u + 1, u} B
  let ν := comparisonUpperStar (ModuleCat.{u + 1} A) T
  let R := Scheme.proEtaleModuleRestriction T B
  have : R.IsEquivalence := Scheme.proEtaleModuleRestriction_isEquivalence T B
  let F := originComparison T B ⋙ originConstantModules T B
  let P : ObjectProperty (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
    Scheme.IsConstructibleEtaleModuleSheaf
  let Q : ObjectProperty (Scheme.proEtaleRingModules T
      (Scheme.proEtaleConstantRing T B)) := Scheme.IsConstructibleProEtaleModuleSheaf T B
  let eF : F ⋙ R ≅ ν := originFixedComparisonIso T B
  have : (F ⋙ R).Full := Functor.Full.of_iso eF.symm
  have : (F ⋙ R).Faithful := Functor.Faithful.of_iso eF.symm
  have : F.Full := Functor.Full.of_comp_faithful F R
  have : F.Faithful := Functor.Faithful.of_comp F R
  have hp (G : P.FullSubcategory) : Q (F.obj G.obj) := by
    apply (Scheme.proEtaleModuleRestriction_constructible_iff T B _).mpr
    have : Scheme.IsConstructibleSheaf G.obj :=
      (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp G.property
    exact isConstructible_of_iso (eF.app G.obj).symm
      (isConstructible_comparisonUpperStar_obj G.obj)
  let H := Q.lift (P.ι ⋙ F) hp
  have : H.EssSurj := ⟨fun M ↦ by
    obtain ⟨G, hG, ⟨eG⟩⟩ := exists_isConstructibleSheaf_iso_comparisonUpperStar_obj A
      ((Scheme.proEtaleModuleRestriction_constructible_iff T B _).mp M.property)
    let G' : P.FullSubcategory :=
      ⟨G, (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr hG⟩
    exact ⟨G', ⟨Q.isoMk (R.preimageIso (eF.app G ≪≫ eG))⟩⟩⟩
  have : H.IsEquivalence := {}
  refine ⟨⟨H.asEquivalence, ⟨Iso.refl _⟩⟩, ?_, ?_⟩
  · let P' := Etale.DerivedCategory.isBoundedConstructible A T
    let Q' := intrinsicOriginBoundedConstructible T B
    let D := originDerivedComparison T B
    let J := Q'.lift (P'.ι ⋙ D)
      (fun L ↦ intrinsicOrigin_image T B L.obj L.property)
    have hplus (L : P'.FullSubcategory) : DerivedCategory.TStructure.t.plus L.obj := by
      obtain ⟨a, b, _, hz⟩ := L.property.2
      exact ⟨a, (DerivedCategory.isGE_iff L.obj a).mpr (fun q hq ↦ hz q (Or.inl hq))⟩
    have hbij (L M : P'.FullSubcategory) : Function.Bijective
        (fun f : L.obj ⟶ M.obj ↦ D.map f) := by
      let E' := originFixedModules T B
      let e := originFixedDerivedIso T B
      have hb := bijective_comparisonUpperStar_mapDerivedCategory_map
        (A := ModuleCat.{u + 1} A) (X := T) L.obj M.obj (hplus M)
      have hcomp : Function.Bijective
          (fun f : L.obj ⟶ M.obj ↦ E'.mapDerivedCategory.map (D.map f)) := by
        have heq : (fun f : L.obj ⟶ M.obj ↦ E'.mapDerivedCategory.map (D.map f)) =
            fun f ↦ (e.app L.obj).hom ≫ ν.mapDerivedCategory.map f ≫ (e.app M.obj).inv := by
          funext f
          exact (NatIso.naturality_2 e f).symm
        rw [heq]
        exact ((e.app L.obj).homCongr (e.app M.obj)).symm.bijective.comp hb
      exact ⟨fun f g h ↦ hcomp.1 (congrArg E'.mapDerivedCategory.map h), fun f ↦ by
        obtain ⟨g, hg⟩ := hcomp.2 (E'.mapDerivedCategory.map f)
        exact ⟨g, E'.mapDerivedCategory.map_injective hg⟩⟩
    have : J.Full := ⟨fun {L M} f ↦ by
      obtain ⟨g, hg⟩ := (hbij L M).2 f.hom
      exact ⟨P'.homMk g, Q'.hom_ext hg⟩⟩
    have : J.Faithful := ⟨fun {L M} f g h ↦
      P'.hom_ext ((hbij L M).1 (congrArg (·.hom) h))⟩
    have : J.EssSurj := ⟨fun K ↦ by
      obtain ⟨L, hL, ⟨e⟩⟩ := intrinsicOrigin_preimage T B K.obj K.property
      exact ⟨⟨L, hL⟩, ⟨Q'.isoMk e⟩⟩⟩
    have : J.IsEquivalence := {}
    exact ⟨J.asEquivalence, ⟨Iso.refl _⟩⟩
  · funext K
    apply propext
    rw [etaleOrigin_iff]
    exact ⟨intrinsicOrigin_preimage T B K, fun ⟨L, hL, ⟨e⟩⟩ ↦
      intrinsicOrigin_iso T B e (intrinsicOrigin_image T B L hL)⟩

/-- Constructible finite-level pro-etale sheaves and bounded constructible complexes
are exactly those obtained from the etale site by the specified comparison inverse image.
The coefficient ring is the recorded quotient by the chosen uniformizer power, with
finiteness supplied by its positive-level theorem rather than an extra hypothesis.
Source: Weil blueprint, smooth purity, lemma of this name; Stacks Tags 09AK and 09AL;
Bhatt--Scholze, Sections 5.1, 5.2 and 6.2
(blueprint: lem-sf-proetale-constructible-origin).

Proof plan, following the node's nine steps:
1. Choose the finite constructible locally closed partition of a constructible etale
sheaf. Comparison commutes with restriction to every stratum by
lem-weil-pbc-comparison-pullback. Clause (a) of lem-sf-proetale-locally-constant-origin
makes each inverse image lisse with finite stalks. The same partition works pro-etale.
2. The comparison unit is invertible on all etale module sheaves by
prop-weil-pbc-site-comparison-finite-level. The adjunction then gives bijections on Hom
sets, so comparison is fully faithful. A pro-etale sheaf is classical, meaning in its
essential image, exactly when its counit is invertible: one direction takes its direct
image, and the other uses the triangle identity and invertible unit.
3. Classicality is Zariski-local. Direct image commutes with restriction to an open
because both evaluate the same pro-etale sheaf on each etale object over that open.
Comparison commutes with restriction by lem-weil-pbc-comparison-pullback, so the counit
restricts to the open's counit. Covering-family locality in clause (1) of
lem-cbc-proetale-stalk-conservative glues these local isomorphisms. Geometric stalks
of arbitrary pro-etale sheaves are not used for this detection.
4. Classical sheaves are closed under extensions. The short exact sequence gives a
triangle by lem-sf-derived-ses-triangle. Exact comparison is triangulated by
lem-sf-exact-functor-derived-triangulated. Full faithfulness on bounded below complexes
from thm-weil-pbc-site-comparison lifts the boundary between the two classical terms.
Complete the lifted boundary to a triangle and rotate; TR3 and
lem-sf-triangle-morphism-iso identify its image with the original triangle.
The long exact cohomology sequence, lem-sf-derived-homology-long-exact, shows the lifted
middle term is concentrated in degree zero. By lem-sf-derived-concentrated-single it is
a sheaf in degree zero. Taking degree-zero cohomology proves the extension classical.
5. Induct on the number of nonempty strata, simultaneously for all schemes.
For no strata the scheme is empty and take the zero sheaf. Near any point choose the
affine open of lem-sf-constructible-partition-local-closed-stratum, so its stratum is
closed and its open complement is quasi-compact. Restrict strata with their fibre-product
scheme structures. Induction makes the restriction to the complement classical; clause
(b) of lem-sf-proetale-locally-constant-origin makes the closed restriction classical.
The open-closed exact sequence of lem-sf-proetale-open-closed-sequence has classical end
terms by lem-cbc-proetale-extension-zero-comparison and the degree-zero part of
prop-weil-pbc-comparison-direct-image. Step 4 and then step 3 give classicality.
6. If the comparison image of an etale sheaf is intrinsically constructible, restrict
to its given finite partition. Clause (b) of the locally constant origin lemma and full
faithfulness from step 2 descend each lisse stratum to a lisse etale sheaf. Thus the
original etale sheaf is constructible. Steps 1, 2, 5, and this reflection give (i).
7. Exact comparison commutes with all cohomology functors. Hence the image of an etale
bounded constructible complex has intrinsically constructible cohomology in the same
finite degree interval. Full faithfulness on bounded below complexes gives full
faithfulness on this full subcategory, by thm-weil-pbc-site-comparison.
8. Induct on the finite cohomological amplitude of an intrinsic complex. The zero
complex descends to zero. With one nonzero degree, apply (i) to its cohomology sheaf
and lem-sf-derived-concentrated-single, then shift. Otherwise use the top-degree
truncation triangle of lem-sf-derived-truncation-triangle. Its outer terms descend by
induction, and full faithfulness on bounded below complexes lifts the boundary between
them. Complete it to a triangle on the etale side and identify the image with the given
triangle using TR3 and lem-sf-triangle-morphism-iso. Its long exact cohomology sequence
shows that the lifted middle complex is bounded constructible. This proves (ii).
9. By def-weil-pbc-proetale-modules, the etale-origin object property is the essential
image of etale bounded constructible complexes. Step 7 proves its inclusion in the
intrinsic property and step 8 the reverse. Equality follows by propositional and function
extensionality. All changes of coefficient presentation use the constant scalar maps:
originConstantRingComparison is invertible by its universal property, and the recorded
finiteCoefficientScalarMap is locally bijective. Associated module sheafification and
restriction of scalars therefore identify the module sheaves and their exact derived
functors canonically, including the natural isomorphisms in the two equivalence clauses. -/
theorem constructible_proEtale_origin
    (D : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) (hn : 1 ≤ n) (T : Scheme.{u}) :
    @ConstructibleOriginComparison.{u} T (Padic.coefficientExtensionRing l E n) _
      (Padic.finite_coefficientExtensionRing l E n hn) := by
  exact @constructible_proEtale_origin_finite_ring T (Padic.coefficientExtensionRing l E n)
    _ (Padic.finite_coefficientExtensionRing l E n hn)

end AlgebraicGeometry.ProEtale
