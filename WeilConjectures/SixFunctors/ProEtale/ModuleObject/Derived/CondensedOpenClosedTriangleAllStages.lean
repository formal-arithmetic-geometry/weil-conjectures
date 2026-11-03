/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.AlgebraicGeometry.StrictCompletionRestriction.StrictSectionScalarPresentation
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedSixOperations
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.StrictWeilCondensed.StrictWeilCondensed
public import WeilConjectures.SmoothPurity.WeilSheafComplex
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicDerivedOpenAdjunction
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZeroAdjunction
public import WeilConjectures.SmoothPurity.Sf.SfDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek
public import WeilConjectures.CategoryTheory.Triangulated.Recollement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite

import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafOperations
import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafClosedLocalization
import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafBaseChangeMates
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.FullyFaithful
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import WeilConjectures.CategoryTheory.Triangulated.TriangleMorphismExtension
import WeilConjectures.AlgebraicGeometry.Pullback.PullbackConstantModelConstructible
import WeilConjectures.AlgebraicGeometry.IntegralCtfEqualsBc
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
import WeilConjectures.AlgebraicGeometry.Adic.AdicConstructibilityPredicateComparison
import WeilConjectures.AlgebraicGeometry.ProEtale.Constructible.ProEtaleConstructibleOrigin
import WeilConjectures.AlgebraicGeometry.Support.SupportComparisonPullbackCoherence
import WeilConjectures.ConstructibleSheaf.OpenClosed
import WeilConjectures.AlgebraicGeometry.ProEtale.Extension.ProEtaleExtensionZeroComparison
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonFiniteLevel
import WeilConjectures.AlgebraicGeometry.Open.OpenClosedRecollement
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteCoefficientModelComparison
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
import WeilConjectures.SmoothPurity.FiniteFieldDatum.FrobeniusDetailed
public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.ExactDerivedAdjunctionSupplement
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientIsoConstructible
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteEncodingCompactification
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteEncodingConstructibility
public import WeilConjectures.AlgebraicGeometry.Integral.Constant.IntegralConstantModelHeartClosureSupplement
public import WeilConjectures.AlgebraicGeometry.SixFunctors.ShriekCoefficientIsomorphism
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.BoundedConstructible
public import WeilConjectures.SixFunctors.FiniteFieldDatum.FrobeniusSquareCartesian
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ConstructibleOrigin
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ClosedImmersionFullyFaithful
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ExceptionalInverseImageCurrent
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralModelsOperations
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenClosed
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.AdmissibleBoundedConstructibleTriangulated
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Constructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.OpenClosed
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.BaseChange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Finite

/-! # The open-closed triangle for every admissible coefficient ring

Source: latest blueprint, part-duality-trace-formula/sec-lefschetz-verdier/
sec-kunneth-formulas-and-external-duality/sk-thm-sf-kunneth-verdier/sk-prop-sf-localization/
prop-sf-open-closed-triangle-all-stages.md and its proof
(blueprint: prop-sf-open-closed-triangle-all-stages).

All operations act on the ordinary uncompleted derived category of internal modules
on the small pro-etale site. The first two arrows are the actual adjunction counit
and unit. The connecting transformation is restricted to the bounded constructible
full subcategory; its naturality expresses functoriality in every ambient morphism.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry Scheme WeilConjectures
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

private theorem ses_triangle_transport
    {C : Type uC} [Category.{vC} C] [Preadditive C] [HasZeroObject C]
    [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    {T : Triangle C} (hT : T ∈ distTriang C) {A B D : C}
    (e₁ : A ≅ T.obj₁) (e₂ : B ≅ T.obj₂) (e₃ : D ≅ T.obj₃)
    (a : A ⟶ B) (b : B ⟶ D)
    (ha : a ≫ e₂.hom = e₁.hom ≫ T.mor₁)
    (hb : b ≫ e₃.hom = e₂.hom ≫ T.mor₂) :
    ∃ w, Triangle.mk a b w ∈ distTriang C := by
  refine ⟨e₃.hom ≫ T.mor₃ ≫ (shiftFunctor C (1 : ℤ)).map e₁.inv,
    isomorphic_distinguished _ hT _ ?_⟩
  refine Triangle.isoMk _ _ e₁ e₂ e₃ ha hb ?_
  change (e₃.hom ≫ T.mor₃ ≫ (shiftFunctor C (1 : ℤ)).map e₁.inv) ≫
    (shiftFunctor C (1 : ℤ)).map e₁.hom = e₃.hom ≫ T.mor₃
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id]
  rw [(shiftFunctor C (1 : ℤ)).map_id, Category.comp_id]

private theorem termwise_ses_triangle
    {C : Type uC} [Category.{vC} C] [Abelian C] [HasDerivedCategory.{wC} C]
    {D : Type uD} [Category.{vD} D] [Abelian D] [HasDerivedCategory.{wD} D]
    {E : Type uE} [Category.{vE} E] [Abelian E] [HasDerivedCategory.{wE} E]
    (P : C ⥤ D) (J : D ⥤ C) (Q : C ⥤ E) (I : E ⥤ C)
    [P.Additive] [J.Additive] [Q.Additive] [I.Additive]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [PreservesFiniteLimits J] [PreservesFiniteColimits J]
    [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
    [PreservesFiniteLimits I] [PreservesFiniteColimits I]
    (aj : J ⊣ P) (ai : Q ⊣ I)
    (h : ∀ M, ∃ z : aj.counit.app M ≫ ai.unit.app M = 0,
      (ShortComplex.mk (aj.counit.app M) (ai.unit.app M) z).ShortExact)
    (K : _root_.DerivedCategory C) :
    ∃ w, Triangle.mk (aj.mapExactDerivedCategory.counit.app K)
      (ai.mapExactDerivedCategory.unit.app K) w ∈ distTriang (_root_.DerivedCategory C) := by
  classical
  have hrep (L : CochainComplex C ℤ) :
      ∃ w, Triangle.mk
        (aj.mapExactDerivedCategory.counit.app (_root_.DerivedCategory.Q.obj L))
        (ai.mapExactDerivedCategory.unit.app (_root_.DerivedCategory.Q.obj L)) w ∈
          distTriang (_root_.DerivedCategory C) := by
    let a := (aj.mapHomologicalComplex (.up ℤ)).counit.app L
    let b := (ai.mapHomologicalComplex (.up ℤ)).unit.app L
    let S := ShortComplex.mk a b (by ext n : 1; exact (h (L.X n)).choose)
    have hS : S.ShortExact :=
      HomologicalComplex.shortExact_of_degreewise_shortExact S
        (fun n ↦ (h (L.X n)).choose_spec)
    let e₁ := J.mapDerivedCategory.mapIso (P.mapDerivedCategoryFactors.app L) ≪≫
      J.mapDerivedCategoryFactors.app ((P.mapHomologicalComplex (.up ℤ)).obj L)
    let e₃ := I.mapDerivedCategory.mapIso (Q.mapDerivedCategoryFactors.app L) ≪≫
      I.mapDerivedCategoryFactors.app ((Q.mapHomologicalComplex (.up ℤ)).obj L)
    apply ses_triangle_transport (_root_.DerivedCategory.triangleOfSES_distinguished hS)
      e₁ (Iso.refl _) e₃
    · change aj.mapExactDerivedCategory.counit.app (_root_.DerivedCategory.Q.obj L) ≫
          𝟙 _ = e₁.hom ≫ _root_.DerivedCategory.Q.map a
      rw [Category.comp_id]
      simp only [Adjunction.mapExactDerivedCategory, Adjunction.localization_counit_app]
      simp only [e₁, a, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Iso.symm_inv,
        Category.assoc]
    · have hu : ai.mapExactDerivedCategory.unit.app (_root_.DerivedCategory.Q.obj L) =
          _root_.DerivedCategory.Q.map b ≫ e₃.inv := by
        simp only [Adjunction.mapExactDerivedCategory, Adjunction.localization_unit_app]
        rfl
      rw [hu]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Iso.refl_hom,
        Category.id_comp, _root_.DerivedCategory.triangleOfSES_mor₂]
      rfl
  let L := _root_.DerivedCategory.Q.objPreimage K
  let e := _root_.DerivedCategory.Q.objObjPreimageIso K
  obtain ⟨w, hw⟩ := hrep L
  apply ses_triangle_transport hw
    ((P.mapDerivedCategory ⋙ J.mapDerivedCategory).mapIso e.symm) e.symm
    ((Q.mapDerivedCategory ⋙ I.mapDerivedCategory).mapIso e.symm)
  · exact (aj.mapExactDerivedCategory.counit.naturality e.inv).symm
  · exact (ai.mapExactDerivedCategory.unit.naturality e.inv).symm

/-- The specified composite j_! j^*, using exact termwise localization.
Source: latest blueprint, displayed open-closed triangle
(blueprint: prop-sf-open-closed-triangle-all-stages). -/
abbrev sfOpenClosedOpen {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :=
  (upperStar Λ j).mapDerivedCategory ⋙ (openImmersionLowerShriek Λ j).mapDerivedCategory

/-- The specified composite Ri_* i^*, with the exact termwise inverse image.
Source: latest blueprint, displayed open-closed triangle
(blueprint: prop-sf-open-closed-triangle-all-stages). -/
abbrev sfOpenClosedClosed {Z X : Scheme.{u}} (i : Z ⟶ X) :=
  (upperStar Λ i).mapDerivedCategory ⋙ (lowerStar Λ i).rightDerivedFunctor

/-- The existing recollement triangle constructor with the specified open counit
and closed unit; only the connecting map is a parameter.
Source: latest blueprint, The triangle paragraph; def-weil-open-closed-recollement
(blueprint: prop-sf-open-closed-triangle-all-stages). -/
abbrev sfOpenClosedTriangle {Z U X : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X)
    [IsOpenImmersion j]
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (δ : (sfOpenClosedClosed Λ i).obj K ⟶ ((sfOpenClosedOpen Λ j).obj K) ⟦(1 : ℤ)⟧) :=
  Recollement.triangle
    ((upperStarLowerStarAdjunction Λ i).mapDerivedCategoryRightDerivedAdjunction)
    (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j) K δ

-- The exact pullback transports finite constant local models.

private theorem constantModel_pullback {S T : Scheme.{u}}
    [CompactSpace S] [QuasiSeparatedSpace S] [CompactSpace T] [QuasiSeparatedSpace T]
    (f : S ⟶ T)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)))
    (hK : constantModelBoundedConstructible Λ T K) :
    constantModelBoundedConstructible Λ S ((upperStar Λ f).mapDerivedCategory.obj K) := by
  refine ⟨(upperStar Λ f).bounded_mapDerivedCategory_obj hK.1, fun q ↦ ?_⟩
  exact constructible_iso ((Functor.mapDerivedCategoryHomologyFunctorIso _ q).app K)
    ((constantModelPullback Λ f _ (hK.2 q)).1)

-- Coefficient isomorphisms preserve the actual finite constant models.

private theorem bc_coefficient_iso_iff
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (e : Mon.mk Λ ≅ Mon.mk Λ') (T : Scheme.{u}) (K) :
    constantModelBoundedConstructible Λ' T ((shriekCoefficientTransport e T).obj K) ↔
      constantModelBoundedConstructible Λ T K := by
  let φ := e.inv.hom
  have : IsIso φ := inferInstanceAs (IsIso e.inv.hom)
  let F := Mod.comap (D := Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (coefficientMap φ T)
  have : F.IsEquivalence :=
    inferInstanceAs (Mod.comapEquivalenceOfIsIso (coefficientMap φ T)).functor.IsEquivalence
  change (_ ∧ _) ↔ (_ ∧ _)
  refine and_congr
    ⟨F.bounded_of_bounded_mapDerivedCategory_obj, F.bounded_mapDerivedCategory_obj⟩ ?_
  apply forall_congr'
  intro q
  exact (Iff.intro
    (constructible_iso ((F.mapDerivedCategoryHomologyFunctorIso q).app K).symm)
    (constructible_iso ((F.mapDerivedCategoryHomologyFunctorIso q).app K))).trans
      (constantModel_comap_iff φ T _)

private theorem open_bc_coefficient_iso
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (e : Mon.mk Λ ≅ Mon.mk Λ') {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j]
    (h : ∀ L, constantModelBoundedConstructible Λ' U L →
      constantModelBoundedConstructible Λ' T
        ((openImmersionLowerShriek Λ' j).mapDerivedCategory.obj L))
    (L) (hL : constantModelBoundedConstructible Λ U L) :
    constantModelBoundedConstructible Λ T
      ((openImmersionLowerShriek Λ j).mapDerivedCategory.obj L) := by
  have : IsIso e.inv.hom := inferInstanceAs (IsIso ((Mon.forget _).map e.inv))
  let J := openImmersionLowerShriek Λ j
  let J' := openImmersionLowerShriek Λ' j
  let eJ : J.mapDerivedCategory ⋙ shriekCoefficientTransport e T ≅
      shriekCoefficientTransport e U ⋙ J'.mapDerivedCategory :=
    (Functor.mapDerivedCategoryCompIso J (Mod.comap (coefficientMap e.inv.hom T))).symm ≪≫
      Functor.mapDerivedCategoryNatIso (comapOpenImmersionLowerShriekIso e.inv.hom j) ≪≫
      Functor.mapDerivedCategoryCompIso (Mod.comap (coefficientMap e.inv.hom U)) J'
  apply (bc_coefficient_iso_iff e T _).mp
  exact (constantModelConstructibleFiniteTor_wellDefined Λ' T).2.1.of_iso
    (eJ.symm.app L) (h _ ((bc_coefficient_iso_iff e U L).mpr hL))

private noncomputable def closed_identity_derived_iso (T : Scheme.{u}) :
    (lowerStar Λ (𝟙 T)).rightDerivedFunctor ≅ 𝟭 _ := by
  have : PreservesFiniteColimits (lowerStar Λ (𝟙 T)) :=
    preservesFiniteColimits_of_natIso (lowerStarId Λ T).symm
  exact (lowerStar Λ (𝟙 T)).rightDerivedFunctorIsoMapDerivedCategory ≪≫
    Functor.mapDerivedCategoryNatIso (lowerStarId Λ T) ≪≫ Functor.mapDerivedCategoryIdIso _

private theorem integral_open_bc
    (ell : ℕ) [Fact ell.Prime] (E : PadicAlgCl.FiniteIntermediateField ell)
    {U T : Scheme.{u}} [IsNoetherian U] [IsNoetherian T]
    (j : U ⟶ T) [IsOpenImmersion j] (L)
    (hL : constantModelBoundedConstructible (Profinite.padicIntegersRingObj ell E) U L) :
    constantModelBoundedConstructible (Profinite.padicIntegersRingObj ell E) T
      ((openImmersionLowerShriek (Profinite.padicIntegersRingObj ell E) j
        ).mapDerivedCategory.obj L) := by
  have h := (integralModelsOperations ell E).2.2.1 j (𝟙 T) L hL
  exact (constantModelConstructibleFiniteTor_wellDefined _ T).2.1.of_iso
    ((closed_identity_derived_iso (Profinite.padicIntegersRingObj ell E) T).app _) h

-- Finite coefficients: descend to an etale complex, extend there, and compare back.

private theorem finite_open_bc
    (B : Type u) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    [DiscreteTopology B] [Finite B] {U T : Scheme.{u}}
    [CompactSpace U] [QuasiSeparatedSpace U] [CompactSpace T] [QuasiSeparatedSpace T]
    (j : U ⟶ T) [IsOpenImmersion j] [QuasiCompact j] (L)
    (hL : constantModelBoundedConstructible (Profinite.continuousCoefficientRingObj B) U L) :
    constantModelBoundedConstructible (Profinite.continuousCoefficientRingObj B) T
      ((openImmersionLowerShriek (Profinite.continuousCoefficientRingObj B) j
        ).mapDerivedCategory.obj L) := by
  classical
  let eU := (FiniteDiscreteOrdinary.encoding_exists B U).some
  let eT := (FiniteDiscreteOrdinary.encoding_exists B T).some
  let A := ModuleCat.{u + 1} (ULift.{u + 1} B)
  let JP := (ProEtale.openImmersionLowerShriek A j).mapDerivedCategory
  let JE := Etale.openImmersionLowerShriek A j
  let νU := comparisonUpperStar A U
  let νT := comparisonUpperStar A T
  have hi : ProEtale.DerivedCategory.boundedConstructibleIntrinsic (ULift.{u + 1} B) U
      (eU.fixedDerived.functor.obj L) := by
    have h := ((FiniteDiscreteOrdinary.encoding_constructibility B U eU).2 L).mp hL
    exact ⟨h.1, fun q ↦ (AdmissibleTriangulated.ordinary_iff B U _).mp (h.2 q)⟩
  obtain ⟨G, hG, ⟨eG⟩⟩ :=
    ProEtale.DerivedCategory.boundedConstructible_of_boundedConstructibleIntrinsic hi
  have hGj := Etale.boundedConstructible_mapDerivedCategory_openImmersionLowerShriek
    (ULift.{u + 1} B) j hG
  let eν : JE.mapDerivedCategory ⋙ νT.mapDerivedCategory ≅ νU.mapDerivedCategory ⋙ JP :=
    (Functor.mapDerivedCategoryCompIso JE νT).symm ≪≫
      Functor.mapDerivedCategoryNatIso
        (openImmersionLowerShriekComparisonUpperStarIso A j) ≪≫
      Functor.mapDerivedCategoryCompIso νU (ProEtale.openImmersionLowerShriek A j)
  have hp : ProEtale.DerivedCategory.boundedConstructible A T
      (JP.obj (eU.fixedDerived.functor.obj L)) :=
    ⟨JE.mapDerivedCategory.obj G, hGj, ⟨eν.app G ≪≫ JP.mapIso eG⟩⟩
  have hout := ProEtale.DerivedCategory.boundedConstructible_le_boundedConstructibleIntrinsic
    (JP.obj (eU.fixedDerived.functor.obj L)) hp
  have henc := ProEtale.DerivedCategory.boundedConstructibleIntrinsic.of_iso
    ((FiniteDiscreteOrdinary.encodingDerivedOpenShriekIso B j eT eU).app L).symm hout
  apply ((FiniteDiscreteOrdinary.encoding_constructibility B T eT).2 _).mpr
  exact ⟨henc.1, fun q ↦ (AdmissibleTriangulated.ordinary_iff B T _).mpr (henc.2 q)⟩

private theorem field_open_bc
    (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)] (hk : Finite k ∨ IsAlgClosed k)
    {U T : Over (Spec (.of k))}
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
    [LocallyOfFiniteType T.hom] [QuasiCompact T.hom] [IsSeparated T.hom]
    (j : U ⟶ T) [IsOpenImmersion j.left]
    (hΛ : (∃ E : PadicAlgCl.FiniteIntermediateField ell,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ell)))
    (L) (hL : constantModelBoundedConstructible Λ U.left L) :
    constantModelBoundedConstructible Λ T.left
      ((openImmersionLowerShriek Λ j.left).mapDerivedCategory.obj L) := by
  have : IsLocallyNoetherian U.left := LocallyOfFiniteType.isLocallyNoetherian U.hom
  have : CompactSpace U.left := QuasiCompact.compactSpace_of_compactSpace U.hom
  have hnonfin : Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℤ_[ell])) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℚ_[ell])) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ell,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ell E)) ∨
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ell)) := by
    rcases hΛ with ⟨E, hE⟩ | h
    · exact Or.inr (Or.inr (Or.inl ⟨E, Or.inr hE⟩))
    · exact Or.inr (Or.inr (Or.inr h))
  have hadm : IsLocalizingAdmissibleCoefficient ell Λ := by
    rcases hΛ with h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
  have hctf := congrFun (integral_ctf_equals_bc ell U.left (Mon.mk Λ) hnonfin).2.2.2 L
  have hLc : (constantModelBoundedConstructible Λ U.left ⊓
      _root_.DerivedCategory.finiteTorAmplitude _) L := hctf.mpr hL
  obtain ⟨hU, hT, hSU, hST, hfun, sU, sT, H⟩ :=
    exceptionalInverseImage_exists_current Λ ell k hk j hadm
  let := hU
  let := hT
  let := sU
  let := sT
  obtain ⟨F, sF, H⟩ := H
  let := sF
  obtain ⟨eF, _, _, _, _, he, hF, G, sG, H⟩ := H
  let M := (ObjectProperty.ιOfLE hSU).obj ⟨L, hLc⟩
  obtain ⟨e⟩ := he (Compactification.ofIsOpenImmersion j.left)
  have h := (hF M hLc).1
  exact (constantModelConstructibleFiniteTor_wellDefined Λ T.left).2.1.of_iso
    (e.app M ≪≫ (closed_identity_derived_iso Λ T.left).app _) h

/-- The natural distinguished open-closed triangle, its constructible vertices,
shifted orthogonality and uniqueness, at precisely the four coefficient stages.
The finite ring A is a discrete representative of the specified quotient A_{E,n};
the four alternatives identify Λ as a condensed ring, not merely as an abelian sheaf.

Source: latest blueprint, prop-sf-open-closed-triangle-all-stages, The triangle,
Hom vanishing and Constructibility (blueprint: prop-sf-open-closed-triangle-all-stages).

Proof: (1) On module sheaves the counit j_!j^*M → M and unit M → i_*i^*M
form a short exact sequence. Exact open and closed restriction check its exactness.
(2) Apply this sequence termwise to a representative complex. The derived triangle
of a short exact sequence gives a distinguished triangle. Exact-adjunction
localization and uniqueness of adjoints identify its arrows with the specified
counit and unit, including the comparison i_*=Ri_*.
(3) Disjoint support and the closed derived adjunction give shifted cross-object
orthogonality. Triangle-morphism extension gives uniqueness and naturality.
(4) Pullback preserves finite constant models. For integral coefficients use
integralModelsOperations (3). For E and Qbar use Dbc=Dctf and existence (2),
evaluating its compactification comparison at the trivial open compactification.
For finite coefficients use the exact normalized coefficient encoding, express
the encoded bounded constructible complex as ν^*G, extend G by zero on the etale
site, and compare extension by zero with ν^*. Transport along the given condensed
coefficient isomorphisms in each case. These comparisons preserve the actual models.
(5) Dbc is triangulated for each admissible coefficient; the closed vertex belongs
to it by closure at the third vertex of the constructed triangle. -/
theorem sf_openClosed_triangle_all_stages
    (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime] (_hell : ell ≠ D.p)
    (E : PadicAlgCl.FiniteIntermediateField ell) (n : ℕ) (_hn : 1 ≤ n)
    (A : Type) [CommRing A] [TopologicalSpace A] [DiscreteTopology A]
    [IsTopologicalRing A] (_eA : A ≃+* Padic.coefficientExtensionRing ell E n)
    (_hΛ : Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj A)) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ell E)) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E)) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ell)))
    (X : Over (Spec (.of D.k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    {Z U : Scheme.{u}} (i : Z ⟶ X.left) (j : U ⟶ X.left)
    [IsClosedImmersion i] [IsOpenImmersion j]
    (_hij : Set.range j = (Set.range i)ᶜ) :
    ∃ δ : (constantModelBoundedConstructible Λ X.left).ι ⋙ sfOpenClosedClosed Λ i ⟶
        (constantModelBoundedConstructible Λ X.left).ι ⋙ sfOpenClosedOpen Λ j ⋙
          shiftFunctor _ (1 : ℤ),
      ∀ K : ConstantModelBoundedConstructible Λ X.left,
        sfOpenClosedTriangle Λ i j K.obj (δ.app K) ∈ distTriang _ ∧
        constantModelBoundedConstructible Λ X.left ((sfOpenClosedOpen Λ j).obj K.obj) ∧
        constantModelBoundedConstructible Λ X.left ((sfOpenClosedClosed Λ i).obj K.obj) ∧
        (∀ m : ℤ, Subsingleton
          (((sfOpenClosedOpen Λ j).obj K.obj) ⟦m⟧ ⟶ (sfOpenClosedClosed Λ i).obj K.obj)) ∧
        (∀ δ' : (sfOpenClosedClosed Λ i).obj K.obj ⟶
            ((sfOpenClosedOpen Λ j).obj K.obj) ⟦(1 : ℤ)⟧,
          sfOpenClosedTriangle Λ i j K.obj δ' ∈ distTriang _ → δ' = δ.app K) := by
  classical
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : IsNoetherian X.left := ⟨⟩
  have : TopologicalSpace.NoetherianSpace U :=
    j.isOpenEmbedding.isEmbedding.isInducing.noetherianSpace
  have : TopologicalSpace.NoetherianSpace Z :=
    i.isClosedEmbedding.isInducing.noetherianSpace
  have : QuasiSeparatedSpace X.left := inferInstance
  have : QuasiSeparatedSpace U := inferInstance
  have : QuasiSeparatedSpace Z := inferInstance
  have : QuasiCompact j := ⟨fun _ _ _ ↦
    j.isOpenEmbedding.isEmbedding.isCompact_iff.2
      (TopologicalSpace.NoetherianSpace.isCompact _)⟩
  have hc : IsCompl (Set.range i.base) (Set.range j.base) := by
    rw [_hij]
    exact isCompl_compl
  have hd : Disjoint (Set.range j.base) (Set.range i.base) := hc.symm.disjoint
  have : IsLocallyNoetherian U := LocallyOfFiniteType.isLocallyNoetherian j
  have : CompactSpace U := QuasiCompact.compactSpace_of_compactSpace j
  have : IsNoetherian U := {}
  have hchar : ringChar D.k = D.p := by
    let : Fintype D.k₀ := Fintype.ofFinite D.k₀
    let : Fact D.p.Prime := ⟨D.prime⟩
    let : CharP D.k₀ D.p := charP_of_card_eq_prime_pow (by
      simpa only [Nat.card_eq_fintype_card] using D.card_base.trans D.cardinality_eq)
    let : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
    exact ringChar.eq D.k D.p
  have : Fact (ringChar D.k).Prime := ⟨by rw [hchar]; exact D.prime⟩
  have : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  have : Fact (ringChar D.k ≠ ell) := ⟨by rw [hchar]; exact _hell.symm⟩
  let Uo : Over (Spec (.of D.k)) := Over.mk (j ≫ X.hom)
  let jo : Uo ⟶ X := Over.homMk j rfl
  have : IsOpenImmersion jo.left := inferInstanceAs (IsOpenImmersion j)
  have : LocallyOfFiniteType Uo.hom := inferInstanceAs (LocallyOfFiniteType (j ≫ X.hom))
  have : QuasiCompact Uo.hom := inferInstanceAs (QuasiCompact (j ≫ X.hom))
  have : IsSeparated Uo.hom := inferInstanceAs (IsSeparated (j ≫ X.hom))
  have hconstruct : (constantModelBoundedConstructible Λ X.left).IsTriangulated ∧
      ∀ L, constantModelBoundedConstructible Λ U L →
        constantModelBoundedConstructible Λ X.left
          ((openImmersionLowerShriek Λ j).mapDerivedCategory.obj L) := by
    rcases _hΛ with he | he | he | he
    · obtain ⟨e⟩ := he
      have : Finite (Padic.coefficientExtensionRing ell E n) :=
        Padic.finite_coefficientExtensionRing ell E n _hn
      have : Finite A := Finite.of_injective _eA _eA.injective
      obtain ⟨eA⟩ := AdmissibleTriangulated.finiteCoefficientLiftIso.{u} A
      let e' := e ≪≫ eA
      exact ⟨AdmissibleTriangulated.coefficient_iso e' X.left
        (AdmissibleTriangulated.finite_case (ULift.{u} A) X.left),
        open_bc_coefficient_iso e' j (finite_open_bc (ULift.{u} A) j)⟩
    · obtain ⟨e⟩ := he
      obtain ⟨hk, he⟩ := isConstantModelConstructible_serre_padicIntegers X.left ell E
      exact ⟨AdmissibleTriangulated.coefficient_iso e X.left
        (AdmissibleTriangulated.triangulated_of_serre _ X.left hk he),
        open_bc_coefficient_iso e j (integral_open_bc ell E j)⟩
    · exact ⟨AdmissibleTriangulated.coefficient_iso he.some X.left
        ((constantModelBoundedConstructible_field_triangulated ell X.left).1 E).2.1,
        fun L hL ↦ field_open_bc Λ ell D.k (Or.inr inferInstance) jo
          (Or.inl ⟨E, he⟩) L hL⟩
    · exact ⟨AdmissibleTriangulated.coefficient_iso he.some X.left
        (constantModelBoundedConstructible_field_triangulated ell X.left).2.2.1,
        fun L hL ↦ field_open_bc Λ ell D.k (Or.inr inferInstance) jo (Or.inr he) L hL⟩
  have : (constantModelBoundedConstructible Λ X.left).IsTriangulated := hconstruct.1
  have : (constantModelBoundedConstructible Λ X.left).IsClosedUnderIsomorphisms :=
    (constantModelConstructibleFiniteTor_wellDefined Λ X.left).2.1
  let P := (upperStar Λ j).mapDerivedCategory
  let J := (openImmersionLowerShriek Λ j).mapDerivedCategory
  let I := (upperStar Λ i).mapDerivedCategory
  let R := (lowerStar Λ i).rightDerivedFunctor
  let aj := derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j
  let ai := (upperStarLowerStarAdjunction Λ i).mapDerivedCategoryRightDerivedAdjunction
  have hIJ (M) : IsZero (I.obj (J.obj M)) :=
    (isZero_leftDerivedUpperStar_obj_openImmersionLowerShriek_of_disjoint Λ j i hd M).of_iso
      ((leftDerivedUpperStarIsoMapDerivedCategory Λ i).symm.app _)
  have horth (M N) (q : ℤ) : Subsingleton ((J.obj M) ⟦q⟧ ⟶ R.obj N) := by
    have hz : IsZero (I.obj ((J.obj M) ⟦q⟧)) :=
      ((shiftFunctor _ q).map_isZero (hIJ M)).of_iso ((I.commShiftIso q).app _)
    have : Subsingleton (I.obj ((J.obj M) ⟦q⟧) ⟶ N) := ⟨fun _ _ ↦ hz.eq_of_src _ _⟩
    exact (ai.homEquiv _ _).symm.subsingleton
  have hzeroij (M) : IsZero ((upperStar Λ i).obj ((openImmersionLowerShriek Λ j).obj M)) :=
    isZero_upperStar_obj_openImmersionLowerShriek_of_disjoint Λ j i hd M
  have hzeroji (M) : IsZero ((upperStar Λ j).obj ((lowerStar Λ i).obj M)) := by
    apply isZero_of_isZero_X Λ
    exact (ProEtale.isZero_upperStar_lowerStar_of_disjoint Ab.{u + 1} i j hd.symm M.X).of_iso
      (upperStarObjXIso Λ j ((lowerStar Λ i).obj M))
  let a0 := openImmersionLowerShriekUpperStarAdjunction Λ j
  let b0 := upperStarLowerStarAdjunction Λ i
  have hfg0 : a0.counit ≫ b0.unit = 0 := by
    apply NatTrans.ext
    funext M
    apply (a0.homEquiv _ _).injective
    exact (hzeroji (M := (upperStar Λ i).obj M)).eq_of_tgt _ _
  have hS0 (M) : (ShortComplex.mk (a0.counit.app M) (b0.unit.app M)
      (by simpa using congr_app hfg0 M)).ShortExact := by
    let Q := ShortComplex.mk (a0.counit.app M) (b0.unit.app M)
      (by simpa using congr_app hfg0 M)
    have hSi : (Q.map (upperStar Λ i)).ShortExact := by
      have hzi : IsZero ((upperStar Λ i).obj ((openImmersionLowerShriek Λ j).obj
          ((upperStar Λ j).obj M))) := hzeroij _
      have hgi : IsIso ((upperStar Λ i).map (b0.unit.app M)) := by
        have h := b0.left_triangle_components M
        rw [← IsIso.inv_eq_of_inv_hom_id h]
        infer_instance
      have : IsIso ((upperStar Λ i).map (b0.unit.app M)) := hgi
      have hfi : (Q.map (upperStar Λ i)).f = 0 := hzi.eq_of_src _ _
      have hmf : Mono (Q.map (upperStar Λ i)).f :=
        ⟨fun x y hxy ↦ hzi.eq_of_tgt x y⟩
      have hmg : Mono (Q.map (upperStar Λ i)).g := by
        change Mono ((upperStar Λ i).map (b0.unit.app M))
        exact ((isIso_iff_mono_and_epi _).mp hgi).1
      have he : Epi (Q.map (upperStar Λ i)).g := by
        change Epi ((upperStar Λ i).map (b0.unit.app M))
        exact ((isIso_iff_mono_and_epi _).mp hgi).2
      exact ShortComplex.ShortExact.mk' ((ShortComplex.exact_iff_mono _ hfi).2 hmg) hmf he
    have hSj : (Q.map (upperStar Λ j)).ShortExact := by
      have hzj : IsZero ((upperStar Λ j).obj ((lowerStar Λ i).obj
          ((upperStar Λ i).obj M))) :=
        hzeroji (M := (upperStar Λ i).obj M)
      have hfj : IsIso ((upperStar Λ j).map (a0.counit.app M)) := by
        have h := a0.right_triangle_components (Y := M)
        rw [← IsIso.inv_eq_of_hom_inv_id h]
        infer_instance
      have : IsIso ((upperStar Λ j).map (a0.counit.app M)) := hfj
      have hgj : (Q.map (upperStar Λ j)).g = 0 := hzj.eq_of_tgt _ _
      have hmf : Mono (Q.map (upperStar Λ j)).f := by
        change Mono ((upperStar Λ j).map (a0.counit.app M))
        exact ((isIso_iff_mono_and_epi _).mp hfj).1
      have hef : Epi (Q.map (upperStar Λ j)).f := by
        change Epi ((upperStar Λ j).map (a0.counit.app M))
        exact ((isIso_iff_mono_and_epi _).mp hfj).2
      have heg : Epi (Q.map (upperStar Λ j)).g :=
        ⟨fun x y hxy ↦ hzj.eq_of_src x y⟩
      exact ShortComplex.ShortExact.mk' ((ShortComplex.exact_iff_epi _ hgj).2 hef) hmf heg
    have hreflect := jointlyReflectIsomorphisms_upperStar_of_isCompl Λ i j hc
    rw [hreflect.shortExact_iff]
    intro b
    cases b
    · change (Q.map (upperStar Λ i)).ShortExact
      exact hSi
    · change (Q.map (upperStar Λ j)).ShortExact
      exact hSj
  have hex (K) : ∃ δ, sfOpenClosedTriangle Λ i j K δ ∈ distTriang _ := by
    have : IsFinite i := ((IsClosedImmersion.iff_isFinite_and_mono i).1 inferInstance).1
    have : LocallyOfFinitePresentation i := inferInstance
    have : PreservesFiniteColimits (lowerStar Λ i) :=
      preservesFiniteColimits_lowerStar_of_isFinite Λ i
    let ajd := a0.mapExactDerivedCategory
    let aid := b0.mapExactDerivedCategory
    let a := Adjunction.leftAdjointUniq ajd aj
    let c := Adjunction.rightAdjointUniq aid ai
    obtain ⟨w, hw⟩ := termwise_ses_triangle (upperStar Λ j)
      (openImmersionLowerShriek Λ j) (upperStar Λ i) (lowerStar Λ i)
      a0 b0 (fun M ↦ ⟨by simpa using congr_app hfg0 M, hS0 M⟩) K
    apply ses_triangle_transport hw (a.symm.app (P.obj K)) (Iso.refl _)
      (c.symm.app (I.obj K))
    · change aj.counit.app K ≫ 𝟙 _ = a.inv.app (P.obj K) ≫ ajd.counit.app K
      rw [Category.comp_id, ← Adjunction.leftAdjointUniq_hom_app_counit ajd aj K]
      change aj.counit.app K =
        a.inv.app (P.obj K) ≫ a.hom.app (P.obj K) ≫ aj.counit.app K
      rw [← Category.assoc, a.inv_hom_id_app]
      exact (Category.id_comp _).symm
    · change ai.unit.app K ≫ c.inv.app (I.obj K) = 𝟙 _ ≫ aid.unit.app K
      rw [Category.id_comp, ← Adjunction.unit_rightAdjointUniq_hom_app aid ai K]
      change (aid.unit.app K ≫ c.hom.app (I.obj K)) ≫ c.inv.app (I.obj K) = _
      rw [Category.assoc, c.hom_inv_id_app]
      exact Category.comp_id _
  let d := fun K : ConstantModelBoundedConstructible Λ X.left ↦ (hex K.obj).choose
  have hT (K : ConstantModelBoundedConstructible Λ X.left) :
      sfOpenClosedTriangle Λ i j K.obj (d K) ∈ distTriang _ := (hex K.obj).choose_spec
  let δ : (constantModelBoundedConstructible Λ X.left).ι ⋙ sfOpenClosedClosed Λ i ⟶
      (constantModelBoundedConstructible Λ X.left).ι ⋙ sfOpenClosedOpen Λ j ⋙
        shiftFunctor _ (1 : ℤ) :=
    { app := d
      naturality K L f := by
        obtain ⟨τ, h₁, h₂, h₃, hcomm⟩ :=
          ((triangle_morphism_extension _ _ (hT K) (hT L) f.hom).2.1
            (horth (P.obj K.obj) (I.obj L.obj) 1)).2.2
            ((sfOpenClosedOpen Λ j).map f.hom) ((sfOpenClosedClosed Λ i).map f.hom)
            (aj.counit.naturality f.hom) (ai.unit.naturality f.hom).symm
        exact hcomm.symm }
  refine ⟨δ, fun K ↦ ⟨hT K, ?_, ?_, ?_, ?_⟩⟩
  · exact hconstruct.2 _ (constantModel_pullback Λ j K.obj K.property)
  · exact (constantModelBoundedConstructible Λ X.left).ext_of_isTriangulatedClosed₃
      _ (hT K) (hconstruct.2 _ (constantModel_pullback Λ j K.obj K.property)) K.property
  · exact horth (P.obj K.obj) (I.obj K.obj)
  · intro δ' hδ'
    exact (triangle_morphism_extension _ _ (hT K) (hT K) (𝟙 K.obj)).2.2
      (horth (P.obj K.obj) (I.obj K.obj) 1) δ' hδ'

-- The following two categorical proof steps keep the concrete module functors abstract.

private theorem shiftedMap_subsingleton
    {C B : Type*} [Category* C] [Category* B] [HasShift C ℤ] [HasShift B ℤ]
    (F : C ⥤ B) [F.Full] [F.Faithful] [F.CommShift ℤ]
    (X Y : C) (q : ℤ) (h : Subsingleton (X⟦q⟧ ⟶ Y)) :
    Subsingleton ((F.obj X) ⟦q⟧ ⟶ F.obj Y) := by
  have hs : Subsingleton (F.obj (X⟦q⟧) ⟶ F.obj Y) := by
    refine ⟨fun a b ↦ ?_⟩
    rw [← F.map_preimage a, ← F.map_preimage b]
    exact congrArg F.map (h.elim _ _)
  exact @Equiv.subsingleton _ _
    (((F.commShiftIso q).app X).homCongr (Iso.refl (F.obj Y))).symm hs

private theorem triangleIso_of_middle
    {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C]
    [HasShift C ℤ] [∀ q : ℤ, (shiftFunctor C q).Additive] [Pretriangulated C]
    (T T' : Triangle C) (hT : T ∈ distTriang C) (hT' : T' ∈ distTriang C)
    (phi : T'.obj₂ ≅ T.obj₂)
    (hforward : Subsingleton (T'.obj₁⟦(0 : ℤ)⟧ ⟶ T.obj₃))
    (hbackward : Subsingleton (T.obj₁⟦(0 : ℤ)⟧ ⟶ T'.obj₃))
    (hself : Subsingleton (T.obj₁⟦(1 : ℤ)⟧ ⟶ T.obj₃))
    (hself' : Subsingleton (T'.obj₁⟦(1 : ℤ)⟧ ⟶ T'.obj₃)) :
    ∃ e : T' ≅ T, e.hom.hom₂ = phi.hom := by
  obtain ⟨a, ha⟩ := exists_triangleHom_of_comp_eq_zero hT' hT phi.hom (by
    have : Subsingleton (T'.obj₁ ⟶ T.obj₃) :=
      @Equiv.subsingleton _ _
        (((shiftFunctorZero _ ℤ).app T'.obj₁).homCongr (Iso.refl T.obj₃)).symm hforward
    exact Subsingleton.elim _ _)
  obtain ⟨b, hb⟩ := exists_triangleHom_of_comp_eq_zero hT hT' phi.inv (by
    have : Subsingleton (T.obj₁ ⟶ T'.obj₃) :=
      @Equiv.subsingleton _ _
        (((shiftFunctorZero _ ℤ).app T.obj₁).homCongr (Iso.refl T'.obj₃)).symm hbackward
    exact Subsingleton.elim _ _)
  refine ⟨{ hom := a, inv := b, hom_inv_id := ?_, inv_hom_id := ?_ }, ha⟩
  · have := hself'
    apply triangleHom_ext_of_subsingleton hT' hT'
    change a.hom₂ ≫ b.hom₂ = 𝟙 _
    rw [ha, hb]
    exact phi.hom_inv_id
  · have := hself
    apply triangleHom_ext_of_subsingleton hT hT
    change b.hom₂ ≫ a.hom₂ = 𝟙 _
    rw [hb, ha]
    exact phi.inv_hom_id

/-- For finite-field models and field coefficients the Frobenius isomorphism
extends to the localization triangle, with its prescribed middle component.
The outer components are the induced Weil structures: the two triangle squares
force the adjunction-compatible open and closed exchange maps. The third square
is exactly equivariance of the connecting arrow, including the shift comparison.
Native Weil complexes are covered by their recorded realization as strict pairs.

Source: latest blueprint, prop-sf-open-closed-triangle-all-stages, Weil structures
(blueprint: prop-sf-open-closed-triangle-all-stages).

Proof (node step 7): the geometric Frobenius squares of the model immersions are
cartesian. Their canonical inverse-image comparisons preserve open and closed
support. The derived adjunctions and disjoint-support vanishing give shifted
cross-object orthogonality for the triangle and its exact Frobenius pullback.
Extend the middle Weil isomorphism and its inverse by triangle-morphism extension.
The first two squares are the unit/counit equations for the outer exchange maps.
Shifted orthogonality makes both composites identities, so this is a triangle
isomorphism. Its third square includes the shift comparison and proves equivariance
of the connecting map. Thus all three arrows are Weil-equivariant. -/
theorem sf_openClosed_triangle_weil
    (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime] (hell : ell ≠ D.p)
    (c : WeilCoefficient ell)
    (X₀ Z₀ U₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    [LocallyOfFiniteType Z₀.hom] [QuasiCompact Z₀.hom]
    [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom]
    (i₀ : Z₀ ⟶ X₀) (j₀ : U₀ ⟶ X₀)
    (i : (D.geometricFiber Z₀).left ⟶ (D.geometricFiber X₀).left)
    (j : (D.geometricFiber U₀).left ⟶ (D.geometricFiber X₀).left)
    (_hi : i = ((Over.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map i₀).left)
    (_hj : j = ((Over.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map j₀).left)
    [IsClosedImmersion i] [IsOpenImmersion j]
    (_hij : Set.range j = (Set.range i)ᶜ)
    (K : strictWeilComplexCategory D ell hell X₀ c)
    (δ : (sfOpenClosedClosed (WeilCoefficient.ab c) i).obj K.obj.carrier ⟶
      ((sfOpenClosedOpen (WeilCoefficient.ab c) j).obj K.obj.carrier) ⟦(1 : ℤ)⟧)
    (_hδ : sfOpenClosedTriangle (WeilCoefficient.ab c) i j K.obj.carrier δ ∈ distTriang _) :
    ∃ e : ((upperStar (WeilCoefficient.ab c)
          (D.geometricFrobenius X₀).hom).mapDerivedCategory).mapTriangle.obj
        (sfOpenClosedTriangle (WeilCoefficient.ab c) i j K.obj.carrier δ) ≅
          sfOpenClosedTriangle (WeilCoefficient.ab c) i j K.obj.carrier δ,
      e.hom.hom₂ = K.obj.str.hom := by
  classical
  let L := WeilCoefficient.ab c
  let P := (upperStar L j).mapDerivedCategory
  let J := (openImmersionLowerShriek L j).mapDerivedCategory
  let I := (upperStar L i).mapDerivedCategory
  let R := (lowerStar L i).rightDerivedFunctor
  let G := (upperStar L (D.geometricFrobenius X₀).hom).mapDerivedCategory
  let aj := derivedOpenImmersionLowerShriekUpperStarAdjunction L j
  let ai := (upperStarLowerStarAdjunction L i).mapDerivedCategoryRightDerivedAdjunction
  let T := sfOpenClosedTriangle L i j K.obj.carrier δ
  let T' := G.mapTriangle.obj T
  have hT : T ∈ distTriang _ := _hδ
  have hT' : T' ∈ distTriang _ := G.map_distinguished T hT
  have hd : Disjoint (Set.range j.base) (Set.range i.base) := by
    rw [_hij]
    exact disjoint_compl_left
  have hIJ (M) : IsZero (I.obj (J.obj M)) :=
    (isZero_leftDerivedUpperStar_obj_openImmersionLowerShriek_of_disjoint L j i hd M).of_iso
      ((leftDerivedUpperStarIsoMapDerivedCategory L i).symm.app _)
  have hclosed (M) (hM : IsZero (I.obj M)) (N) (q : ℤ) :
      Subsingleton (M⟦q⟧ ⟶ R.obj N) := by
    have hz : IsZero (I.obj (M⟦q⟧)) :=
      ((shiftFunctor _ q).map_isZero hM).of_iso ((I.commShiftIso q).app M)
    have : Subsingleton (I.obj (M⟦q⟧) ⟶ N) := ⟨fun _ _ ↦ hz.eq_of_src _ _⟩
    exact (ai.homEquiv _ _).symm.subsingleton
  have hPR (N) : IsZero (P.obj (R.obj N)) := by
    apply (IsZero.iff_id_eq_zero _).2
    have : Subsingleton (I.obj (J.obj (P.obj (R.obj N))) ⟶ N) :=
      ⟨fun _ _ ↦ (hIJ _).eq_of_src _ _⟩
    have : Subsingleton (J.obj (P.obj (R.obj N)) ⟶ R.obj N) :=
      (ai.homEquiv _ _).symm.subsingleton
    exact (aj.homEquiv _ _).symm.injective (Subsingleton.elim _ _)
  have hsj : CommSq (D.geometricFrobenius U₀).hom j j
      (D.geometricFrobenius X₀).hom := by
    subst j
    exact ⟨(D.frobenius_square_cartesian U₀ X₀ j₀).2.2.2.2.1⟩
  have hsi : CommSq (D.geometricFrobenius Z₀).hom i i
      (D.geometricFrobenius X₀).hom := by
    subst i
    exact ⟨(D.frobenius_square_cartesian Z₀ X₀ i₀).2.2.2.2.1⟩
  let ej := (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (upperStarSquareComparison L hsj) ≪≫
      Functor.mapDerivedCategoryCompIso _ _
  let ei := (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (upperStarSquareComparison L hsi) ≪≫
      Functor.mapDerivedCategoryCompIso _ _
  have hIG : IsZero (I.obj T'.obj₁) :=
    (((upperStar L (D.geometricFrobenius Z₀).hom).mapDerivedCategory).map_isZero
      (hIJ (P.obj K.obj.carrier))).of_iso (ei.app T.obj₁)
  have hPG : IsZero (P.obj T'.obj₃) :=
    (((upperStar L (D.geometricFrobenius U₀).hom).mapDerivedCategory).map_isZero
      (hPR (I.obj K.obj.carrier))).of_iso (ej.app T.obj₃)
  have hforward (q : ℤ) : Subsingleton (T'.obj₁⟦q⟧ ⟶ T.obj₃) :=
    hclosed T'.obj₁ hIG (I.obj K.obj.carrier) q
  have hbackward (q : ℤ) : Subsingleton (T.obj₁⟦q⟧ ⟶ T'.obj₃) := by
    have : Subsingleton ((P.obj K.obj.carrier) ⟦q⟧ ⟶ P.obj T'.obj₃) :=
      ⟨fun _ _ ↦ hPG.eq_of_tgt _ _⟩
    have hs : Subsingleton (J.obj ((P.obj K.obj.carrier) ⟦q⟧) ⟶ T'.obj₃) :=
      (aj.homEquiv _ _).subsingleton
    exact @Equiv.subsingleton _ _
      (((J.commShiftIso q).app (P.obj K.obj.carrier)).homCongr
        (Iso.refl T'.obj₃)).symm hs
  have hself : Subsingleton (T.obj₁⟦(1 : ℤ)⟧ ⟶ T.obj₃) :=
    hclosed T.obj₁ (hIJ _) (I.obj K.obj.carrier) 1
  have hself' : Subsingleton (T'.obj₁⟦(1 : ℤ)⟧ ⟶ T'.obj₃) := by
    have : G.Full := by dsimp [G]; infer_instance
    have : G.Faithful := by dsimp [G]; infer_instance
    exact shiftedMap_subsingleton G T.obj₁ T.obj₃ 1 hself
  exact triangleIso_of_middle T T' hT hT' K.obj.str
    (hforward 0) (hbackward 0) hself hself'

end AlgebraicGeometry.ProEtale.CondensedRing
