/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q17
-/
module

public import Sheaf.Paper.EtaleProEtaleCoefficientCompatibility
public import Sheaf.Paper.ProperOpenCoefficientRefinement
public import Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Sheaf.Paper.EtaleProEtaleAdjunctionTransfer
public import Sheaf.AlgebraicGeometry.EtaleCompactSupportNormalization
public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
public import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import all Sheaf.Paper.EtaleProEtaleScalarMate
import all Sheaf.SixFunctors.EtaleOpenTensor
import WeilConjectures.CategoryTheory.DerivedCategory.AdjunctionUnit
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import all Sheaf.SixFunctors.EtaleOpenTensorDefs
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.CategoryTheory.DerivedCategory.Constructible

/-!
# Scalar compatibility of the etale sum-extension counit

Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/
sk-lem-sp-reduction/sk-lem-sp-reduction-exceptional.proof.md, Charts, integral summation;
Stacks Project, etale-cohomology.tex, Tag 03S3
(blueprint: lem-sp-etale-sum-counit-scalar).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.CoefficientCompatibility

namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

private noncomputable def etaleCounitScalarFirstDerived
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U V : Scheme.{u}} (e : U ⟶ V) [Etale e]
    (K : DerivedCategoryModule A V) :=
  (sumCoefficientIso φ e).hom.app
      ((upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.obj K) ≫
    (etaleLowerShriek (ModuleCat.{u + 1} B) e inferInstance).mapDerivedCategory.map
      ((properOpenCoefficientPullbackIso φ e).inv.app K) ≫
    (derivedEtaleLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} B) e inferInstance).counit.app ((scalarExtension φ V).obj K)

private theorem exactFactorh
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (P : CochainComplex C ℤ) :
    F.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.quotient _ _).obj P) =
      F.mapDerivedCategoryFactors.hom.app P := by
  rw [Functor.mapDerivedCategoryFactorsh_hom_app]
  change F.mapDerivedCategory.map (𝟙 (_root_.DerivedCategory.Q.obj P)) ≫
    F.mapDerivedCategoryFactors.hom.app P ≫
      𝟙 (_root_.DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P)) ≫
        _root_.DerivedCategory.Qh.map
          (𝟙 ((HomotopyCategory.quotient D (.up ℤ)).obj
            ((F.mapHomologicalComplex (.up ℤ)).obj P))) = _
  have hi : _root_.DerivedCategory.Qh.map
      (𝟙 ((HomotopyCategory.quotient D (.up ℤ)).obj
        ((F.mapHomologicalComplex (.up ℤ)).obj P))) =
      𝟙 (_root_.DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P)) :=
    _root_.DerivedCategory.Qh.map_id _
  rw [hi, CategoryTheory.Functor.map_id]
  change (𝟙 _ ≫ F.mapDerivedCategoryFactors.hom.app P ≫ 𝟙 _ ≫ 𝟙 _) =
    F.mapDerivedCategoryFactors.hom.app P
  simp only [Category.id_comp, Category.comp_id]

private theorem exactAdjCounit
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [MonoidalCategory C] [MonoidalPreadditive C]
    [HasCountableCoproducts C]
    [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
    [HasColimitsOfShape ℤ C] [HasExactColimitsOfShape ℤ C]
    [∀ (X : C), PreservesColimitsOfShape ℤ ((MonoidalCategory.curriedTensor C).obj X)]
    [∀ (X : C), PreservesColimitsOfShape ℤ ((MonoidalCategory.curriedTensor C).flip.obj X)]
    [Abelian.HasFunctorialFlatResolution C]
    [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions D]
    {F : C ⥤ D} {G : D ⥤ C} (a : F ⊣ G) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (P : CochainComplex D ℤ) :
    a.mapDerivedCategoryAdjunction.counit.app (_root_.DerivedCategory.Q.obj P) =
      F.mapDerivedCategory.map (G.mapDerivedCategoryFactors.hom.app P) ≫
        F.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj P) ≫
          _root_.DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).counit.app P) := by
  have h := a.mapDerivedCategoryAdjunction_counit_app_Qh_obj
    ((HomotopyCategory.quotient _ (.up ℤ)).obj P)
  rw [Adjunction.mapHomotopyCategory_counit_app_quotient] at h
  change a.mapDerivedCategoryAdjunction.counit.app (_root_.DerivedCategory.Q.obj P) = _ at h
  rw [h]
  change F.mapDerivedCategory.map
      (G.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.quotient _ _).obj P)) ≫
      F.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.quotient _ _).obj
        ((G.mapHomologicalComplex (.up ℤ)).obj P)) ≫
      _root_.DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).counit.app P) = _
  rw [exactFactorh, exactFactorh]

private theorem derivedAdj_eq (A : Type (u + 1)) [CommRing A]
    {U V : Scheme.{u}} (e : U ⟶ V) [Etale e] :
    (etaleLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategoryAdjunction =
      derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) e inferInstance := by
  apply Adjunction.ext_counit
  apply Localization.natTrans_ext _root_.DerivedCategory.Q
    (HomologicalComplex.quasiIso _ (.up ℤ))
  intro P
  rw [exactAdjCounit]
  rw [derivedEtaleLowerShriekUpperStarAdjunction, Adjunction.localization_counit_app]
  rfl

private theorem pullback_inverse_mate
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U V : Scheme.{u}} (e : U ⟶ V) [Etale e] :
    ((mateEquiv
      (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars V.smallEtaleTopology φ))
      (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars U.smallEtaleTopology φ))).symm
        (TwoSquare.mk _ _ _ _
          (Functor.mapDerivedCategorySquareIso
            (upperStarRestrictScalarsIsoSheaf φ e)).hom)).natTrans =
      (properOpenCoefficientPullbackIso φ e).inv := by
  set_option backward.isDefEq.respectTransparency false in
    let a := Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars V.smallEtaleTopology φ)
    let b := Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars U.smallEtaleTopology φ)
    let x := TwoSquare.mk _ _ _ _ (scalarRestrictionPullbackIso φ e).hom
    let i := leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) e
    let j := leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) e
    have heq : TwoSquare.mk _ _ _ _
        (Functor.mapDerivedCategorySquareIso (upperStarRestrictScalarsIsoSheaf φ e)).hom =
        TwoSquare.mk _ _ _ _
          (Functor.whiskerLeft (Sheaf.derivedRestrictScalars V.smallEtaleTopology φ)
            i.inv ≫ x.natTrans ≫
            Functor.whiskerRight j.hom
              (Sheaf.derivedRestrictScalars U.smallEtaleTopology φ)) := by
      ext M
      dsimp only [x, i, j, scalarRestrictionPullbackIso, NatTrans.comp_app,
        Functor.whiskerLeft_app, Functor.whiskerRight_app, Iso.trans_hom,
        Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Iso.symm_hom]
      simp only [Category.assoc, Iso.inv_hom_id_app_assoc,
        ← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
      erw [Category.comp_id]
    rw [heq, inverse_mate_transport a b x i j]
    have hm : ((mateEquiv a b).symm x).natTrans = (scalarPullbackIso φ e).inv :=
      congrArg Iso.inv (scalarPullback_eq φ e)
    rw [hm]
    ext M
    simp only [properOpenCoefficientPullbackIso, Iso.trans_inv,
      Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv, Iso.symm_inv,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app, i, j,
      Category.assoc, ProEtale.pbcFixedScalarExtension]

private theorem firstDerived_eq_second
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U V : Scheme.{u}} (e : U ⟶ V) [Etale e]
    (K : DerivedCategoryModule A V) :
    etaleCounitScalarFirstDerived φ e K = (scalarExtension φ V).map
      ((derivedEtaleLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} A) e inferInstance).counit.app K) := by
  let a := (etaleLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategoryAdjunction
  let b := (etaleLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} B) e inferInstance).mapDerivedCategoryAdjunction
  let x := Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars V.smallEtaleTopology φ)
  let z := Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars U.smallEtaleTopology φ)
  let α := (mateEquiv x z).symm (TwoSquare.mk _ _ _ _
    (Functor.mapDerivedCategorySquareIso (upperStarRestrictScalarsIsoSheaf φ e)).hom)
  have hm : ((mateEquiv a b).symm α).natTrans = (sumCoefficientIso φ e).inv := by
    have hh := scalarOpenInverseMate a b x z
      (Functor.mapDerivedCategorySquareIso (upperStarRestrictScalarsIsoSheaf φ e)).symm
    rw [uniq_eq_conjugate] at hh
    exact hh
  have h := mateEquiv_counit_symm a b α K
  change _ = ((mateEquiv a b).symm α).natTrans.app _ ≫ _ at h
  rw [hm] at h
  have hr : α.natTrans = (properOpenCoefficientPullbackIso φ e).inv :=
    pullback_inverse_mate φ e
  change (etaleLowerShriek (ModuleCat.{u + 1} B) e inferInstance).mapDerivedCategory.map
      (α.natTrans.app K) ≫ b.counit.app ((scalarExtension φ V).obj K) =
    (sumCoefficientIso φ e).inv.app _ ≫ (scalarExtension φ V).map (a.counit.app K) at h
  rw [hr] at h
  have hh := congrArg (fun t ↦ (sumCoefficientIso φ e).hom.app
    ((upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.obj K) ≫ t) h
  simpa only [a, b, derivedAdj_eq, Category.assoc, Iso.hom_inv_id_app_assoc,
    etaleCounitScalarFirstDerived] using hh

private theorem boundedConstructible_iff_source
    (R : Type (u + 1)) [CommRing R] [Finite R] (X : Scheme.{u})
    (M : DerivedCategoryModule R X) :
    DerivedCategory.isBoundedConstructible R X M ↔
      DerivedCategory.boundedConstructible (ModuleCat.{u + 1} R) X M := by
  constructor
  · rintro ⟨hc, a, b, -, hz⟩
    refine ⟨⟨⟨a, ?_⟩, ⟨b, ?_⟩⟩, fun i ↦
      (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp (hc i)⟩
    · exact (_root_.DerivedCategory.isGE_iff M a).mpr fun i hi ↦ hz i (.inl hi)
    · exact (_root_.DerivedCategory.isLE_iff M b).mpr fun i hi ↦ hz i (.inr hi)
  · rintro ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hc⟩
    refine ⟨fun i ↦
      (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr (hc i),
      min a b, b, min_le_right _ _, fun i hi ↦ ?_⟩
    rcases hi with hi | hi
    · exact (_root_.DerivedCategory.isGE_iff M a).mp ha i
        (hi.trans_le (min_le_left _ _))
    · exact (_root_.DerivedCategory.isLE_iff M b).mp hb i hi

/-- Extension of coefficients commutes with the sum/evaluation counit, including its
mate and its graph-normalized compact-support form.
Source: blueprint main-20261015, reduction-exceptional proof, Charts, retained Step 8;
Stacks Project, etale-cohomology.tex, Tag 03S3
(blueprint: lem-sp-etale-sum-counit-scalar).

Here `properOpenCoefficientPullbackIso.inv` is precisely a_e: it transports the inverse
of the K-flat-normalized `scalarPullbackIso` to exact inverse image. The two occurrences
of `normalizedSumComparison.hom` followed by the sum counit are the normalized compact
counits. Thus the final clause uses the actual `etaleCoefficientMap`, for every chosen
compactification and every graph-normalized comparison, rather than a free map.

Proof (the seven steps of the DAG node):
1. Finite type over the field makes U and V Noetherian
(lem-weil-pbc-finite-type-over-noetherian). For K bounded constructible of finite Tor
amplitude, lem-sf-etale-flat-constructible supplies a bounded flat constructible model.
It is K-flat by lem-weil-pbc-independent-bounded-flat-kflat. Exact inverse image preserves
its flatness and finite degree interval, so e^*K is bounded and has finite Tor amplitude.
For constructibility, pull the constructible stratification of each cohomology sheaf
back along e (lemma-constructible-pullback-stratification); the strata remain constructible
by lem-pur-scheme-constructible-preimage. Pull back its trivializing etale covers and use
lemma-constructible-pullback-constant. Exact inverse image commutes with cohomology by
prop-weil-pbc-inverse-image-modules-exact. Hence e^*K is an allowed ctf input for sigma.
2. Resolve K by a flat-term K-flat complex P (lem-pc-kflat-resolution). Inverse image
preserves these properties by lem-weil-pbc-ringed-topoi-derived-tensor-pullback, and sum
extension does so by lem-pur-etale-sum-flat-kflat. Thus lem-pur-derived-change-of-rings
computes all three scalar extensions by termwise tensor. The whole-derived adjunction
of lem-amb-etale-adjoint-locality has the degreewise sheaf counit on these models.
3. By lem-weil-pbc-etale-inverse-image-restriction, inverse image of a sheaf F at (W,s)
is F(W). The presheaf presenting sum extension of that inverse image is the direct sum
of F(W) over lifts s, by def-weil-pbc-etale-sum-extension. The counit sends each included
x to x, hence a finite family to its sum. This map respects restriction and sheafifies
by def-weil-presheaf-modules-sheafification; its adjoint is the identity, so it is exactly
the sum/evaluation counit. No assertion that arbitrary sheaf sections are sums is used.
4. On P, the normalized sigma of lem-sp-et-proet-coefficient-compatibility sends
inclusion_s(x) tensor b to inclusion_s(x tensor b). The inverse of the ordinary comparison
underlying def-pur-etale-scalar-pullback-iso sends x tensor b to the same tensor at (W,s).
The left composite and tensor of the fold map therefore both send every pure generator
to x tensor b. Linearity and the tensor and sum sheafification universal properties
(def-pur-sheaf-tensor-product and def-weil-presheaf-modules-sheafification) give equal
B-linear sheaf maps, compatible with differentials since B is in degree zero.
5. Localize this chain-map equality using def-weil-pbc-derived-categories. The K-flat
computations and resolution independence in lem-pur-derived-change-of-rings identify
the maps with the displayed derived composites on QP. Naturality and QP isomorphic to K
transport the equality to K. Neither flatness nor finite projective dimension of B/A
was assumed.
6. Precompose by sigma inverse at e^*K. The resulting counit transpose is exactly the
one defining the mate of sigma inverse, with L1=E_A, L2=E_B, G=T_U and H=T_V in
def-weil-pbc-adjunction-mate. Injectivity of the adjunction bijection gives the second
clause at K, with this orientation.
7. Write C_R for normalizedSumComparison and F_R for compact support. By
lem-asd-etale-compact-support-normalization the normalized compact counit is C_R at
 e_R^*K followed by v_R. The etale clause of lem-sp-et-proet-coefficient-compatibility says
beta(L) followed by C_B at T_U L equals T_V(C_A at L) followed by sigma(L).
Set L=e_A^*K, use naturality of C_B at a_e(K), and apply Step 5. Functoriality turns
the result into T_V of the normalized A compact counit, the last displayed equation.
-/
theorem etaleSumCounitScalar
    (ell p : ℕ) [Fact ell.Prime] (_hp : 0 < p) (_hEll : p ≠ ell)
    (k : Type u) [Field k] [CharP k p]
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (n : ℕ) (_hA : (ell ^ n : A) = 0) (_hB : (ell ^ n : B) = 0) (φ : A →+* B)
    {U V : Scheme.{u}} [U.Over (Spec (.of k))] [V.Over (Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [IsSeparated (U ↘ Spec (.of k))]
    [LocallyOfFiniteType (V ↘ Spec (.of k))] [QuasiCompact (V ↘ Spec (.of k))]
    [IsSeparated (V ↘ Spec (.of k))]
    (e : U ⟶ V) [e.IsOver (Spec (.of k))]
    [Etale e] [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    (K : DerivedCategoryModule A V) (_hK : ProEtale.AdjunctionTransfer.etaleProperty A V K) :
    ((sumCoefficientIso φ e).hom.app
        ((upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.obj K) ≫
      (etaleLowerShriek (ModuleCat.{u + 1} B) e inferInstance).mapDerivedCategory.map
        ((properOpenCoefficientPullbackIso φ e).inv.app K) ≫
      (derivedEtaleLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} B) e inferInstance).counit.app ((scalarExtension φ V).obj K) =
    (scalarExtension φ V).map
      ((derivedEtaleLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} A) e inferInstance).counit.app K)) ∧
    ((properOpenCoefficientPullbackIso φ e).inv.app K =
      (mateEquiv
        (derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) e inferInstance)
        (derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) e inferInstance)
        (TwoSquare.mk _ _ _ _ (sumCoefficientIso φ e).inv)).natTrans.app K) ∧
    (∀ (c : Compactification e)
        (NA : EtaleCompactSupportNormalization A) (NB : EtaleCompactSupportNormalization B),
      etaleCoefficientMap φ c
          ((upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.obj K) ≫
        (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c).map
          ((properOpenCoefficientPullbackIso φ e).inv.app K) ≫
        (normalizedSumComparison B k NB e c).hom.app
          ((upperStar (ModuleCat.{u + 1} B) e).mapDerivedCategory.obj
            ((scalarExtension φ V).obj K)) ≫
        (derivedEtaleLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} B) e inferInstance).counit.app ((scalarExtension φ V).obj K) =
      (scalarExtension φ V).map
        ((normalizedSumComparison A k NA e c).hom.app
            ((upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.obj K) ≫
          (derivedEtaleLowerShriekUpperStarAdjunction
            (ModuleCat.{u + 1} A) e inferInstance).counit.app K)) := by
  classical
  obtain ⟨a, b, hab⟩ := _hK.2
  have hab' : DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} A) V
      (min a b) b K :=
    _root_.DerivedCategory.torAmplitudeIn.mono (min_le_left _ _) le_rfl hab
  have htor := DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.mpr hab'
  obtain ⟨P, ⟨hz, hf⟩, ⟨κ₀⟩⟩ :=
    (hasTorAmplitudeIn_iff_exists_flatModel A (min a b) b (min_le_right _ _) K
      ((boundedConstructible_iff_source A V K).mp _hK.1)).mp htor
  let κ := κ₀.symm
  have heK : ProEtale.AdjunctionTransfer.etaleProperty A U
      ((upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.obj K) := by
    let F := upperStar (ModuleCat.{u + 1} A) e
    let Q : CochainComplex (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ :=
      (F.mapHomologicalComplex (.up ℤ)).obj P
    have : Q.IsStrictlyGE (min a b) := (Q.isStrictlyGE_iff _).mpr fun i hi ↦
      F.map_isZero (hz i (.inl hi))
    have : Q.IsStrictlyLE b := (Q.isStrictlyLE_iff _).mpr fun i hi ↦
      F.map_isZero (hz i (.inr hi))
    have hQ : ∀ i : ℤ, ObjectProperty.flat (Q.X i) := fun i ↦
      Functor.PreservesFlat.flat_obj (F := F) (hf i)
    have η : _root_.DerivedCategory.Q.obj Q ≅ F.mapDerivedCategory.obj K :=
      (F.mapDerivedCategoryFactors.app P).symm ≪≫ F.mapDerivedCategory.mapIso κ
    refine ⟨(boundedConstructible_iff_source A U _).mpr
      (((boundedConstructible_iff_source A V K).mp _hK.1).mapDerivedCategory_upperStar e),
      min a b, b, ?_⟩
    exact (_root_.DerivedCategory.torAmplitudeIn _ (min a b) b).prop_of_iso η
      (_root_.DerivedCategory.torAmplitudeIn_Q_obj_of_flat Q (min a b) b hQ)
  have hmain := firstDerived_eq_second φ e K
  refine ⟨hmain, ?_, ?_⟩
  · let adjA := derivedEtaleLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) e inferInstance
    let adjB := derivedEtaleLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} B) e inferInstance
    let α := TwoSquare.mk _ _ _ _ (sumCoefficientIso φ e).inv
    apply (adjB.homEquiv _ _).symm.injective
    simp only [Adjunction.homEquiv_counit]
    have hm := mateEquiv_counit adjA adjB α K
    change _ = (sumCoefficientIso φ e).inv.app _ ≫ _ at hm
    rw [hm]
    apply (cancel_epi ((sumCoefficientIso φ e).hom.app _)).mp
    simpa only [Category.assoc, Iso.hom_inv_id_app_assoc,
      etaleCounitScalarFirstDerived] using hmain
  · intro c NA NB
    have hs := etaleProEtaleCoefficientCompatibility_sum ell p _hp _hEll k
      (show ∃ m : ℕ, ∀ x : A, (ell ^ m) • x = 0 from
        ⟨n, fun x ↦ by rw [nsmul_eq_mul, Nat.cast_pow, _hA, zero_mul]⟩)
      (show ∃ m : ℕ, ∀ x : B, (ell ^ m) • x = 0 from
        ⟨n, fun x ↦ by rw [nsmul_eq_mul, Nat.cast_pow, _hB, zero_mul]⟩)
      φ e c NA NB _ heK
    have hn := (normalizedSumComparison B k NB e c).hom.naturality
      ((properOpenCoefficientPullbackIso φ e).inv.app K)
    dsimp only [Functor.comp_obj] at hn
    slice_lhs 2 3 => rw [hn]
    slice_lhs 1 2 => rw [hs]
    dsimp only [etaleCounitScalarFirstDerived] at hmain
    simp only [Category.assoc]
    rw [hmain, ← Functor.map_comp]

end AlgebraicGeometry.Etale
