/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.OpenImmersion

import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushIntegralDerivedIso
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.QlbarDirectImageComparison
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedContinuitySections
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
import WeilConjectures.AlgebraicGeometry.Bounded.BoundedComplexDirectImagePresheaf
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.Algebra.Field.ULift
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartTriangulated
public import WeilConjectures.AlgebraicGeometry.Integral.Constant.IntegralConstantModelHeartClosureSupplement
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralCoefficientExtComparison
public import WeilConjectures.AlgebraicGeometry.IntegralOpenDirectImage.IntegralOpenDirectImageGeneral
public import WeilConjectures.AlgebraicGeometry.OpenCoefficientScalarModels
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.SixFunctors.Integral.IntegralModelsGeneratorsGeneral

/-! # Open direct image for the three ell-adic coefficient rings

Source: literature/blueprint/latest/blueprint/part-six-operations/
sec-constructibility-upper-shriek/sec-ladic-summary/sk-prop-open-coefficients/
_section.md and sk-prop-open-coefficients.proof.md
(blueprint: lem-sfb-admissible-direct-image).

The three conjuncts use the existing finite constant scalar local-model definition
of bounded constructibility and the ordinary ambient right derived module direct image.
-/

@[expose] public section

set_option autoImplicit false
universe u

open CategoryTheory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

private theorem open_bc_iso
    {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}}
    {K L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))} (e : K ≅ L)
    (hK : constantModelBoundedConstructible Λ X K) :
    constantModelBoundedConstructible Λ X L := by
  exact ⟨DerivedCategory.TStructure.t.bounded.prop_of_iso e hK.1,
    fun n ↦ constructible_iso (Λ := Λ) ((DerivedCategory.homologyFunctor _ n).mapIso e) (hK.2 n)⟩

private theorem open_bc_transport
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (e : Λ ≅ Λ') [IsMonHom e.hom] (X : Scheme.{u})
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :
    constantModelBoundedConstructible Λ' X
      ((Mod.comap (coefficientMap e.inv X)).mapDerivedCategory.obj K) ↔
      constantModelBoundedConstructible Λ X K := by
  let F : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X) ⥤
      Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ' X) :=
    Mod.comap (coefficientMap e.inv X)
  constructor
  · intro h
    refine ⟨F.bounded_of_bounded_mapDerivedCategory_obj h.1, fun n ↦ ?_⟩
    apply (constantModel_comap_iff e.inv X _).1
    exact constructible_iso (Λ := Λ')
      ((F.mapDerivedCategoryHomologyFunctorIso n).app K).symm (h.2 n)
  · intro h
    refine ⟨F.bounded_mapDerivedCategory_obj h.1, fun n ↦ ?_⟩
    exact constructible_iso (Λ := Λ') ((F.mapDerivedCategoryHomologyFunctorIso n).app K)
      ((constantModel_comap_iff e.inv X _).2 (h.2 n))

/-- Direct image along a quasi-compact open immersion preserves bounded constructibility
for integral, finite-extension and algebraic-closure coefficients.
Source: blueprint sk-prop-open-coefficients, statement and proof
(blueprint: lem-sfb-admissible-direct-image).

We realize the finite extension inside the fixed algebraic closure, with its induced
valuation topology, as in the coefficient framework. Its ring of integers is
`Profinite.padicIntegersRingObj`; the algebraic-closure ring uses sections taking values
in one finite subextension. All three coefficient rings are pulled back by `condensedRingObj`.

Proof:
1. For O_E, apply det-thm-sf-pf-adic-open (any field with characteristic different from ell,
   so both standing field cases): Rj_* commutes with derived inverse limits and cones, so
   Rj_*K is derived complete and its reduction modulo the uniformizer is Rj_* of the
   reduction of K. The reduction comes from the etale site; Tag 09A6 identifies its direct
   image with the pullback of the etale one, bounded constructible by open finiteness, and
   the integral criterion gives Rj_*K in Dbc(X, O_E).
2. For E and Qlbar, det-lem-integral-models-generators (integral-models(4)) expresses the
   input by finite cones and shifts of coefficient extensions of integral
   C = a_!L_0 in Dbc(U, O_E). Step 1 makes H = Rj_*C integral bounded constructible; j is
   qcqs and C is bounded.
3. lem-sfb-localized-direct-image-comparison identifies the E-image of C[1/ell] with
   E_X ⊗^L H, and lem-sfb-qlbar-direct-image-comparison identifies the Qlbar-image with
   Qlbar_X ⊗^L_{E_X} (E_X ⊗^L H); their proofs carry the two bounded-continuity colimits
   (telescope inverting ell, finite subextensions). lem-sfb-open-rational-scalar-local-models
   keeps the inputs bounded below and makes both scalar extensions of H bounded
   constructible in the finite constant local model convention.
4. The module pushforward is additive and left exact (sk-def-sfb-module-pushforward-pullback)
   on a Grothendieck module category (lem-sfb-modobj-grothendieck), so Rj_* is triangulated
   (lem-weil-pbc-derived-direct-image-triangulated). The rational Dbc categories are
   triangulated (sk-cor-coefficient-heart-ii); induction through the finite cone-and-shift
   construction of step 2 gives both rational conclusions.
-/
theorem constantModelBoundedConstructible_open_coefficient_direct_image
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (Finite k ∨ IsAlgClosed k)] [Fact (ringChar k ≠ ℓ)]
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    {U X : Scheme.{u}} [U.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [IsSeparated (U ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    (j : U ⟶ X) [j.IsOver (Spec (.of k))] [IsOpenImmersion j] [QuasiCompact j] :
    (∀ K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) U)),
      constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.val) U K →
      constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.val) X
        ((CondensedRing.moduleObjectDerivedPushforward
          (Profinite.padicIntegersRingObj ℓ E.val) j).obj K)) ∧
    (∀ K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousMapRingObj E) U)),
      constantModelBoundedConstructible (Profinite.continuousMapRingObj E) U K →
      constantModelBoundedConstructible (Profinite.continuousMapRingObj E) X
        ((CondensedRing.moduleObjectDerivedPushforward
          (Profinite.continuousMapRingObj E) j).obj K)) ∧
    (∀ K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
        (condensedRingObj (Profinite.padicAlgClRingObj ℓ) U)),
      constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) U K →
      constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) X
        ((CondensedRing.moduleObjectDerivedPushforward
          (Profinite.padicAlgClRingObj ℓ) j).obj K)) := by
  classical
  have integral (F : PadicAlgCl.FiniteIntermediateField ℓ)
      (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ F.val) U)))
      (hK : constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ F.val) U K) :
      constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ F.val) X
        ((CondensedRing.moduleObjectDerivedPushforward
          (Profinite.padicIntegersRingObj ℓ F.val) j).obj K) := by
    let : FiniteDimensional ℚ_[ℓ] (ULift.{u} F.val) :=
      (ULift.moduleEquiv (R := ℚ_[ℓ]) (M := F.val)).symm.finiteDimensional
    let eR := integerRingSheafIso.{u} ℓ ⟨F.val, F.property⟩
    let e : Profinite.padicIntegersRingObj.{u} ℓ F.val ≅
        DerivedNakayama.integerRing ℓ (ULift.{u} F.val) :=
      (sheafCompose (coherentTopology Profinite.{u})
        (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso eR
    have : IsMonHom e.hom := Sheaf.isMonHom_sheafCompose_map _ eR.hom
    have (T : Scheme.{u}) :
        CategoryTheory.Limits.PreservesFiniteLimits
          (Mod.extendScalars (coefficientMap e.inv T)) :=
      CategoryTheory.Limits.preservesFiniteLimits_of_natIso
        (Mod.extendScalarsIsoComapInv _).symm
    have h := (IntegralOpenDirectImage.integral_open_direct_image_any_field
      ℓ (ULift.{u} F.val) j k (Fact.out : ringChar k ≠ ℓ)
      ((Mod.comap (coefficientMap e.inv U)).mapDerivedCategory.obj K)
      ((open_bc_transport e U K).2 hK)).2.2.1
    apply (open_bc_transport e X _).1
    exact open_bc_iso ((CondensedRing.derivedComapLowerStarIso e.inv j).app K).symm h
  have : IsLocallyNoetherian U :=
    LocallyOfFiniteType.isLocallyNoetherian (U ↘ Spec (.of k))
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have : CompactSpace U := QuasiCompact.compactSpace_of_compactSpace (U ↘ Spec (.of k))
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have : QuasiSeparated j := inferInstance
  have generator_image (F : PadicAlgCl.FiniteIntermediateField ℓ) :
      ∀ J, WeilConjectures.SixFunctors.integralModelGenerator U ℓ F J →
        constantModelBoundedConstructible (Profinite.continuousMapRingObj F) X
          ((CondensedRing.moduleObjectDerivedPushforward
            (Profinite.continuousMapRingObj F) j).obj J) := by
    intro J hJ
    rcases hJ with ⟨S, V, a, b, ha, hb, L, hL, rfl⟩
    have := ha
    have := hb
    obtain ⟨π, hπ⟩ := PadicAlgCl.isPrincipal_maximalIdeal_integers ℓ F.val
    let M := integralLowerShriek U (Profinite.padicIntegersRingObj ℓ F.val) a b L
    let C := (DerivedCategory.singleFunctor _ 0).obj M
    have hC := ((integral_models_generators_general k ℓ U F π hπ.symm).2.2
      S V a b L hL).1
    have hH := integral F C hC
    obtain ⟨n, hn⟩ := hC.1.1
    have : C.IsGE n := hn
    have : IsIso ((CondensedRing.derivedPushHom
        (padicIntegersRingObjToContinuousMapRingObj ℓ F) j).app C) :=
      CondensedRing.isIso_derivedPushHom_app_padicIntegers_of_isGE ℓ F j C n
    let A := Mod.extendScalars (padicIntegersToPadicSubfield U ℓ F)
    let eC := A.singleFunctorCompLeftDerivedFunctorIso.app M
    have h := (open_rational_scalar_local_models ℓ F X).1 _ hH
    exact open_bc_iso
      (asIso ((CondensedRing.derivedPushHom
        (padicIntegersRingObjToContinuousMapRingObj ℓ F) j).app C) ≪≫
        (CondensedRing.moduleObjectDerivedPushforward
          (Profinite.continuousMapRingObj F) j).mapIso eC) h
  have qlbar_generator_image (F : PadicAlgCl.FiniteIntermediateField ℓ) :
      ∀ J, WeilConjectures.SixFunctors.qlbarModelGenerator U ℓ F J →
        constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) X
          ((CondensedRing.moduleObjectDerivedPushforward
            (Profinite.padicAlgClRingObj ℓ) j).obj J) := by
    intro J hJ
    rcases hJ with ⟨S, V, a, b, ha, hb, L, hL, rfl⟩
    have := ha
    have := hb
    obtain ⟨π, hπ⟩ := PadicAlgCl.isPrincipal_maximalIdeal_integers ℓ F.val
    let M := integralLowerShriek U (Profinite.padicIntegersRingObj ℓ F.val) a b L
    let C := (DerivedCategory.singleFunctor _ 0).obj M
    have hC := ((integral_models_generators_general k ℓ U F π hπ.symm).2.2
      S V a b L hL).1
    have hH := integral F C hC
    obtain ⟨n, hn⟩ := hC.1.1
    have : C.IsGE n := hn
    have : IsIso ((CondensedRing.derivedPushHom
        (padicIntegersRingObjToContinuousMapRingObj ℓ F) j).app C) :=
      CondensedRing.isIso_derivedPushHom_app_padicIntegers_of_isGE ℓ F j C n
    let AU := Mod.extendScalars (padicIntegersToPadicSubfield U ℓ F)
    let BU := Mod.extendScalars
      (coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ F) U)
    let BX := Mod.extendScalars
      (coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ F) X)
    have hCE := (open_rational_scalar_local_models ℓ F U).1 C hC
    have : IsIso ((CondensedRing.derivedPushHom
        (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ F) j).app
          (AU.leftDerivedFunctor.obj C)) :=
      CondensedRing.isIso_derivedPushHom_padicAlgCl_of_boundedBelow ℓ F j
        ⟨AU.leftDerivedFunctor.obj C, hCE.1.1⟩
    let eE := AU.singleFunctorCompLeftDerivedFunctorIso.app M
    let eB := BU.leftDerivedFunctor.mapIso eE ≪≫
      BU.singleFunctorCompLeftDerivedFunctorIso.app ((finiteCoefficientExtension U ℓ F).obj M)
    have h := (open_rational_scalar_local_models ℓ F X).2.2 _
      ((open_rational_scalar_local_models ℓ F X).1 _ hH)
    exact open_bc_iso
      (BX.leftDerivedFunctor.mapIso (asIso ((CondensedRing.derivedPushHom
        (padicIntegersRingObjToContinuousMapRingObj ℓ F) j).app C)) ≪≫
        asIso ((CondensedRing.derivedPushHom
          (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ F) j).app
            (AU.leftDerivedFunctor.obj C)) ≪≫
        (CondensedRing.moduleObjectDerivedPushforward
          (Profinite.padicAlgClRingObj ℓ) j).mapIso eB) h
  refine ⟨integral E, ?_, ?_⟩
  · intro K hK
    obtain ⟨π, hπ⟩ := PadicAlgCl.isPrincipal_maximalIdeal_integers ℓ E.val
    have hgen := (WeilConjectures.SixFunctors.integral_models_generators_general
      k ℓ U E π hπ.symm).1 K hK
    let P := constantModelBoundedConstructible (Profinite.continuousMapRingObj E) X
    have : P.IsTriangulated :=
      ((constantModelBoundedConstructible_field_triangulated ℓ X).1 E).2.1
    have : P.IsClosedUnderIsomorphisms :=
      ((constantModelBoundedConstructible_field_triangulated ℓ X).1 E).1
    rw [unary_relation_sInf_iff] at hgen
    exact hgen (P.inverseImage
      (CondensedRing.lowerStar (Profinite.continuousMapRingObj E) j).rightDerivedFunctor)
      ⟨generator_image E, inferInstance, inferInstance⟩
  · intro K hK
    obtain ⟨π, hπ⟩ := PadicAlgCl.isPrincipal_maximalIdeal_integers ℓ E.val
    obtain ⟨F, hgen⟩ := (WeilConjectures.SixFunctors.integral_models_generators_general
      k ℓ U E π hπ.symm).2.1 K hK
    let P := constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) X
    have : P.IsTriangulated :=
      (constantModelBoundedConstructible_field_triangulated ℓ X).2.2.1
    have : P.IsClosedUnderIsomorphisms :=
      (constantModelBoundedConstructible_field_triangulated ℓ X).2.1
    rw [unary_relation_sInf_iff] at hgen
    exact hgen (P.inverseImage
      (CondensedRing.lowerStar (Profinite.padicAlgClRingObj ℓ) j).rightDerivedFunctor)
      ⟨qlbar_generator_image F, inferInstance, inferInstance⟩

end AlgebraicGeometry.ProEtale
