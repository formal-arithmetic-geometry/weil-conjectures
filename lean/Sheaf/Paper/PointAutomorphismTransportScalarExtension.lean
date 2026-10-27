/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q29
-/
module
import Mathlib.Algebra.CharP.CharAndCard
import all Sheaf.Paper.PointSectionsScalarExtension
import all Sheaf.Paper.IsomorphismComparisonScalarExtension
import Sheaf.Paper.IsomorphismComparisonNatural
import Sheaf.Paper.IntegralPullbackComparisonRealization
public import Sheaf.Paper.PointAutomorphismRestrictionNatural
public import Sheaf.Paper.PointSectionsScalarExtension
public import Sheaf.Paper.IsomorphismComparisonScalarExtension
public import Sheaf.Paper.IntegralScalarExtensionUniverses
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Paper.SfRationalizationKaroubi
import Sheaf.Paper.CoefficientComplexRationalization

/-! # Point-automorphism transport and completed coefficient extension

Source: Deligne, Weil II, (1.1.3) and (1.1.7), pp. 150--151 (context); the explicit pro-etale
completed-coefficient calculation in the DAG is agent-written.
(blueprint: lem-weil-point-automorphism-transport-scalar-extension).

All definitions below are applications, scalar unliftings, or composites of recorded canonical
maps. The integral coefficients remain the completed coefficient sheaf. The theorem declarations
state the integral, rational, identity and tower clauses and the required prime-invertibility
input; all their proofs are postponed.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u
open scoped ChangeOfRings
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.ProEtale
namespace WeilConjectures
attribute [local instance 2000] pointScalarModuleDerived
  pointIntegralModuleTensorAdditive pointIntegralModuleTensorLimits
  pointIntegralModuleTensorColimits
attribute [local irreducible] completedScalarChangeData completedOrdinaryScalarExtension
  completedDerivedScalarExtension completedScalarCounit completedScalarTensorSection
  completedIntegralCoefficientSheafUnrestricted integralOperationsGoodComplex
variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)

/-- The coefficient prime is a unit in every stalk of the geometric point. This supplies
an existing comparison input from the finite-field hypotheses, rather than assuming it.

Source: the finite-field conventions, blueprint order 411, and the coefficient convention
l different from p (blueprint: lem-weil-point-automorphism-transport-scalar-extension).

Proof: the cardinality of k_0 and primality of p identify its characteristic with p
(charP_of_card_eq_prime_pow). A distinct prime l is nonzero in k_0 and hence is a unit
(CharP.cast_ne_zero_of_ne_of_prime). Map this unit through the inclusion k_0 into k,
then through the inverse of Gamma(Spec k)=k and the germ at each x. Ring homomorphisms
preserve units and natural-number casts, giving the stated unit in every stalk. -/
theorem pointTransportPrimeUnits (_hl : l ≠ D.p) :
    ∀ x : Spec (.of D.k), IsUnit (l : (Spec (.of D.k)).presheaf.stalk x) := by
  classical
  let : Fintype D.k₀ := Fintype.ofFinite D.k₀
  have : Fact D.p.Prime := ⟨D.prime⟩
  have : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using D.card_base.trans D.cardinality_eq)
  have hunit : IsUnit (l : D.k₀) :=
    (CharP.cast_ne_zero_of_ne_of_prime D.k₀ (Fact.out : l.Prime) _hl.symm).isUnit
  intro x
  simpa only [map_natCast] using (hunit.map (algebraMap D.k₀ D.k)).map
    ((Scheme.ΓSpecIso (CommRingCat.of D.k)).inv ≫
      (Spec (.of D.k)).presheaf.germ ⊤ x (by trivial)).hom

variable (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (g : Spec (.of D.k) ⟶ Spec (.of D.k)) [IsIso g]

/-- The recorded restriction/coprojection map, with the canonical coefficient unlift. The chosen
module transformation is fixed by equality on every section in
point_automorphism_restriction_natural; no arbitrary transformation is selected.

Source: Deligne, Weil II, (1.1.3) and (1.1.7), pp. 150--151 (context); the explicit pro-etale
completed-coefficient calculation in the DAG is agent-written.
(blueprint: lem-weil-point-automorphism-transport-scalar-extension). -/
def pointAutomorphismRestrictionModules :
    pointCompletedSections D.k l E ⟶
      inverseImageIntegralModules l E g ⋙ pointCompletedSections D.k l E :=
  Functor.whiskerRight
    (point_automorphism_restriction_natural l E D hl g none).2.2.choose
    (ModuleCat.restrictScalars
      (ULift.ringEquiv : ULift.{u + 1}
        (Padic.coefficientExtensionIntegers l E) ≃+* _).symm.toRingHom)

/-- The same restriction transformation localized termwise on all complexes, followed by the
canonical exact-functor composition comparison. This has exactly the endpoints Gamma and G
followed by Gamma. Localization uniquely determines it from the module transformation; no
constructibility hypothesis is imposed.

Source: Deligne, Weil II, (1.1.3) and (1.1.7), pp. 150--151 (context); the explicit pro-etale
completed-coefficient calculation in the DAG is agent-written.
(blueprint: lem-weil-point-automorphism-transport-scalar-extension). -/
def pointAutomorphismRestrictionDerived :
    pointCompletedDerivedSections D.k l E ⟶
      inverseImageIntegralDerived l E g ⋙ pointCompletedDerivedSections D.k l E :=
  Localization.liftNatTrans DerivedCategory.Q
    (HomologicalComplex.quasiIso _ (.up ℤ))
    ((pointCompletedSections D.k l E).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    ((Functor.mapHomologicalComplex
      (inverseImageIntegralModules l E g ⋙ pointCompletedSections D.k l E) (.up ℤ)) ⋙
        DerivedCategory.Q)
    (pointCompletedDerivedSections D.k l E)
    (inverseImageIntegralModules l E g ⋙ pointCompletedSections D.k l E).mapDerivedCategory
    (Functor.whiskerRight
      (NatTrans.mapHomologicalComplex (pointAutomorphismRestrictionModules D l hl E g) (.up ℤ))
      DerivedCategory.Q) ≫
    (Functor.mapDerivedCategoryCompIso (inverseImageIntegralModules l E g)
      (pointCompletedSections D.k l E)).hom


/-- The specified integral kappa at the geometric point, with its prime-invertibility inputs
supplied by the finite-field datum. This is a direct application of
inverseImagePullbackComparisonDerived, retaining its chosen K-flat quotient-cone construction.

Source: Deligne, Weil II, (1.1.3) and (1.1.7), pp. 150--151 (context); the explicit pro-etale
completed-coefficient calculation in the DAG is agent-written.
(blueprint: lem-weil-point-automorphism-transport-scalar-extension). -/
def pointTransportKappa (K : DerivedCategory (integralTowerModules l E (Spec (.of D.k)))) :=
  inverseImagePullbackComparisonDerived l E g (pointTransportPrimeUnits D l hl)
    (pointTransportPrimeUnits D l hl) K

/-- The point transport t is restriction sigma followed by sections of the specified kappa. It is
defined on each object; no naturality of this composite is asserted.

Source: Deligne, Weil II, (1.1.3) and (1.1.7), pp. 150--151 (context); the explicit pro-etale
completed-coefficient calculation in the DAG is agent-written.
(blueprint: lem-weil-point-automorphism-transport-scalar-extension). -/
def pointTransport (K : DerivedCategory (integralTowerModules l E (Spec (.of D.k)))) :=
  (pointAutomorphismRestrictionDerived D l hl E g).app K ≫
    (pointCompletedDerivedSections D.k l E).map (pointTransportKappa D l hl E g K)

set_option linter.defProp false in
/-- The recorded isomorphism-pullback admissibility assertion for G_E K, specialized to the
geometric point. This is an existing proof projection, not a new constructibility assumption.

Source: Deligne, Weil II, (1.1.3) and (1.1.7), pp. 150--151 (context); the explicit pro-etale
completed-coefficient calculation in the DAG is agent-written.
(blueprint: lem-weil-point-automorphism-transport-scalar-extension). -/
def pointTransportInverseConstructible
    (K : DerivedCategory (integralTowerModules l E (Spec (.of D.k))))
    (hK : sfIntegralConstructible l E (Spec (.of D.k)) K) :=
  (isomorphismComparisonInputs_constructible l E g (pointTransportPrimeUnits D l hl)
    (pointTransportPrimeUnits D l hl) K hK).1

set_option linter.defProp false in
/-- The recorded isomorphism-pullback admissibility assertion for P_E K, specialized to the
geometric point. Its completeness component is used in the specified scalar-pullback comparison.

Source: Deligne, Weil II, (1.1.3) and (1.1.7), pp. 150--151 (context); the explicit pro-etale
completed-coefficient calculation in the DAG is agent-written.
(blueprint: lem-weil-point-automorphism-transport-scalar-extension). -/
def pointTransportPullbackConstructible
    (K : DerivedCategory (integralTowerModules l E (Spec (.of D.k))))
    (hK : sfIntegralConstructible l E (Spec (.of D.k)) K) :=
  (isomorphismComparisonInputs_constructible l E g (pointTransportPrimeUnits D l hl)
    (pointTransportPrimeUnits D l hl) K hK).2

variable (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

/-- The existing sections isomorphism phi, with the intrinsic constructibility predicate converted
by pointIntegralConstructible_iff. Its definition is exactly the inverse of Gamma(chi) after
theta.

Source: Deligne, Weil II, (1.1.3) and (1.1.7), pp. 150--151 (context); the explicit pro-etale
completed-coefficient calculation in the DAG is agent-written.
(blueprint: lem-weil-point-automorphism-transport-scalar-extension). -/
def pointTransportPhi
    (K : DerivedCategory (integralTowerModules l E (Spec (.of D.k))))
    (hK : sfIntegralConstructible l E (Spec (.of D.k)) K) :=
  pointSectionsScalarExtensionIso l E L ι D hl K
    ((pointIntegralConstructible_iff l E D hl K).mpr hK)

/-- The specified beta packaged as an isomorphism: chi at G_E K inverse, then the existing derived
tensor comparison b, then G_L applied to chi at K. Its hom is definitionally
isomorphismComparisonScalarBeta. The scalarCompletion comparison is identified with the recorded
universal chi by isomorphismScalarModel_existsUnique.

Source: Deligne, Weil II, (1.1.3) and (1.1.7), pp. 150--151 (context); the explicit pro-etale
completed-coefficient calculation in the DAG is agent-written.
(blueprint: lem-weil-point-automorphism-transport-scalar-extension). -/
def pointTransportBetaIso
    (K : DerivedCategory (integralTowerModules l E (Spec (.of D.k))))
    (hK : sfIntegralConstructible l E (Spec (.of D.k)) K) :=
  (scalarCompletionIso l E L ι (Spec (.of D.k)) _
    (pointTransportInverseConstructible D l hl E g K hK).1).symm ≪≫
    (isomorphismScalarTensorDerived l E L ι g).app K ≪≫
    (inverseImageIntegralDerived l L g).mapIso
      (scalarCompletionIso l E L ι (Spec (.of D.k)) K hK.1)

/-- The specified completed pullback/scalar isomorphism alpha. It is precisely
scalarPullbackCompleted; its hom is definitionally isomorphismComparisonScalarAlpha. The
admissibility input comes from the recorded isomorphism-derived-pullback assertion.

Source: Deligne, Weil II, (1.1.3) and (1.1.7), pp. 150--151 (context); the explicit pro-etale
completed-coefficient calculation in the DAG is agent-written.
(blueprint: lem-weil-point-automorphism-transport-scalar-extension). -/
def pointTransportAlphaIso
    (K : DerivedCategory (integralTowerModules l E (Spec (.of D.k))))
    (hK : sfIntegralConstructible l E (Spec (.of D.k)) K) :=
  scalarPullbackCompleted l E L ι g K hK.1
    (pointTransportPullbackConstructible D l hl E g K hK).1

private theorem transportKappa_natural
    {K J : DerivedCategory (integralTowerModules l E (Spec (.of D.k)))} (f : K ⟶ J) :
    (inverseImageIntegralDerived l E g).map f ≫ pointTransportKappa D l hl E g J =
      pointTransportKappa D l hl E g K ≫ (integralDerivedPullback l E g).map f := by
  obtain ⟨κ, hk, _, _, _⟩ := inverseImagePullbackComparisonIntegral_natural.{u, u, 0, 0}
    l E g (pointTransportPrimeUnits D l hl) (pointTransportPrimeUnits D l hl)
  simpa only [hk, pointTransportKappa] using κ.naturality f

private theorem transportKappa_isIso
    (K : DerivedCategory (integralTowerModules l E (Spec (.of D.k))))
    (hK : sfIntegralConstructible l E (Spec (.of D.k)) K) :
    IsIso (pointTransportKappa D l hl E g K) := by
  obtain ⟨S, hS⟩ := coefficientDerivedSystemEvaluationCalculus l E (Spec (.of D.k))
  obtain ⟨R, _⟩ := integralPullbackComparisonRealization l E E (AlgHom.id ℚ_[l] E)
  let T := (R.coefficient E).system (Spec (.of D.k))
  let := (R.coefficient E).complete (Spec (.of D.k)) ⟨K, hK⟩
  have hu : IsIso (S.adjunction.unit.app K) := by
    have h := T.adjunction.unit_leftAdjointUniq_hom_app S.adjunction K
    rw [← h]
    infer_instance
  let := hu
  obtain ⟨κ, hk, _, hn, _⟩ := inverseImagePullbackComparisonIntegral_natural.{u, u, 0, 0}
    l E g (pointTransportPrimeUnits D l hl) (pointTransportPrimeUnits D l hl)
  obtain ⟨θ, hθ⟩ := hn S hS
  change IsIso (inverseImagePullbackComparisonDerived l E g _ _ K)
  rw [← hk K, hθ K]
  infer_instance

private theorem transport_natural
    {K J : DerivedCategory (integralTowerModules l E (Spec (.of D.k)))} (f : K ⟶ J) :
    (pointCompletedDerivedSections D.k l E).map f ≫ pointTransport D l hl E g J =
      pointTransport D l hl E g K ≫ (pointCompletedDerivedSections D.k l E).map
        ((integralDerivedPullback l E g).map f) := by
  have hn := (pointAutomorphismRestrictionDerived D l hl E g).naturality f
  dsimp only [Functor.comp_map] at hn
  simp only [pointTransport, ← Category.assoc]
  rw [hn]
  simp only [Category.assoc, ← Functor.map_comp]
  rw [transportKappa_natural]

private theorem transportRestrictionModules_isIso
    (F : integralTowerModules l E (Spec (.of D.k))) :
    IsIso ((pointAutomorphismRestrictionModules D l hl E g).app F) := by
  let r := pointRestrictionArrow g
  have : IsIso r := by
    let e : (Scheme.proEtaleIsoPostcompose g).obj (Scheme.ProEt.mk (𝟙 _)) ≅
        Scheme.ProEt.mk (𝟙 (Spec (.of D.k))) :=
      MorphismProperty.Over.isoMk (asIso g)
    change IsIso e.hom
    infer_instance
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  have h := ConcreteCategory.bijective_of_isIso (F.val.presheaf.map r.op)
  have he : ⇑((pointAutomorphismRestrictionModules D l hl E g).app F) =
      ⇑(F.val.presheaf.map r.op) := by
    funext x
    exact (point_automorphism_restriction_natural l E D hl g none).2.2.choose_spec.1 F x
  rw [he]
  exact h

private def transportRestrictionIso :
    pointCompletedSections D.k l E ≅
      inverseImageIntegralModules l E g ⋙ pointCompletedSections D.k l E := by
  letI : ∀ F, IsIso ((pointAutomorphismRestrictionModules D l hl E g).app F) :=
    transportRestrictionModules_isIso D l hl E g
  let := NatIso.isIso_of_isIso_app (pointAutomorphismRestrictionModules D l hl E g)
  exact asIso (pointAutomorphismRestrictionModules D l hl E g)

private theorem transportRestrictionIso_hom :
    (transportRestrictionIso D l hl E g).hom =
      pointAutomorphismRestrictionModules D l hl E g := rfl

private theorem transportRestrictionDerived_eq :
    pointAutomorphismRestrictionDerived D l hl E g =
      (Functor.mapDerivedCategoryNatIso (transportRestrictionIso D l hl E g)).hom ≫
        (Functor.mapDerivedCategoryCompIso (inverseImageIntegralModules l E g)
          (pointCompletedSections D.k l E)).hom := by
  rfl

private theorem transportRestrictionDerived_isIso :
    IsIso (pointAutomorphismRestrictionDerived D l hl E g) := by
  rw [transportRestrictionDerived_eq]
  infer_instance

attribute [local irreducible] pointAutomorphismRestrictionDerived transportRestrictionIso

private def transportExactSectionsTensor :
    pointCompletedSections D.k l E ⋙ pointIntegralModuleTensor l E L ι ≅
      integralOrdinaryScalar l E L ι (Spec (.of D.k)) ⋙ pointCompletedSections D.k l L :=
  pointSectionsTensor D.k l E L ι ≪≫
    Functor.isoWhiskerRight (isomorphismScalarSheafModel l E L ι (Spec (.of D.k))).symm
      (pointCompletedSections D.k l L)

private theorem transportExactSectionsTensor_one
    (F : integralTowerModules l E (Spec (.of D.k)))
    (x : (pointCompletedSections D.k l E).obj F) :
    (transportExactSectionsTensor D l E L ι).hom.app F
        ((1 : Padic.coefficientExtensionIntegers l L) ⊗ₜ[_,
          integralScalarIntegerInclusion l E L ι] x) =
      integralOrdinaryTensorSection l E L ι (Spec (.of D.k)) F
        (op (Scheme.ProEt.mk (𝟙 _))) 1 x := by
  have h := (isomorphismScalarSheafModel_existsUnique l E L ι
    (Spec (.of D.k))).exists.choose_spec F (op (Scheme.ProEt.mk (𝟙 _))) 1 x
  dsimp only [transportExactSectionsTensor, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Iso.symm_hom]
  change ((isomorphismScalarSheafModel l E L ι (Spec (.of D.k))).inv.app F).val.app _
    ((pointSectionsTensor D.k l E L ι).hom.app F _) = _
  erw [(pointSectionsTensor_existsUnique D.k l E L ι).exists.choose_spec]
  rw [map_one, ← h]
  exact ConcreteCategory.congr_hom (congrArg (fun f ↦ f.val.app
    (op (Scheme.ProEt.mk (𝟙 (Spec (.of D.k))))))
    ((isomorphismScalarSheafModel l E L ι (Spec (.of D.k))).hom_inv_id_app F)) _

private theorem transportRestrictionModules_apply
    (F : integralTowerModules l E (Spec (.of D.k)))
    (x : (pointCompletedSections D.k l E).obj F) :
    (pointAutomorphismRestrictionModules D l hl E g).app F x =
      pointRestrictionRaw l E g none F x := by
  exact (point_automorphism_restriction_natural l E D hl g none).2.2.choose_spec.1 F x

private theorem transportOrdinaryRestrictionSquare
    (F : integralTowerModules l E (Spec (.of D.k))) :
    (pointIntegralModuleTensor l E L ι).map
        ((pointAutomorphismRestrictionModules D l hl E g).app F) ≫
      (transportExactSectionsTensor D l E L ι).hom.app
        ((inverseImageIntegralModules l E g).obj F) ≫
      (pointCompletedSections D.k l L).map ((isomorphismScalarTensor l E L ι g).hom.app F) =
    (transportExactSectionsTensor D l E L ι).hom.app F ≫
      (pointAutomorphismRestrictionModules D l hl L g).app
        ((integralOrdinaryScalar l E L ι (Spec (.of D.k))).obj F) := by
  apply ((ModuleCat.extendRestrictScalarsAdj.{u + 1, u, u}
    (integralScalarIntegerInclusion l E L ι)).homEquiv _ _).injective
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change ((isomorphismScalarTensor l E L ι g).hom.app F).val.app _
    ((transportExactSectionsTensor D l E L ι).hom.app _
      ((1 : Padic.coefficientExtensionIntegers l L) ⊗ₜ[_,
        integralScalarIntegerInclusion l E L ι]
        ((pointAutomorphismRestrictionModules D l hl E g).app F x))) =
    (pointAutomorphismRestrictionModules D l hl L g).app _
      ((transportExactSectionsTensor D l E L ι).hom.app F
        ((1 : Padic.coefficientExtensionIntegers l L) ⊗ₜ[_,
          integralScalarIntegerInclusion l E L ι] x))
  rw [transportExactSectionsTensor_one, transportExactSectionsTensor_one,
    transportRestrictionModules_apply, transportRestrictionModules_apply]
  have h := (isomorphismScalarTensor_existsUnique l E L ι g).exists.choose_spec
    F (Scheme.ProEt.mk (𝟙 _)) (pointRestrictionRaw l E g none F x) 1
  rw [map_one] at h
  exact h.trans (ordinaryTensorSection_restrict l E L ι
    (Spec (.of D.k)) F (pointRestrictionArrow g).op x).symm

private theorem deriveRestrictionSquare
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    [HasDerivedCategory D]
    (G : A ⥤ A) (H : B ⥤ B) (S : A ⥤ C) (U : B ⥤ D)
    (T : A ⥤ B) (V : C ⥤ D)
    [G.Additive] [H.Additive] [S.Additive] [U.Additive] [T.Additive] [V.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (σ : S ≅ G ⋙ S) (τ : U ≅ H ⋙ U) (θ : S ⋙ V ≅ T ⋙ U)
    (b : G ⋙ T ≅ T ⋙ H)
    (h : Functor.isoWhiskerRight σ V ≪≫ Functor.isoWhiskerLeft G θ ≪≫
      Functor.isoWhiskerRight b U = θ ≪≫ Functor.isoWhiskerLeft T τ)
    (K : DerivedCategory A) :
    V.mapDerivedCategory.map
        ((Functor.mapDerivedCategoryNatIso σ).hom.app K ≫
          (Functor.mapDerivedCategoryCompIso G S).hom.app K) ≫
      (Functor.mapDerivedCategorySquareIso θ).hom.app (G.mapDerivedCategory.obj K) ≫
      U.mapDerivedCategory.map ((Functor.mapDerivedCategorySquareIso b).hom.app K) =
    (Functor.mapDerivedCategorySquareIso θ).hom.app K ≫
      (Functor.mapDerivedCategoryNatIso τ).hom.app (T.mapDerivedCategory.obj K) ≫
      (Functor.mapDerivedCategoryCompIso H U).hom.app (T.mapDerivedCategory.obj K) := by
  have hm := congrArg (fun e ↦ (Functor.mapDerivedCategoryNatIso e).hom) h
  simp only [Functor.mapDerivedCategoryNatIso_trans] at hm
  have hσ := Functor.mapDerivedCategoryNatIso_isoWhiskerRight σ V
  have hθ := Functor.mapDerivedCategoryNatIso_isoWhiskerLeft G θ
  have hb := Functor.mapDerivedCategoryNatIso_isoWhiskerRight b U
  have hτ := Functor.mapDerivedCategoryNatIso_isoWhiskerLeft T τ
  have hGS := Functor.mapDerivedCategoryCompIso_assoc G S V
  have hGT := Functor.mapDerivedCategoryCompIso_assoc G T U
  have hTH := Functor.mapDerivedCategoryCompIso_assoc T H U
  have he :
      Functor.whiskerRight
          ((Functor.mapDerivedCategoryNatIso σ).hom ≫
            (Functor.mapDerivedCategoryCompIso G S).hom) V.mapDerivedCategory ≫
        Functor.whiskerLeft G.mapDerivedCategory
          (Functor.mapDerivedCategorySquareIso θ).hom ≫
        Functor.whiskerRight (Functor.mapDerivedCategorySquareIso b).hom
          U.mapDerivedCategory =
      (Functor.mapDerivedCategorySquareIso θ).hom ≫
        Functor.whiskerLeft T.mapDerivedCategory
          ((Functor.mapDerivedCategoryNatIso τ).hom ≫
            (Functor.mapDerivedCategoryCompIso H U).hom) := by
    apply (cancel_epi (Functor.mapDerivedCategoryCompIso S V).hom).mp
    simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
      Functor.whiskerRight_comp, Functor.whiskerLeft_comp, Category.assoc]
    rw [← reassoc_of% hσ, ← reassoc_of% hGS]
    simp only [← Functor.whiskerLeft_comp_assoc, Iso.hom_inv_id_assoc]
    simp only [Functor.whiskerLeft_comp, Category.assoc]
    rw [← reassoc_of% hθ, reassoc_of% hGT]
    simp only [← Functor.whiskerRight_comp_assoc, Iso.hom_inv_id_assoc]
    rw [← reassoc_of% hb, ← hTH]
    rw [reassoc_of% hm, reassoc_of% hτ]
  exact congr_app he K

private theorem transportScalarTensorDerived_eq :
    isomorphismScalarTensorDerived l E L ι g =
      Functor.mapDerivedCategorySquareIso (isomorphismScalarTensor l E L ι g) := rfl

attribute [local irreducible] isomorphismScalarTensorDerived
  Functor.mapDerivedCategoryNatIso

private theorem transportExactRestrictionSquare
    (K : DerivedCategory (integralTowerModules l E (Spec (.of D.k)))) :
    (pointIntegralModuleDerivedTensor l E L ι).map
        ((pointAutomorphismRestrictionDerived D l hl E g).app K) ≫
      (Functor.mapDerivedCategorySquareIso
        (transportExactSectionsTensor D l E L ι)).hom.app
          ((inverseImageIntegralDerived l E g).obj K) ≫
      (pointCompletedDerivedSections D.k l L).map
        ((isomorphismScalarTensorDerived l E L ι g).hom.app K) =
    (Functor.mapDerivedCategorySquareIso (transportExactSectionsTensor D l E L ι)).hom.app K ≫
      (pointAutomorphismRestrictionDerived D l hl L g).app
        ((integralOrdinaryDerivedScalar l E L ι (Spec (.of D.k))).obj K) := by
  rw [transportRestrictionDerived_eq D l hl E g,
    transportRestrictionDerived_eq D l hl L g, transportScalarTensorDerived_eq]
  simp only [NatTrans.comp_app]
  apply deriveRestrictionSquare
    (inverseImageIntegralModules l E g) (inverseImageIntegralModules l L g)
    (pointCompletedSections D.k l E) (pointCompletedSections D.k l L)
    (integralOrdinaryScalar l E L ι (Spec (.of D.k))) (pointIntegralModuleTensor l E L ι)
    (transportRestrictionIso D l hl E g) (transportRestrictionIso D l hl L g)
    (transportExactSectionsTensor D l E L ι) (isomorphismScalarTensor l E L ι g) _ K
  apply Iso.ext
  simp only [Iso.trans_hom, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    transportRestrictionIso_hom]
  apply NatTrans.ext
  funext F
  exact transportOrdinaryRestrictionSquare D l hl E g L ι F

private theorem transportScalarModel_exact :
    (isomorphismScalarModel_existsUnique l E L ι (Spec (.of D.k))).exists.choose ≪≫
        pointOrdinaryDerivedComparison D.k l E L ι =
      Functor.mapDerivedCategoryNatIso
        (isomorphismScalarSheafModel l E L ι (Spec (.of D.k))) := by
  apply Iso.ext
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso _ (.up ℤ))
  intro P
  apply (cancel_mono ((completedOrdinaryScalarExtension l E L ι
    (Spec (.of D.k))).mapDerivedCategoryFactors.hom.app P)).mp
  dsimp only [Iso.trans_hom, NatTrans.comp_app]
  rw [Category.assoc,
    show (pointOrdinaryDerivedComparison D.k l E L ι).hom.app _ ≫ _ = _ from
      (pointOrdinaryDerivedComparison_existsUnique D.k l E L ι).exists.choose_spec P]
  exact ((isomorphismScalarModel_existsUnique l E L ι
    (Spec (.of D.k))).exists.choose_spec.1 P).trans
      (Functor.mapDerivedCategoryNatIso_fac
        (isomorphismScalarSheafModel l E L ι (Spec (.of D.k))) P).symm

private theorem transportExactTensor_normalization
    (K : DerivedCategory (integralTowerModules l E (Spec (.of D.k)))) :
    (Functor.mapDerivedCategorySquareIso (transportExactSectionsTensor D l E L ι)).hom.app K ≫
      (pointCompletedDerivedSections D.k l L).map
        ((Functor.mapDerivedCategoryNatIso
          (isomorphismScalarSheafModel l E L ι (Spec (.of D.k)))).hom.app K) =
    (Functor.mapDerivedCategorySquareIso (pointSectionsTensor D.k l E L ι)).hom.app K := by
  have hw := congr_app (Functor.mapDerivedCategoryNatIso_isoWhiskerRight
    (isomorphismScalarSheafModel l E L ι (Spec (.of D.k))).symm
    (pointCompletedSections D.k l L)) K
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app] at hw
  simp only [transportExactSectionsTensor, Functor.mapDerivedCategorySquareIso,
    Functor.mapDerivedCategoryNatIso_trans, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Category.assoc]
  rw [reassoc_of% hw]
  rw [Functor.mapDerivedCategoryNatIso_symm]
  simp only [← Functor.map_comp, Iso.inv_hom_id_app]
  simp only [CategoryTheory.Functor.map_id, Category.comp_id]

private theorem transportPhi_inv_exact
    (K : DerivedCategory (integralTowerModules l E (Spec (.of D.k))))
    (hK : sfIntegralConstructible l E (Spec (.of D.k)) K) :
    (pointTransportPhi D l hl E L ι K hK).inv =
      (Functor.mapDerivedCategorySquareIso (transportExactSectionsTensor D l E L ι)).hom.app K ≫
        (pointCompletedDerivedSections D.k l L).map
          ((scalarCompletion l E L ι (Spec (.of D.k))).app K) := by
  have hm := congrArg (fun e ↦ e.hom.app K) (transportScalarModel_exact D l E L ι)
  dsimp only [Iso.trans_hom, NatTrans.comp_app] at hm
  have hc := congr_app (isomorphismScalarModel_existsUnique l E L ι
    (Spec (.of D.k))).exists.choose_spec.2 K
  dsimp only [NatTrans.comp_app] at hc
  have ht := transportExactTensor_normalization D l E L ι K
  have he :
      (Functor.mapDerivedCategorySquareIso (transportExactSectionsTensor D l E L ι)).hom.app K ≫
        (pointCompletedDerivedSections D.k l L).map
          ((isomorphismScalarModel_existsUnique l E L ι
            (Spec (.of D.k))).exists.choose.hom.app K) =
      (pointDerivedSectionsTensor D.k l E L ι).hom.app K := by
    apply (cancel_mono ((pointCompletedDerivedSections D.k l L).map
      ((pointOrdinaryDerivedComparison D.k l E L ι).hom.app K))).mp
    simp only [Category.assoc, ← Functor.map_comp, hm]
    simp only [pointDerivedSectionsTensor, Iso.trans_hom, Iso.symm_hom,
      NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
      Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
    simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
      NatTrans.comp_app, Category.assoc] at ht
    exact ht.trans (congrArg (fun f ↦
      (Functor.mapDerivedCategoryCompIso (pointCompletedSections D.k l E)
        (pointIntegralModuleTensor l E L ι)).inv.app K ≫
      (Functor.mapDerivedCategoryNatIso (pointSectionsTensor D.k l E L ι)).hom.app K ≫ f)
      (Category.comp_id ((Functor.mapDerivedCategoryCompIso
        (completedOrdinaryScalarExtension l E L ι (Spec (.of D.k)))
        (pointCompletedSections D.k l L)).hom.app K)).symm)
  simp only [pointTransportPhi, pointSectionsScalarExtensionIso, Iso.symm_inv,
    Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom]
  rw [← he]
  simp only [Category.assoc, ← Functor.map_comp]
  exact congrArg (fun f ↦
    (Functor.mapDerivedCategorySquareIso (transportExactSectionsTensor D l E L ι)).hom.app K ≫
      (pointCompletedDerivedSections D.k l L).map f) hc

/-- The comparison psi = phi at G_E K after Gamma(beta inverse), using only the named canonical
maps.

Source: Deligne, Weil II, (1.1.3) and (1.1.7), pp. 150--151 (context); the explicit pro-etale
completed-coefficient calculation in the DAG is agent-written.
(blueprint: lem-weil-point-automorphism-transport-scalar-extension). -/
def pointTransportPsi
    (K : DerivedCategory (integralTowerModules l E (Spec (.of D.k))))
    (hK : sfIntegralConstructible l E (Spec (.of D.k)) K) :=
  (pointCompletedDerivedSections D.k l L).map (pointTransportBetaIso D l hl E g L ι K hK).inv ≫
    (pointTransportPhi D l hl E L ι _
      (pointTransportInverseConstructible D l hl E g K hK)).hom

private theorem transportInverseSquare
    (K : DerivedCategory (integralTowerModules l E (Spec (.of D.k))))
    (hK : sfIntegralConstructible l E (Spec (.of D.k)) K) :
    (pointAutomorphismRestrictionDerived D l hl L g).app
        ((integralScalarExtension l E L ι (Spec (.of D.k))).obj K) ≫
        pointTransportPsi D l hl E g L ι K hK =
      (pointTransportPhi D l hl E L ι K hK).hom ≫
        (pointIntegralModuleDerivedTensor l E L ι).map
          ((pointAutomorphismRestrictionDerived D l hl E g).app K) := by
  let S := pointCompletedDerivedSections D.k l L
  let η := Functor.mapDerivedCategorySquareIso (transportExactSectionsTensor D l E L ι)
  let χ := scalarCompletion l E L ι (Spec (.of D.k))
  have h := transportExactRestrictionSquare D l hl E g L ι K
  have hn := (pointAutomorphismRestrictionDerived D l hl L g).naturality (χ.app K)
  dsimp only [Functor.comp_map] at hn
  have hb :
      (pointTransportPhi D l hl E L ι _
        (pointTransportInverseConstructible D l hl E g K hK)).inv ≫
          S.map (pointTransportBetaIso D l hl E g L ι K hK).hom =
        η.hom.app ((inverseImageIntegralDerived l E g).obj K) ≫
          S.map ((isomorphismScalarTensorDerived l E L ι g).hom.app K) ≫
          S.map ((inverseImageIntegralDerived l L g).map (χ.app K)) := by
    rw [transportPhi_inv_exact]
    simp only [pointTransportBetaIso, Iso.trans_hom, Iso.symm_hom,
      Iso.app_hom, Functor.mapIso_hom, S, CategoryTheory.Functor.map_comp,
      Category.assoc]
    rw [← CategoryTheory.Functor.map_comp_assoc]
    have hc : (scalarCompletion l E L ι (Spec (.of D.k))).app
          ((inverseImageIntegralDerived l E g).obj K) ≫
        (scalarCompletionIso l E L ι (Spec (.of D.k)) _
          (pointTransportInverseConstructible D l hl E g K hK).1).inv = 𝟙 _ :=
      (scalarCompletionIso l E L ι (Spec (.of D.k)) _
        (pointTransportInverseConstructible D l hl E g K hK).1).hom_inv_id
    rw [hc, CategoryTheory.Functor.map_id, Category.id_comp]
    rfl
  have hs :
      (pointIntegralModuleDerivedTensor l E L ι).map
          ((pointAutomorphismRestrictionDerived D l hl E g).app K) ≫
        (pointTransportPhi D l hl E L ι _
          (pointTransportInverseConstructible D l hl E g K hK)).inv ≫
          S.map (pointTransportBetaIso D l hl E g L ι K hK).hom =
      (pointTransportPhi D l hl E L ι K hK).inv ≫
        (pointAutomorphismRestrictionDerived D l hl L g).app
          ((integralScalarExtension l E L ι (Spec (.of D.k))).obj K) := by
    rw [hb]
    dsimp only [η, S]
    rw [reassoc_of% h, ← hn]
    rw [transportPhi_inv_exact]
    exact (Category.assoc _ _ _).symm
  apply (cancel_epi (pointTransportPhi D l hl E L ι K hK).inv).mp
  simp only [pointTransportPsi, Iso.inv_hom_id_assoc]
  rw [← reassoc_of% hs]
  rw [← CategoryTheory.Functor.map_comp_assoc]
  simp only [Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp,
    Iso.inv_hom_id, Category.comp_id]

/-- The pullback sections comparison psi prime = phi at P_E K after Gamma(alpha inverse), using the
specified scalar-operation comparison.

Source: Deligne, Weil II, (1.1.3) and (1.1.7), pp. 150--151 (context); the explicit pro-etale
completed-coefficient calculation in the DAG is agent-written.
(blueprint: lem-weil-point-automorphism-transport-scalar-extension). -/
def pointTransportPullbackPsi
    (K : DerivedCategory (integralTowerModules l E (Spec (.of D.k))))
    (hK : sfIntegralConstructible l E (Spec (.of D.k)) K) :=
  (pointCompletedDerivedSections D.k l L).map (pointTransportAlphaIso D l hl E g L ι K hK).inv ≫
    (pointTransportPhi D l hl E L ι _
      (pointTransportPullbackConstructible D l hl E g K hK)).hom


/-- The existing rational sections comparison: integral phi tensored with L and then the canonical
balanced localization map. No idempotent completion is introduced.

Source: Deligne, Weil II, (1.1.3) and (1.1.7), pp. 150--151 (context); the explicit pro-etale
completed-coefficient calculation in the DAG is agent-written.
(blueprint: lem-weil-point-automorphism-transport-scalar-extension). -/
def pointTransportRationalPhi
    (K : DerivedCategory (integralTowerModules l E (Spec (.of D.k))))
    (hK : sfIntegralConstructible l E (Spec (.of D.k)) K) :=
  pointRationalSectionsScalarExtensionIso l E L ι D hl K
    ((pointIntegralConstructible_iff l E D hl K).mpr hK)

private theorem transportPullbackSquare
    (K : DerivedCategory (integralTowerModules l E (Spec (.of D.k))))
    (hK : sfIntegralConstructible l E (Spec (.of D.k)) K) :
    pointTransport D l hl L g
        ((integralScalarExtension l E L ι (Spec (.of D.k))).obj K) ≫
        pointTransportPullbackPsi D l hl E g L ι K hK =
      (pointTransportPhi D l hl E L ι K hK).hom ≫
        (pointIntegralModuleDerivedTensor l E L ι).map (pointTransport D l hl E g K) := by
  let S := pointCompletedDerivedSections D.k l L
  let T := integralScalarExtension l E L ι (Spec (.of D.k))
  let b := pointTransportBetaIso D l hl E g L ι K hK
  let a := pointTransportAlphaIso D l hl E g L ι K hK
  have hc : T.map (pointTransportKappa D l hl E g K) ≫ a.hom =
      b.hom ≫ pointTransportKappa D l hl L g (T.obj K) := by
    exact isomorphismComparison_scalarExtension l E L ι g
      (pointTransportPrimeUnits D l hl) (pointTransportPrimeUnits D l hl) K hK
  have hi : pointTransportKappa D l hl L g (T.obj K) ≫ a.inv =
      b.inv ≫ T.map (pointTransportKappa D l hl E g K) := by
    apply (cancel_epi b.hom).mp
    rw [← Category.assoc, ← hc]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]
  have hn := pointScalarSectionsNatural l E L ι D hl
    ((inverseImageIntegralDerived l E g).obj K) ((integralDerivedPullback l E g).obj K)
    ((pointIntegralConstructible_iff l E D hl _).mpr
      (pointTransportInverseConstructible D l hl E g K hK))
    ((pointIntegralConstructible_iff l E D hl _).mpr
      (pointTransportPullbackConstructible D l hl E g K hK))
    (pointTransportKappa D l hl E g K)
  simp only [pointTransport, pointTransportPullbackPsi, Category.assoc]
  rw [← S.map_comp_assoc, hi, S.map_comp_assoc]
  change S.map (T.map (pointTransportKappa D l hl E g K)) ≫
      (pointTransportPhi D l hl E L ι _
        (pointTransportPullbackConstructible D l hl E g K hK)).hom =
    (pointTransportPhi D l hl E L ι _
      (pointTransportInverseConstructible D l hl E g K hK)).hom ≫
      (pointIntegralModuleDerivedTensor l E L ι).map
        ((pointCompletedDerivedSections D.k l E).map
          (pointTransportKappa D l hl E g K)) at hn
  rw [hn]
  have h := transportInverseSquare D l hl E g L ι K hK
  simp only [pointTransportPsi] at h
  rw [reassoc_of% h]
  simp only [CategoryTheory.Functor.map_comp]

private theorem transport_isIso
    (K : DerivedCategory (integralTowerModules l E (Spec (.of D.k))))
    (hK : sfIntegralConstructible l E (Spec (.of D.k)) K) :
    IsIso (pointTransport D l hl E g K) := by
  let := transportKappa_isIso D l hl E g K hK
  let := transportRestrictionDerived_isIso D l hl E g
  unfold pointTransport
  infer_instance

/-- Rationalize psi and apply the canonical module tensor/rationalization associator at Gamma(G_E
K).

Source: Deligne, Weil II, (1.1.3) and (1.1.7), pp. 150--151 (context); the explicit pro-etale
completed-coefficient calculation in the DAG is agent-written.
(blueprint: lem-weil-point-automorphism-transport-scalar-extension). -/
def pointTransportRationalPsi
    (K : DerivedCategory (integralTowerModules l E (Spec (.of D.k))))
    (hK : sfIntegralConstructible l E (Spec (.of D.k)) K) :=
  (pointModuleDerivedRationalization l L).map (pointTransportPsi D l hl E g L ι K hK) ≫
    (pointDerivedTensorRationalization l E L ι).hom.app
      ((pointCompletedDerivedSections D.k l E).obj ((inverseImageIntegralDerived l E g).obj K))

/-- Rationalize psi prime and apply the canonical module tensor/rationalization associator at
Gamma(P_E K). This is the pullback comparison for raw rationalization.

Source: Deligne, Weil II, (1.1.3) and (1.1.7), pp. 150--151 (context); the explicit pro-etale
completed-coefficient calculation in the DAG is agent-written.
(blueprint: lem-weil-point-automorphism-transport-scalar-extension). -/
def pointTransportRationalPullbackPsi
    (K : DerivedCategory (integralTowerModules l E (Spec (.of D.k))))
    (hK : sfIntegralConstructible l E (Spec (.of D.k)) K) :=
  (pointModuleDerivedRationalization l L).map (pointTransportPullbackPsi D l hl E g L ι K hK) ≫
    (pointDerivedTensorRationalization l E L ι).hom.app
      ((pointCompletedDerivedSections D.k l E).obj ((integralDerivedPullback l E g).obj K))

/-- Restriction and specified pullback transport commute with completed scalar extension; tensoring
the second equation gives the raw rationalized compatibility.

Source: Deligne, Weil II, (1.1.3) and (1.1.7), pp. 150--151 (context); the explicit pro-etale
completed-coefficient calculation in the DAG is agent-written.
(blueprint: lem-weil-point-automorphism-transport-scalar-extension).

Proof:
1. The isomorphism-derived-pullback theorem makes G_E K and P_E K constructible and complete.
The finite-free completed scalar comparison and the point-sections scalar comparison therefore
apply to K and both these objects. Put eta_H = Gamma(chi_H) theta_H = phi_H inverse.
2. Before completing, choose a flat-term K-flat resolution P of K. At U=(s,id), V=(s,g),
restriction sigma sends x to x restricted to V. The sections-tensor map sends x tensor a to its
sheafified pure tensor. The local formula for b sends the transported tensor to precisely that
same restricted tensor. Constant coefficients obey sigma(a)=c inverse(a), which is exactly the
transported coefficient action. Pure tensors generate, so the two maps agree in every degree,
commute with differentials, and descend through exact sections and ordinary finite-free tensor.
The K-flat tensor-model lemma identifies the resulting map with b_K.
3. Apply derived naturality of sigma at coefficient L to chi_K, including its possibly
nonconstructible source. Substitute beta = G(chi) b chi_G inverse. This gives Gamma(beta) eta_G
(sigma_E tensor 1) = sigma_L eta_K. Cancel the two invertible comparisons to obtain the first
integral equation.
4. The specified-comparison theorem gives alpha T(kappa_E) = kappa_L beta. Apply sections,
invert alpha and beta, and use naturality of phi at the derived morphism kappa_E between the two
admissible objects. The first equation then gives the second integral equation. No naturality of
t is used.
5. For identity and towers, the ordinary b unit and associator identities hold on local iterated
tensors: both composites send ((y tensor a) tensor b) to g inverse of (x tensor a_0 b_0).
Balancing, sheafification and localization give the ordinary identities.
6. Conjugate these identities by chi to obtain beta coherence; move chi past b by naturality and
cancel adjacent chi inverse/chi. The sections associator identity for phi then yields the psi
unit and tower identities. Repeat with the specified alpha tower identity and naturality of phi
at alpha to obtain the psi prime identities. The completed associator is exactly the
chi-conjugated ordinary associator.
7. Apply tensor with L to the second integral equation. The recorded coefficient-complex
rationalization comparison identifies the two tensor orders by the balanced multiplication map,
including fractions. Exactness gives the displayed rational equation. Its unit and mixed
integral/field tower identities transport the coherence equations to raw rationalization, which
retains integral objects and tensors morphisms with the fraction field. -/
theorem point_automorphism_transport_scalar_extension
    (K : DerivedCategory (integralTowerModules l E (Spec (.of D.k))))
    (hK : sfIntegralConstructible l E (Spec (.of D.k)) K) :
    ((pointAutomorphismRestrictionDerived D l hl L g).app
        ((integralScalarExtension l E L ι (Spec (.of D.k))).obj K) ≫
        pointTransportPsi D l hl E g L ι K hK =
      (pointTransportPhi D l hl E L ι K hK).hom ≫
        (pointIntegralModuleDerivedTensor l E L ι).map
          ((pointAutomorphismRestrictionDerived D l hl E g).app K)) ∧
    (pointTransport D l hl L g
        ((integralScalarExtension l E L ι (Spec (.of D.k))).obj K) ≫
        pointTransportPullbackPsi D l hl E g L ι K hK =
      (pointTransportPhi D l hl E L ι K hK).hom ≫
        (pointIntegralModuleDerivedTensor l E L ι).map (pointTransport D l hl E g K)) ∧
    ((pointModuleDerivedRationalization l L).map
        (pointTransport D l hl L g
          ((integralScalarExtension l E L ι (Spec (.of D.k))).obj K)) ≫
        pointTransportRationalPullbackPsi D l hl E g L ι K hK =
      (pointTransportRationalPhi D l hl E L ι K hK).hom ≫
        (pointCoefficientFieldDerivedTensor l E L ι).map
          ((pointModuleDerivedRationalization l E).map (pointTransport D l hl E g K))) := by
  refine ⟨transportInverseSquare D l hl E g L ι K hK,
    transportPullbackSquare D l hl E g L ι K hK, ?_⟩
  simp only [pointTransportRationalPullbackPsi, pointTransportRationalPhi,
    pointRationalSectionsScalarExtensionIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.app_hom, Category.assoc]
  rw [← Functor.map_comp_assoc, transportPullbackSquare, Functor.map_comp_assoc]
  exact congrArg (fun f ↦
    (pointModuleDerivedRationalization l L).map (pointTransportPhi D l hl E L ι K hK).hom ≫ f)
    ((pointDerivedTensorRationalization l E L ι).hom.naturality
      (pointTransport D l hl E g K))

private theorem transportUnitPasting
    {C : Type*} [Category C] (T : C ⥤ C) (a : T ≅ 𝟭 C)
    {A B X Y : C} (t : A ⟶ B) (s : X ⟶ Y) [IsIso s]
    (φ : X ⟶ T.obj A) (ψ : Y ⟶ T.obj B) (u : X ⟶ A) (v : Y ⟶ B)
    (hs : s ≫ ψ = φ ≫ T.map t) (hφ : φ ≫ a.hom.app A = u)
    (hn : u ≫ t = s ≫ v) : ψ ≫ a.hom.app B = v := by
  apply (cancel_epi s).mp
  rw [← Category.assoc, hs, Category.assoc, a.hom.naturality t,
    ← Category.assoc, hφ]
  exact hn

private theorem transportTowerPasting
    {C D E : Type*} [Category C] [Category D] [Category E]
    (T : C ⥤ D) (U : D ⥤ E) (V : C ⥤ E) (a : T ⋙ U ≅ V)
    {A B : C} {X Y : D} {Z W P Q : E}
    (t : A ⟶ B) (s : X ⟶ Y) (r : Z ⟶ W) (q : P ⟶ Q) [IsIso r]
    (φ₁ : X ⟶ T.obj A) (φ₂ : Z ⟶ U.obj X) (φ₃ : P ⟶ V.obj A)
    (ψ₁ : Y ⟶ T.obj B) (ψ₂ : W ⟶ U.obj Y) (ψ₃ : Q ⟶ V.obj B)
    (b : Z ⟶ P) (c : W ⟶ Q)
    (h₁ : s ≫ ψ₁ = φ₁ ≫ T.map t)
    (h₂ : r ≫ ψ₂ = φ₂ ≫ U.map s)
    (h₃ : q ≫ ψ₃ = φ₃ ≫ V.map t)
    (hφ : b ≫ φ₃ = φ₂ ≫ U.map φ₁ ≫ a.hom.app A)
    (hn : b ≫ q = r ≫ c) :
    c ≫ ψ₃ = ψ₂ ≫ U.map ψ₁ ≫ a.hom.app B := by
  apply (cancel_epi r).mp
  simp only [← Category.assoc]
  rw [← hn, Category.assoc b q, h₃, ← Category.assoc, hφ, h₂]
  simp only [Category.assoc, ← U.map_comp]
  rw [h₁, U.map_comp, Category.assoc]
  exact congrArg (fun f ↦ φ₂ ≫ U.map φ₁ ≫ f) (a.hom.naturality t).symm

set_option linter.defProp false in
/-- Constructibility of T K, supplied by the existing intrinsic scalar-extension preservation
theorem. This allows the second extension in every coefficient tower.

Source: Deligne, Weil II, (1.1.3) and (1.1.7), pp. 150--151 (context); the explicit pro-etale
completed-coefficient calculation in the DAG is agent-written.
(blueprint: lem-weil-point-automorphism-transport-scalar-extension). -/
def pointTransportScalarConstructible
    (K : DerivedCategory (integralTowerModules l E (Spec (.of D.k))))
    (hK : sfIntegralConstructible l E (Spec (.of D.k)) K) :=
  sfIntegralScalarExtension_constructible D.p l hl E L ι (Spec (.of D.k)) K hK

/-- The canonical completed identity-extension isomorphism already specified by the sections
comparison: invert chi and use ordinary tensor multiplication.

Source: Deligne, Weil II, (1.1.3) and (1.1.7), pp. 150--151 (context); the explicit pro-etale
completed-coefficient calculation in the DAG is agent-written.
(blueprint: lem-weil-point-automorphism-transport-scalar-extension). -/
def pointTransportScalarUnit
    (K : DerivedCategory (integralTowerModules l E (Spec (.of D.k))))
    (hK : sfIntegralConstructible l E (Spec (.of D.k)) K) :=
  pointIntegralScalarUnit l E D hl K ((pointIntegralConstructible_iff l E D hl K).mpr hK)

variable (M : Type u) [Field M] [Algebra ℚ_[l] M] [FiniteDimensional ℚ_[l] M]
  (j : L →ₐ[ℚ_[l]] M)

/-- The canonical completed coefficient-tower associator already specified by the sections
comparison: conjugate the ordinary derived tensor associator by the prescribed completion
comparisons.

Source: Deligne, Weil II, (1.1.3) and (1.1.7), pp. 150--151 (context); the explicit pro-etale
completed-coefficient calculation in the DAG is agent-written.
(blueprint: lem-weil-point-automorphism-transport-scalar-extension). -/
def pointTransportScalarAssoc
    (K : DerivedCategory (integralTowerModules l E (Spec (.of D.k))))
    (hK : sfIntegralConstructible l E (Spec (.of D.k)) K) :=
  pointIntegralScalarAssoc l E L ι M j D hl K
    ((pointIntegralConstructible_iff l E D hl K).mpr hK)

/-- Both transport comparisons respect the canonical identity coefficient extension, integrally and
after raw rationalization.

Source: Deligne, Weil II, (1.1.3) and (1.1.7), pp. 150--151 (context); the explicit pro-etale
completed-coefficient calculation in the DAG is agent-written.
(blueprint: lem-weil-point-automorphism-transport-scalar-extension).

Proof:
1. The ordinary tensor multiplication identifies the identity extension with the identity
functor. The ordinary b unit formula is multiplication on pure tensors.
2. Conjugate by the specified completion comparison chi. The identity comparison becomes
pointTransportScalarUnit, exactly the unit from the point-sections scalar-comparison lemma. For
alpha use the scalar-operation identity clause with that same completed unit.
3. Insert the unit identity for phi into psi = phi_G Gamma(beta inverse), respectively psi prime
= phi_P Gamma(alpha inverse), and cancel the completion comparisons. This gives the two integral
equalities below, with Gamma(G(unit)) and Gamma(P(unit)) as their canonical right sides.
4. Apply fraction-field tensor and the balanced localization unit identity of the
coefficient-complex rationalization comparison. Multiplication of coefficient factors, including
denominators, yields the two rational equalities. No naturality of t is used. -/
theorem point_automorphism_transport_scalar_unit
    (K : DerivedCategory (integralTowerModules l E (Spec (.of D.k))))
    (hK : sfIntegralConstructible l E (Spec (.of D.k)) K) :
    (pointTransportPsi D l hl E g E (AlgHom.id ℚ_[l] E) K hK ≫
        (pointIntegralModuleDerivedUnit l E).hom.app
          ((pointCompletedDerivedSections D.k l E).obj
            ((inverseImageIntegralDerived l E g).obj K)) =
      (pointCompletedDerivedSections D.k l E).map
        ((inverseImageIntegralDerived l E g).map (pointTransportScalarUnit D l hl E K hK).hom)) ∧
    (pointTransportPullbackPsi D l hl E g E (AlgHom.id ℚ_[l] E) K hK ≫
        (pointIntegralModuleDerivedUnit l E).hom.app
          ((pointCompletedDerivedSections D.k l E).obj
            ((integralDerivedPullback l E g).obj K)) =
      (pointCompletedDerivedSections D.k l E).map
        ((integralDerivedPullback l E g).map (pointTransportScalarUnit D l hl E K hK).hom)) ∧
    (pointTransportRationalPsi D l hl E g E (AlgHom.id ℚ_[l] E) K hK ≫
        (pointCoefficientFieldDerivedUnit l E).hom.app
          ((pointModuleDerivedRationalization l E).obj
            ((pointCompletedDerivedSections D.k l E).obj
              ((inverseImageIntegralDerived l E g).obj K))) =
      (pointModuleDerivedRationalization l E).map
        ((pointCompletedDerivedSections D.k l E).map
          ((inverseImageIntegralDerived l E g).map
            (pointTransportScalarUnit D l hl E K hK).hom))) ∧
    (pointTransportRationalPullbackPsi D l hl E g E (AlgHom.id ℚ_[l] E) K hK ≫
        (pointCoefficientFieldDerivedUnit l E).hom.app
          ((pointModuleDerivedRationalization l E).obj
            ((pointCompletedDerivedSections D.k l E).obj
              ((integralDerivedPullback l E g).obj K))) =
      (pointModuleDerivedRationalization l E).map
        ((pointCompletedDerivedSections D.k l E).map
          ((integralDerivedPullback l E g).map
            (pointTransportScalarUnit D l hl E K hK).hom))) := by
  have hs := transportInverseSquare D l hl E g E (AlgHom.id ℚ_[l] E) K hK
  have hp := transportPullbackSquare D l hl E g E (AlgHom.id ℚ_[l] E) K hK
  have hφ := pointScalarSectionsUnit l E D hl K
    ((pointIntegralConstructible_iff l E D hl K).mpr hK)
  let := transportRestrictionDerived_isIso D l hl E g
  let := transport_isIso D l hl E g
    ((integralScalarExtension l E E (AlgHom.id ℚ_[l] E) (Spec (.of D.k))).obj K)
    (pointTransportScalarConstructible D l hl E E (AlgHom.id ℚ_[l] E) K hK)
  have hσ := (pointAutomorphismRestrictionDerived D l hl E g).naturality
    (pointTransportScalarUnit D l hl E K hK).hom
  have ht := transport_natural D l hl E g (pointTransportScalarUnit D l hl E K hK).hom
  have hu := transportUnitPasting (pointIntegralModuleDerivedTensor l E E (AlgHom.id ℚ_[l] E))
    (pointIntegralModuleDerivedUnit l E) _ _ _ _ _ _ hs hφ hσ
  have hv := transportUnitPasting (pointIntegralModuleDerivedTensor l E E (AlgHom.id ℚ_[l] E))
    (pointIntegralModuleDerivedUnit l E) _ _ _ _ _ _ hp hφ ht
  refine ⟨hu, hv, ?_, ?_⟩
  · simp only [pointTransportRationalPsi, Category.assoc]
    rw [pointRationalizationUnit, ← Functor.map_comp, hu]
    rfl
  · simp only [pointTransportRationalPullbackPsi, Category.assoc]
    rw [pointRationalizationUnit, ← Functor.map_comp, hv]

/-- Both transport comparisons respect successive finite coefficient extensions under the canonical
integral and rational associators.

Source: Deligne, Weil II, (1.1.3) and (1.1.7), pp. 150--151 (context); the explicit pro-etale
completed-coefficient calculation in the DAG is agent-written.
(blueprint: lem-weil-point-automorphism-transport-scalar-extension).

Proof:
1. On a flat-term K-flat model, both ordinary inverse-image tensor tower composites agree on
every local iterated pure tensor. This is the pure-tensor formula for b and the ordinary derived
tensor associator; it descends by the tensor-model and exact localization lemmas.
2. Substitute beta = G(chi) b chi_G inverse. Naturality of b moves the middle chi comparison
past b, and the adjacent inverse comparisons cancel. The result is beta_ME A_G = G_M(A) beta_ML
T_ML(beta_LE), with precisely the chi-conjugated completed associator A in
pointIntegralScalarAssoc.
3. Insert psi = phi_G Gamma(beta inverse). The associator identity for phi and naturality of
phi_ML at beta_LE cancel T_ML(beta_LE). This gives the first integral identity below.
4. The scalar-operation comparison gives the same tower identity for alpha. Insert psi prime =
phi_P Gamma(alpha inverse), and use naturality of phi_ML at alpha_LE and the same sections
associator identity. This gives the second integral identity, without assuming naturality of t.
5. Tensor these equalities with M and use the mixed integral/field tower identity of the
balanced rationalization comparison. Both routes multiply the coefficient factors in the same
order, including fractions. This gives the two rational tower equations with the existing
coefficient-field derived associator. -/
theorem point_automorphism_transport_scalar_tower
    (K : DerivedCategory (integralTowerModules l E (Spec (.of D.k))))
    (hK : sfIntegralConstructible l E (Spec (.of D.k)) K) :
    ((pointCompletedDerivedSections D.k l M).map
        ((inverseImageIntegralDerived l M g).map
          (pointTransportScalarAssoc D l hl E L ι M j K hK).hom) ≫
        pointTransportPsi D l hl E g M (j.comp ι) K hK =
      pointTransportPsi D l hl L g M j _
          (pointTransportScalarConstructible D l hl E L ι K hK) ≫
        (pointIntegralModuleDerivedTensor l L M j).map
          (pointTransportPsi D l hl E g L ι K hK) ≫
        (pointIntegralModuleDerivedAssoc l E L ι M j).hom.app
          ((pointCompletedDerivedSections D.k l E).obj
            ((inverseImageIntegralDerived l E g).obj K))) ∧
    ((pointCompletedDerivedSections D.k l M).map
        ((integralDerivedPullback l M g).map
          (pointTransportScalarAssoc D l hl E L ι M j K hK).hom) ≫
        pointTransportPullbackPsi D l hl E g M (j.comp ι) K hK =
      pointTransportPullbackPsi D l hl L g M j _
          (pointTransportScalarConstructible D l hl E L ι K hK) ≫
        (pointIntegralModuleDerivedTensor l L M j).map
          (pointTransportPullbackPsi D l hl E g L ι K hK) ≫
        (pointIntegralModuleDerivedAssoc l E L ι M j).hom.app
          ((pointCompletedDerivedSections D.k l E).obj
            ((integralDerivedPullback l E g).obj K))) ∧
    ((pointModuleDerivedRationalization l M).map
        ((pointCompletedDerivedSections D.k l M).map
          ((inverseImageIntegralDerived l M g).map
            (pointTransportScalarAssoc D l hl E L ι M j K hK).hom)) ≫
        pointTransportRationalPsi D l hl E g M (j.comp ι) K hK =
      pointTransportRationalPsi D l hl L g M j _
          (pointTransportScalarConstructible D l hl E L ι K hK) ≫
        (pointCoefficientFieldDerivedTensor l L M j).map
          (pointTransportRationalPsi D l hl E g L ι K hK) ≫
        (pointCoefficientFieldDerivedAssoc l E L ι M j).hom.app
          ((pointModuleDerivedRationalization l E).obj
            ((pointCompletedDerivedSections D.k l E).obj
              ((inverseImageIntegralDerived l E g).obj K)))) ∧
    ((pointModuleDerivedRationalization l M).map
        ((pointCompletedDerivedSections D.k l M).map
          ((integralDerivedPullback l M g).map
            (pointTransportScalarAssoc D l hl E L ι M j K hK).hom)) ≫
        pointTransportRationalPullbackPsi D l hl E g M (j.comp ι) K hK =
      pointTransportRationalPullbackPsi D l hl L g M j _
          (pointTransportScalarConstructible D l hl E L ι K hK) ≫
        (pointCoefficientFieldDerivedTensor l L M j).map
          (pointTransportRationalPullbackPsi D l hl E g L ι K hK) ≫
        (pointCoefficientFieldDerivedAssoc l E L ι M j).hom.app
          ((pointModuleDerivedRationalization l E).obj
            ((pointCompletedDerivedSections D.k l E).obj
              ((integralDerivedPullback l E g).obj K)))) := by
  have hK' := pointTransportScalarConstructible D l hl E L ι K hK
  let A := pointTransportScalarAssoc D l hl E L ι M j K hK
  have hφ := pointScalarSectionsTower l E L ι M j D hl K
    ((pointIntegralConstructible_iff l E D hl K).mpr hK)
  let := transportRestrictionDerived_isIso D l hl M g
  let := transport_isIso D l hl M g
    ((integralScalarExtension l L M j (Spec (.of D.k))).obj
      ((integralScalarExtension l E L ι (Spec (.of D.k))).obj K))
    (pointTransportScalarConstructible D l hl L M j _ hK')
  have hs₁ := transportInverseSquare D l hl E g L ι K hK
  have hs₂ := transportInverseSquare D l hl L g M j _ hK'
  have hs₃ := transportInverseSquare D l hl E g M (j.comp ι) K hK
  have ht₁ := transportPullbackSquare D l hl E g L ι K hK
  have ht₂ := transportPullbackSquare D l hl L g M j _ hK'
  have ht₃ := transportPullbackSquare D l hl E g M (j.comp ι) K hK
  have hσ := (pointAutomorphismRestrictionDerived D l hl M g).naturality A.hom
  have ht := transport_natural D l hl M g A.hom
  have hu := transportTowerPasting (pointIntegralModuleDerivedTensor l E L ι)
    (pointIntegralModuleDerivedTensor l L M j) (pointIntegralModuleDerivedTensor l E M (j.comp ι))
    (pointIntegralModuleDerivedAssoc l E L ι M j) _ _ _ _ _ _ _ _ _ _ _ _
    hs₁ hs₂ hs₃ hφ hσ
  have hv := transportTowerPasting (pointIntegralModuleDerivedTensor l E L ι)
    (pointIntegralModuleDerivedTensor l L M j) (pointIntegralModuleDerivedTensor l E M (j.comp ι))
    (pointIntegralModuleDerivedAssoc l E L ι M j) _ _ _ _ _ _ _ _ _ _ _ _
    ht₁ ht₂ ht₃ hφ ht
  dsimp only [Functor.comp_map] at hu
  refine ⟨hu, hv, ?_, ?_⟩
  · simp only [pointTransportRationalPsi, Category.assoc, Functor.map_comp]
    rw [← Functor.map_comp_assoc, hu]
    simp only [Functor.map_comp, Category.assoc]
    rw [pointRationalizationTower]
    have hn := (pointDerivedTensorRationalization l L M j).hom.naturality
      (pointTransportPsi D l hl E g L ι K hK)
    simp only [Functor.comp_map] at hn
    rw [reassoc_of% hn]
  · simp only [pointTransportRationalPullbackPsi, Category.assoc, Functor.map_comp]
    rw [← Functor.map_comp_assoc, hv]
    simp only [Functor.map_comp, Category.assoc]
    rw [pointRationalizationTower]
    have hn := (pointDerivedTensorRationalization l L M j).hom.naturality
      (pointTransportPullbackPsi D l hl E g L ι K hK)
    simp only [Functor.comp_map] at hn
    rw [reassoc_of% hn]

end WeilConjectures
