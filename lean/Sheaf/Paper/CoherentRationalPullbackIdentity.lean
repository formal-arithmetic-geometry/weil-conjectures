/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.RationalCoefficientCategoryComparison

/-! # Scalar-compatible identity maps before common-stage descent

Source: Bhatt--Scholze, Remark 6.8.15; Stacks Tag 099N.
(blueprint: lem-sf-coherent-rational-pullback-identity).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 10000
universe u v
open CategoryTheory AlgebraicGeometry TensorProduct
namespace WeilConjectures
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)
open GeneralAlgebraicallyClosedCoefficients

section Rationalization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (X : Scheme.{u}) [∀ x : X, Invertible (l : X.residueField x)]
private theorem transport_heq {C : Type*} [Category C] {A B A' B' : C}
    (hA : A = A') (hB : B = B') (f : A ⟶ B) (g : A' ⟶ B') (h : HEq f g) :
    eqToHom hA.symm ≫ f ≫ eqToHom hB = g := by
  subst A'
  subst B'
  simpa using eq_of_heq h
private theorem rationalizeUnit
    (e : constructibleIntegralPullback l E (𝟙 X) ≅ 𝟭 _) :
    ∃ c : rationalDerivedPullback l E (𝟙 X) ≅ 𝟭 _,
      ∀ K : sfRationalConstructibleCategory l E X,
        HEq (c.hom.app K)
          ((sfRationalConstructibleLocalization l E X).map (e.hom.app K.obj)) := by
  let F := rationalDerivedPullback l E (𝟙 X)
  let I := constructibleIntegralPullback l E (𝟙 X)
  let Q := sfRationalConstructibleLocalization l E X
  have hobj := (rationalDerivedPullback_existsUnique l E (𝟙 X)).exists.choose_spec.2.1
  let F' := F.copyObj (fun K ↦ Q.obj (I.obj K.obj)) (fun K ↦ eqToIso (hobj K))
  have hm (K L : sfIntegralConstructibleCategory l E X) (a : K ⟶ L)
      (c : Localization.Away (Padic.coefficientExtensionUniformizer l E)) :
      F'.map (c ⊗ₜ[Padic.coefficientExtensionIntegers l E] a : Q.obj K ⟶ Q.obj L) =
        (c ⊗ₜ[Padic.coefficientExtensionIntegers l E] I.map a) := by
    exact transport_heq (hobj (Q.obj K)) (hobj (Q.obj L)) _ _
      ((rationalDerivedPullback_existsUnique l E (𝟙 X)).exists.choose_spec.2.2 K L a c)
  let c : F' ≅ 𝟭 _ := NatIso.ofComponents (fun K ↦ Q.mapIso (e.app K.obj)) (by
    intro K L a
    have : F.Additive := (rationalDerivedPullback_existsUnique l E (𝟙 X)).exists.choose_spec.1
    have : F'.Additive := Functor.additive_of_iso (F.isoCopyObj _ _)
    induction a using TensorProduct.induction_on with
    | zero => simp
    | tmul c a =>
      rw [hm K.obj L.obj a c]
      change ScalarLocalization.composition _ _ _ _ _ _
          (1 ⊗ₜ (e.hom.app L.obj)) (c ⊗ₜ I.map a) =
        ScalarLocalization.composition _ _ _ _ _ _
          (c ⊗ₜ a) (1 ⊗ₜ (e.hom.app K.obj))
      simp only [ScalarLocalization.composition_tmul, one_mul, mul_one]
      exact congrArg (fun b ↦ c ⊗ₜ b) (e.hom.naturality a)
    | add a b ha hb =>
      change F'.map ((a : K ⟶ L) + b) ≫ _ = _
      rw [Functor.map_add, Preadditive.add_comp, Functor.map_add, Preadditive.comp_add]
      exact congrArg₂ (· + ·) ha hb)
  exact ⟨F.isoCopyObj _ _ ≪≫ c, fun K ↦ eqToHom_comp_heq _ (hobj K)⟩

private theorem map_heq {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A B A' B' : C} (hA : A = A') (hB : B = B') {f : A ⟶ B} {g : A' ⟶ B'}
    (h : HEq f g) : HEq (F.map f) (F.map g) := by
  subst A'
  subst B'
  cases h
  rfl

variable (L : Type u) [Field L] [Algebra ℚ_[l] L]
  [FiniteDimensional ℚ_[l] L] (ι : E →ₐ[ℚ_[l]] L)

private theorem rationalUnit_scalar (eE : constructibleIntegralPullback l E (𝟙 X) ≅ 𝟭 _)
    (eL : constructibleIntegralPullback l L (𝟙 X) ≅ 𝟭 _)
    (rE : rationalDerivedPullback l E (𝟙 X) ≅ 𝟭 _)
    (rL : rationalDerivedPullback l L (𝟙 X) ≅ 𝟭 _)
    (hrE : ∀ K : sfRationalConstructibleCategory l E X,
      HEq (rE.hom.app K) ((sfRationalConstructibleLocalization l E X).map
        (eE.hom.app K.obj)))
    (hrL : ∀ K : sfRationalConstructibleCategory l L X,
      HEq (rL.hom.app K) ((sfRationalConstructibleLocalization l L X).map
        (eL.hom.app K.obj)))
    (hc : ∀ K : sfIntegralConstructibleCategory l E X,
      (integralPullbackScalarComparison l E L ι (𝟙 X) K).hom ≫
          eL.hom.app ((sfConstructibleIntegralScalarExtension 0 l
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι X).obj K) =
        (sfConstructibleIntegralScalarExtension 0 l
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι X).map (eE.hom.app K))
    (K : sfRationalConstructibleCategory l E X) :
    (rationalPullbackScalarComparison l E L ι (𝟙 X)).hom.app K ≫
        rL.hom.app ((sfRationalScalarExtension l E X 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj K) =
      (sfRationalScalarExtension l E X 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).map (rE.hom.app K) := by
  obtain ⟨KI⟩ := K
  let K : sfRationalConstructibleCategory l E X := ⟨KI⟩
  let S := sfRationalScalarExtension l E X 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι
  let SI := sfConstructibleIntegralScalarExtension 0 l
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι X
  let QE := sfRationalConstructibleLocalization l E X
  let QL := sfRationalConstructibleLocalization l L X
  let IE := constructibleIntegralPullback l E (𝟙 X)
  let IL := constructibleIntegralPullback l L (𝟙 X)
  let FE := rationalDerivedPullback l E (𝟙 X)
  let FL := rationalDerivedPullback l L (𝟙 X)
  have hS := (sfRationalScalarExtension_existsUnique l E X 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).exists.choose_spec.2.1
  have hFE := (rationalDerivedPullback_existsUnique l E (𝟙 X)).exists.choose_spec.2.1
  have hFL := (rationalDerivedPullback_existsUnique l L (𝟙 X)).exists.choose_spec.2.1
  have hA : S.obj (FE.obj K) = QL.obj (SI.obj (IE.obj K.obj)) :=
    (hS (FE.obj K)).trans
      (congrArg (fun V : sfRationalConstructibleCategory l E X ↦ QL.obj (SI.obj V.obj)) (hFE K))
  have hB : FL.obj (S.obj K) = QL.obj (IL.obj (SI.obj K.obj)) :=
    (hFL (S.obj K)).trans
      (congrArg (fun V : sfRationalConstructibleCategory l L X ↦ QL.obj (IL.obj V.obj)) (hS K))
  have hC : S.obj K = QL.obj (SI.obj K.obj) := hS K
  have hα := (rationalPullbackScalarComparison_existsUnique l E L ι
    (𝟙 X)).exists.choose_spec K
  have hβ : HEq (rL.hom.app (S.obj K))
      (QL.map (eL.hom.app (SI.obj K.obj))) :=
    (hrL (S.obj K)).trans
      (congr_arg_heq (fun V ↦ QL.map (eL.hom.app V)) (congrArg ScalarLocalization.obj hC))
  have hleft := heq_comp hA hB hC hα hβ
  have hright₁ := map_heq S (hFE K) rfl (hrE K)
  have hright₂ := (sfRationalScalarExtension_existsUnique l E X 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).exists.choose_spec.2.2
      (IE.obj K.obj) K.obj (eE.hom.app K.obj) 1
  have hright : HEq (S.map (rE.hom.app K))
      (QL.map (SI.map (eE.hom.app K.obj))) := by
    apply hright₁.trans
    change HEq (S.map (1 ⊗ₜ[Padic.coefficientExtensionIntegers l E] eE.hom.app K.obj))
      (1 ⊗ₜ[Padic.coefficientExtensionIntegers l L] SI.map (eE.hom.app K.obj))
    simpa only [map_one, S, SI, IE, K, Functor.id_obj,
      sfRationalConstructibleLocalization, ScalarLocalization.localization,
      sfRationalScalarExtension] using hright₂
  apply eq_of_heq
  apply hleft.trans
  apply HEq.trans _ hright.symm
  apply heq_of_eq
  rw [← Functor.map_comp, hc K.obj]

end Rationalization

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private def integralIdentityUnit
    (l : ℕ) [Fact l.Prime] (Ω : Type v)
    [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (S : FdCoefficientComparisonSystem.{u} l Ω)
    (hs : FdComparisonSchemeCoherence l Ω S)
    (X : Scheme.{u}) [IsNoetherian X]
    [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
    [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
    (E : Index l Ω) :
    constructibleIntegralPullback l (Coefficient.{u} l Ω E) (𝟙 X) ≅ 𝟭 _ :=
  (hs.1 X E).choose

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem integralIdentityUnit_hom
    (l : ℕ) [Fact l.Prime] (Ω : Type v)
    [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (S : FdCoefficientComparisonSystem.{u} l Ω)
    (hs : FdComparisonSchemeCoherence l Ω S)
    (X : Scheme.{u}) [IsNoetherian X]
    [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
    [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
    (E : Index l Ω) (K : sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) X) :
    ((integralIdentityUnit l Ω S hs X E).hom.app K).hom =
      (integralComparisonUnit l (Coefficient.{u} l Ω E) S.realization X K).hom :=
  (hs.1 X E).choose_spec.choose_spec.1 K

attribute [local irreducible] integralIdentityUnit

set_option maxHeartbeats 400000 in
-- The coherence projections and coefficient-size transports need extra elaboration heartbeats.
/-- Identity pullback at each rational coefficient stage admits unit comparisons compatible
with the prescribed scalar comparisons.
Source: Bhatt--Scholze, Remark 6.8.15; Stacks Tag 099N
(blueprint: lem-sf-coherent-rational-pullback-identity).
Proof: take the integral natural identity isomorphisms specified by the scheme-unit
clause of hs. Rationalize their components and inverses using the recorded object
formula for rationalDerivedPullback. Its pure-tensor map formula proves naturality on
pure tensors from integral naturality. Tensor induction and additivity extend it to
every rational arrow. The scalar-scheme-unit equation of S.realization_coherent and
the comparison identification in hs give compatibility with the actual integral
scalar/pullback maps. Localize that equation, using the pure-tensor scalar-extension
formula, to obtain the rational scalar equation. Finally conjugate by the two
operationStageTransitionIso components. Naturality of the rational unit and transition
comparison cancels the conjugating maps and gives the displayed equation for the
recorded stage functor. This includes identity coefficient extensions and zero objects. -/
theorem coherentRationalPullbackIdentity
    (l : ℕ) [Fact l.Prime] (Ω : Type v)
    [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (S : FdCoefficientComparisonSystem.{u} l Ω)
    (hs : FdComparisonSchemeCoherence l Ω S)
    (X : Scheme.{u}) [IsNoetherian X]
    [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
    [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))] :
    ∃ e : ∀ E : Index l Ω,
        rationalDerivedPullback l (Coefficient.{u} l Ω E) (𝟙 X) ≅ 𝟭 _,
      ∀ (P : generalAlgebraicallyClosedConstructibleCategory l Ω X)
        (L : Index l Ω) (h : P.stage ≤ L),
        (commonStagePullbackComparison l Ω (𝟙 X) P L h).hom ≫
            (e L).hom.app (P.toStage h) =
          ((stageSystem l Ω X).T h).map ((e P.stage).hom.app P.obj) := by
  let eI (E : Index l Ω) :
      constructibleIntegralPullback l (Coefficient.{u} l Ω E) (𝟙 X) ≅ 𝟭 _ :=
    integralIdentityUnit l Ω S hs X E
  have heI (E : Index l Ω) (K : sfIntegralConstructibleCategory l
      (Coefficient.{u} l Ω E) X) :
      ((eI E).hom.app K).hom =
        (integralComparisonUnit l (Coefficient.{u} l Ω E) S.realization X K).hom :=
    integralIdentityUnit_hom l Ω S hs X E K
  choose e he using fun E : Index l Ω ↦ rationalizeUnit l (Coefficient.{u} l Ω E) X (eI E)
  refine ⟨e, ?_⟩
  intro P L h
  have hc (K : sfIntegralConstructibleCategory l (Coefficient.{u} l Ω P.stage) X) :
      (integralPullbackScalarComparison l (Coefficient.{u} l Ω P.stage)
        (Coefficient.{u} l Ω L) (coefficientInclusion l Ω P.stage L h) (𝟙 X) K).hom ≫
          (eI L).hom.app ((sfConstructibleIntegralScalarExtension 0 l
            (Nat.Prime.ne_zero (Fact.out : l.Prime))
            (Coefficient.{u} l Ω P.stage) (Coefficient.{u} l Ω L)
            (coefficientInclusion l Ω P.stage L h) X).obj K) =
        (sfConstructibleIntegralScalarExtension 0 l
          (Nat.Prime.ne_zero (Fact.out : l.Prime))
          (Coefficient.{u} l Ω P.stage) (Coefficient.{u} l Ω L)
          (coefficientInclusion l Ω P.stage L h) X).map ((eI P.stage).hom.app K) := by
    apply ObjectProperty.hom_ext
    change _ ≫ _ = (integralScalarExtension l _ _ _ X).map
      (((eI P.stage).hom.app K).hom)
    rw [heI, heI]
    have hα :
        (integralPullbackScalarComparison l (Coefficient.{u} l Ω P.stage)
          (Coefficient.{u} l Ω L) (coefficientInclusion l Ω P.stage L h) (𝟙 X) K).hom.hom =
        (integralComparisonScalar l (Coefficient.{u} l Ω P.stage)
          (Coefficient.{u} l Ω L) (coefficientInclusion l Ω P.stage L h)
          S.realization (𝟙 X) K).hom := by
      simpa only [Coefficient, Iso.refl_hom, Scheme.pbcFiniteField, Scheme.pbcFiniteFieldField,
        Scheme.pbcFiniteFieldAlgebra, Scheme.pbcFiniteFieldInclusion, coefficientInclusion]
        using hs.2.2 (Iso.refl X) P.stage L h K
    refine (congrArg (fun q ↦ q ≫ _) hα).trans ?_
    simpa only [Coefficient, Iso.refl_hom, Scheme.pbcFiniteField, Scheme.pbcFiniteFieldField,
      Scheme.pbcFiniteFieldAlgebra, Scheme.pbcFiniteFieldInclusion, coefficientInclusion,
      integralComparisonConstructibleScalar, sfConstructibleIntegralScalarExtension]
      using (S.realization_coherent P.stage L h).scalarSchemeUnit X K
  have hr := rationalUnit_scalar l (Coefficient.{u} l Ω P.stage) X
    (Coefficient.{u} l Ω L) (coefficientInclusion l Ω P.stage L h)
    (eI P.stage) (eI L) (e P.stage) (e L) (he P.stage) (he L) hc P.obj
  let t := operationStageTransitionIso l Ω X P.stage L h
  change (t.hom.app _ ≫
    (rationalPullbackScalarComparison l (Coefficient.{u} l Ω P.stage)
      (Coefficient.{u} l Ω L) (coefficientInclusion l Ω P.stage L h) (𝟙 X)).hom.app P.obj ≫
    (rationalDerivedPullback l (Coefficient.{u} l Ω L) (𝟙 X)).map (t.inv.app P.obj)) ≫
      (e L).hom.app (((stageSystem l Ω X).T h).obj P.obj) = _
  simp only [Category.assoc]
  have hn := (e L).hom.naturality (t.inv.app P.obj)
  dsimp only [Functor.id_map] at hn
  rw [hn]
  have hr' := congrArg (fun q ↦ t.hom.app _ ≫ q ≫ t.inv.app P.obj) hr
  simp only [Category.assoc] at hr'
  apply hr'.trans
  have ht := t.hom.naturality ((e P.stage).hom.app P.obj)
  have ht' := congrArg (fun q ↦ q ≫ t.inv.app P.obj) ht.symm
  simpa only [transition, Functor.id_obj, Category.assoc, Iso.hom_inv_id_app,
    Category.comp_id] using ht'

end WeilConjectures
