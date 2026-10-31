/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ReconstructedPairRefinementData
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful

/-! # Reconstructed RefinementSingleDegree

Source: blueprint sk-prop-sp-unique-adjoint, categorical proof, and
sk-thm-purity-transport Steps 2--4
(blueprint: lem-pur-reconstructed-refinement-single-degree).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
attribute [-instance] WeilConjectures.IntegralHom.derivedCategory
attribute [-instance] WeilConjectures.integralExceptionalSystemDerived
attribute [-instance] WeilConjectures.integralExceptionalLevelDerived
attribute [local instance 5000] AlgebraicGeometry.strictEtaleLevelDerived
  AlgebraicGeometry.strictEtaleSystemDerived
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
open WeilConjectures CompactSupportCondensedRealization PurIntegralSupportComparison
namespace WeilConjectures.ReconstructedPairRefinement
private theorem iso_map_eq {A B : Type*} [Category A] [Category B]
    {F G : A ⥤ B} (e : F ≅ G) {X Y : A} (f g : X ⟶ Y)
    (h : F.map f = F.map g) : G.map f = G.map g := by
  rw [← NatIso.naturality_1 e f, ← NatIso.naturality_1 e g, h]

private theorem pure_hom_ext {A : Type*} [Category A] [Abelian A]
    [HasDerivedCategory A] (r : ℤ) {X Y : DerivedCategory A}
    [X.IsGE r] [X.IsLE r] [Y.IsGE r] [Y.IsLE r]
    (f g : X ⟶ Y)
    (h : (DerivedCategory.homologyFunctor A r).map f =
      (DerivedCategory.homologyFunctor A r).map g) : f = g := by
  obtain ⟨U, ⟨i⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE X r
  obtain ⟨V, ⟨j⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE Y r
  let S := DerivedCategory.singleFunctor A r
  let H := DerivedCategory.homologyFunctor A r
  have : (S ⋙ H).Faithful := Functor.Faithful.of_iso
    (DerivedCategory.singleFunctorCompHomologyFunctorIso A r).symm
  apply (cancel_epi i.inv).1
  apply (cancel_mono j.hom).1
  obtain ⟨a, ha⟩ := S.map_surjective (i.inv ≫ f ≫ j.hom)
  obtain ⟨b, hb⟩ := S.map_surjective (i.inv ≫ g ≫ j.hom)
  simp only [Category.assoc]
  rw [← ha, ← hb]
  congr 1
  apply (S ⋙ H).map_injective
  change H.map f = H.map g at h
  simp only [Functor.comp_map, ha, hb, Functor.map_comp, h]

private theorem family_pure_hom_ext
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    {I : Type*} {B : I → Type*} [∀ n, Category (B n)] [∀ n, Abelian (B n)]
    [∀ n, HasDerivedCategory (B n)] (F : ∀ n, A ⥤ B n)
    [∀ n, (F n).Additive] [∀ n, PreservesFiniteLimits (F n)]
    [∀ n, PreservesFiniteColimits (F n)]
    (ext : ∀ {M N : A} (f g : M ⟶ N), (∀ n, (F n).map f = (F n).map g) → f = g)
    (r : ℤ) {X Y : DerivedCategory A}
    (hX : ∀ n, ((F n).mapDerivedCategory.obj X).IsGE r ∧
      ((F n).mapDerivedCategory.obj X).IsLE r)
    (hY : ∀ n, ((F n).mapDerivedCategory.obj Y).IsGE r ∧
      ((F n).mapDerivedCategory.obj Y).IsLE r)
    (f g : X ⟶ Y) (h : ∀ n, (F n).mapDerivedCategory.map f =
      (F n).mapDerivedCategory.map g) : f = g := by
  have zero (M : A) (hm : ∀ n, IsZero ((F n).obj M)) : IsZero M := by
    rw [IsZero.iff_id_eq_zero]
    apply ext
    intro n
    exact (hm n).eq_of_src _ _
  have bounds (K : DerivedCategory A)
      (hk : ∀ n, ((F n).mapDerivedCategory.obj K).IsGE r ∧
        ((F n).mapDerivedCategory.obj K).IsLE r) : K.IsGE r ∧ K.IsLE r := by
    constructor
    · apply (DerivedCategory.isGE_iff K r).2
      intro q hq
      apply zero
      intro n
      have := (hk n).1
      exact (DerivedCategory.isZero_of_isGE _ r q hq).of_iso
        (((F n).mapDerivedCategoryHomologyFunctorIso q).app K)
    · apply (DerivedCategory.isLE_iff K r).2
      intro q hq
      apply zero
      intro n
      have := (hk n).2
      exact (DerivedCategory.isZero_of_isLE _ r q hq).of_iso
        (((F n).mapDerivedCategoryHomologyFunctorIso q).app K)
  obtain ⟨_, _⟩ := bounds X hX
  obtain ⟨_, _⟩ := bounds Y hY
  apply pure_hom_ext r
  apply ext
  intro n
  exact iso_map_eq ((F n).mapDerivedCategoryHomologyFunctorIso r).symm f g
    (congrArg (DerivedCategory.homologyFunctor (B n) r).map (h n))

variable (l : ℕ) [Fact l.Prime] (E : Type u) [NormedField E]
  [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
  (C : ComparisonFamily l k)
  (X Y : CondensedERealization.Base k) (f : X.scheme ⟶ Y.scheme)
  [f.IsOver (Spec (.of k))]

/-- Detection of the supplied Brown square in one common cohomological degree.
Source: Stacks Tags 06XS and 08J5; parent proof Step 4.
Proof: exact conservative evaluations detect that both supplied systems are
concentrated in degree r. Their good-truncation maps identify them with the shifted
heart. The target is isomorphic to the first supplied system via theta, so it is
concentrated in that same degree. On the shifted heart the degree-r cohomology
functor is fully faithful. The exact evaluation comparisons carry its map to the
cohomology of each displayed evaluated map. Joint faithfulness of evaluation on
ordinary strict coefficient systems identifies these heart maps. Full faithfulness
of the shifted heart then gives the asserted equality in the derived category.
No faithfulness of evaluations on arbitrary derived morphisms is asserted.
(blueprint: lem-pur-reconstructed-refinement-single-degree). -/
theorem reconstructedRefinementSingleDegree :
    (∀ (c d : Compactification f)
    (D₁ : At l E k C X Y f c) (D₂ : At l E k C X Y f d) (w : c.Refinement d)
    (L : CondensedERealization.Integral l E Y.scheme)
    (A₁ : D₁.Supplied L) (A₂ : D₂.Supplied L) (r : ℤ)
    (s : A₂.system ≅ A₁.system),
    (∀ n : ℕ, ((D₁.transport.siteX.proEvaluation.evaluation n).obj A₁.system).IsGE r ∧
      ((D₁.transport.siteX.proEvaluation.evaluation n).obj A₁.system).IsLE r) →
    (∀ n : ℕ, ((D₁.transport.siteX.proEvaluation.evaluation n).obj A₂.system).IsGE r ∧
      ((D₁.transport.siteX.proEvaluation.evaluation n).obj A₂.system).IsLE r) →
    (∀ n : ℕ, (D₁.transport.siteX.proEvaluation.evaluation n).map
        (s.hom ≫ (D₁.pair L A₁).theta.hom) =
      (D₁.transport.siteX.proEvaluation.evaluation n).map
        ((D₂.pair L A₂).theta.hom ≫ mate D₁ D₂ w L A₁ A₂)) →
    s.hom ≫ (D₁.pair L A₁).theta.hom =
      (D₂.pair L A₂).theta.hom ≫ mate D₁ D₂ w L A₁ A₂) := by
  intro c d D₁ D₂ w L A₁ A₂ r s h₁ h₂ h
  let P := D₁.transport.siteX.proEvaluation
  let F := SheafOfModules.coefficientEvaluation
    (J := Scheme.ProEt.topology X.scheme)
    (O := integralExceptionalIntegers l E) (ell := integralExceptionalUniformizer l E)
  have lim (n : ℕ) : PreservesFiniteLimits (F n) :=
    (SheafOfModules.coefficientEvaluation_exact n).1
  have colim (n : ℕ) : PreservesFiniteColimits (F n) :=
    (SheafOfModules.coefficientEvaluation_exact n).2
  let e (n : ℕ) : P.evaluation n ≅ (F n).mapDerivedCategory :=
    Localization.liftNatIso DerivedCategory.Q
      (HomologicalComplex.quasiIso _ (.up ℤ)) _ _ _ _
      (P.evaluationFactors n ≪≫ (F n).mapDerivedCategoryFactors.symm)
  have ext {M N : SheafOfModules.CoefficientSystem
      (J := Scheme.ProEt.topology X.scheme)
      (integralExceptionalIntegers l E) (integralExceptionalUniformizer l E)}
      (a b : M ⟶ N) (hab : ∀ n, (F n).map a = (F n).map b) : a = b := by
    change SheafOfModules.CoefficientSystem.Hom
      (J := Scheme.ProEt.topology X.scheme)
      (O := integralExceptionalIntegers l E)
      (ell := integralExceptionalUniformizer l E) M N at a b
    cases a
    cases b
    congr 1
    funext n
    exact hab n
  apply family_pure_hom_ext F (fun a b hab ↦ ext a b hab) r
  · intro n
    have := (h₂ n).1
    have := (h₂ n).2
    exact ⟨DerivedCategory.TStructure.t.isGE_of_iso ((e n).app A₂.system) r,
      DerivedCategory.TStructure.t.isLE_of_iso ((e n).app A₂.system) r⟩
  · intro n
    have := (h₁ n).1
    have := (h₁ n).2
    let t := (e n).app A₁.system ≪≫
      ((F n).mapDerivedCategory.mapIso (D₁.pair L A₁).theta)
    exact ⟨DerivedCategory.TStructure.t.isGE_of_iso t r,
      DerivedCategory.TStructure.t.isLE_of_iso t r⟩
  · intro n
    exact iso_map_eq (e n) _ _ (h n)

end WeilConjectures.ReconstructedPairRefinement
