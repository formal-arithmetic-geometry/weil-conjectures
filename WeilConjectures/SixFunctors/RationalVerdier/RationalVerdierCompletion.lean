/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.RationalVerdier.RationalVerdierModels
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import all Mathlib.CategoryTheory.Limits.HasLimits

/-! # Normalized completion for an arbitrary ordinary tensor presentation

Source: Bhatt--Scholze Lemma 6.5.5 and blueprint thm-coef-rational-verdier, paragraph 1
(blueprint: lem-coef-rational-verdier-completion). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.Pretriangulated CategoryTheory.Pretriangulated.Opposite
open scoped TensorProduct

namespace WeilConjectures.RationalVerdier

private theorem chosen_spec {A : Sort*} {P : A → Prop}
    (h : ∃ a, P a) (a : A) (ha : a = h.choose) : P a :=
  ha.symm ▸ h.choose_spec

private theorem compose_four {C : Type*} [Category* C]
    {A B C' D E : C} (f : A ⟶ B) (g : B ⟶ C') (h : C' ⟶ D) (k : D ⟶ E)
    (r : A ⟶ C') (hr : f ≫ g = r) : f ≫ (g ≫ h) ≫ k = r ≫ h ≫ k := by
  simpa only [Category.assoc] using congrArg (fun z ↦ (z ≫ h) ≫ k) hr

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

/-- Every normalized ordinary tensor presentation admits the recorded completion map.
Source: Bhatt--Scholze Lemma 6.5.5 and blueprint thm-coef-rational-verdier, paragraph 1
(blueprint: lem-coef-rational-verdier-completion).
Proof: restrict the ordinary K-flat comparison to good complexes. The good-complex
localization is fully faithful on functor categories, so the ratio of this comparison
and the one supplied by constructibleTensorCompletion descends to a natural isomorphism.
Compose it with the completion comparison in that theorem. Its representative equation
is the prescribed chain map, and its values on constructible pairs are invertible
because both factors are invertible. -/
theorem completion_exists
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (a : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l E X)) :
    Nonempty (Completion D l hl X E a) := by
  classical
  have hc := chosen_spec (third_exists_first (@constructibleTensorCompletion l _ E _ _ _ X
    (QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of D.k)))
    (quasiSeparatedSpace_of_quasiSeparated (X ↘ Spec (.of D.k)))
    (units D l hl X)))
    (completionChain D l hl X E) (by unfold completionChain; rfl)
  change ∃ T e, _ at hc
  obtain ⟨T, e, _, _, tau, he, htau⟩ := hc
  let q := integralOperationsGoodLocalization l E X
  let W := (HomologicalComplex.quasiIso (integralTowerModules l E X) (.up ℤ)).inverseImage
    (integralOperationsGoodComplex l E X).ι
  have : q.IsLocalization W := integralOperationsGoodLocalization_isLocalization l E X
  let j : (integralOperationsGoodComplex l E X).FullSubcategory ⥤
      (IntegralHom.flat.{u, u} X
        (completedIntegralCommRingSheafUnrestricted l E X)).FullSubcategory :=
    ObjectProperty.lift _ (integralOperationsGoodComplex l E X).ι (fun P ↦ P.property.1)
  let ea : ((integralOperationsGoodComplex l E X).ι.prod
        (integralOperationsGoodComplex l E X).ι) ⋙ constructibleTensorTotal l E X ⋙
        DerivedCategory.Q ≅ (q.prod q) ⋙ a.tensor :=
    Functor.isoWhiskerLeft (j.prod j) a.representative
  let FF := Localization.fullyFaithfulWhiskeringLeft (q.prod q) (W.prod W)
    (IntegralHom.Derived.{u, u} X (completedIntegralCommRingSheafUnrestricted l E X))
  let i : a.tensor ≅ T := FF.preimageIso (ea.symm ≪≫ e)
  have hi : Functor.isoWhiskerLeft (q.prod q) i = ea.symm ≪≫ e := by
    apply Iso.ext
    exact FF.map_preimage _
  refine ⟨{ map := i.hom ≫ tau, invertible := ?_, representative := ?_ }⟩
  · intro K M
    have := (htau K.obj M.obj K.property M.property).2
    change IsIso (i.hom.app (K.obj, M.obj) ≫ tau.app (K.obj, M.obj))
    infer_instance
  · intro P Q
    apply heq_of_eq
    have hcomp : ea.hom ≫ Functor.whiskerLeft (q.prod q) i.hom = e.hom := by
      have h := congrArg Iso.hom hi
      change Functor.whiskerLeft (q.prod q) i.hom = ea.inv ≫ e.hom at h
      rw [h, Iso.hom_inv_id_assoc]
    have hcomp' := congrArg (fun z ↦ z.app (P, Q)) hcomp
    change ea.hom.app (P, Q) ≫
      i.hom.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) =
        e.hom.app (P, Q) at hcomp'
    change ea.hom.app (P, Q) ≫
      (i.hom.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) ≫
        tau.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj)) ≫ _ = _
    exact (compose_four _ _ _ _ _ hcomp').trans (he P Q)

end WeilConjectures.RationalVerdier
