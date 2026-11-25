/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Whiskering
public import WeilConjectures.SmoothPurity.Finite.FiniteSystemPullbackCoherence
public import WeilConjectures.SmoothPurity.Supporting.CoefDerivedSystemEvaluationCalculus
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
import WeilConjectures.SmoothPurity.Pur.PurNormalizedReconstructionAdjunctionCalculus
import WeilConjectures.SmoothPurity.Completed.CompletedCoefficientPresentationTransport
import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructibleTriangulated
import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-! # Fully faithful coherent reduction of constructible integral objects

## References

* Stacks Project, Tags 099N(2),(5) and 0941
* B. Bhatt, P. Scholze, *The pro-étale topology for schemes*, Lemma 3.5.7
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Positive uniformizer quotients, in the coefficient universe. -/
abbrev integralSystemRings (n : ℕ) : CommRingCat.{u} :=
  CommRingCat.of (Padic.coefficientExtensionRing l E (n + 1))

/-- The actual adjacent quotient maps. -/
abbrev integralSystemTransition (n : ℕ) :
    integralSystemRings l E (n + 1) ⟶ integralSystemRings l E n :=
  CommRingCat.ofHom (Padic.coefficientExtensionTransition l E (n + 1))

/-- Finiteness of each positive quotient. -/
instance integralSystemRings_finite (n : ℕ) : Finite (integralSystemRings l E n) :=
  Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n))

/-- The already specified reduction, restricted to the actual constructible category.
The sequence-site presentations agree definitionally, including quotient maps. -/
def integralSystemReduction (X : Scheme.{u}) : sfIntegralConstructibleCategory l E X ⥤
    finiteSystemDerived (integralSystemRings l E) (integralSystemTransition l E) X :=
  (sfIntegralConstructible l E X).ι ⋙
    (coefficientDerivedSystemEvaluationCalculus l E X).choose.reduction

/-- Evaluation of coherent reduction is the specified derived scalar extension. -/
def integralSystemReductionEvaluation (X : Scheme.{u}) (n : ℕ) :
    integralSystemReduction l E X ⋙
        finiteSystemDerivedEvaluation (integralSystemRings l E) (integralSystemTransition l E) X n ≅
      (sfIntegralConstructible l E X).ι ⋙ scalarReductionDerivedExtension l E X n :=
  isoWhiskerLeft (sfIntegralConstructible l E X).ι
    ((coefficientDerivedSystemEvaluationCalculus l E X).choose.reductionEvaluation n)

private theorem restricted_full_faithful
    {C D : Type*} [Category C] [Category D] (P : ObjectProperty C)
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    (hu : ∀ X : P.FullSubcategory, IsIso (adj.unit.app X.obj)) :
    (P.ι ⋙ F).Full ∧ (P.ι ⋙ F).Faithful := by
  let inst (X : P.FullSubcategory) := hu X
  let ff : (P.ι ⋙ F).FullyFaithful :=
    { preimage := fun {X Y} f ↦ ⟨adj.homEquiv _ _ f ≫ inv (adj.unit.app Y.obj)⟩
      map_preimage := by
        intro X Y f
        change F.map (adj.homEquiv _ _ f ≫ inv (adj.unit.app Y.obj)) = f
        have he : F.map (inv (adj.unit.app Y.obj)) = adj.counit.app (F.obj Y.obj) := by
          apply (cancel_epi (F.map (adj.unit.app Y.obj))).1
          rw [← Functor.map_comp]
          simp
        rw [Functor.map_comp, he]
        exact (adj.homEquiv _ _).symm_apply_apply f
      preimage_map := by
        intro X Y f
        ext
        change adj.homEquiv _ _ (F.map f.hom) ≫ inv (adj.unit.app Y.obj) = f.hom
        rw [Adjunction.homEquiv_unit]
        change (adj.unit.app X.obj ≫ (F ⋙ G).map f.hom) ≫ _ = _
        rw [← adj.unit.naturality f.hom]
        simp }
  exact ⟨ff.full, ff.faithful⟩

/-- Coherent reduction is fully faithful on derived-complete constructible objects. -/
theorem integralSystemReduction_fullyFaithful (X : Scheme.{u})
    [∀ x : X, Invertible (l : X.residueField x)] :
    (integralSystemReduction l E X).Full ∧ (integralSystemReduction l E X).Faithful := by
  have hl : IsUnit (l : Γ(X, ⊤)) := by
    apply AlgebraicGeometry.RingedSpace.isUnit_of_isUnit_germ X.toSheafedSpace ⊤
    intro x hx
    apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
    simpa only [map_natCast] using
      (isUnit_of_invertible (l : X.residueField x)).ne_zero
  let S := (coefficientDerivedSystemEvaluationCalculus l E X).choose
  have hu (K : sfIntegralConstructibleCategory l E X) :
      IsIso (S.adjunction.unit.app K.obj) := by
    let T := purCoefficientModel l E X
    let M := T.inverse.obj K.obj
    have hm : sfIntegralConstructible l E X (T.functor.obj M) :=
      (sfIntegralConstructible l E X).prop_of_iso (T.counitIso.app K.obj).symm K.property
    have hp := purCoefficientModel_predicates l E X M
    have hc := hp.1.mp (hp.2.mpr hm.1)
    have hi := (purNormalizedReconstruction l E X hl S).2 _ hc
    have hn := S.adjunction.unit.naturality (T.counitIso.app K.obj).hom
    dsimp only [Functor.id_map, Functor.id_obj, Functor.comp_obj] at hn
    have : IsIso (S.adjunction.unit.app (T.functor.obj M)) := hi
    have : IsIso ((T.counitIso.app K.obj).hom ≫ S.adjunction.unit.app K.obj) := by
      exact hn ▸ (inferInstance : IsIso (S.adjunction.unit.app (T.functor.obj M) ≫
        (S.reduction ⋙ coefficientSequenceLimit l E X).map (T.counitIso.app K.obj).hom))
    exact (isIso_comp_left_iff (T.counitIso.app K.obj).hom _).mp inferInstance
  exact restricted_full_faithful (sfIntegralConstructible l E X) S.adjunction hu

end WeilConjectures
