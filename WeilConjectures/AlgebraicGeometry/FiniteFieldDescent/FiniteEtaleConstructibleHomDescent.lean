/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import Mathlib.FieldTheory.Separable
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Finite-stage descent and Hom continuity for constructible finite-coefficient complexes

Source: `literature/stacks-project/etale-cohomology.tex`, Lemma 09YU (3),
constructible sheaves over inverse limits with affine transition maps; bounded finite-Tor
complexes are obtained by finite flat resolutions and descent of morphisms.
(blueprint: lem-sfb-finite-etale-constructible-hom-descent).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Etale.FiniteFieldDescent

variable {K : Type u} [Field K] {Y : Scheme.{u}} (f : Y ⟶ Spec (.of K))

/-- The canonical fibre product `Y_A` at a field extension `A/K`.
Source: Stacks Lemma 09YU (3) (blueprint: lem-sfb-finite-etale-constructible-hom-descent). -/
noncomputable abbrev scheme (A : Type u) [Field A] [Algebra K A] : Scheme.{u} :=
  pullback f (Spec.map (CommRingCat.ofHom (algebraMap K A)))

/-- The canonical transition `Y_B ⟶ Y_A` induced by a `K`-algebra map `A ⟶ B`.
Source: Stacks Lemma 09YU (3) (blueprint: lem-sfb-finite-etale-constructible-hom-descent). -/
noncomputable def projection {A B : Type u} [Field A] [Field B] [Algebra K A]
    [Algebra K B] (h : A →ₐ[K] B) : scheme f B ⟶ scheme f A :=
  pullback.map _ _ _ _ (𝟙 Y) (Spec.map (CommRingCat.ofHom h.toRingHom)) (𝟙 _)
    (by simp)
    (by
      rw [Category.comp_id, ← Spec.map_comp]
      congr 1
      ext x
      exact (h.commutes x).symm)

/-- The derived inverse-image functor along a transition of finite stages.
Source: Stacks Lemma 09YU (3) (blueprint: lem-sfb-finite-etale-constructible-hom-descent). -/
noncomputable abbrev pull (Λ : Type (u + 1)) [CommRing Λ]
    {A B : Type u} [Field A] [Field B] [Algebra K A] [Algebra K B]
    (h : A →ₐ[K] B) :=
  (upperStar (ModuleCat.{u + 1} Λ) (projection f h)).leftDerivedFunctor

/-- The canonical compositor for two successive field-stage pullbacks.
Source: Stacks Lemma 09YU (3), blueprint `lem-sfb-finite-etale-constructible-hom-descent`. -/
noncomputable def pullCompIso {A B C : Type u} [Field A] [Field B] [Field C]
    [Algebra K A] [Algebra K B] [Algebra K C]
    (Λ : Type (u + 1)) [CommRing Λ] (h : A →ₐ[K] B) (i : B →ₐ[K] C) :
    pull f Λ (i.comp h) ≅ pull f Λ h ⋙ pull f Λ i :=
  leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) (projection f i) (projection f h)
    (projection f (i.comp h)) (by
      apply pullback.hom_ext
      · simp [projection, Category.assoc]
      · simp [projection, Category.assoc, ← Spec.map_comp]
        congr 1)

/-- The canonical compositor from a finite intermediate stage to `L`.
Source: Stacks Lemma 09YU (3), blueprint `lem-sfb-finite-etale-constructible-hom-descent`. -/
noncomputable def pullValCompIso {L : Type u} [Field L] [Algebra K L]
    {E E' : IntermediateField K L} (hEE' : E ≤ E')
    (Λ : Type (u + 1)) [CommRing Λ] :
    pull f Λ (IntermediateField.val E) ≅
      pull f Λ (IntermediateField.inclusion hEE') ⋙
        pull f Λ (IntermediateField.val E') :=
  (eqToIso (congrArg (fun j : E →ₐ[K] L => pull f Λ j)
    (by ext x; rfl))).trans
    (pullCompIso f Λ (IntermediateField.inclusion hEE')
      (IntermediateField.val E'))

/-- Finite intermediate stages above a fixed finite stage.
Source: Stacks Lemma 09YU (3), blueprint `lem-sfb-finite-etale-constructible-hom-descent`. -/
def finiteStageIndex {L : Type u} [Field L] [Algebra K L]
    (E₀ : IntermediateField K L) :=
  {E : IntermediateField K L // E₀ ≤ E ∧ FiniteDimensional K E}

/-- The canonical transition on finite-stage Hom sets.
Source: Stacks Lemma 09YU (3), blueprint `lem-sfb-finite-etale-constructible-hom-descent`. -/
noncomputable def finiteStageHomTransition {L : Type u} [Field L] [Algebra K L]
    (Λ : Type (u + 1)) [CommRing Λ]
    {E₀ : IntermediateField K L}
    {P₀ Q₀ : DerivedCategoryModule Λ (scheme f E₀)}
    {E E' : finiteStageIndex E₀} (h : E ≤ E')
    (u : (pull f Λ (IntermediateField.inclusion E.property.1)).obj P₀ ⟶
      (pull f Λ (IntermediateField.inclusion E.property.1)).obj Q₀) :
    (pull f Λ (IntermediateField.inclusion E'.property.1)).obj P₀ ⟶
      (pull f Λ (IntermediateField.inclusion E'.property.1)).obj Q₀ := by
  let h₀E' : E₀ ≤ E'.1 := E'.property.1
  let hEE' : E.1 ≤ E'.1 := h
  let compIso :=
    (eqToIso (congrArg (fun j : E₀ →ₐ[K] E'.1 => pull f Λ j)
      (show IntermediateField.inclusion h₀E' =
          (IntermediateField.inclusion hEE').comp
            (IntermediateField.inclusion E.property.1) by
        ext x
        rfl))).trans
      (pullCompIso f Λ (IntermediateField.inclusion E.property.1)
        (IntermediateField.inclusion hEE'))
  exact compIso.hom.app P₀ ≫
      (pull f Λ (IntermediateField.inclusion hEE')).map u ≫ compIso.inv.app Q₀

/-- The canonical leg from a finite-stage Hom set to the limiting Hom set.
Source: Stacks Lemma 09YU (3), blueprint `lem-sfb-finite-etale-constructible-hom-descent`. -/
noncomputable def finiteStageHomLeg {L : Type u} [Field L] [Algebra K L]
    (Λ : Type (u + 1)) [CommRing Λ]
    {E₀ : IntermediateField K L}
    {P₀ Q₀ : DerivedCategoryModule Λ (scheme f E₀)}
    {E : finiteStageIndex E₀}
    (u : (pull f Λ (IntermediateField.inclusion E.property.1)).obj P₀ ⟶
      (pull f Λ (IntermediateField.inclusion E.property.1)).obj Q₀) :
    (pull f Λ (IntermediateField.val E₀)).obj P₀ ⟶
      (pull f Λ (IntermediateField.val E₀)).obj Q₀ :=
  (pullValCompIso f E.property.1 Λ).hom.app P₀ ≫
      (pull f Λ (IntermediateField.val E.1)).map u ≫
    (pullValCompIso f E.property.1 Λ).inv.app Q₀

end AlgebraicGeometry.Etale.FiniteFieldDescent
