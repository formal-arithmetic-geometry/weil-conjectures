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
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import WeilConjectures.AlgebraicGeometry.FiniteFieldDescent.FiniteEtaleConstructibleObjectDescent
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.Basic
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat

/-! # Finite-stage Hom systems for constructible finite-coefficient complexes

For a finite type scheme `Y` over a field `K` and a field extension `L/K`, the Hom
sets between pullbacks of two complexes from a finite stage `E₀` to the finite intermediate fields
above `E₀` form a directed system with a cocone to the Hom set over `L`.

## References

* Stacks Project, Lemma 09YU
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Etale.FiniteFieldDescent

variable {K : Type u} [Field K] {Y : Scheme.{u}} (f : Y ⟶ Spec (.of K))

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

instance finiteStageIndexSemilatticeSup {L : Type u} [Field L] [Algebra K L]
    (E₀ : IntermediateField K L) : SemilatticeSup (finiteStageIndex E₀) :=
  Subtype.semilatticeSup (fun _ _ hx hy ↦ by
    let _ := hx.2
    let _ := hy.2
    exact ⟨hx.1.trans le_sup_left, inferInstance⟩)

/-- The canonical transition on finite-stage Hom sets.
Source: Stacks Lemma 09YU (3), blueprint `lem-sfb-finite-etale-constructible-hom-descent`. -/
noncomputable def finiteStageHomTransition {L : Type u} [Field L] [Algebra K L]
    (Λ : Type (u + 1)) [CommRing Λ]
    {E₀ : IntermediateField K L}
    {P₀ Q₀ : DerivedCategoryModule Λ (scheme f E₀)}
    {E E' : finiteStageIndex E₀} (h : E ≤ E')
    (u : (pull f Λ (A := E₀) (B := E.1) (IntermediateField.inclusion E.property.1)).obj P₀ ⟶
      (pull f Λ (A := E₀) (B := E.1) (IntermediateField.inclusion E.property.1)).obj Q₀) :
    (pull f Λ (A := E₀) (B := E'.1) (IntermediateField.inclusion E'.property.1)).obj P₀ ⟶
      (pull f Λ (A := E₀) (B := E'.1) (IntermediateField.inclusion E'.property.1)).obj Q₀ := by
  let h₀E' : E₀ ≤ E'.1 := E'.property.1
  let hEE' : E.1 ≤ E'.1 := h
  let compIso :=
    (eqToIso (congrArg (fun j : E₀ →ₐ[K] E'.1 => pull f Λ (A := E₀) (B := E'.1) j)
      (show IntermediateField.inclusion h₀E' =
          (IntermediateField.inclusion hEE').comp
            (IntermediateField.inclusion E.property.1) by
        ext x
        rfl))).trans
      (pullCompIso f Λ (IntermediateField.inclusion E.property.1)
        (IntermediateField.inclusion hEE'))
  exact compIso.hom.app P₀ ≫
      (pull f Λ (A := E.1) (B := E'.1) (IntermediateField.inclusion hEE')).map u ≫
    compIso.inv.app Q₀

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

/-- A concrete pullback Hom cocone over all finite stages above `E₀`.
Source: Stacks Lemma 09YU (3), blueprint `lem-sfb-finite-etale-constructible-hom-descent`. -/
structure FiniteStageHomSystem {L : Type u} [Field L] [Algebra K L]
    (Λ : Type (u + 1)) [CommRing Λ]
    {E₀ : IntermediateField K L}
    (P₀ Q₀ : DerivedCategoryModule Λ (scheme f E₀)) where
  F : finiteStageIndex E₀ ⥤ Type (u + 1)
  objEquiv : ∀ E, F.obj E ≃
    ((pull f Λ (IntermediateField.inclusion E.property.1)).obj P₀ ⟶
      (pull f Λ (IntermediateField.inclusion E.property.1)).obj Q₀)
  map_eq : ∀ {E E'} (h : E ⟶ E') (x : F.obj E),
    objEquiv E' (F.map h x) =
      finiteStageHomTransition f Λ (leOfHom h) (objEquiv E x)
  c : Cocone F
  vertexEquiv : c.pt ≃
    ((pull f Λ (IntermediateField.val E₀)).obj P₀ ⟶
      (pull f Λ (IntermediateField.val E₀)).obj Q₀)
  leg_eq : ∀ (E) (x : F.obj E),
    vertexEquiv (c.ι.app E x) = finiteStageHomLeg f Λ (objEquiv E x)

end AlgebraicGeometry.Etale.FiniteFieldDescent

namespace AlgebraicGeometry.Etale.FiniteFieldDescent

variable {K : Type u} [Field K] {Y : Scheme.{u}} (f : Y ⟶ Spec (.of K))

/-- The leg of a finite-stage Hom system sends a pulled-back morphism to its pullback to `L`. -/
theorem finiteStageHomLeg_map {L : Type u} [Field L] [Algebra K L]
    (Λ : Type (u + 1)) [CommRing Λ] {E₀ : IntermediateField K L}
    {P₀ Q₀ : DerivedCategoryModule Λ (scheme f E₀)}
    (E : finiteStageIndex E₀) (u : P₀ ⟶ Q₀) :
    finiteStageHomLeg f Λ (E := E)
        ((pull f Λ (IntermediateField.inclusion E.property.1)).map u) =
      (pull f Λ (IntermediateField.val E₀)).map u := by
  unfold finiteStageHomLeg
  rw [← Functor.comp_map, ← NatTrans.naturality_assoc]
  simp

/-- The transition of a finite-stage Hom system sends a pulled-back morphism to its pullback to the
larger stage. -/
theorem finiteStageHomTransition_map {L : Type u} [Field L] [Algebra K L]
    (Λ : Type (u + 1)) [CommRing Λ] {E₀ : IntermediateField K L}
    {P₀ Q₀ : DerivedCategoryModule Λ (scheme f E₀)}
    {E E' : finiteStageIndex E₀} (h : E ≤ E') (u : P₀ ⟶ Q₀) :
    finiteStageHomTransition f Λ h
        ((pull f Λ (IntermediateField.inclusion E.property.1)).map u) =
      (pull f Λ (IntermediateField.inclusion E'.property.1)).map u := by
  unfold finiteStageHomTransition
  dsimp only
  rw [← Functor.comp_map, ← NatTrans.naturality_assoc]
  simp

end AlgebraicGeometry.Etale.FiniteFieldDescent
