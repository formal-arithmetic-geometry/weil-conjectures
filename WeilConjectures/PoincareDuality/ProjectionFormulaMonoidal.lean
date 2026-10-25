/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.PoincareDuality.ProjectionFormulaMonoidalOfCompactification

/-!

# The exceptional projection morphism is a module structure

The exceptional projection morphism `PF^!_{f,K,B} : Rf_! K ⊗ᴸ B ⟶ Rf_! (K ⊗ᴸ Lf^* B)` on bounded
constructible complexes (`ProEtale.CondensedRing.boundedConstructibleExceptionalProjection`) is
compatible with the unit and the tensor structure of `Lf^*` in its second variable (the axioms of
a module functor), in exactly the form of the hypotheses `hunit` and `hassoc` of
`CategoryTheory.Adjunction.isIso_exceptionalTensorMap`.

These are the images under the faithful inclusion of the statements on the unbounded derived
categories (`WeilConjectures.PoincareDuality.ProjectionFormulaMonoidalOfCompactification`), proved
for an arbitrary compactification and specialised to `compactificationOverField f`.

## Main statements

- `ProEtale.CondensedRing.boundedConstructibleExceptionalProjection_unit`,
  `ProEtale.CondensedRing.boundedConstructibleExceptionalProjection_tensor`.

## Implementation notes

The underlying morphisms are first rewritten into the ambient derived categories with the
`rfl`-lemmas `ProEtale.CondensedRing.boundedConstructibleLowerShriekOfCompactification_map_hom`
and the like, so that the ambient statement applies syntactically.

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-! ### The module axioms on bounded constructible complexes -/

section BoundedConstructible

variable (ℓ : ℕ) [Fact ℓ.Prime] [IsEllAdicFinitenessCoefficient ℓ Λ] {k : Type u} [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y)

/-- The exceptional projection morphism of a compactification `c`, restricted to bounded
constructible complexes, is unital. -/
lemma boundedConstructibleExceptionalProjectionMorphismOfCompactification_unit
    (c : Compactification f.left) (K : Dᵇc(X.left)⟦Λ⟧) :
    ObjectProperty.homMk
        (X := (boundedConstructibleLowerShriekOfCompactification Λ ℓ c).obj K ⊗ 𝟙_ _)
        (Y := (boundedConstructibleLowerShriekOfCompactification Λ ℓ c).obj
          (K ⊗ (boundedConstructibleUpperStar Λ ℓ f).obj (𝟙_ _)))
        (exceptionalProjectionMorphismOfCompactification Λ c K.obj (𝟙_ _)) =
      (ρ_ _).hom ≫ (boundedConstructibleLowerShriekOfCompactification Λ ℓ c).map
        ((ρ_ K).inv ≫ K ◁ ε (boundedConstructibleUpperStar Λ ℓ f)) := by
  refine ObjectProperty.hom_ext (P := boundedConstructible _) ?_
  exact exceptionalProjectionMorphismOfCompactification_unit Λ c K.obj

/-- `Rf_!^c` on bounded constructible complexes is `Rf_!(c)` on underlying morphisms. -/
lemma boundedConstructibleLowerShriekOfCompactification_map_hom (c : Compactification f.left)
    {K K' : Dᵇc(X.left)⟦Λ⟧} (φ : K ⟶ K') :
    ((boundedConstructibleLowerShriekOfCompactification Λ ℓ c).map φ).hom =
      (Rf_!(c)⟦Λ⟧).map φ.hom :=
  rfl

/-- `Rf_!^c` on bounded constructible complexes is `Rf_!(c)` on underlying objects. -/
lemma boundedConstructibleLowerShriekOfCompactification_obj_obj (c : Compactification f.left)
    (K : Dᵇc(X.left)⟦Λ⟧) :
    ((boundedConstructibleLowerShriekOfCompactification Λ ℓ c).obj K).obj =
      (Rf_!(c)⟦Λ⟧).obj K.obj :=
  rfl

/-- The multiplication of the derived pullback on bounded constructible complexes is that of
`Lf^*` on underlying objects. -/
lemma boundedConstructibleUpperStar_μ_hom (B C : Dᵇc(Y.left)⟦Λ⟧) :
    (μ (boundedConstructibleUpperStar Λ ℓ f) B C).hom = μ L((f.left)^*⟦Λ⟧) B.obj C.obj :=
  rfl

/-- The exceptional projection morphism of a compactification `c`, restricted to bounded
constructible complexes, is associative. -/
lemma boundedConstructibleExceptionalProjectionMorphismOfCompactification_tensor
    (c : Compactification f.left) (K : Dᵇc(X.left)⟦Λ⟧) (B C : Dᵇc(Y.left)⟦Λ⟧) :
    ObjectProperty.homMk
        (X := (boundedConstructibleLowerShriekOfCompactification Λ ℓ c).obj K ⊗ (B ⊗ C))
        (Y := (boundedConstructibleLowerShriekOfCompactification Λ ℓ c).obj
          (K ⊗ (boundedConstructibleUpperStar Λ ℓ f).obj (B ⊗ C)))
        (exceptionalProjectionMorphismOfCompactification Λ c K.obj (B ⊗ C).obj) =
      (α_ _ _ _).inv ≫
        ObjectProperty.homMk
          (X := (boundedConstructibleLowerShriekOfCompactification Λ ℓ c).obj K ⊗ B)
          (Y := (boundedConstructibleLowerShriekOfCompactification Λ ℓ c).obj
            (K ⊗ (boundedConstructibleUpperStar Λ ℓ f).obj B))
          (exceptionalProjectionMorphismOfCompactification Λ c K.obj B.obj) ▷ C ≫
        ObjectProperty.homMk
          (X := (boundedConstructibleLowerShriekOfCompactification Λ ℓ c).obj
            (K ⊗ (boundedConstructibleUpperStar Λ ℓ f).obj B) ⊗ C)
          (Y := (boundedConstructibleLowerShriekOfCompactification Λ ℓ c).obj
            ((K ⊗ (boundedConstructibleUpperStar Λ ℓ f).obj B) ⊗
              (boundedConstructibleUpperStar Λ ℓ f).obj C))
          (exceptionalProjectionMorphismOfCompactification Λ c
            (K ⊗ (boundedConstructibleUpperStar Λ ℓ f).obj B).obj C.obj) ≫
        (boundedConstructibleLowerShriekOfCompactification Λ ℓ c).map
          ((α_ _ _ _).hom ≫ K ◁ μ (boundedConstructibleUpperStar Λ ℓ f) B C) := by
  refine ObjectProperty.hom_ext (P := boundedConstructible _) ?_
  dsimp only [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom,
    ObjectProperty.FullSubcategory.tensorObj_obj, ObjectProperty.FullSubcategory.whiskerLeft_hom,
    ObjectProperty.FullSubcategory.whiskerRight_hom,
    ObjectProperty.FullSubcategory.associator_hom_hom,
    ObjectProperty.FullSubcategory.associator_inv_hom,
    boundedConstructibleLowerShriekOfCompactification_map_hom,
    boundedConstructibleLowerShriekOfCompactification_obj_obj, boundedConstructibleUpperStar_μ_hom,
    boundedConstructibleUpperStar_obj_obj]
  exact exceptionalProjectionMorphismOfCompactification_tensor Λ c K.obj B.obj C.obj

/-- **Unitality of the exceptional projection morphism** on bounded constructible complexes, in
the form of the hypothesis `hunit` of `CategoryTheory.Adjunction.isIso_exceptionalTensorMap`. -/
lemma boundedConstructibleExceptionalProjection_unit (A : Dᵇc(X.left)⟦Λ⟧) :
    ((boundedConstructibleExceptionalProjection Λ ℓ f).app A).app (𝟙_ _) =
      (ρ_ ((boundedConstructibleLowerShriek Λ ℓ f).obj A)).hom ≫
        (boundedConstructibleLowerShriek Λ ℓ f).map
          ((ρ_ A).inv ≫ A ◁ ε (boundedConstructibleUpperStar Λ ℓ f)) :=
  boundedConstructibleExceptionalProjectionMorphismOfCompactification_unit Λ ℓ f
    (compactificationOverField f) A

/-- **Associativity of the exceptional projection morphism** on bounded constructible complexes,
in the form of the hypothesis `hassoc` of `CategoryTheory.Adjunction.isIso_exceptionalTensorMap`.
-/
lemma boundedConstructibleExceptionalProjection_tensor (A : Dᵇc(X.left)⟦Λ⟧)
    (B C : Dᵇc(Y.left)⟦Λ⟧) :
    ((boundedConstructibleExceptionalProjection Λ ℓ f).app A).app (B ⊗ C) =
      (α_ _ _ _).inv ≫ (((boundedConstructibleExceptionalProjection Λ ℓ f).app A).app B ▷ C) ≫
        ((boundedConstructibleExceptionalProjection Λ ℓ f).app
          (A ⊗ (boundedConstructibleUpperStar Λ ℓ f).obj B)).app C ≫
        (boundedConstructibleLowerShriek Λ ℓ f).map
          ((α_ _ _ _).hom ≫ A ◁ μ (boundedConstructibleUpperStar Λ ℓ f) B C) :=
  boundedConstructibleExceptionalProjectionMorphismOfCompactification_tensor Λ ℓ f
    (compactificationOverField f) A B C

end BoundedConstructible

end AlgebraicGeometry.ProEtale.CondensedRing
