/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import WeilConjectures.CategoryTheory.DerivedCategory.CompactGenerators
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf

/-!
# Brown representability for derived categories of sheaves of modules

Let `C` be an essentially small site (with objects in `Type (u + 1)` and morphisms in `Type u`,
like the small étale and pro-étale sites of a scheme), and `Λ` a ring. We show that the derived
category of sheaves of `Λ`-modules on `C` has Brown representability (Stacks `0F5Y`), so that
every triangulated functor out of it which preserves coproducts is a left adjoint.

* For presheaves, the free presheaves `Λ[U]` (left adjoint to evaluation at `U`, applied to
  `Λ`) are projective and compact, and they detect zero objects; placed in degree `0` they form
  a family of compact generators of the derived category of presheaves, which hence has Brown
  representability.
* For sheaves, sheafification `a` is exact and preserves coproducts, and it is left adjoint to
  the inclusion `ι` of sheaves into presheaves. On derived categories this gives an adjunction
  `D(a) ⊣ R(ι)` whose right adjoint is fully faithful, `ι` being fully faithful and preserving
  K-injective complexes. Brown representability descends along such an adjunction.

## Main statements

- `CategoryTheory.Presheaf.hasBrownRepresentability_derivedCategory`: the derived category of
  presheaves of `Λ`-modules has Brown representability.
- `CategoryTheory.Sheaf.hasBrownRepresentability_derivedCategory`: the derived category of
  sheaves of `Λ`-modules has Brown representability.
- `CategoryTheory.Sheaf.isLeftAdjoint_of_preservesCoproducts`: a triangulated functor out of the
  derived category of sheaves of `Λ`-modules which preserves coproducts is a left adjoint.
-/

@[expose] public section

universe u

open CategoryTheory Limits Abelian Pretriangulated Opposite

namespace CategoryTheory

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]

/-- The category of presheaves on an essentially small category with values in a Grothendieck
abelian category is Grothendieck abelian: it is the category of sheaves for the trivial
topology. -/
local instance isGrothendieckAbelian_presheaf (A : Type*) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] : IsGrothendieckAbelian.{u + 1} (Cᵒᵖ ⥤ A) :=
  IsGrothendieckAbelian.of_equivalence (sheafBotEquivalence (C := C) A)

namespace Presheaf

variable (Λ : Type (u + 1)) [Ring Λ]

/-- Coproducts indexed by the (small) `Hom`-types of `C` exist in `ModuleCat Λ`. -/
local instance (a b : Cᵒᵖ) : HasCoproductsOfShape (a ⟶ b) (ModuleCat.{u + 1} Λ) :=
  hasCoproductsOfShape_of_small.{u + 1} _ _

/-- Presheaves of `Λ`-modules form a Grothendieck abelian category, hence have K-injective
resolutions. -/
local instance : HasKInjectiveResolutions (Cᵒᵖ ⥤ ModuleCat.{u + 1} Λ) :=
  hasKInjectiveResolutions_of_isGrothendieckAbelian.{u + 1}

/-- The free presheaf of `Λ`-modules `Λ[U]` on an object `U`: the value at `U` of the left
adjoint of the evaluation at `U`, applied to `Λ`. Morphisms `Λ[U] ⟶ F` correspond to elements
of `F(U)`. -/
noncomputable def freeModule (U : C) : Cᵒᵖ ⥤ ModuleCat.{u + 1} Λ :=
  (evaluationLeftAdjoint (ModuleCat.{u + 1} Λ) (op U)).obj (ModuleCat.of Λ Λ)

/-- The left adjoint of an evaluation functor is additive. -/
instance (U : Cᵒᵖ) : (evaluationLeftAdjoint (ModuleCat.{u + 1} Λ) U).Additive :=
  (evaluationAdjunctionRight (ModuleCat.{u + 1} Λ) U).left_adjoint_additive

/-- `Λ[U]` is projective, as the image of `Λ` by a left adjoint of an exact functor. -/
instance projective_freeModule (U : C) : Projective (freeModule Λ U) :=
  (evaluationAdjunctionRight (ModuleCat.{u + 1} Λ) (op U)).map_projective _ inferInstance

/-- `Λ[U]` is compact: morphisms `Λ[U] ⟶ F` are elements of `F(U)`, and evaluation at `U`
commutes with coproducts. -/
lemma isCompactObject_freeModule (U : C) : IsCompactObject (freeModule Λ U) :=
  (ModuleCat.isCompactObject_self Λ).of_adjunction
    (evaluationAdjunctionRight (ModuleCat.{u + 1} Λ) (op U))

/-- The free presheaves detect zero objects. -/
lemma isZero_of_forall_freeModule_hom_eq_zero (M : Cᵒᵖ ⥤ ModuleCat.{u + 1} Λ)
    (hM : ∀ (U : C) (g : freeModule Λ U ⟶ M), g = 0) : IsZero M := by
  refine Functor.isZero _ fun U ↦ ?_
  rw [IsZero.iff_id_eq_zero]
  ext x
  let adj := evaluationAdjunctionRight (ModuleCat.{u + 1} Λ) U
  let g₀ : ModuleCat.of Λ Λ ⟶ M.obj U := ModuleCat.ofHom (LinearMap.toSpanSingleton Λ _ x)
  have h₀ : g₀ = 0 := by
    rw [← (adj.homEquiv _ _).apply_symm_apply g₀, hM U.unop ((adj.homEquiv _ _).symm g₀)]
    exact adj.homAddEquiv_zero _ _
  have := congrArg (fun g ↦ g.hom (1 : Λ)) h₀
  simpa [g₀] using this

variable [HasDerivedCategory.{u + 1} (Cᵒᵖ ⥤ ModuleCat.{u + 1} Λ)]

/-- **Brown representability** for the derived category of presheaves of `Λ`-modules: it is
compactly generated by the free presheaves `Λ[U]`. -/
theorem hasBrownRepresentability_derivedCategory :
    HasBrownRepresentability (DerivedCategory (Cᵒᵖ ⥤ ModuleCat.{u + 1} Λ)) :=
  DerivedCategory.hasBrownRepresentability_of_projective (fun U : C ↦ freeModule Λ U)
    (isCompactObject_freeModule Λ) (isZero_of_forall_freeModule_hom_eq_zero Λ)

end Presheaf

namespace Sheaf

variable (J : GrothendieckTopology C) (Λ : Type (u + 1)) [Ring Λ]

/-- Sheaves of `Λ`-modules form a Grothendieck abelian category, hence have K-injective
resolutions. -/
local instance : HasKInjectiveResolutions (Sheaf J (ModuleCat.{u + 1} Λ)) :=
  hasKInjectiveResolutions_of_isGrothendieckAbelian.{u + 1}

/-- The category of sheaves of `Λ`-modules has small colimits. -/
local instance : HasColimitsOfSize.{u + 1, u + 1} (Sheaf J (ModuleCat.{u + 1} Λ)) :=
  IsGrothendieckAbelian.hasColimits _

/-- The inclusion of sheaves into presheaves preserves K-injective complexes, being right
adjoint to the exact sheafification functor. -/
local instance : (sheafToPresheaf J (ModuleCat.{u + 1} Λ)).PreservesKInjectiveComplexes :=
  (sheafificationAdjunction J (ModuleCat.{u + 1} Λ)).preservesKInjectiveComplexes

variable [HasDerivedCategory.{u + 1} (Sheaf J (ModuleCat.{u + 1} Λ))]

/-- **Brown representability** for the derived category of sheaves of `Λ`-modules on an
essentially small site (Stacks `0F5Y`): every additive cohomological functor sending coproducts
to products is representable. It descends from the derived category of presheaves along the
adjunction `D(a) ⊣ R(ι)` induced by sheafification `a ⊣ ι`, whose right adjoint is fully
faithful. -/
theorem hasBrownRepresentability_derivedCategory :
    HasBrownRepresentability (DerivedCategory (Sheaf J (ModuleCat.{u + 1} Λ))) := by
  let := HasDerivedCategory.ofIsGrothendieckAbelian.{u + 1} (Cᵒᵖ ⥤ ModuleCat.{u + 1} Λ)
  let adj := Adjunction.mapDerivedCategoryRightDerivedAdjunction
    (sheafificationAdjunction J (ModuleCat.{u + 1} Λ))
  have (K : Type (u + 1)) : PreservesColimitsOfShape (Discrete K)
      (presheafToSheaf J (ModuleCat.{u + 1} Λ)).mapDerivedCategory :=
    Functor.preservesColimitsOfShape_mapDerivedCategory _ K
  exact (Presheaf.hasBrownRepresentability_derivedCategory Λ).of_adjunction adj

/-- **Brown representability for sheaves of modules** (Stacks `0F5Y`): a triangulated functor
`F : D(C, Λ) ⥤ D` out of the derived category of sheaves of `Λ`-modules on an essentially small
site which preserves coproducts is a left adjoint.

This is the homological-algebra input of the existence of the exceptional right adjoint
(blueprint `sk-prop-sf-existence` (a) and `thm-amb-etale-exceptional-adjoint`). -/
theorem isLeftAdjoint_of_preservesCoproducts {D : Type*} [Category.{u + 1} D] [HasZeroObject D]
    [HasShift D ℤ] [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    (F : DerivedCategory (Sheaf J (ModuleCat.{u + 1} Λ)) ⥤ D) [F.CommShift ℤ]
    [F.IsTriangulated] [∀ K : Type (u + 1), PreservesColimitsOfShape (Discrete K) F] :
    F.IsLeftAdjoint :=
  (hasBrownRepresentability_derivedCategory J Λ).isLeftAdjoint F

end Sheaf

end CategoryTheory
