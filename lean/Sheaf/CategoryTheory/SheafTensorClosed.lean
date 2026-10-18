/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.CategoryTheory.SheafTensorStructure
public import Sheaf.CategoryTheory.PresheafTensorInternalHom

import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Closedness and exactness of the sheaf tensor product

Source: blueprint `det-def-sfb-sheaf-tensor-closed` (blueprint: det-def-sfb-sheaf-tensor-closed).

The statement packages the tensor-Hom bijection, its naturality, preservation of colimits,
additivity, and right exactness for the sheaf tensor structure.
-/

@[expose] public section

universe uC vC w uA vA

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonoidalClosed

namespace CategoryTheory

section InternalHom

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
  {A : Type uA} [Category.{vA} A] [Abelian A] [IsGrothendieckAbelian.{w} A]
  [MonoidalCategory A] [SymmetricCategory A] [MonoidalClosed A]
  [MonoidalPreadditive A]

/-- The specified internal Hom of sheaves: the existing presheaf internal Hom, bundled
using its sheaf condition. This introduces no new end construction.

Source: blueprint `sk-def-sfb-sheaf-tensor/det-def-sfb-sheaf-tensor-closed.md`, first
paragraph (blueprint: det-def-sfb-sheaf-tensor-closed). -/
noncomputable def sfbSheafInternalHom (J : GrothendieckTopology C) (F H : Sheaf J A) :
    Sheaf J A := by
  letI : ∀ (P Q : Cᵒᵖ ⥤ A), Enriched.FunctorCategory.HasFunctorEnrichedHom A P Q :=
    (presheaf_enrichedHoms_exist (C := C) (A := A)).2
  exact ⟨Enriched.FunctorCategory.functorEnrichedHom A F.obj H.obj,
    Presheaf.isSheaf_functorEnrichedHom F.obj H.obj H.property⟩

/-- Pre- and postcomposition on the specified internal Hom, inherited from the canonical
presheaf closed structure and regarded as a sheaf morphism by fullness.

Source: blueprint `sk-def-sfb-sheaf-tensor/det-def-sfb-sheaf-tensor-closed.md`, naturality
clause and proof step 1 (blueprint: det-def-sfb-sheaf-tensor-closed). -/
noncomputable def sfbSheafInternalHomMap {J : GrothendieckTopology C}
    {F F' H H' : Sheaf J A} (f : F' ⟶ F) (h : H ⟶ H') :
    sfbSheafInternalHom J F H ⟶ sfbSheafInternalHom J F' H' := by
  let e := presheaf_enrichedHoms_exist (C := C) (A := A)
  letI : ∀ (P Q : Cᵒᵖ ⥤ A), Enriched.FunctorCategory.HasEnrichedHom A P Q := e.1
  letI : ∀ (P Q : Cᵒᵖ ⥤ A), Enriched.FunctorCategory.HasFunctorEnrichedHom A P Q := e.2
  letI : MonoidalClosed (Cᵒᵖ ⥤ A) := MonoidalClosed.FunctorCategory.monoidalClosed
  exact ObjectProperty.homMk
    ((MonoidalClosed.pre f.hom).app H.obj ≫ (ihom F'.obj).map h.hom)

end InternalHom

/-- Data expressing closedness, colimit preservation, additivity and right exactness of the
sheaf tensor structure.

Source: blueprint `sk-def-sfb-sheaf-tensor/det-def-sfb-sheaf-tensor-closed.md`, displayed
bijection and all following clauses (blueprint: det-def-sfb-sheaf-tensor-closed) -/
structure SfbSheafTensorClosedData
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    {A : Type uA} [Category.{vA} A] [Abelian A] [IsGrothendieckAbelian.{w} A]
    [MonoidalCategory A] [SymmetricCategory A] [MonoidalClosed A]
    [MonoidalPreadditive A]
    {J : GrothendieckTopology C} [HasWeakSheafify J A]
    (S : SfbSheafTensorStructure (A := A) J) where
  closed : letI := S.monoidal; MonoidalClosed (Sheaf J A)
  homEquiv : letI := S.monoidal; ∀ (F G H : Sheaf J A),
    (MonoidalCategoryStruct.tensorObj F G ⟶ H) ≃
      (G ⟶ sfbSheafInternalHom J F H)
  natural : letI := S.monoidal; ∀ (F F' G G' H H' : Sheaf J A) (f : F' ⟶ F) (g : G' ⟶ G)
    (h : H ⟶ H') (t : MonoidalCategoryStruct.tensorObj F G ⟶ H),
    homEquiv F' G' H' (MonoidalCategoryStruct.tensorHom f g ≫ t ≫ h) =
      g ≫ homEquiv F G H t ≫
        sfbSheafInternalHomMap f h
  leftPreservesColimits : letI := S.monoidal; ∀ F : Sheaf J A,
    PreservesColimitsOfSize.{w, w} (MonoidalCategory.tensorLeft F)
  rightPreservesColimits : letI := S.monoidal; ∀ F : Sheaf J A,
    PreservesColimitsOfSize.{w, w} (MonoidalCategory.tensorRight F)
  leftAdditive : letI := S.monoidal; ∀ F : Sheaf J A,
    Functor.Additive (MonoidalCategory.tensorLeft F)
  rightAdditive : letI := S.monoidal; ∀ F : Sheaf J A,
    Functor.Additive (MonoidalCategory.tensorRight F)
  leftRightExact : letI := S.monoidal; ∀ F : Sheaf J A,
    PreservesFiniteColimits (MonoidalCategory.tensorLeft F)
  rightRightExact : letI := S.monoidal; ∀ F : Sheaf J A,
    PreservesFiniteColimits (MonoidalCategory.tensorRight F)

/-- The tensor product of sheaves is closed and right exact.

Source: blueprint `det-def-sfb-sheaf-tensor-closed` (blueprint: det-def-sfb-sheaf-tensor-closed).
Proof, following the node's six steps:
1. By `det-def-sfb-sheaf-tensor-presheaf`, the presheaf internal Hom has its canonical
pre- and postcomposition maps. By `det-def-sfb-sheaf-tensor-hom-sheaf` its value on a
sheaf is a sheaf; fullness makes these maps sheaf morphisms.
2. For F, G, H, use `det-def-sfb-sheaf-tensor-structure` to identify the tensor with the
sheafified presheaf tensor. Apply `def-weil-pbc-sheafification` to remove sheafification
from Hom into H, then the presheaf tensor-Hom adjunction, then fullness. Each step is
natural in all three variables. Thus tensorLeft F is left adjoint to the specified Hom.
3. The coefficient category has small colimits by `def-sp-grothendieck-abelian`.
Form presheaf colimits objectwise; their universal property gives compatible natural
transformations. Sheafification converts this into the sheaf colimit universal property
(`def-weil-pbc-category-colimit`), also for empty and finite diagrams.
4. Apply `lem-weil-pbc-left-adjoint-preserves-colimits` (Stacks 0038) to step 2.
Symmetry from `det-def-sfb-sheaf-tensor-structure` makes tensorRight F a left adjoint
to the same Hom, so both tensor functors preserve small colimits.
5. By `def-sp-abelian`, sheaf morphisms have componentwise sums and negatives, and the
zero presheaf is a sheaf. Pointwise binary biproducts are sheaves since matching pairs
glue coordinatewise. The componentwise inclusions and projections satisfy the biproduct
identities of `def-weil-additive-category`, giving an additive sheaf category.
6. Each tensor functor preserves zero objects and binary coproducts, hence zero maps,
projections, diagonals and codiagonals. Apply it to the expression for f + g as diagonal,
f ⊕ g, codiagonal, obtaining additivity (`def-weil-pbc-additive-functor`, Stacks 0DLP).
Finite diagrams are small, so preservation of all finite colimits gives right exactness
(Stacks 0034), including preservation of cokernels. -/
theorem sfbSheafTensorClosed
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    {A : Type uA} [Category.{vA} A] [Abelian A] [IsGrothendieckAbelian.{w} A]
    [MonoidalCategory A] [SymmetricCategory A] [MonoidalClosed A]
    [MonoidalPreadditive A]
    (J : GrothendieckTopology C) [HasWeakSheafify J A] :
    Nonempty (SfbSheafTensorClosedData (sfbSheafTensorStructure (A := A) J)) := by
  sorry

end CategoryTheory
