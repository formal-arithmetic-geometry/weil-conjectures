/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.CategoryTheory.SheafTensorStructure
public import Sheaf.CategoryTheory.PresheafTensorInternalHom

import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
import Mathlib.CategoryTheory.Monoidal.Closed.Braided
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Sites.Sheafification
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
  let h := presheaf_enrichedHoms_exist (C := C) (A := A)
  let : ∀ (F G : Cᵒᵖ ⥤ A), Enriched.FunctorCategory.HasEnrichedHom A F G := h.1
  let : ∀ (F G : Cᵒᵖ ⥤ A), Enriched.FunctorCategory.HasFunctorEnrichedHom A F G := h.2
  let : MonoidalClosed (Cᵒᵖ ⥤ A) := MonoidalClosed.FunctorCategory.monoidalClosed
  let S := sfbSheafTensorStructure (A := A) J
  let := S.monoidal
  let := S.symmetric
  let := S.sheafificationMonoidal
  let a := presheafToSheaf J A
  let adj := sheafificationAdjunction J A
  let e (F G : Sheaf J A) : a.obj (F.obj ⊗ G.obj) ≅ F ⊗ G :=
    (Functor.Monoidal.μIso a F.obj G.obj).symm ≪≫
      tensorIso (asIso (adj.counit.app F)) (asIso (adj.counit.app G))
  have enat {F F' G G' : Sheaf J A} (f : F' ⟶ F) (g : G' ⟶ G) :
      (e F' G').hom ≫ (f ⊗ₘ g) = a.map (f.hom ⊗ₘ g.hom) ≫ (e F G).hom := by
    dsimp only [e, Iso.trans_hom, Iso.symm_hom, tensorIso, asIso_hom]
    rw [Category.assoc, tensorHom_comp_tensorHom,
      ← adj.counit_naturality f, ← adj.counit_naturality g,
      ← tensorHom_comp_tensorHom]
    simp only [← Category.assoc]
    congr 1
    exact Functor.OplaxMonoidal.δ_natural a f.hom g.hom
  let E (F G H : Sheaf J A) : (F ⊗ G ⟶ H) ≃ (G ⟶ sfbSheafInternalHom J F H) :=
    (Iso.homCongr (e F G).symm (Iso.refl H)).trans
      ((adj.homEquiv _ H).trans
        (((ihom.adjunction F.obj).homEquiv G.obj H.obj).trans
          (Sheaf.homEquiv (X := G) (Y := sfbSheafInternalHom J F H)).symm))
  have eb (F G H : Sheaf J A) (t : F ⊗ G ⟶ H) :
      ((E F G H) t).hom = MonoidalClosed.curry (adj.homEquiv _ H ((e F G).hom ≫ t)) := by
    change (sheafToPresheaf J A).map ((E F G H) t) = _
    simp [E, Iso.homCongr, Sheaf.homEquiv, Functor.FullyFaithful.homEquiv,
      MonoidalClosed.curry]
    rfl
  have nat : ∀ (F F' G G' H H' : Sheaf J A) (f : F' ⟶ F) (g : G' ⟶ G)
      (h : H ⟶ H') (t : F ⊗ G ⟶ H),
      E F' G' H' ((f ⊗ₘ g) ≫ t ≫ h) =
        g ≫ E F G H t ≫ sfbSheafInternalHomMap f h := by
    intro F F' G G' H H' f g h t
    apply (fullyFaithfulSheafToPresheaf J A).map_injective
    change ((E F' G' H') ((f ⊗ₘ g) ≫ t ≫ h)).hom =
      g.hom ≫ ((E F G H) t).hom ≫ (sfbSheafInternalHomMap f h).hom
    rw [eb, eb]
    rw [← Category.assoc (e F' G').hom, enat]
    rw [Category.assoc, adj.homEquiv_naturality_left]
    rw [← Category.assoc (e F G).hom t h, adj.homEquiv_naturality_right]
    change MonoidalClosed.curry ((f.hom ⊗ₘ g.hom) ≫
      adj.homEquiv _ H ((e F G).hom ≫ t) ≫ h.hom) =
      g.hom ≫ MonoidalClosed.curry (adj.homEquiv _ H ((e F G).hom ≫ t)) ≫
        ((MonoidalClosed.pre f.hom).app H.obj ≫ (ihom F'.obj).map h.hom)
    rw [← Category.assoc, MonoidalClosed.curry_natural_right, tensorHom_def', Category.assoc,
      MonoidalClosed.curry_natural_left, ← MonoidalClosed.curry_pre_app]
    simp only [Category.assoc]
    rfl
  let hc : MonoidalClosed (Sheaf J A) :=
    Monoidal.Reflective.monoidalClosed adj
  let := hc
  have hl (F : Sheaf J A) : PreservesColimitsOfSize.{w, w} (tensorLeft F) :=
    (ihom.adjunction F).leftAdjoint_preservesColimits
  have hr (F : Sheaf J A) : PreservesColimitsOfSize.{w, w} (tensorRight F) :=
    inferInstance
  have : HasBinaryBiproducts (Sheaf J A) := HasBinaryBiproducts.of_hasBinaryProducts
  have hal (F : Sheaf J A) : Functor.Additive (tensorLeft F) := by
    have := preservesBinaryBiproducts_of_preservesBinaryCoproducts (tensorLeft F)
    exact Functor.additive_of_preservesBinaryBiproducts _
  have har (F : Sheaf J A) : Functor.Additive (tensorRight F) := by
    have : PreservesColimitsOfSize.{0, 0} (tensorRight F) :=
      inferInstance
    have := preservesBinaryBiproducts_of_preservesBinaryCoproducts (tensorRight F)
    exact Functor.additive_of_preservesBinaryBiproducts _
  refine ⟨{
    closed := hc
    homEquiv := E
    natural := nat
    leftPreservesColimits := hl
    rightPreservesColimits := hr
    leftAdditive := hal
    rightAdditive := har
    leftRightExact := fun F ↦ (hl F).preservesFiniteColimits
    rightRightExact := fun F ↦ (hr F).preservesFiniteColimits }⟩

end CategoryTheory
