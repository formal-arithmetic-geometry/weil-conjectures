/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Functor.Flat
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Limits.Colimits

/-!
# Left exactness of left Kan extension along a flat functor, without smallness

`CategoryTheory.Functor.lanEvaluationIsoColim` in Mathlib identifies the evaluation of the
left Kan extension functor `F.lan` at `X` with the colimit over the comma category
`CostructuredArrow F X`, but only for small categories. This file provides the same
isomorphism assuming only that the pointwise left Kan extensions along `F` exist and that
the colimits of shape `CostructuredArrow F X` exist in the target
(`CategoryTheory.Functor.lanEvaluationIsoColim'`).

The consequence we are after is `CategoryTheory.preservesFiniteLimits_op_lan_of_flat`: left
Kan extension along the opposite of a representably flat functor is left exact as soon as
the pointwise left Kan extensions exist and filtered colimits of the relevant size are exact
in the target. This is the variant of `CategoryTheory.lan_preservesFiniteLimits_of_flat`
that replaces smallness of the categories and concreteness of the target by AB5 at the
relevant size.

`lanEvaluationIsoColim'` is taken verbatim from the `proetale` dependency
(`Proetale.Topology.Comparison.CohomologyComparison`), which is not otherwise imported here;
the import direction would be the wrong way round and that file is heavy.

The same pointwise description shows that left Kan extension along a representably coflat
functor `L` is strong monoidal for the pointwise tensor products, as soon as the tensor
product of the target preserves the colimits of shape `CostructuredArrow L X` in each
variable. The left Kan extension functor `L.lan` is oplax monoidal, being left adjoint to the
monoidal restriction functor (`CategoryTheory.Functor.lanOplaxMonoidal`), and its comparison
maps are isomorphisms (`CategoryTheory.Functor.isIso_lan_δ`,
`CategoryTheory.Functor.isIso_lan_η`): at `X` they compare two colimits over the filtered,
hence sifted, category `CostructuredArrow L X`.

TODO: upstream `lanEvaluationIsoColim'` to `Mathlib/CategoryTheory/Functor/Flat.lean`,
deriving Mathlib's `lanEvaluationIsoColim` from it (and renaming: the prime is only kept
here to match the copy in `proetale`), then drop this copy and the one in `proetale`.
-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open Limits Opposite

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {H : Type u₃} [Category.{v₃} H]

namespace Functor

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Variant of `CategoryTheory.Functor.lanEvaluationIsoColim` without the smallness
assumptions on the categories involved: the evaluation of `F.lan` at `X` is the colimit
over the costructured arrows over `X`.

```
                            F.lan
       (C ⥤ H) ───────────────────────────────▶ (D ⥤ H)
          │                                        │
  whisker │                                        │ evaluation at `X`
  by proj │                                        │
          ▼                                        ▼
(CostructuredArrow F X ⥤ H) ────────colim────────▶ H
```

Here `whisker by proj` is restriction along `CostructuredArrow.proj F X`.
-/
noncomputable def lanEvaluationIsoColim' (F : C ⥤ D) (X : D)
    [∀ G : C ⥤ H, F.HasPointwiseLeftKanExtension G]
    [HasColimitsOfShape (CostructuredArrow F X) H] :
    F.lan ⋙ (evaluation D H).obj X ≅
      (Functor.whiskeringLeft _ _ H).obj (CostructuredArrow.proj F X) ⋙ colim :=
  NatIso.ofComponents (fun G ↦
    IsColimit.coconePointUniqueUpToIso
      (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit F G X)
      (colimit.isColimit _)) (fun {G₁ G₂} φ ↦ by
    apply (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit F G₁ X).hom_ext
    intro T
    have h₁ := fun (G : C ⥤ H) ↦ IsColimit.comp_coconePointUniqueUpToIso_hom
      (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit F G X) (colimit.isColimit _) T
    have h₂ := congr_app (F.lanUnit.naturality φ) T.left
    dsimp at h₁ h₂ ⊢
    simp only [Category.assoc] at h₁ ⊢
    simp only [Functor.lan, Functor.lanUnit] at h₂ ⊢
    rw [reassoc_of% h₁, NatTrans.naturality_assoc, ← reassoc_of% h₂, h₁,
      ι_colimMap, Functor.whiskerLeft_app]
    rfl)

section Monoidal

open MonoidalCategory

variable (L : C ⥤ D) (H) [MonoidalCategory H]

@[simp]
lemma whiskeringLeft_μ_app (P Q : D ⥤ H) (c : C) :
    (LaxMonoidal.μ ((whiskeringLeft C D H).obj L) P Q).app c = 𝟙 _ :=
  rfl

@[simp]
lemma whiskeringLeft_ε_app (c : C) :
    (LaxMonoidal.ε ((whiskeringLeft C D H).obj L)).app c = 𝟙 _ :=
  rfl

variable [∀ F : C ⥤ H, L.HasPointwiseLeftKanExtension F]

/-- Left Kan extension `L.lan` is oplax monoidal for the pointwise tensor products, being
left adjoint to the monoidal restriction functor along `L`. -/
noncomputable instance lanOplaxMonoidal : (L.lan : (C ⥤ H) ⥤ (D ⥤ H)).OplaxMonoidal :=
  (L.lanAdjunction H).leftAdjointOplaxMonoidal

/-- The adjunction `L.lan ⊣ (whiskeringLeft C D H).obj L` is monoidal. -/
instance isMonoidal_lanAdjunction : (L.lanAdjunction H).IsMonoidal :=
  inferInstanceAs (letI := (L.lanAdjunction H).leftAdjointOplaxMonoidal
    (L.lanAdjunction H).IsMonoidal)

variable {H}

/-- The comparison map `δ : L.lan (P ⊗ Q) ⟶ L.lan P ⊗ L.lan Q` restricts along the units to
the tensor product of the units. -/
@[reassoc (attr := simp)]
lemma lanUnit_app_app_δ_app (P Q : C ⥤ H) (c : C) :
    (L.lanUnit.app (P ⊗ Q)).app c ≫ (OplaxMonoidal.δ L.lan P Q).app (L.obj c) =
      (L.lanUnit.app P).app c ⊗ₘ (L.lanUnit.app Q).app c := by
  simpa using congr_app (Adjunction.unit_app_tensor_comp_map_δ (L.lanAdjunction H) P Q) c

/-- The comparison map `η : L.lan 𝟙 ⟶ 𝟙` restricts along the unit to the identity. -/
@[reassoc (attr := simp)]
lemma lanUnit_app_app_η_app (c : C) :
    (L.lanUnit.app (𝟙_ (C ⥤ H))).app c ≫ (OplaxMonoidal.η (L.lan (H := H))).app (L.obj c) =
      𝟙 _ := by
  simpa using congr_app (Adjunction.unit_app_unit_comp_map_η (L.lanAdjunction H)) c

variable [RepresentablyCoflat L]

/-- For a representably coflat `L`, the comparison map `δ : L.lan (P ⊗ Q) ⟶ L.lan P ⊗ L.lan Q`
is an isomorphism if the tensor product preserves colimits of shape `CostructuredArrow L X` in
each variable: at `X` it compares the colimit of `P ⊗ Q` with the tensor product of the colimits
of `P` and `Q` over the sifted category `CostructuredArrow L X`. -/
instance isIso_lan_δ
    [∀ (X : D) (M : H), PreservesColimitsOfShape (CostructuredArrow L X) (tensorLeft M)]
    [∀ (X : D) (M : H), PreservesColimitsOfShape (CostructuredArrow L X) (tensorRight M)]
    (P Q : C ⥤ H) : IsIso (OplaxMonoidal.δ L.lan P Q) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro X
  have : IsSifted (CostructuredArrow L X) := IsFiltered.isSifted
  have : PreservesColimit₂ (CostructuredArrow.proj L X ⋙ P) (CostructuredArrow.proj L X ⋙ Q)
      (curriedTensor H) :=
    PreservesColimit₂.of_preservesColimits_in_each_variable _
  let φ : (LeftExtension.mk _ (L.leftKanExtensionUnit (P ⊗ Q))).coconeAt X ⟶
      ((LeftExtension.mk _ (L.leftKanExtensionUnit P)).coconeAt X).tensor
        ((LeftExtension.mk _ (L.leftKanExtensionUnit Q)).coconeAt X) :=
    { hom := (OplaxMonoidal.δ L.lan P Q).app X
      w f := by
        change ((L.lanUnit.app (P ⊗ Q)).app f.left ≫ (L.lan.obj (P ⊗ Q)).map f.hom) ≫
            (OplaxMonoidal.δ L.lan P Q).app X =
          ((L.lanUnit.app P).app f.left ≫ (L.lan.obj P).map f.hom) ⊗ₘ
            ((L.lanUnit.app Q).app f.left ≫ (L.lan.obj Q).map f.hom)
        rw [Category.assoc, (OplaxMonoidal.δ L.lan P Q).naturality f.hom,
          lanUnit_app_app_δ_app_assoc]
        exact tensorHom_comp_tensorHom _ _ _ _ }
  have := IsColimit.hom_isIso (L.isPointwiseLeftKanExtensionLeftKanExtensionUnit (P ⊗ Q) X)
    ((L.isPointwiseLeftKanExtensionLeftKanExtensionUnit P X).tensor
      (L.isPointwiseLeftKanExtensionLeftKanExtensionUnit Q X)) φ
  exact (Cocone.forget _).map_isIso φ

/-- For a representably coflat `L`, the comparison map `η : L.lan 𝟙 ⟶ 𝟙` is an isomorphism:
at `X` it is the colimit of a constant functor over the connected category
`CostructuredArrow L X`. -/
instance isIso_lan_η : IsIso (OplaxMonoidal.η (L.lan (H := H))) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro X
  have : IsConnected (CostructuredArrow L X) := IsFiltered.isConnected _
  let φ : (LeftExtension.mk _ (L.leftKanExtensionUnit (𝟙_ (C ⥤ H)))).coconeAt X ⟶
      constCocone (CostructuredArrow L X) (𝟙_ H) :=
    { hom := (OplaxMonoidal.η (L.lan (H := H))).app X
      w f := by
        change ((L.lanUnit.app (𝟙_ (C ⥤ H))).app f.left ≫
            (L.lan.obj (𝟙_ (C ⥤ H))).map f.hom) ≫ (OplaxMonoidal.η (L.lan (H := H))).app X =
          𝟙 (𝟙_ H)
        rw [Category.assoc, (OplaxMonoidal.η (L.lan (H := H))).naturality f.hom,
          lanUnit_app_app_η_app_assoc]
        rfl }
  have := IsColimit.hom_isIso (L.isPointwiseLeftKanExtensionLeftKanExtensionUnit _ X)
    (isColimitConstCocone _ _) φ
  exact (Cocone.forget (CostructuredArrow.proj L X ⋙ 𝟙_ (C ⥤ H))).map_isIso φ

end Monoidal

end Functor

/-- Left Kan extension along the opposite of a representably flat functor `F` is left
exact, provided the pointwise left Kan extensions along `F.op` exist and filtered colimits
of shape the comma categories `CostructuredArrow F.op K` are exact in the target.

This is the variant of `CategoryTheory.lan_preservesFiniteLimits_of_flat` that assumes AB5
at the relevant size instead of smallness of `C` and `D` and concreteness of `H`. -/
instance preservesFiniteLimits_op_lan_of_flat (F : C ⥤ D) [RepresentablyFlat F]
    [∀ G : Cᵒᵖ ⥤ H, F.op.HasPointwiseLeftKanExtension G]
    [HasFiniteLimits H] [HasFilteredColimitsOfSize.{v₁, max u₁ v₂} H]
    [AB5OfSize.{v₁, max u₁ v₂} H] :
    PreservesFiniteLimits (F.op.lan : (Cᵒᵖ ⥤ H) ⥤ (Dᵒᵖ ⥤ H)) := by
  constructor
  intro J _ _
  refine preservesLimitsOfShape_of_evaluation _ _ fun K ↦ ?_
  -- flatness of `F` makes `StructuredArrow (unop K) F` cofiltered, hence
  -- `CostructuredArrow F.op K` filtered, and the Kan extension is pointwise a filtered
  -- colimit, which is exact by AB5
  have : IsFiltered (CostructuredArrow F.op K) :=
    IsFiltered.of_equivalence (structuredArrowOpEquivalence F (unop K))
  exact preservesLimitsOfShape_of_natIso (Functor.lanEvaluationIsoColim' F.op K).symm

end CategoryTheory
