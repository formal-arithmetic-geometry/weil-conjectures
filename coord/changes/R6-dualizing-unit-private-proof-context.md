# DualizingUnitComposite private proof context

## Reason

The three original theorem holes are proved using a general projection-unit calculation
and two specializations to etale derived categories. The private helpers use a new universe
and a local section of coefficient-category variables. Preflight classifies these commands
as a proof-context change requiring this record. All existing declaration signatures,
public imports and definitions remain verbatim. No instance or attribute is added.
The transparency option is scoped to the single private naturality theorem.

## Old

The original context preceding the existing namespace, verbatim:

```lean
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor

```

## New

The replacement context and fully proved private helpers, verbatim:

```lean
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor

/-- A right-unital projection has the canonical tensor transpose at the unit.
This is the unit/counit calculation used in Step 1
(blueprint: lem-pur-dualizing-unit-composite). -/
private theorem projection_tensor_unit
    {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] [MonoidalCategory D]
    {F : D ⥤ C} {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    (π : ∀ (M : C) (N : D), L.obj M ⊗ N ⟶ L.obj (M ⊗ F.obj N))
    [∀ M N, IsIso (π M N)] (u : F.obj (𝟙_ D) ≅ 𝟙_ C)
    (hπ : π (R.obj (𝟙_ D)) (𝟙_ D) ≫
      L.map (R.obj (𝟙_ D) ◁ u.hom ≫ (ρ_ (R.obj (𝟙_ D))).hom) =
        (ρ_ (L.obj (R.obj (𝟙_ D)))).hom) :
    adj.projectionTensorMap π (𝟙_ D) (𝟙_ D) ≫ R.map (λ_ (𝟙_ D)).hom =
      R.obj (𝟙_ D) ◁ u.hom ≫ (ρ_ (R.obj (𝟙_ D))).hom := by
  apply Adjunction.ext_of_comp_counit (adj := adj)
  rw [Functor.map_comp, Category.assoc]
  erw [adj.counit_naturality]
  rw [Adjunction.map_projectionTensorMap_comp_counit_assoc]
  apply (cancel_epi (π (R.obj (𝟙_ D)) (𝟙_ D))).1
  simp only [IsIso.hom_inv_id_assoc]
  rw [← Category.assoc, hπ]
  simpa only [Functor.comp_obj, Functor.id_obj, unitors_equal] using
    (rightUnitor_naturality (adj.counit.app (𝟙_ D)))

universe uA
section TensorHelpers
open AlgebraicGeometry.Etale
open scoped AlgebraicGeometry.Etale
variable {A : Type uA} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [Etale.UpperStarPreservesFlat A]
  {FC : A → A → Type (u + 1)} {CC : A → Type (u + 1)}
  [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
  {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] [(R(f)_![A]).IsLeftAdjoint]
  [IsIso (projectionMap A f)]

/-- Specialize the formal unit calculation to the published etale projection.
Source: Step 1 (blueprint: lem-pur-dualizing-unit-composite). -/
private theorem tensor_unit :
    dualizingComplexTensorMapOfIsIso f (𝟙_ _) =
      (dualizingComplex A f) ◁ (leftDerivedUpperStarUnitIso A f).hom ≫
        (ρ_ (dualizingComplex A f)).hom := by
  exact projection_tensor_unit (rightDerivedUpperShriekAdjunction A f)
    (fun M N ↦ ((projectionMap A f).app M).app N)
    (leftDerivedUpperStarUnitIso A f) (projectionMap_rightUnitality A f _)

set_option backward.isDefEq.respectTransparency false in
/-- Naturality of the specified transpose in its coefficient input.
Source: Step 1 (blueprint: lem-pur-dualizing-unit-composite). -/
private theorem tensor_naturality
    {K L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)} (v : K ⟶ L) :
    (dualizingComplex A f) ◁ (L((f)^*[A])).map v ≫
        dualizingComplexTensorMapOfIsIso f L =
      dualizingComplexTensorMapOfIsIso f K ≫ (R(f)^![A]).map v := by
  have hn := (rightDerivedUpperShriekAdjunction A f).projectionTensorMap_naturality_right
    (fun M N ↦ ((projectionMap A f).app M).app N)
    (fun M _ _ v ↦ ((projectionMap A f).app M).naturality v) (𝟙_ _) v
  dsimp only [dualizingComplexTensorMapOfIsIso, rightDerivedUpperShriekTensorMap, dualizingComplex]
  rw [← Category.assoc, hn, Category.assoc, ← Functor.map_comp,
    leftUnitor_naturality, Functor.map_comp, Category.assoc]

end TensorHelpers

```

## Users

`python3 tools/downstream.py Sheaf.Paper.DualizingUnitComposite` reports zero downstream
modules. A textual search also finds no external use of the three theorem names. Existing
DAG parents continue to use this item; no parent dependency or unit route changes.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.DualizingUnitComposite | R6 | Three theorem proofs completed; private proof context only. |

No consumer adaptation is required. No target statement or definition changes, so no target
meaning review is reopened.

## Status

landed 20261022T144121-L-1501506 2026-10-22 (merge of deliver/R6/Sheaf.Paper.DualizingUnitComposite)
