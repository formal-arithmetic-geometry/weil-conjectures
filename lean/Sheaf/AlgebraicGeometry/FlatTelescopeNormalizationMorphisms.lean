/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G2
-/
module

public import Sheaf.AlgebraicGeometry.FlatTelescopeStageMap
public import Sheaf.AlgebraicGeometry.BoundedFlatModelNormalization
import Sheaf.AlgebraicGeometry.FlatTelescopePullbackSumColimit
import Sheaf.AlgebraicGeometry.FlatTelescopeConeNormalizationDescent

/-! # Morphisms extending a bounded normalization

Source: steps 1--3 of lem-sc-flat-telescope-bounded-normalization-extension. -/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated MonoidalCategory
namespace AlgebraicGeometry

private noncomputable def normalizationShiftIso {Z Y : Scheme.{u}} (f : Z ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [Functor.Monoidal (derivedPullback f)]
    (e : (derivedPullback f).obj ((𝟙_ (schemeDerivedCategory Y))⟦(1 : ℤ)⟧) ≅
      (𝟙_ (schemeDerivedCategory Z))⟦(1 : ℤ)⟧)
    (K : schemeDerivedCategory Y) :
    (derivedPullback f).obj (K⟦(1 : ℤ)⟧) ≅ ((derivedPullback f).obj K)⟦(1 : ℤ)⟧ :=
  (derivedPullback f).mapIso (schemeCanonicalShiftUnitIso Y K).symm ≪≫
    asIso (Functor.OplaxMonoidal.δ (derivedPullback f)
      ((𝟙_ (schemeDerivedCategory Y))⟦(1 : ℤ)⟧) K) ≪≫
    tensorIso e (Iso.refl _) ≪≫ schemeCanonicalShiftUnitIso Z ((derivedPullback f).obj K)

private theorem unit_shift_naturality (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    {K N : schemeDerivedCategory X} (b : K ⟶ N) :
    (schemeCanonicalShiftUnitIso X K).hom ≫ b⟦(1 : ℤ)⟧' =
      ((𝟙_ (schemeDerivedCategory X))⟦(1 : ℤ)⟧) ◁ b ≫
        (schemeCanonicalShiftUnitIso X N).hom := by
  let := schemeCanonicalTensorShift X
  let : ∀ M : schemeDerivedCategory X, (tensorRight M).CommShift ℤ :=
    fun M ↦ Functor.CommShift₂.commShiftFlipObj (h := .int) M
  have : NatTrans.CommShift ((curriedTensor (schemeDerivedCategory X)).flip.map b) ℤ :=
    Functor.CommShift₂.commShift_flip_map (h := .int) b
  dsimp [schemeCanonicalShiftUnitIso]
  simp only [Category.assoc]
  rw [← Functor.map_comp, ← leftUnitor_naturality, Functor.map_comp]
  simpa only [Category.assoc, tensorRight, Functor.flip, curriedTensor] using
    congrArg (fun g ↦ g ≫ (shiftFunctor (schemeDerivedCategory X) (1 : ℤ)).map (λ_ N).hom)
      (NatTrans.shift_app_comm ((curriedTensor (schemeDerivedCategory X)).flip.map b)
        (1 : ℤ) (𝟙_ (schemeDerivedCategory X)))

private theorem unit_shift_inv_naturality (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    {K N : schemeDerivedCategory X} (b : K ⟶ N) :
    b⟦(1 : ℤ)⟧' ≫ (schemeCanonicalShiftUnitIso X N).inv =
      (schemeCanonicalShiftUnitIso X K).inv ≫
        ((𝟙_ (schemeDerivedCategory X))⟦(1 : ℤ)⟧) ◁ b := by
  apply (cancel_epi (schemeCanonicalShiftUnitIso X K).hom).1
  rw [← Category.assoc, unit_shift_naturality]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]

private theorem normalizationShift_naturality {Z Y : Scheme.{u}} (f : Z ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [Functor.Monoidal (derivedPullback f)]
    (e : (derivedPullback f).obj ((𝟙_ (schemeDerivedCategory Y))⟦(1 : ℤ)⟧) ≅
      (𝟙_ (schemeDerivedCategory Z))⟦(1 : ℤ)⟧)
    {K N : schemeDerivedCategory Y} (b : K ⟶ N) :
    (derivedPullback f).map (b⟦(1 : ℤ)⟧') ≫
        (normalizationShiftIso f e N).hom =
      (normalizationShiftIso f e K).hom ≫
        ((derivedPullback f).map b)⟦(1 : ℤ)⟧' := by
  dsimp only [normalizationShiftIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, asIso_hom]
  simp only [tensorIso, Iso.refl_hom, tensorHom_def, whiskerLeft_id,
    Category.comp_id, Category.assoc]
  rw [← (derivedPullback f).map_comp_assoc, unit_shift_inv_naturality,
    Functor.map_comp_assoc, ← Functor.OplaxMonoidal.δ_natural_right_assoc]
  rw [whisker_exchange_assoc, ← unit_shift_naturality]


private noncomputable def quotientNormalizationShiftIso
    {Z Y : Scheme.{u}} (f : Z ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [Functor.Monoidal (derivedPullback f)]
    (e : (derivedPullback f).obj ((𝟙_ (schemeDerivedCategory Y))⟦(1 : ℤ)⟧) ≅
      (𝟙_ (schemeDerivedCategory Z))⟦(1 : ℤ)⟧)
    (X : HomotopyCategory (SheafOfModules.{u} (moduleRings Y.toRingedSpace))
      (ComplexShape.up ℤ)) :=
    (derivedPullback f).mapIso ((DerivedCategory.Qh.commShiftIso (1 : ℤ)).app X) ≪≫
      normalizationShiftIso f e (DerivedCategory.Qh.obj X)

private theorem quotientNormalizationShift_naturality
    {Z Y : Scheme.{u}} (f : Z ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [Functor.Monoidal (derivedPullback f)]
    (e : (derivedPullback f).obj ((𝟙_ (schemeDerivedCategory Y))⟦(1 : ℤ)⟧) ≅
      (𝟙_ (schemeDerivedCategory Z))⟦(1 : ℤ)⟧)
    {X X' : HomotopyCategory (SheafOfModules.{u} (moduleRings Y.toRingedSpace))
      (ComplexShape.up ℤ)} (i : X ⟶ X') :
    (DerivedCategory.Qh ⋙ derivedPullback f).map (i⟦(1 : ℤ)⟧') ≫
        (quotientNormalizationShiftIso f e X').hom =
      (quotientNormalizationShiftIso f e X).hom ≫
        ((DerivedCategory.Qh ⋙ derivedPullback f).map i)⟦(1 : ℤ)⟧' := by
  dsimp only [quotientNormalizationShiftIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.app_hom, Functor.comp_map]
  rw [← (derivedPullback f).map_comp_assoc,
    DerivedCategory.Qh.commShiftIso_hom_naturality,
    (derivedPullback f).map_comp_assoc, normalizationShift_naturality]
  simp only [Category.assoc]

private theorem sum_comparison_naturality
    {C D : Type*} [Category C] [Category D] (L G : C ⥤ D)
    {E E' : ℕ → C} {S S' : C} (i : ∀ n, E n ⟶ S) (i' : ∀ n, E' n ⟶ S')
    (a : ∀ n, E n ⟶ E' n) (m : S ⟶ S')
    (hi : ∀ n, i n ≫ m = a n ≫ i' n)
    (β : ∀ n, L.obj (E n) ⟶ G.obj (E n))
    (β' : ∀ n, L.obj (E' n) ⟶ G.obj (E' n))
    (hβ : ∀ n, L.map (a n) ≫ β' n = β n ≫ G.map (a n))
    (σ : L.obj S ⟶ G.obj S) (σ' : L.obj S' ⟶ G.obj S')
    (hσ : ∀ n, L.map (i n) ≫ σ = β n ≫ G.map (i n))
    (hσ' : ∀ n, L.map (i' n) ≫ σ' = β' n ≫ G.map (i' n))
    (hc : IsColimit (Cofan.mk (L.obj S) (fun n ↦ L.map (i n)))) :
    L.map m ≫ σ' = σ ≫ G.map m := by
  apply Cofan.IsColimit.hom_ext hc
  intro n
  change L.map (i n) ≫ _ = L.map (i n) ≫ _
  calc
    L.map (i n) ≫ (L.map m ≫ σ') = L.map (a n) ≫ (L.map (i' n) ≫ σ') := by
      rw [← L.map_comp_assoc, hi n, L.map_comp_assoc]
    _ = L.map (a n) ≫ (β' n ≫ G.map (i' n)) := by rw [hσ' n]
    _ = β n ≫ (G.map (a n) ≫ G.map (i' n)) := by
      rw [← Category.assoc, hβ n, Category.assoc]
    _ = β n ≫ (G.map (i n) ≫ G.map m) := by
      rw [← G.map_comp, ← hi n, G.map_comp]
    _ = L.map (i n) ≫ (σ ≫ G.map m) := by
      simpa only [Category.assoc] using
        congrArg (fun g ↦ g ≫ G.map m) (hσ n).symm

private theorem sum_comparison_shift
    {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
    (L G : C ⥤ D) [G.CommShift ℤ]
    {E : ℕ → C} {S : C} (i : ∀ n, E n ⟶ S)
    (b : ∀ X, L.obj (X⟦(1 : ℤ)⟧) ⟶ (L.obj X)⟦(1 : ℤ)⟧)
    (hbn : ∀ n, L.map ((i n)⟦(1 : ℤ)⟧') ≫ b S = b (E n) ≫ (L.map (i n))⟦(1 : ℤ)⟧')
    (β₀ : ∀ n, L.obj (E n) ⟶ G.obj (E n))
    (β₁ : ∀ n, L.obj ((E n)⟦(1 : ℤ)⟧) ⟶ G.obj ((E n)⟦(1 : ℤ)⟧))
    (hβ : ∀ n, β₁ n ≫ (G.commShiftIso (1 : ℤ)).hom.app (E n) =
      b (E n) ≫ (β₀ n)⟦(1 : ℤ)⟧')
    (σ₀ : L.obj S ⟶ G.obj S)
    (σ₁ : L.obj (S⟦(1 : ℤ)⟧) ⟶ G.obj (S⟦(1 : ℤ)⟧))
    (hσ₀ : ∀ n, L.map (i n) ≫ σ₀ = β₀ n ≫ G.map (i n))
    (hσ₁ : ∀ n, L.map ((i n)⟦(1 : ℤ)⟧') ≫ σ₁ =
      β₁ n ≫ G.map ((i n)⟦(1 : ℤ)⟧'))
    (hc : IsColimit (Cofan.mk (L.obj (S⟦(1 : ℤ)⟧))
      (fun n ↦ L.map ((i n)⟦(1 : ℤ)⟧')))) :
    σ₁ ≫ (G.commShiftIso (1 : ℤ)).hom.app S = b S ≫ σ₀⟦(1 : ℤ)⟧' := by
  apply Cofan.IsColimit.hom_ext hc
  intro n
  change L.map ((i n)⟦(1 : ℤ)⟧') ≫ _ = L.map ((i n)⟦(1 : ℤ)⟧') ≫ _
  calc
    L.map ((i n)⟦(1 : ℤ)⟧') ≫ (σ₁ ≫ (G.commShiftIso (1 : ℤ)).hom.app S) =
        β₁ n ≫ (G.map ((i n)⟦(1 : ℤ)⟧') ≫
          (G.commShiftIso (1 : ℤ)).hom.app S) := by
            rw [← Category.assoc, hσ₁ n, Category.assoc]
    _ = β₁ n ≫ ((G.commShiftIso (1 : ℤ)).hom.app (E n) ≫
        (G.map (i n))⟦(1 : ℤ)⟧') := by rw [G.commShiftIso_hom_naturality]
    _ = b (E n) ≫ ((β₀ n)⟦(1 : ℤ)⟧' ≫ (G.map (i n))⟦(1 : ℤ)⟧') := by
      rw [← Category.assoc, hβ n, Category.assoc]
    _ = b (E n) ≫ ((L.map (i n))⟦(1 : ℤ)⟧' ≫ σ₀⟦(1 : ℤ)⟧') := by
      rw [← Functor.map_comp, ← hσ₀ n, Functor.map_comp]
    _ = L.map ((i n)⟦(1 : ℤ)⟧') ≫ (b S ≫ σ₀⟦(1 : ℤ)⟧') := by
      simpa only [Category.assoc] using
        congrArg (fun g ↦ g ≫ σ₀⟦(1 : ℤ)⟧') (hbn n).symm

/-- Construct the forward comparison maps on telescope representatives; this
assertion does not supply inverse maps or assert invertibility.

Source: steps 1--3 of lem-sc-flat-telescope-bounded-normalization-extension,
Stacks Tags 06YS and 06YJ for the models; the normalization is the inherited
agent expansion, not an assertion of those tags.

Proof. On a bounded-flat tower take the sum of the supplied beta morphisms.
Compute derived pullback on the K-flat sum and use the termwise-pullback
coproduct comparison. Bounded naturality intertwines one minus transition.
On the transition cone use this map and its translate. The bounded shift
identity makes the connecting component commute with the differential, giving
the forward cone comparison. Apply the same formulas to maps of towers.
Compare presentations through the common flat arrow-diagram refinement:
precomposition with its localized augmentation is invertible, so cancellation
identifies the transported forward maps. This gives the stated stage naturality.
For a presentation that is also bounded-flat, bounded naturality applied to
its augmentation identifies the result with beta. The cone shift calculation
is the sum of the bounded shift identities, with exactly the supplied e.
Zero towers use zero maps, and the upper bound is allowed to vary with the stage.
No inverse map is constructed in this argument.
(blueprint: lem-sc-flat-telescope-normalization-morphisms). -/
theorem exists_flat_telescope_normalization_morphisms
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y] (f : Z ⟶ Y) [IsProper f]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [Functor.Monoidal (derivedPullback f)]
    [(Scheme.Modules.tensorPullback f).Additive]
    (e : (derivedPullback f).obj ((𝟙_ (schemeDerivedCategory Y))⟦(1 : ℤ)⟧) ≅
        (𝟙_ (schemeDerivedCategory Z))⟦(1 : ℤ)⟧)
    (β : ∀ X : HomotopyCategory
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ),
        boundedFlatShiftRepresentative Y X →
          ((DerivedCategory.Qh ⋙ derivedPullback f).obj X ≅
            ((Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
              (DerivedCategory.Qh : HomotopyCategory
                (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
                schemeDerivedCategory Z)).obj X))
    (hβnat : (∀ (X X' : HomotopyCategory
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ))
          (hX : boundedFlatShiftRepresentative Y X) (hX' : boundedFlatShiftRepresentative Y X')
          (s : X ⟶ X'),
          (DerivedCategory.Qh ⋙ derivedPullback f).map s ≫ (β X' hX').hom =
            (β X hX).hom ≫
              ((Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
                (DerivedCategory.Qh : HomotopyCategory
                  (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
                  schemeDerivedCategory Z)).map s))
    (hβshift : ∀ (P : CochainComplex
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
        (hb : ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (P.X i))
        (hf : ∀ i : ℤ, SheafOfModules.IsFlat (P.X i)),
        let X := (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P
        let G := (Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          (DerivedCategory.Qh : HomotopyCategory
            (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
            schemeDerivedCategory Z)
        (β (X⟦(1 : ℤ)⟧) ⟨P, hb, hf, Or.inr rfl⟩).hom ≫
            (G.commShiftIso (1 : ℤ)).hom.app X =
          (derivedPullback f).map ((DerivedCategory.Qh.commShiftIso (1 : ℤ)).hom.app X) ≫
            ((derivedPullback f).mapIso
                (schemeCanonicalShiftUnitIso Y (DerivedCategory.Qh.obj X)).symm ≪≫
              asIso (Functor.OplaxMonoidal.δ (derivedPullback f)
                ((𝟙_ (schemeDerivedCategory Y))⟦(1 : ℤ)⟧) (DerivedCategory.Qh.obj X)) ≪≫
              tensorIso e (Iso.refl _) ≪≫
              schemeCanonicalShiftUnitIso Z
                ((derivedPullback f).obj (DerivedCategory.Qh.obj X))).hom ≫
            (β X ⟨P, hb, hf, Or.inl rfl⟩).hom⟦(1 : ℤ)⟧') :
      ∃ α : ∀ X : HomotopyCategory
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ),
        flatTelescopeShiftRepresentative Y X →
          ((DerivedCategory.Qh ⋙ derivedPullback f).obj X ⟶
            ((Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
              (DerivedCategory.Qh : HomotopyCategory
                (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
                schemeDerivedCategory Z)).obj X),
        (∀ (X X' : HomotopyCategory
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ))
          (hX : flatTelescopeShiftRepresentative Y X) (hX' : flatTelescopeShiftRepresentative Y X')
          (s : X ⟶ X'), flatTelescopeStageMap Y s →
          (DerivedCategory.Qh ⋙ derivedPullback f).map s ≫ (α X' hX') =
            (α X hX) ≫
              ((Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
                (DerivedCategory.Qh : HomotopyCategory
                  (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
                  schemeDerivedCategory Z)).map s) ∧
        (∀ (X : HomotopyCategory
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ))
          (hX : flatTelescopeShiftRepresentative Y X)
          (hb : boundedFlatShiftRepresentative Y X), α X hX = (β X hb).hom) ∧
        ∀ (P : CochainComplex
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
        (htel : isFlatTelescope Y P),
        let X := (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P
        let G := (Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          (DerivedCategory.Qh : HomotopyCategory
            (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
            schemeDerivedCategory Z)
        (α (X⟦(1 : ℤ)⟧) ⟨P, htel, Or.inr rfl⟩) ≫
            (G.commShiftIso (1 : ℤ)).hom.app X =
          (derivedPullback f).map ((DerivedCategory.Qh.commShiftIso (1 : ℤ)).hom.app X) ≫
            ((derivedPullback f).mapIso
                (schemeCanonicalShiftUnitIso Y (DerivedCategory.Qh.obj X)).symm ≪≫
              asIso (Functor.OplaxMonoidal.δ (derivedPullback f)
                ((𝟙_ (schemeDerivedCategory Y))⟦(1 : ℤ)⟧) (DerivedCategory.Qh.obj X)) ≪≫
              tensorIso e (Iso.refl _) ≪≫
              schemeCanonicalShiftUnitIso Z
                ((derivedPullback f).obj (DerivedCategory.Qh.obj X))).hom ≫
            (α X ⟨P, htel, Or.inl rfl⟩)⟦(1 : ℤ)⟧' := by
  classical
  let A := SheafOfModules.{u} (moduleRings Y.toRingedSpace)
  have : HasColimitsOfShape (Discrete ℕ) (CochainComplex A ℤ) := inferInstance
  let q := HomotopyCategory.quotient A (ComplexShape.up ℤ)
  let L : HomotopyCategory A (ComplexShape.up ℤ) ⥤ schemeDerivedCategory Z :=
    DerivedCategory.Qh ⋙ derivedPullback f
  let G := (Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    (DerivedCategory.Qh : HomotopyCategory
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
      schemeDerivedCategory Z)
  let hbStage := fun (E : ℕ → CochainComplex A ℤ)
    (hb : ∀ n : ℕ, ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero ((E n).X i))
    (hf : ∀ (n : ℕ) (i : ℤ), SheafOfModules.IsFlat ((E n).X i)) (n : ℕ) ↦
      (show boundedFlatShiftRepresentative Y (q.obj (E n)) from
        ⟨E n, hb n, hf n, Or.inl rfl⟩)
  let hbStage₁ := fun (E : ℕ → CochainComplex A ℤ)
    (hb : ∀ n : ℕ, ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero ((E n).X i))
    (hf : ∀ (n : ℕ) (i : ℤ), SheafOfModules.IsFlat ((E n).X i)) (n : ℕ) ↦
      (show boundedFlatShiftRepresentative Y ((q.obj (E n))⟦(1 : ℤ)⟧) from
        ⟨E n, hb n, hf n, Or.inr rfl⟩)
  let hc₀ (E : ℕ → CochainComplex A ℤ) :
      IsColimit (Cofan.mk (L.obj (q.obj (∐ E)))
        (fun n ↦ L.map (q.map (Sigma.ι E n)))) :=
    (flat_telescope_pullback_sum_colimit f E).1.some
  let hc₁ (E : ℕ → CochainComplex A ℤ) :
      IsColimit (Cofan.mk (L.obj ((q.obj (∐ E))⟦(1 : ℤ)⟧))
        (fun n ↦ L.map ((q.map (Sigma.ι E n))⟦(1 : ℤ)⟧'))) :=
    (flat_telescope_pullback_sum_colimit f E).2.some
  let σ₀ := fun E hb hf ↦ (show L.obj (q.obj (∐ E)) ⟶ G.obj (q.obj (∐ E)) from
    Cofan.IsColimit.desc (hc₀ E)
    (fun n ↦ (β (q.obj (E n)) (hbStage E hb hf n)).hom ≫
      G.map (q.map (Sigma.ι E n))))
  let σ₁ := fun E hb hf ↦ (show L.obj ((q.obj (∐ E))⟦(1 : ℤ)⟧) ⟶
      G.obj ((q.obj (∐ E))⟦(1 : ℤ)⟧) from Cofan.IsColimit.desc (hc₁ E)
    (fun n ↦ (β ((q.obj (E n))⟦(1 : ℤ)⟧) (hbStage₁ E hb hf n)).hom ≫
      G.map ((q.map (Sigma.ι E n))⟦(1 : ℤ)⟧')))
  have hι₀ (E : ℕ → CochainComplex A ℤ) hb hf (n : ℕ) :
      L.map (q.map (Sigma.ι E n)) ≫ σ₀ E hb hf =
        (β (q.obj (E n)) (hbStage E hb hf n)).hom ≫ G.map (q.map (Sigma.ι E n)) :=
    Cofan.IsColimit.fac (hc₀ E) _ n
  have hι₁ (E : ℕ → CochainComplex A ℤ) hb hf (n : ℕ) :
      L.map ((q.map (Sigma.ι E n))⟦(1 : ℤ)⟧') ≫ σ₁ E hb hf =
        (β ((q.obj (E n))⟦(1 : ℤ)⟧) (hbStage₁ E hb hf n)).hom ≫
          G.map ((q.map (Sigma.ι E n))⟦(1 : ℤ)⟧') :=
    Cofan.IsColimit.fac (hc₁ E) _ n
  have hnat₀ (E E' : ℕ → CochainComplex A ℤ) hb hf hb' hf'
      (a : ∀ n : ℕ, E n ⟶ E' n) :
      L.map (q.map (Limits.Sigma.map a)) ≫ σ₀ E' hb' hf' =
        σ₀ E hb hf ≫ G.map (q.map (Limits.Sigma.map a)) := by
    apply sum_comparison_naturality L G (fun n ↦ q.map (Sigma.ι E n)) (fun n ↦ q.map (Sigma.ι E' n))
      (fun n ↦ q.map (a n)) (q.map (Limits.Sigma.map a)) _
      (fun n ↦ (β (q.obj (E n)) (hbStage E hb hf n)).hom)
      (fun n ↦ (β (q.obj (E' n)) (hbStage E' hb' hf' n)).hom)
      (fun n ↦ hβnat _ _ (hbStage E hb hf n) (hbStage E' hb' hf' n) (q.map (a n)))
      (σ₀ E hb hf) (σ₀ E' hb' hf') (hι₀ E hb hf) (hι₀ E' hb' hf') (hc₀ E)
    intro n
    rw [← q.map_comp, ← q.map_comp, Limits.Sigma.ι_map]
  have hnat₁ (E E' : ℕ → CochainComplex A ℤ) hb hf hb' hf'
      (a : ∀ n : ℕ, E n ⟶ E' n) :
      L.map ((q.map (Limits.Sigma.map a))⟦(1 : ℤ)⟧') ≫ σ₁ E' hb' hf' =
        σ₁ E hb hf ≫ G.map ((q.map (Limits.Sigma.map a))⟦(1 : ℤ)⟧') := by
    apply sum_comparison_naturality L G
      (fun n ↦ (q.map (Sigma.ι E n))⟦(1 : ℤ)⟧')
      (fun n ↦ (q.map (Sigma.ι E' n))⟦(1 : ℤ)⟧')
      (fun n ↦ (q.map (a n))⟦(1 : ℤ)⟧') ((q.map (Limits.Sigma.map a))⟦(1 : ℤ)⟧') _
      (fun n ↦ (β ((q.obj (E n))⟦(1 : ℤ)⟧) (hbStage₁ E hb hf n)).hom)
      (fun n ↦ (β ((q.obj (E' n))⟦(1 : ℤ)⟧) (hbStage₁ E' hb' hf' n)).hom)
      (fun n ↦ hβnat _ _ (hbStage₁ E hb hf n) (hbStage₁ E' hb' hf' n) ((q.map (a n))⟦(1 : ℤ)⟧'))
      (σ₁ E hb hf) (σ₁ E' hb' hf') (hι₁ E hb hf) (hι₁ E' hb' hf') (hc₁ E)
    intro n
    simp only [← Functor.map_comp, Limits.Sigma.ι_map]
  let b := quotientNormalizationShiftIso f e
  have hshift (E : ℕ → CochainComplex A ℤ) hb hf :
      σ₁ E hb hf ≫ (G.commShiftIso (1 : ℤ)).hom.app (q.obj (∐ E)) =
        (b (q.obj (∐ E))).hom ≫ (σ₀ E hb hf)⟦(1 : ℤ)⟧' := by
    apply sum_comparison_shift L G (fun n ↦ q.map (Sigma.ι E n))
      (fun X ↦ (b X).hom)
      (fun n ↦ quotientNormalizationShift_naturality f e (q.map (Sigma.ι E n)))
      (fun n ↦ (β (q.obj (E n)) (hbStage E hb hf n)).hom)
      (fun n ↦ (β ((q.obj (E n))⟦(1 : ℤ)⟧) (hbStage₁ E hb hf n)).hom) _
      (σ₀ E hb hf) (σ₁ E hb hf) (hι₀ E hb hf) (hι₁ E hb hf) (hc₁ E)
    intro n
    simpa only [b, quotientNormalizationShiftIso, normalizationShiftIso,
      Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Category.assoc] using
      hβshift (E n) (hb n) (hf n)
  apply exists_flat_telescope_cone_normalization_descent f e β hβnat σ₀ σ₁
    hι₀ hι₁ hnat₀ hnat₁
  intro E hb hf
  simpa only [b, quotientNormalizationShiftIso, normalizationShiftIso,
    Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Category.assoc] using hshift E hb hf

end AlgebraicGeometry
