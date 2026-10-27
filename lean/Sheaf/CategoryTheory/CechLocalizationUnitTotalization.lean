/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N6
-/
module


public import Sheaf.CategoryTheory.CechLocalizationUnitModels
import Sheaf.CategoryTheory.CechPushforwardAugmentedFamily
import Sheaf.CategoryTheory.ExactUnitAugmentedFamily

/-! # The closed-localization unit under nonnegative Cech descent

Source: main-20261015, direct-images.proof.md (3); Stacks Tags 03FC, 015J and 015F.
(blueprint: lem-sfb-cech-localization-unit-totalization).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w uP vP uA vA wA uB vB wB

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.CechLocalizationUnit

private theorem map_square_then {A B : Type*} [Category A] [Category B]
    (L : A ⥤ B) {X Y X' Y' : A} {Z W : B}
    (f : X ⟶ Y) (a : X ⟶ X') (b : Y ⟶ Y') (g : X' ⟶ Y')
    (r : L.obj X' ⟶ Z) (s : L.obj Y' ⟶ W) (k : Z ⟶ W)
    (h : f ≫ b = a ≫ g) (j : L.map g ≫ s = r ≫ k) :
    L.map f ≫ (L.map b ≫ s) = (L.map a ≫ r) ≫ k := by
  rw [← L.map_comp_assoc, h, L.map_comp, Category.assoc, j, Category.assoc]

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

set_option linter.unusedVariables false in
/-- The specified exact-adjunction unit is preserved by augmented nonnegative Cech descent,
by derived direct images, and by exact restriction to an object of B's site.

Source: main-20261015 direct-images.proof.md (3), the agent-formulated first-quadrant
input preceding the root-tower calculation; Stacks 03FC, 015J, 015F, 09T5, 0D6E,
03DJ and 04IX (blueprint: lem-sfb-cech-localization-unit-totalization).

Proof: Resolve N functorially in nonnegative degrees. Apply the Cech slice direct-image
functors to that resolution. Use D.image and its specified localization adjunctions, with
D.unit fixing D.augmentation to restriction of sections. D.augmentation_naturality
fixes compatibility with every nerve and refinement map. Injective sheaves have acyclic
augmented Cech complexes,
so its finite-diagonal total is a quasi-isomorphism (03FC). Apply f_* and the
nonnegative derived-totalization comparison, normalized at that augmentation (015J).
Exactness of f^* and the slice inverse images identifies the columns with R(f v_n)_*
by the adjunction-normalized composition comparison (09T5, 0D6E). Apply the exact
H termwise. Naturality of the specified unit on every finite biproduct inclusion
identifies eta on the total with the total of eta on the columns, with the same signs.
Resolve both resulting diagrams compatibly in nonnegative degrees before applying g_*;
015J applied to their strict unit map gives the commuting square. Apply exact t^*;
it preserves each finite diagonal. These constructions commute with all coefficient
maps, all Cech operators and all cover refinements, giving the natural isomorphisms
recorded in Comparison. Their augmentation equations retain the original restriction
of sections. Finally apply the exact overFunctor on B at U (03DJ, 04IX) to the whole
square, with the pulled-back coefficient ring. This is precisely the restriction of
the original specified unit, and uses no sliced version of the arbitrary h adjunction.
All complexes used for totalization are nonnegative; no unbounded product is used. -/
theorem cech_localization_unit_totalization
    {CX CV CY CZ CB : Type u}
    [SmallCategory CX] [SmallCategory CV] [SmallCategory CY]
    [SmallCategory CZ] [SmallCategory CB]
    {JX : GrothendieckTopology CX} {JV : GrothendieckTopology CV}
    {JY : GrothendieckTopology CY} {JZ : GrothendieckTopology CZ}
    {JB : GrothendieckTopology CB}
    (RX : Sheaf JX CommRingCat.{u}) (RV : Sheaf JV CommRingCat.{u})
    (RY : Sheaf JY CommRingCat.{u}) (RZ : Sheaf JZ CommRingCat.{u})
    (RB : Sheaf JB CommRingCat.{u})
    [IsGrothendieckAbelian.{u} (Modules RX)] [IsGrothendieckAbelian.{u} (Modules RV)]
    [IsGrothendieckAbelian.{u} (Modules RY)] [IsGrothendieckAbelian.{u} (Modules RZ)]
    [IsGrothendieckAbelian.{u} (Modules RB)]
    [HasDerivedCategory.{u + 1} (Modules RX)] [HasDerivedCategory.{u + 1} (Modules RV)]
    [HasDerivedCategory.{u + 1} (Modules RY)] [HasDerivedCategory.{u + 1} (Modules RZ)]
    [HasDerivedCategory.{u + 1} (Modules RB)]
    (f : RingedToposMorphism
      ((sheafCompose JX (forget₂ CommRingCat RingCat)).obj RX)
      ((sheafCompose JV (forget₂ CommRingCat RingCat)).obj RV))
    (g : RingedToposMorphism
      ((sheafCompose JV (forget₂ CommRingCat RingCat)).obj RV)
      ((sheafCompose JY (forget₂ CommRingCat RingCat)).obj RY))
    (t : RingedToposMorphism
      ((sheafCompose JB (forget₂ CommRingCat RingCat)).obj RB)
      ((sheafCompose JY (forget₂ CommRingCat RingCat)).obj RY))
    (fInverse : Modules RV ⥤ Modules RX) [fInverse.Additive]
    [PreservesFiniteLimits fInverse] [PreservesFiniteColimits fInverse]
    (fAdj : fInverse ⊣ f.modules)
    (gInverse : Modules RY ⥤ Modules RV) [gInverse.Additive]
    [PreservesFiniteLimits gInverse] [PreservesFiniteColimits gInverse]
    (gAdj : gInverse ⊣ g.modules)
    (tInverse : Modules RY ⥤ Modules RB) [tInverse.Additive]
    [PreservesFiniteLimits tInverse] [PreservesFiniteColimits tInverse]
    (tAdj : tInverse ⊣ t.modules)
    (hInverse : Modules RV ⥤ Modules RZ) (hDirect : Modules RZ ⥤ Modules RV)
    [hInverse.Additive] [hDirect.Additive]
    [PreservesFiniteLimits hInverse] [PreservesFiniteColimits hInverse]
    [PreservesFiniteLimits hDirect] [PreservesFiniteColimits hDirect]
    (hAdj : hInverse ⊣ hDirect)
    {P : Type uP} [Category.{vP} P]
    (V : Pᵒᵖ ⥤ Sheaf JX (Type u)) (N : P ⥤ Modules RX)
    (cover : ∀ p : P, Epi (terminal.from (V.obj (op p))))
    (D : CoherentCechImageModel ((sheafCompose JX (forget₂ CommRingCat RingCat)).obj RX)) :
    ∃ (c : Comparison RX D f.modules g.modules tInverse
      (hInverse ⋙ hDirect) hAdj.unit V N),
      ∀ U : CB,
        Comparison.Restricts RX D f.modules g.modules tInverse
          (hInverse ⋙ hDirect) hAdj.unit V N c (restrictDerived RB U) := by
  classical
  let := gAdj.isRightAdjoint
  obtain ⟨b⟩ := cech_pushforward_augmented_family RX RV f fInverse fAdj V N cover D
  let M := N ⋙ DerivedCategory.singleFunctor (Modules RX) 0 ⋙ f.modules.rightDerivedFunctor
  obtain ⟨d⟩ := exact_unit_augmented_family g.modules tInverse
    (hInverse ⋙ hDirect) hAdj.unit M b.model b.pointIso
  let L := g.modules.rightDerivedFunctor ⋙ tInverse.mapDerivedCategory
  let LH := (hInverse ⋙ hDirect).mapDerivedCategory ⋙ L
  let c : Comparison RX D f.modules g.modules tInverse
      (hInverse ⋙ hDirect) hAdj.unit V N := {
    source := d.source
    target := d.target
    sourcePoint := d.sourcePoint
    targetPoint := d.targetPoint
    sourceColumns := fun p n ↦ L.mapIso (b.columnIso p n) ≪≫ d.sourceColumns p n
    targetColumns := fun p n ↦ LH.mapIso (b.columnIso p n) ≪≫ d.targetColumns p n
    source_operator := fun p n m θ ↦
      map_square_then L _ _ _ _ _ _ _ (b.operator p n m θ) (d.source_operator p n m θ)
    target_operator := fun p n m θ ↦
      map_square_then LH _ _ _ _ _ _ _ (b.operator p n m θ) (d.target_operator p n m θ)
    source_natural := fun p q k n ↦
      map_square_then L _ _ _ _ _ _ _ (b.natural p q k n) (d.source_natural p q k n)
    target_natural := fun p q k n ↦
      map_square_then LH _ _ _ _ _ _ _ (b.natural p q k n) (d.target_natural p q k n)
    source_augmentation := by
      intro p n
      change _ = L.map _ ≫ (L.map _ ≫ _)
      rw [d.source_augmentation, b.augmentation]
      change L.map (_ ≫ _) ≫ _ = _
      rw [L.map_comp, Category.assoc]
    target_augmentation := by
      intro p n
      change _ = LH.map _ ≫ (LH.map _ ≫ _)
      rw [d.target_augmentation, b.augmentation]
      change LH.map (_ ≫ _) ≫ _ = _
      rw [LH.map_comp, Category.assoc]
    unitColumns := d.unitColumns
    unit_columns := by
      intro p n
      change (L.map _ ≫ _) ≫ _ = L.map _ ≫ (LH.map _ ≫ _)
      rw [Category.assoc, d.unit_columns]
      change L.map _ ≫ (L.map _ ≫ _) = L.map _ ≫ (L.map _ ≫ _)
      rw [← L.map_comp_assoc, ← L.map_comp_assoc]
      have h := (exactUnit hAdj.unit).naturality (b.columnIso p n).hom
      dsimp only [Functor.id_map] at h
      exact congrArg (fun k ↦ L.map k ≫ (d.targetColumns p n).hom) h
    sourceComparison := d.sourceComparison
    targetComparison := d.targetComparison
    source_normalization := d.source_normalization
    target_normalization := d.target_normalization
    unit_total := d.unit_total }
  refine ⟨c, fun U p ↦ ?_⟩
  exact congrArg (fun k ↦ (restrictDerived RB U).map k) (c.unit_total p)

end CategoryTheory.CechLocalizationUnit
