/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q4
-/
module

public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Sheaf.AlgebraicGeometry.SchemeCanonicalShiftUnitIso
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.Functor
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Sheaf.Algebra.Homology.KFlat
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Sheaf.AlgebraicGeometry.NormalizedDerivedPullbackKFlatCounit
import Sheaf.AlgebraicGeometry.DerivedPullbackKFlatCounitAdjustmentFactor
import Sheaf.Algebra.Homology.KFlatResolution

/-! # Adjustment of a K-flat counit to the translated-unit shift

Source: Stacks Project, Tag 06YJ, K-flat computation; the supplied-tensorator
normalization of the parent cone node, expanded by the agent.
(blueprint: lem-sc-derived-pullback-kflat-counit-shift-adjustment).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated MonoidalCategory
namespace AlgebraicGeometry

set_option maxHeartbeats 800000 in
-- Naturality of the canonical tensor shift unfolds the derived monoidal structure.
/-- A K-flat counit can be adjusted by a natural automorphism of its source
so that its translation square has the supplied translated-unit tensorator form.
This asserts a shift square, without any assertion about cone connecting maps.

Source: Stacks Project, Tag 06YJ, Lemma 20.27.1; the supplied-tensorator
normalization in step 3 of the parent cone node, expanded by the agent.

Proof. Compute derived pullback on the resolving class of K-flat complexes.
Use the structure sheaf in degree zero for the tensor unit and its translate
for the shifted unit. Both are K-flat. Termwise pullback identifies these
representatives with the corresponding complexes over Z. Rewrite translation
of a representative P as the translated unit tensor P, using the first-variable
Koszul comparison and the translated left unitor. Transport this rewrite with
the supplied inverse tensorator. The monoidal unit map identifies the unshifted
unit; its translated comparison, together with the chosen K-flat comparison,
gives e. Choose the resolving-class comparison jointly with this rewrite:
tensorator associativity and the two unit equations identify its translation
square with the composite displayed below. The Koszul maps and the tensorator
are natural, so this comparison is natural in P and respects replacement maps.
The resolving-class universal property extends the comparison to the homotopy
category, including objects which are not themselves K-flat.

Compare this normalized resolving-class comparison with ε₀. On each K-flat
representative their ratio is an automorphism, since both comparisons are
invertible there. Naturality makes these ratios compatible with replacement
maps. The same resolving-class universal property therefore descends their
ratio to a natural automorphism a of Qh followed by derived pullback, with
normalized comparison a.hom followed by ε₀. Its inverse descends the reverse
ratios; their two compositions are identities on the resolving class and hence
everywhere by the universal property. Substitute this comparison in the shift
square to obtain the formula. On zero representatives all the maps are the
unique maps of zero objects; the empty scheme causes no exception. The theorem
allows adjustment of ε₀ and chooses e jointly with it: it does not claim that
an arbitrarily fixed e and ε₀ already satisfy the square.
(blueprint: lem-sc-derived-pullback-kflat-counit-shift-adjustment).
-/
theorem exists_derivedPullback_kFlat_counit_shift_adjustment
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y] (f : Z ⟶ Y) [IsProper f]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [Functor.Monoidal (derivedPullback f)]
    [(Scheme.Modules.tensorPullback f).Additive]
    (ε₀ : DerivedCategory.Qh ⋙ derivedPullback f ⟶
      (Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        (DerivedCategory.Qh : HomotopyCategory
          (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
          schemeDerivedCategory Z))
    (hε₀ : ∀ P : CochainComplex
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ,
      CochainComplex.IsKFlat (R := Y.sheaf) P →
      IsIso (ε₀.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P))) :
    ∃ e : (derivedPullback f).obj ((𝟙_ (schemeDerivedCategory Y))⟦(1 : ℤ)⟧) ≅
        (𝟙_ (schemeDerivedCategory Z))⟦(1 : ℤ)⟧,
      ∃ a : (DerivedCategory.Qh ⋙ derivedPullback f) ≅
          (DerivedCategory.Qh ⋙ derivedPullback f),
        let ε := a.hom ≫ ε₀
        ∀ X : HomotopyCategory
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ),
        let G := (Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          (DerivedCategory.Qh : HomotopyCategory
            (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
            schemeDerivedCategory Z)
        ε.app (X⟦(1 : ℤ)⟧) ≫ (G.commShiftIso (1 : ℤ)).hom.app X =
          (derivedPullback f).map ((DerivedCategory.Qh.commShiftIso (1 : ℤ)).hom.app X) ≫
            ((derivedPullback f).mapIso
                (schemeCanonicalShiftUnitIso Y (DerivedCategory.Qh.obj X)).symm ≪≫
              asIso (Functor.OplaxMonoidal.δ (derivedPullback f)
                ((𝟙_ (schemeDerivedCategory Y))⟦(1 : ℤ)⟧) (DerivedCategory.Qh.obj X)) ≪≫
              tensorIso e (Iso.refl _) ≪≫
              schemeCanonicalShiftUnitIso Z
                ((derivedPullback f).obj (DerivedCategory.Qh.obj X))).hom ≫
            (ε.app X)⟦(1 : ℤ)⟧' := by
  obtain ⟨e, ε, hε, hsquare⟩ := exists_normalized_derivedPullback_kFlat_counit
    f ε₀ hε₀
  let F := derivedPullback f
  let A := SheafOfModules.{u} (moduleRings Y.toRingedSpace)
  let Q := DerivedCategory.Qh (C := A)
  let G := (Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    (DerivedCategory.Qh : HomotopyCategory
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
        schemeDerivedCategory Z)
  have hc (S : Scheme.{u})
      [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
      {K N : schemeDerivedCategory S} (g : K ⟶ N) :
      (schemeCanonicalShiftUnitIso S K).hom ≫ g⟦(1 : ℤ)⟧' =
        ((𝟙_ (schemeDerivedCategory S))⟦(1 : ℤ)⟧) ◁ g ≫
          (schemeCanonicalShiftUnitIso S N).hom := by
    let := schemeCanonicalTensorShift S
    let : ∀ M : schemeDerivedCategory S, (tensorRight M).CommShift ℤ :=
      fun M ↦ Functor.CommShift₂.commShiftFlipObj (h := .int) M
    have : NatTrans.CommShift ((curriedTensor (schemeDerivedCategory S)).flip.map g) ℤ :=
      Functor.CommShift₂.commShift_flip_map (h := .int) g
    dsimp [schemeCanonicalShiftUnitIso]
    simp only [Category.assoc]
    rw [← Functor.map_comp, ← leftUnitor_naturality, Functor.map_comp]
    simpa only [Category.assoc, tensorRight, Functor.flip, curriedTensor] using
      congrArg (fun t ↦ t ≫ (shiftFunctor (schemeDerivedCategory S) (1 : ℤ)).map (λ_ N).hom)
        (NatTrans.shift_app_comm ((curriedTensor (schemeDerivedCategory S)).flip.map g)
          (1 : ℤ) (𝟙_ (schemeDerivedCategory S)))
  have hci (S : Scheme.{u})
      [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
      {K N : schemeDerivedCategory S} (g : K ⟶ N) :
      g⟦(1 : ℤ)⟧' ≫ (schemeCanonicalShiftUnitIso S N).inv =
        (schemeCanonicalShiftUnitIso S K).inv ≫
          ((𝟙_ (schemeDerivedCategory S))⟦(1 : ℤ)⟧) ◁ g := by
    apply (cancel_epi (schemeCanonicalShiftUnitIso S K).hom).1
    rw [← Category.assoc, hc S]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]
  let b : shiftFunctor (schemeDerivedCategory Y) (1 : ℤ) ⋙ F ⟶
      F ⋙ shiftFunctor (schemeDerivedCategory Z) (1 : ℤ) :=
    { app := fun K ↦ (F.mapIso (schemeCanonicalShiftUnitIso Y K).symm ≪≫
        asIso (Functor.OplaxMonoidal.δ F
          ((𝟙_ (schemeDerivedCategory Y))⟦(1 : ℤ)⟧) K) ≪≫
        tensorIso e (Iso.refl _) ≪≫ schemeCanonicalShiftUnitIso Z (F.obj K)).hom
      naturality := by
        intro K N g
        dsimp only [Functor.comp_map, Iso.trans_hom, Functor.mapIso_hom,
          Iso.symm_hom, asIso_hom]
        simp only [tensorIso, Iso.refl_hom, tensorHom_def, whiskerLeft_id,
          Category.comp_id, Category.assoc]
        rw [← F.map_comp_assoc, hci Y, F.map_comp_assoc,
          ← Functor.OplaxMonoidal.δ_natural_right_assoc]
        rw [whisker_exchange_assoc, ← hc Z] }
  let l : shiftFunctor (HomotopyCategory A (ComplexShape.up ℤ)) (1 : ℤ) ⋙ (Q ⋙ F) ⟶
      G ⋙ shiftFunctor (schemeDerivedCategory Z) (1 : ℤ) :=
    Functor.whiskerLeft (shiftFunctor _ (1 : ℤ)) ε ≫ (G.commShiftIso (1 : ℤ)).hom
  let r : shiftFunctor (HomotopyCategory A (ComplexShape.up ℤ)) (1 : ℤ) ⋙ (Q ⋙ F) ⟶
      G ⋙ shiftFunctor (schemeDerivedCategory Z) (1 : ℤ) :=
    Functor.whiskerRight (Q.commShiftIso (1 : ℤ)).hom F ≫ Functor.whiskerLeft Q b ≫
      Functor.whiskerRight ε (shiftFunctor _ (1 : ℤ))
  have hsq : ∀ X, l.app X = r.app X := by
    intro X
    obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    obtain ⟨P, s, hP, _, hs, _⟩ := CochainComplex.exists_isKFlatResolution (R := Y.sheaf) K
    let q := HomotopyCategory.quotient A (ComplexShape.up ℤ)
    let t := q.map s
    have ht : HomotopyCategory.quasiIso A (ComplexShape.up ℤ) t :=
      (HomotopyCategory.quotient_map_mem_quasiIso_iff s).2 hs
    have : IsIso (Q.map t) := Localization.inverts Q
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) _ ht
    have hcomm := (Q.commShiftIso (1 : ℤ)).hom.naturality t
    dsimp only [Functor.comp_map] at hcomm
    have : IsIso (Q.map (t⟦(1 : ℤ)⟧') ≫ (Q.commShiftIso (1 : ℤ)).hom.app (q.obj K)) := by
      rw [hcomm]
      infer_instance
    have : IsIso (Q.map (t⟦(1 : ℤ)⟧')) :=
      IsIso.of_isIso_comp_right _ ((Q.commShiftIso (1 : ℤ)).hom.app (q.obj K))
    have : IsIso (F.map (Q.map (t⟦(1 : ℤ)⟧'))) := inferInstance
    apply (cancel_epi (F.map (Q.map (t⟦(1 : ℤ)⟧')))).1
    change ((shiftFunctor _ (1 : ℤ) ⋙ (Q ⋙ F)).map t) ≫ l.app (q.obj K) =
      ((shiftFunctor _ (1 : ℤ) ⋙ (Q ⋙ F)).map t) ≫ r.app (q.obj K)
    rw [l.naturality t, r.naturality t]
    have heq : l.app (q.obj P) = r.app (q.obj P) := hsquare P hP
    rw [heq]
  obtain ⟨a, ha⟩ := exists_derivedPullback_kFlat_counit_adjustment_factor
    f ε₀ hε₀ ε hε
  refine ⟨e, a, ?_⟩
  dsimp
  intro X
  have h := hsq X
  change ε.app (X⟦(1 : ℤ)⟧) ≫ (G.commShiftIso (1 : ℤ)).hom.app X =
    F.map ((Q.commShiftIso (1 : ℤ)).hom.app X) ≫ b.app (Q.obj X) ≫
      (ε.app X)⟦(1 : ℤ)⟧' at h
  rw [← ha] at h
  exact h

end AlgebraicGeometry
