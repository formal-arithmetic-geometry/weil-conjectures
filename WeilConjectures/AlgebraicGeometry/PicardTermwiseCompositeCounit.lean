/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PicardTermwiseModels
import WeilConjectures.AlgebraicGeometry.PicardTermwiseCompositeCounitCore

/-! # Composition equation for explicit termwise comparison morphisms

## References

* Stacks Project, Tags 06YJ and 0D5S
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
noncomputable section

attribute [local instance] Functor.additive_of_preserves_binary_products

variable [∀ Y : Scheme.{v},
  HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem composite_counit_of_associativity
    (W : Scheme.{v}) (E : schemeDerivedCategory W) (U : W.Opens)
    (K : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ)
    (e : (derivedPullback U.ι).obj E ⟶ DerivedCategory.Q.obj
      (((Modules.overEquiv U).functor.mapHomologicalComplex (.up ℤ)).obj K))
    (c : ∀ {X Y Z : Scheme.{v}} (f : X ⟶ Y) (g : Y ⟶ Z),
      derivedPullback g ⋙ derivedPullback f ≅ derivedPullback (f ≫ g))
    (ha : ∀ {A B C D : Scheme.{v}} (i : A ⟶ B) (s : B ⟶ C) (j : C ⟶ D),
      Functor.isoWhiskerRight (c s j) (derivedPullback i) ≪≫ c i (s ≫ j) =
        Functor.associator (derivedPullback j) (derivedPullback s) (derivedPullback i) ≪≫
          Functor.isoWhiskerLeft (derivedPullback j) (c i s) ≪≫ c (i ≫ s) j ≪≫
            eqToIso (congrArg (fun k : A ⟶ D ↦ derivedPullback k) (Category.assoc i s j)))
    (hc : ∀ {T T' : Scheme.{v}} (i : T' ⟶ T) (s : T ⟶ U.toScheme),
      let P := ((Modules.overEquiv U).functor.mapHomologicalComplex (.up ℤ)).obj K
      (c i s).inv.app (DerivedCategory.Q.obj P) ≫
          (derivedPullback i).map ((picardTermwiseCounit s).app P) ≫
            (picardTermwiseCounit i).app (picardTermwiseModel W U K s) =
        (picardTermwiseCounit (i ≫ s)).app P ≫ DerivedCategory.Q.map
          (picardTermwiseModelRestrictionIso W U K i s (i ≫ s) rfl).hom) :
    let P := ((Modules.overEquiv U).functor.mapHomologicalComplex (.up ℤ)).obj K
    let b : ∀ {T : Scheme.{v}} (t : T ⟶ W) (s : T ⟶ U.toScheme),
        s ≫ U.ι = t → ((derivedPullback t).obj E ⟶
          DerivedCategory.Q.obj (picardTermwiseModel W U K s)) :=
      fun {T} _t s hf ↦
        ((c s U.ι ≪≫ eqToIso
          (congrArg (fun g : T ⟶ W ↦ derivedPullback g) hf)).inv.app E) ≫
        (derivedPullback s).map e ≫ (picardTermwiseCounit s).app P
    ∀ {T T' : Scheme.{v}} (i : T' ⟶ T) (t : T ⟶ W) (t' : T' ⟶ W)
      (s : T ⟶ U.toScheme) (s' : T' ⟶ U.toScheme)
      (ht : i ≫ t = t') (hs : i ≫ s = s')
      (hf : s ≫ U.ι = t) (hf' : s' ≫ U.ι = t'),
      b t' s' hf' ≫
          DerivedCategory.Q.map (picardTermwiseModelRestrictionIso W U K i s s' hs).hom =
        ((c i t ≪≫ eqToIso
          (congrArg (fun g : T' ⟶ W ↦ derivedPullback g) ht)).inv.app E) ≫
          (derivedPullback i).map (b t s hf) ≫
            (picardTermwiseCounit i).app (picardTermwiseModel W U K s) := by
  classical
  dsimp only
  intro T T' i t t' s s' ht hs hf hf'
  subst t' s' t
  let P := ((Modules.overEquiv U).functor.mapHomologicalComplex (.up ℤ)).obj K
  change
    ((c (i ≫ s) U.ι ≪≫ eqToIso
      (congrArg (fun g : T' ⟶ W ↦ derivedPullback g) hf')).inv.app E ≫
      (derivedPullback (i ≫ s)).map e ≫ (picardTermwiseCounit (i ≫ s)).app P) ≫
      DerivedCategory.Q.map (picardTermwiseModelRestrictionIso W U K i s (i ≫ s) rfl).hom =
    ((c i (s ≫ U.ι) ≪≫ eqToIso
      (congrArg (fun g : T' ⟶ W ↦ derivedPullback g) rfl)).inv.app E) ≫
      (derivedPullback i).map
        (((c s U.ι ≪≫ eqToIso
          (congrArg (fun g : T ⟶ W ↦ derivedPullback g) rfl)).inv.app E) ≫
          (derivedPullback s).map e ≫ (picardTermwiseCounit s).app P) ≫
      (picardTermwiseCounit i).app (picardTermwiseModel W U K s)
  have h := congrArg (fun x ↦ x.inv.app E) (ha i s U.ι)
  simp only [Iso.trans_inv, NatTrans.comp_app, Functor.isoWhiskerRight_inv,
    Functor.isoWhiskerLeft_inv, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_inv_app, Category.comp_id] at h
  have hc := hc i s
  change (c i s).inv.app (DerivedCategory.Q.obj P) ≫
      (derivedPullback i).map ((picardTermwiseCounit s).app P) ≫
        (picardTermwiseCounit i).app (picardTermwiseModel W U K s) =
    (picardTermwiseCounit (i ≫ s)).app P ≫ DerivedCategory.Q.map
      (picardTermwiseModelRestrictionIso W U K i s (i ≫ s) rfl).hom at hc
  simp only [Iso.trans_inv, NatTrans.comp_app, eqToIso_refl, Iso.refl_inv,
    NatTrans.id_app, Category.id_comp, Functor.map_comp, Category.assoc]
  have hn := (c i s).inv.naturality e
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  simp only [reassoc_of% h, ← reassoc_of% hn]
  rw [hc]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option linter.unusedVariables false in
-- Preserve the original statement, including its unused lambda binder t.
/-- The composites of a fixed morphism with the pinned tensor-pullback counits
satisfy the composition equation. No perfectness, invertibility, or representation
of `E` on the open site is assumed: this is an equation of explicitly given morphisms
(Stacks, Tags 0D5S and 06YJ). -/
theorem picard_termwise_composite_counit
    (W : Scheme.{v}) (E : schemeDerivedCategory W) (U : W.Opens)
    (K : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ)
    (e : (derivedPullback U.ι).obj E ⟶ DerivedCategory.Q.obj
      (((Modules.overEquiv U).functor.mapHomologicalComplex (.up ℤ)).obj K)) :
    let c : ∀ {X Y Z : Scheme.{v}} (f : X ⟶ Y) (g : Y ⟶ Z),
        derivedPullback g ⋙ derivedPullback f ≅ derivedPullback (f ≫ g) :=
      fun f g ↦ Classical.choose (Classical.choose_spec (Classical.choose_spec
        (Classical.choose_spec exists_derivedPullbackComposition))) f g
    let P := ((Modules.overEquiv U).functor.mapHomologicalComplex (.up ℤ)).obj K
    let b : ∀ {T : Scheme.{v}} (t : T ⟶ W) (s : T ⟶ U.toScheme),
        s ≫ U.ι = t → ((derivedPullback t).obj E ⟶
          DerivedCategory.Q.obj (picardTermwiseModel W U K s)) :=
      fun {T} t s hf ↦
        ((c s U.ι ≪≫ eqToIso
          (congrArg (fun g : T ⟶ W ↦ derivedPullback g) hf)).inv.app E) ≫
        (derivedPullback s).map e ≫ (picardTermwiseCounit s).app P
    ∀ {T T' : Scheme.{v}} (i : T' ⟶ T) (t : T ⟶ W) (t' : T' ⟶ W)
      (s : T ⟶ U.toScheme) (s' : T' ⟶ U.toScheme)
      (ht : i ≫ t = t') (hs : i ≫ s = s')
      (hf : s ≫ U.ι = t) (hf' : s' ≫ U.ι = t'),
      b t' s' hf' ≫
          DerivedCategory.Q.map (picardTermwiseModelRestrictionIso W U K i s s' hs).hom =
        ((c i t ≪≫ eqToIso
          (congrArg (fun g : T' ⟶ W ↦ derivedPullback g) ht)).inv.app E) ≫
          (derivedPullback i).map (b t s hf) ≫
            (picardTermwiseCounit i).app (picardTermwiseModel W U K s) := by
  classical
  have H := exists_derivedPullbackComposition.{v, v + 1}
  have H₁ := Classical.choose_spec H
  have H₂ := Classical.choose_spec H₁
  have H₃ := Classical.choose_spec H₂
  let c := @Classical.choose _ _ H₃
  have H₄ := Classical.choose_spec H₃
  exact fun {T T'} ↦ composite_counit_of_associativity W E U K e c
    ((Classical.choose_spec H₄.2).2.2)
    (fun i s ↦ picard_termwise_counit_composition W U K i s)

end
end AlgebraicGeometry.Scheme
