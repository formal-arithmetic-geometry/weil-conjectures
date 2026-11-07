/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization

public import WeilConjectures.AlgebraicGeometry.SchemeDerivedBaseChangeMap
import WeilConjectures.AlgebraicGeometry.PinnedBaseChangeMateShifts
public import WeilConjectures.AlgebraicGeometry.PinnedSingleTensorShifts
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors

/-! # Shift covariance of the pinned single-complex base-change composite
Source: Stacks Project, Tags 08FE, 08HY, 08IB and 0D5U.
(blueprint: lem-pc-pinned-single-base-change-shift). -/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory Limits
noncomputable section
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency.types false

/-- The source functor of the base-change comparison on single complexes.
Source: Stacks Project, Tag 08HY (blueprint: lem-pc-pinned-single-base-change-shift). -/
def singleDegreeBaseChangeSource
    {X S S' : Scheme.{u}}
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S'.toRingedSpace))]
    (f : X ⟶ S) (g : S' ⟶ S) (n : ℤ) :
    X.Modules ⥤ schemeDerivedCategory.{u, w} S' :=
  ((DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n ⋙
    schemeDerivedDirectImage.{u, w, w} f) ⋙ derivedPullback.{u, w} g)

/-- The target functor after applying the single-complex tensor counit.
Source: Stacks Project, Tag 08HY (blueprint: lem-pc-pinned-single-base-change-shift). -/
def singleDegreeBaseChangeTarget
    {X X' S' : Scheme.{u}}
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X'.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S'.toRingedSpace))]
    (g' : X' ⟶ X) (f' : X' ⟶ S') (n : ℤ) :
    X.Modules ⥤ schemeDerivedCategory.{u, w} S' :=
  ((Scheme.Modules.tensorPullback g' ⋙ DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings X'.toRingedSpace)) n) ⋙ schemeDerivedDirectImage.{u, w, w} f')

/-- The base-change comparison followed by the composition-pinned tensor counit.
This uses the same composition-pinned left-derived counit as the original comparison.
Source: Stacks Project, Tag 08HY (blueprint: lem-pc-pinned-single-base-change-shift). -/
def singleDegreeBaseChangeComposite
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ {Y Z : Scheme.{u}} (k : Y ⟶ Z), (Scheme.Modules.tensorPullback k).Additive]
    {X S X' S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    (g' : X' ⟶ X) (f' : X' ⟶ S') (h : g' ≫ f = f' ≫ g)
    (n : ℤ) (G : X.Modules) :
    (singleDegreeBaseChangeSource.{u, w} f g n).obj G ⟶
      (singleDegreeBaseChangeTarget.{u, w} g' f' n).obj G :=
  let ε := (Classical.choose
    (Classical.choose_spec exists_derivedPullbackComposition.{u, w})) g'
  let c : (derivedPullback.{u, w} g').obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj G) ⟶
      (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings X'.toRingedSpace)) n).obj
          ((Scheme.Modules.tensorPullback g').obj G) :=
    cast (by rfl) (ε.app ((HomotopyCategory.singleFunctor _ n).obj G) ≫
      DerivedCategory.Qh.{w}.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex
          (Scheme.Modules.tensorPullback g') (ComplexShape.up ℤ) n).hom.app G)))
  schemeDerivedBaseChangeMap.{u, w} f f' g g' h
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj G) ≫
    (schemeDerivedDirectImage.{u, w, w} f').map c

set_option maxHeartbeats 800000 in
-- The nested family comparison must identify the shared sheaf-module category instances.
/-- The tensor comparison is a morphism of single-functor families.
Source: Stacks Project, Tag 08HY; the derived counit universal property and
Mathlib's termwise mapped-single shift identity.
(blueprint: lem-pc-pinned-single-tensor-shifts).
Proof: whisker the pinned left-derived counit by each homotopy single functor,
then compose with Qh applied to the termwise mapped-single comparison. Naturality
follows from the naturality of these two factors. For the shift equation, expand
the single shift using SingleFunctors.postcomp. Apply the counit's
NatTrans.CommShift equation, then the termwise identity
Functor.mapHomologicalComplex_map_singleFunctors_shiftIso_hom_app. Naturality of
the quotient shift comparisons moves them through the mapped-single map.
Functor.map_comp and associativity cancel inverse quotient comparisons. This
proves the Hom.comm equation for every triple k+i=j, including zero and negative
integers, without exactness or flatness of tensor pullback. -/
theorem exists_pinned_single_tensor_shifts
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ {Y Z : Scheme.{u}} (k : Y ⟶ Z), (Scheme.Modules.tensorPullback k).Additive]
    {X X' : Scheme.{u}} (g' : X' ⟶ X) (s : (derivedPullback.{u, w} g').CommShift ℤ)
    (hs : letI := s; NatTrans.CommShift (pinnedPullbackCounit.{u, w} g') ℤ) :
    letI := s
    ∃ τ : (DerivedCategory.singleFunctors
        (SheafOfModules.{u} (moduleRings X.toRingedSpace))).postcomp
          (derivedPullback.{u, w} g') ⟶
      (DerivedCategory.singleFunctors
        (SheafOfModules.{u} (moduleRings X'.toRingedSpace))).precomp
          (Scheme.Modules.tensorPullback g'),
      ∀ n G, (τ.hom n).app G = pinnedSingleTensorCounit.{u, w} g' n G := by
  dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at *
  let := s
  have := hs
  let F := HomotopyCategory.singleFunctors
    (SheafOfModules.{u} (moduleRings X.toRingedSpace))
  let T : SheafOfModules.{u} (moduleRings X.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings X'.toRingedSpace) := Scheme.Modules.tensorPullback g'
  let c := (F.postcompPostcompIso DerivedCategory.Qh (derivedPullback g')).hom ≫
    SingleFunctors.postcompNatTrans F (pinnedPullbackCounit g') ≫
    (F.postcompPostcompIso (T.mapHomotopyCategory (ComplexShape.up ℤ))
      DerivedCategory.Qh).inv ≫
    SingleFunctors.postcompHom (SingleFunctors.mappedHomotopySingleIso T).hom
      DerivedCategory.Qh ≫
    (SingleFunctors.precompPostcompIso (HomotopyCategory.singleFunctors
      (SheafOfModules.{u} (moduleRings X'.toRingedSpace))) T DerivedCategory.Qh).hom
  let e := DerivedCategory.singleFunctorsPostcompQhIso
    (SheafOfModules.{u} (moduleRings X'.toRingedSpace))
  let d : ((HomotopyCategory.singleFunctors
      (SheafOfModules.{u} (moduleRings X'.toRingedSpace))).postcomp
        DerivedCategory.Qh).precomp T ⟶
      (DerivedCategory.singleFunctors
        (SheafOfModules.{u} (moduleRings X'.toRingedSpace))).precomp T :=
    { hom := fun n ↦ Functor.whiskerLeft T (e.inv.hom n)
      comm := fun k i j h ↦ by
        ext G
        simpa [SingleFunctors.precomp] using congr_app (e.inv.comm k i j h) (T.obj G) }
  refine ⟨SingleFunctors.postcompHom
    (DerivedCategory.singleFunctorsPostcompQhIso
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))).hom (derivedPullback g') ≫
      c ≫ d, ?_⟩
  intro n G
  change (derivedPullback g').map (𝟙 _ ≫ 𝟙 _) ≫
    (𝟙 _ ≫ (pinnedPullbackCounit g').app ((F.functor n).obj G) ≫
      𝟙 _ ≫ DerivedCategory.Qh.map
        (((SingleFunctors.mappedHomotopySingleIso T).hom.hom n).app G) ≫ 𝟙 _) ≫
      (𝟙 _ ≫ 𝟙 _) = _
  rw [SingleFunctors.mappedHomotopySingleIso_hom_app]
  simp only [Category.id_comp, Category.comp_id]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  rfl

theorem pinned_single_base_change_shift
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ {Y Z : Scheme.{u}} (k : Y ⟶ Z), (Scheme.Modules.tensorPullback k).Additive]
    {X S X' S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    (g' : X' ⟶ X) (f' : X' ⟶ S') (h : g' ≫ f = f' ≫ g)
    {D : Type*} [Category D] [HasShift D ℤ]
    (H : schemeDerivedCategory.{u, w} S' ⥤ D) [H.CommShift ℤ] (n : ℤ) :
    ∃ a : singleDegreeBaseChangeSource.{u, w} f g n ⋙ H ≅
        (singleDegreeBaseChangeSource.{u, w} f g 0 ⋙ H) ⋙ shiftFunctor D (-n),
    ∃ b : singleDegreeBaseChangeTarget.{u, w} g' f' n ⋙ H ≅
        (singleDegreeBaseChangeTarget.{u, w} g' f' 0 ⋙ H) ⋙ shiftFunctor D (-n),
    ∀ G : X.Modules,
      H.map (singleDegreeBaseChangeComposite.{u, w} f g g' f' h n G) ≫ b.hom.app G =
        a.hom.app G ≫ (shiftFunctor D (-n)).map
          (H.map (singleDegreeBaseChangeComposite.{u, w} f g g' f' h 0 G)) := by
  set_option backward.defeqAttrib.useBackward true in
    dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at *
    obtain ⟨s, hs⟩ := exists_pinned_pullback_counit_shifts.{u, w}
    let := s g
    let := s g'
    obtain ⟨τ, hτ, hτshift⟩ :=
      exists_pinned_base_change_mate_shifts.{u, w} s hs f g g' f' h
    have := hτshift
    obtain ⟨c, hc⟩ := exists_pinned_single_tensor_shifts.{u, w} g' (s g') (hs g')
    let F := DerivedCategory.singleFunctors
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))
    let T := (DerivedCategory.singleFunctors
      (SheafOfModules.{u} (moduleRings X'.toRingedSpace))).precomp
        (Scheme.Modules.tensorPullback g')
    let β : F.postcomp (schemeDerivedDirectImage f ⋙ derivedPullback g) ⟶
        T.postcomp (schemeDerivedDirectImage f') :=
      SingleFunctors.postcompNatTrans F τ ≫
        (F.postcompPostcompIso (derivedPullback g') (schemeDerivedDirectImage f')).inv ≫
        SingleFunctors.postcompHom c (schemeDerivedDirectImage f')
    let βH := SingleFunctors.postcompHom β H
    let a := ((F.postcomp (schemeDerivedDirectImage f ⋙ derivedPullback g)).postcomp H).shiftIso
      (-n) n 0 (by omega) |>.symm
    let b := ((T.postcomp (schemeDerivedDirectImage f')).postcomp H).shiftIso
      (-n) n 0 (by omega) |>.symm
    refine ⟨a, b, ?_⟩
    intro G
    have hb := congr_app (βH.comm (-n) n 0 (by omega)) G
    simp only [NatTrans.comp_app, Functor.whiskerRight_app] at hb
    have hβ (i : ℤ) : (βH.hom i).app G =
        H.map (singleDegreeBaseChangeComposite.{u, w} f g g' f' h i G) := by
      change H.map (τ.app ((F.functor i).obj G) ≫ 𝟙 _ ≫
        (schemeDerivedDirectImage f').map ((c.hom i).app G)) = _
      simp only [Category.id_comp]
      rw [hτ, hc]
      rfl
    rw [hβ n, hβ 0] at hb
    apply (cancel_epi
      ((((F.postcomp (schemeDerivedDirectImage f ⋙ derivedPullback g)).postcomp H).shiftIso
        (-n) n 0 (by omega)).hom.app G)).1
    dsimp only [a, b, Iso.symm_hom]
    simp only [Iso.hom_inv_id_app_assoc]
    rw [← Category.assoc, hb, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]

end AlgebraicGeometry
