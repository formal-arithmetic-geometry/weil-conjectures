/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Z6
-/
module

public import WeilConjectures.AlgebraicGeometry.PinnedSingleBaseChangeShift
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.PerfectHomTransport
public import WeilConjectures.AlgebraicGeometry.Picard.CanonicalSinglePullbackComparison
import Sheaf.AlgebraicGeometry.DerivedPullbackTopCohomology
import WeilConjectures.AlgebraicGeometry.PerfectHomCochainCounit
import WeilConjectures.AlgebraicGeometry.DerivedBaseChangeHorizontalPasting
import WeilConjectures.AlgebraicGeometry.DerivedBaseChangeNaturality

/-! # Horizontal pasting after the single-module tensor counit

Source: Stacks Project, cohomology.tex, Tag 0ATM, remark-compose-base-change-horizontal.
(blueprint: lem-weil-pbc-tensor-single-base-change-pasting).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory Opposite
noncomputable section
namespace AlgebraicGeometry

attribute [local instance_reducible] TopCat.Sheaf
set_option allowUnsafeReducibility true in
attribute [local reducible] Scheme.Modules Scheme.Modules.Hom Scheme.Modules.instCategory
  Scheme.Modules.instAbelian

attribute [local irreducible] Scheme.Modules.tensorPullback Adjunction.leftAdjointUniq

/-- The native category of module sheaves, exposed through the scheme alias.
Source: Mathlib sheaves of modules; Stacks, Tag 0096
(blueprint: lem-weil-pbc-tensor-single-base-change-pasting). -/
local instance (priority := 2000) tensorPasting_moduleCategory (T : Scheme.{u}) :
    Category T.Modules :=
  SheafOfModules.instCategory (R := moduleRings T.toRingedSpace)

/-- The native additive structure, through the same scheme alias.
Source: Mathlib sheaves of modules; Stacks, Tag 0096
(blueprint: lem-weil-pbc-tensor-single-base-change-pasting). -/
local instance (priority := 2000) tensorPasting_modulePreadditive (T : Scheme.{u}) :
    Preadditive T.Modules :=
  SheafOfModules.instPreadditive (moduleRings T.toRingedSpace)

/-- The native abelian structure, through the same scheme alias.
Source: Mathlib sheaves of modules; Stacks, Tag 0096
(blueprint: lem-weil-pbc-tensor-single-base-change-pasting). -/
local instance (priority := 2000) tensorPasting_moduleAbelian (T : Scheme.{u}) :
    Abelian T.Modules :=
  inferInstanceAs (Abelian (SheafOfModules.{u} (moduleRings T.toRingedSpace)))

set_option allowUnsafeReducibility true in
attribute [local reducible] tensorPasting_moduleCategory tensorPasting_modulePreadditive
  tensorPasting_moduleAbelian

attribute [local irreducible] DerivedCategory instCategoryDerivedCategory

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

omit [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] in
private theorem paste
    {A B D : Type*} [Category A] [Category B] [Category D]
    (L : A ⥤ D) (Q : B ⥤ D)
    {y : D} {m n o : A} {b₀ b₁ b₂ b₃ b₄ : B}
    (a : L.obj m ⟶ y) (e : y ⟶ Q.obj b₁) (β : m ⟶ n)
    (δ : L.obj n ⟶ Q.obj b₀) (c : b₀ ⟶ b₁)
    (r : b₁ ⟶ b₄) (q : n ⟶ o) (δ' : L.obj o ⟶ Q.obj b₂)
    (t : b₀ ⟶ b₂) (s : b₂ ⟶ b₃) (p : b₃ ⟶ b₄)
    (hfac : a ≫ e = L.map β ≫ δ ≫ Q.map c)
    (ht : c ≫ r = t ≫ s ≫ p)
    (hn : L.map q ≫ δ' = δ ≫ Q.map t) :
    a ≫ (e ≫ Q.map r) = L.map (β ≫ q) ≫ (δ' ≫ Q.map s) ≫ Q.map p := by
  calc
    _ = (a ≫ e) ≫ Q.map r := (Category.assoc _ _ _).symm
    _ = (L.map β ≫ δ ≫ Q.map c) ≫ Q.map r := by rw [hfac]
    _ = L.map β ≫ δ ≫ Q.map (c ≫ r) := by
      simp only [Functor.map_comp, Category.assoc]
    _ = L.map β ≫ δ ≫ Q.map (t ≫ s ≫ p) := by rw [ht]
    _ = _ := by
      simp only [Functor.map_comp, Category.assoc]
      simpa only [Category.assoc] using
        congrArg (fun k ↦ L.map β ≫ k ≫ Q.map s ≫ Q.map p) hn.symm

omit [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] in
private theorem single_comp
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Preadditive A] [Preadditive B] [Preadditive C]
    [Limits.HasZeroObject A] [Limits.HasZeroObject B] [Limits.HasZeroObject C]
    (F : A ⥤ B) (G : B ⥤ C) (H : A ⥤ C)
    [F.Additive] [G.Additive] [H.Additive] (c : F ⋙ G ≅ H) (N : A) :
    (Functor.mapHomologicalComplexCompIso c (ComplexShape.up ℤ)).hom.app
        ((HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj N) ≫
      (HomologicalComplex.singleMapHomologicalComplex H (ComplexShape.up ℤ) 0).hom.app N =
      (G.mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).hom.app N) ≫
      (HomologicalComplex.singleMapHomologicalComplex G (ComplexShape.up ℤ) 0).hom.app
        (F.obj N) ≫ (HomologicalComplex.single C (ComplexShape.up ℤ) 0).map (c.hom.app N) := by
  apply HomologicalComplex.to_single_hom_ext
  simp [HomologicalComplex.singleMapHomologicalComplex,
    HomologicalComplex.single, Functor.mapHomologicalComplexCompIso,
    NatIso.mapHomologicalComplex, NatTrans.mapHomologicalComplex,
    Functor.mapHomologicalComplex]

omit [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] in
private theorem homotopy_single_comp
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Preadditive A] [Preadditive B] [Preadditive C]
    [Limits.HasZeroObject A] [Limits.HasZeroObject B] [Limits.HasZeroObject C]
    (F : A ⥤ B) (G : B ⥤ C) (H : A ⥤ C)
    [F.Additive] [G.Additive] [H.Additive] (c : F ⋙ G ≅ H) (N : A) :
    (Functor.mapHomotopyCategoryCompIso c (ComplexShape.up ℤ)).hom.app
        ((HomotopyCategory.singleFunctor A 0).obj N) ≫
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex H (ComplexShape.up ℤ) 0).hom.app N) =
      (G.mapHomotopyCategory (ComplexShape.up ℤ)).map
        ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).map
          ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).hom.app N)) ≫
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex G (ComplexShape.up ℤ) 0).hom.app
          (F.obj N)) ≫ (HomotopyCategory.singleFunctor C 0).map (c.hom.app N) := by
  have hq := congrArg
    (fun k ↦ (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map k)
    (single_comp F G H c N)
  simpa only [Functor.map_comp, Functor.mapHomotopyCategory_map,
    HomotopyCategory.singleFunctor, HomotopyCategory.singleFunctors,
    SingleFunctors.postcomp, CochainComplex.singleFunctors, Functor.comp_map,
    Functor.comp_obj, Functor.mapHomotopyCategoryCompIso,
    Quotient.natIsoLift_hom, Functor.isoWhiskerRight_hom, Quotient.natTransLift,
    Functor.whiskerRight_app, HomotopyCategory.quotient_obj_as, Category.assoc] using hq

omit [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] in
private theorem sectionAdjunction_eq {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f) =
      Scheme.Modules.tensorPullbackSectionAdjunction f := by
  apply (Classical.choose_spec
    (Scheme.Modules.existsUnique_tensorPullbackSectionAdjunction f)).2
  intro M U m
  exact (Classical.choose_spec (Scheme.Modules.exists_tensorPullbackAdjunction f)) M (op U) m

omit [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] in
private theorem uniq_inv_mate
    {A B : Type*} [Category A] [Category B]
    {F F' : A ⥤ B} {R R' : B ⥤ A}
    (a : F ⊣ R) (b : F' ⊣ R') (e : R' ≅ R) :
    (a.leftAdjointUniq (b.ofNatIsoRight e)).inv =
      ((conjugateIsoEquiv a b).symm e.symm).hom := by
  ext X
  apply (b.homEquiv _ _).injective
  apply (cancel_mono (e.hom.app _)).1
  rw [Adjunction.leftAdjointUniq_inv_app,
    ← Adjunction.homEquiv_ofNatIsoRight_apply,
    Adjunction.homEquiv_leftAdjointUniq_hom_app]
  have hu := unit_conjugateEquiv_symm a b e.inv X
  change a.unit.app X ≫ e.inv.app _ =
    b.homEquiv _ _ (((conjugateIsoEquiv a b).symm e.symm).hom.app X) at hu
  rw [← hu]
  simp

omit [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] in
private theorem tensorComp_eq {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (Scheme.Modules.tensorPullbackSectionComp f g).inv =
      (perfectHomTensorComp f g).hom := by
  unfold Scheme.Modules.tensorPullbackSectionComp perfectHomTensorComp
  simp only [sectionAdjunction_eq]
  exact uniq_inv_mate _ _ _

omit [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] in
private theorem inverse_comp_eq
    {C : Type*} [Category C] {A B D E F : C} (c : A ≅ B)
    (x : A ⟶ D) (y : D ⟶ E) (z : E ⟶ F) (w : B ⟶ F)
    (hc : c.hom ≫ w = x ≫ y ≫ z) : c.inv ≫ x ≫ y ≫ z = w := by
  rw [← hc]
  simp

attribute [local irreducible] perfectHomTensorComp
  Scheme.Modules.tensorPullbackSectionComp

omit [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] in
private theorem tensorPasting_singleCounit_comp
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Abelian A] [Abelian B] [Abelian C]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B] [HasDerivedCategory.{w} C]
    (F : A ⥤ B) (G : B ⥤ C) (H : A ⥤ C)
    [F.Additive] [G.Additive] [H.Additive]
    (LF : DerivedCategory A ⥤ DerivedCategory B)
    (LG : DerivedCategory B ⥤ DerivedCategory C)
    (LH : DerivedCategory A ⥤ DerivedCategory C)
    (c : F ⋙ G ≅ H) (l : LF ⋙ LG ≅ LH)
    (εF : DerivedCategory.Qh ⋙ LF ⟶
      F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (εG : DerivedCategory.Qh ⋙ LG ⟶
      G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (εH : DerivedCategory.Qh ⋙ LH ⟶
      H.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (N : A)
    (hfac : ∀ K : HomotopyCategory A (.up ℤ),
      l.hom.app (DerivedCategory.Qh.obj K) ≫ εH.app K =
        LG.map (εF.app K) ≫ εG.app ((F.mapHomotopyCategory (.up ℤ)).obj K) ≫
          DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso c (.up ℤ)).hom.app K)) :
    l.hom.app ((DerivedCategory.singleFunctor A 0).obj N) ≫
        derivedSingleComparisonOfCounit H LH εH 0 N =
      LG.map (derivedSingleComparisonOfCounit F LF εF 0 N) ≫
        derivedSingleComparisonOfCounit G LG εG 0 (F.obj N) ≫
          (DerivedCategory.singleFunctor C 0).map (c.hom.app N) := by
  let rF := (HomotopyCategory.quotient B (.up ℤ)).map
    ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app N)
  have ht := homotopy_single_comp F G H c N
  have hn := εG.naturality rF
  change LG.map (DerivedCategory.Qh.map rF) ≫
      εG.app ((HomotopyCategory.singleFunctor B 0).obj (F.obj N)) =
    εG.app ((F.mapHomotopyCategory (.up ℤ)).obj
      ((HomotopyCategory.singleFunctor A 0).obj N)) ≫
        DerivedCategory.Qh.map ((G.mapHomotopyCategory (.up ℤ)).map rF) at hn
  unfold derivedSingleComparisonOfCounit
  exact paste LG DerivedCategory.Qh _ _ _ _ _ _ _ _ _ _ _
    (hfac ((HomotopyCategory.singleFunctor A 0).obj N)) ht hn

/-- The fixed counit as a named map, so applications retain its declared functors. -/
private def tensorPasting_counit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    letI := Scheme.Modules.canonicalTensorPullbackAdditive.{u, w} f
    DerivedCategory.Qh ⋙ derivedPullback f ⟶
      (Scheme.Modules.tensorPullback f).mapHomotopyCategory (.up ℤ) ⋙
        DerivedCategory.Qh.{w} (C := SheafOfModules.{u} (moduleRings X.toRingedSpace)) := by
  letI := Scheme.Modules.canonicalTensorPullbackAdditive.{u, w} f
  exact perfectHomTensorCounit f

attribute [local irreducible] tensorPasting_counit

private theorem tensorPasting_counit_comp {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (K : HomotopyCategory (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (.up ℤ)) :
    letI := Scheme.Modules.canonicalTensorPullbackAdditive.{u, w} f
    letI := Scheme.Modules.canonicalTensorPullbackAdditive.{u, w} g
    letI := Scheme.Modules.canonicalTensorPullbackAdditive.{u, w} (f ≫ g)
    (perfectHomComposition f g).hom.app (DerivedCategory.Qh.obj K) ≫
        (tensorPasting_counit (f ≫ g)).app K =
      (derivedPullback f).map ((tensorPasting_counit g).app K) ≫
        (tensorPasting_counit f).app
          (((Scheme.Modules.tensorPullback g).mapHomotopyCategory (.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map
          ((Functor.mapHomotopyCategoryCompIso (perfectHomTensorComp f g) (.up ℤ)).hom.app K)
        := by
  simpa only [tensorPasting_counit, perfectHomTensorHomotopyComp,
    perfectHomTensorHomotopy] using perfectHomTensorCounit_comp f g K

private theorem tensorPasting_singleComparison_eq
    {X Y : Scheme.{u}} (f : X ⟶ Y) (N : Y.Modules) :
    letI := Scheme.Modules.canonicalTensorPullbackAdditive.{u, w} f
    pinnedModulePullbackComparisonAt f 0 N =
      derivedSingleComparisonOfCounit (Scheme.Modules.tensorPullback f)
        (derivedPullback f) (tensorPasting_counit f) 0 N := by
  unfold tensorPasting_counit
  rfl

-- Match the specified derived counits on homotopy single complexes.
private theorem tensorSingle_composition
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (N : Z.Modules) :
    (perfectHomComposition f g).hom.app
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) 0).obj N) ≫
      pinnedModulePullbackComparisonAt (f ≫ g) 0 N =
    (derivedPullback f).map (pinnedModulePullbackComparisonAt g 0 N) ≫
      pinnedModulePullbackComparisonAt f 0 ((Scheme.Modules.tensorPullback g).obj N) ≫
      (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).map
          ((Scheme.Modules.tensorPullbackSectionComp f g).inv.app N) := by
  let := Scheme.Modules.canonicalTensorPullbackAdditive.{u, w} f
  let := Scheme.Modules.canonicalTensorPullbackAdditive.{u, w} g
  let := Scheme.Modules.canonicalTensorPullbackAdditive.{u, w} (f ≫ g)
  have h := tensorPasting_singleCounit_comp
    (Scheme.Modules.tensorPullback g) (Scheme.Modules.tensorPullback f)
    (Scheme.Modules.tensorPullback (f ≫ g))
    (derivedPullback g) (derivedPullback f) (derivedPullback (f ≫ g))
    (perfectHomTensorComp f g) (perfectHomComposition f g)
    (tensorPasting_counit g) (tensorPasting_counit f) (tensorPasting_counit (f ≫ g)) N
    (fun K ↦ tensorPasting_counit_comp f g K)
  simpa only [← tensorPasting_singleComparison_eq, ← tensorComp_eq] using h


private theorem tensorPasting_horizontal
    {X S Y T Z U : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) (h : U ⟶ T)
    (p : Y ⟶ X) (q : Y ⟶ T) (t : Z ⟶ Y) (r : Z ⟶ U)
    (hs : p ≫ f = q ≫ g) (hi : t ≫ q = r ≫ h)
    (ho : (t ≫ p) ≫ f = r ≫ (h ≫ g)) (E : schemeDerivedCategory.{u, w} X) :
    (derivedPullback h).map (schemeDerivedBaseChangeMap f q g p hs E) ≫
        schemeDerivedBaseChangeMap q r h t hi ((derivedPullback p).obj E) =
      (perfectHomComposition h g).hom.app ((schemeDerivedDirectImage f).obj E) ≫
        schemeDerivedBaseChangeMap f r (h ≫ g) (t ≫ p) ho E ≫
          (schemeDerivedDirectImage r).map ((perfectHomComposition t p).inv.app E) := by
  simpa only [perfectHomComposition] using
    schemeDerivedBaseChange_horizontal_pasting f g h p q t r hs hi E

-- Normalize the three specified counit comparisons.
/-- Horizontal pasting remains valid after applying the specified single-module
counits. The coefficient comparison is the normalized tensor composition, including
transport along a specified equality of the outer projection. Neither square needs to
be cartesian, and no comparison is inverted except the composition isomorphisms.
Source: Stacks Project, cohomology.tex, Tag 0ATM, remark-compose-base-change-horizontal,
with Tag 08HY, remark-base-change, and the single-complex counit factorization.
(blueprint: lem-weil-pbc-tensor-single-base-change-pasting).

Proof:
Apply the derived horizontal pasting theorem to the degree-zero single complex.
Naturality of the second mate moves the first single-module counit through it.
The composition-pinned counit factorization on a homotopy single complex identifies
successive counits with the outer counit followed by normalized tensor composition.
The inverse derived composition factor cancels, and functoriality of the final direct
image combines the coefficient map. Substitute the specified equality of projections.
All maps are morphism identities and cover zero modules and empty schemes. -/
theorem tensorSingleBaseChange_pasting
    {X S Y T Z U : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) (h : U ⟶ T)
    (p : Y ⟶ X) (q : Y ⟶ T) (t : Z ⟶ Y) (r : Z ⟶ U) (p₀ : Z ⟶ X)
    (hs : p ≫ f = q ≫ g) (hi : t ≫ q = r ≫ h) (hp : t ≫ p = p₀)
    (ho : p₀ ≫ f = r ≫ (h ≫ g)) (G : X.Modules) :
    letI : ∀ {V W : Scheme.{u}} (k : V ⟶ W),
      (Scheme.Modules.tensorPullback k).Additive :=
      fun {_ _} k ↦ Scheme.Modules.canonicalTensorPullbackAdditive.{u, w} k
    let e := ((Scheme.Modules.tensorPullbackSectionComp t p).symm.app G) ≪≫
      eqToIso (congrArg (fun k ↦ (Scheme.Modules.tensorPullback k).obj G) hp)
    (derivedPullback h).map (singleDegreeBaseChangeComposite f g p q hs 0 G) ≫
        singleDegreeBaseChangeComposite q h t r hi 0
          ((Scheme.Modules.tensorPullback p).obj G) ≫
        (schemeDerivedDirectImage r).map
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) 0).map e.hom) =
      (perfectHomComposition h g).hom.app ((schemeDerivedDirectImage f).obj
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj G)) ≫
        singleDegreeBaseChangeComposite f (h ≫ g) p₀ r ho 0 G := by
  classical
  subst p₀
  dsimp only
  let : ∀ {V W : Scheme.{u}} (k : V ⟶ W),
      (Scheme.Modules.tensorPullback k).Additive :=
    fun {_ _} k ↦ Scheme.Modules.canonicalTensorPullbackAdditive.{u, w} k
  dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at *
  let E := (DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj G
  let cp := pinnedModulePullbackComparisonAt p 0 G
  let ct := pinnedModulePullbackComparisonAt t 0 ((Scheme.Modules.tensorPullback p).obj G)
  let co := pinnedModulePullbackComparisonAt (t ≫ p) 0 G
  let a := (DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) 0).map
      ((Scheme.Modules.tensorPullbackSectionComp t p).inv.app G)
  let R := schemeDerivedDirectImage r
  let c : ∀ {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C),
      derivedPullback.{u, w} b ⋙ derivedPullback.{u, w} a ≅
        derivedPullback.{u, w} (a ≫ b) :=
    fun {_ _ _} a b ↦ perfectHomComposition a b
  have hn := schemeDerivedBaseChangeMap_naturality q r h t hi cp
  have hf := tensorPasting_horizontal f g h p q t r hs hi ho E
  have hc : (c t p).inv.app E ≫
      (derivedPullback t).map cp ≫ ct ≫ a = co := by
    have hs := tensorSingle_composition t p G
    change (perfectHomComposition t p).hom.app E ≫ co =
      (derivedPullback t).map cp ≫ ct ≫ a at hs
    exact inverse_comp_eq ((perfectHomComposition t p).app E) _ _ _ _ hs
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, eqToIso_refl,
    Iso.refl_hom, Category.comp_id]
  change (derivedPullback h).map
      (schemeDerivedBaseChangeMap f q g p hs E ≫ (schemeDerivedDirectImage q).map cp) ≫
      (schemeDerivedBaseChangeMap q r h t hi
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
            ((Scheme.Modules.tensorPullback p).obj G)) ≫ R.map ct) ≫ R.map a =
    (c h g).hom.app ((schemeDerivedDirectImage f).obj E) ≫
      (schemeDerivedBaseChangeMap f r (h ≫ g) (t ≫ p) ho E ≫ R.map co)
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn, ← Category.assoc _
    (schemeDerivedBaseChangeMap q r h t hi ((derivedPullback p).obj E)), hf]
  simpa only [c, Functor.map_comp, Category.assoc] using
    congrArg (fun k ↦ (c h g).hom.app
      ((schemeDerivedDirectImage f).obj E) ≫
      schemeDerivedBaseChangeMap f r (h ≫ g) (t ≫ p) ho E ≫ R.map k) hc

end AlgebraicGeometry
