/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.Order.Category.Preord
public import Mathlib.Order.WellFounded
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite

public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients

import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.AbelianImages

/-! # Derived left extension of arbitrary semilinear systems

Source: Zheng, Six Operations and Lefschetz--Verdier, Construction 4.1, printed p. 21;
Stacks Project, Tags 03DA, 03DB, 06YS, 06YT, 06XN and 09T5
(blueprint: lem-pur-system-level-left-extension).

Index `n : ℕ` denotes the positive level `n+1`. Strict systems have all iterated
transitions, with their identity and composition laws; this is equivalent to specifying
successive transitions. No normalization, coefficient flatness or bound is imposed.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w})

/-- Modules at the positive level `n+1`. Source: Zheng, Construction 4.1, p. 21
(blueprint: lem-pur-system-level-left-extension). -/
abbrev systemLevel (n : ℕ) :=
  ringedSiteModules.{w} (derivedChangeRingIndependentCoefficients J (B.obj (op n)))

/-- The actual coefficient restriction, not a chosen functor.
Source: Stacks 03CZ; Zheng, Construction 4.1
(blueprint: lem-pur-system-level-left-extension). -/
abbrev systemRestriction {m n : ℕ} (h : m ≤ n) : systemLevel B m ⥤ systemLevel B n :=
  restrictScalars ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map
    (B.map (homOfLE h).op))

/-- Strict semilinear systems with their iterated transitions. Identity and composition
are written on sections, avoiding any arbitrary scalar-restriction identifications.
Source: Zheng, Construction 4.1, p. 21
(blueprint: lem-pur-system-level-left-extension). -/
structure StrictRingSystem where
  level : ∀ n : ℕ, systemLevel B n
  transition : ∀ {m n : ℕ} (h : m ≤ n), level n ⟶ (systemRestriction B h).obj (level m)
  identity : ∀ (n : ℕ) (U : Cᵒᵖ) (x : (level n).val.obj U),
    (transition (Nat.le_refl n)).val.app U x = x
  compose : ∀ {l m n : ℕ} (h : l ≤ m) (k : m ≤ n) (U : Cᵒᵖ)
    (x : (level n).val.obj U),
    (transition (h.trans k)).val.app U x =
      (transition h).val.app U ((transition k).val.app U x)

variable {B}

/-- Componentwise linear maps commuting with the specified semilinear transitions.
Source: Zheng, Construction 4.1, p. 21
(blueprint: lem-pur-system-level-left-extension). -/
structure StrictRingSystem.Hom (M N : StrictRingSystem B) where
  app : ∀ n : ℕ, M.level n ⟶ N.level n
  comm : ∀ {m n : ℕ} (h : m ≤ n),
    app n ≫ N.transition h = M.transition h ≫ (systemRestriction B h).map (app m)

/-- Componentwise identities commute with transitions.
Source: Zheng, Construction 4.1 (blueprint: lem-pur-system-level-left-extension).
Proof: functoriality of scalar restriction and the two identity laws give both sides
as the same transition. -/
theorem strictRingSystem_id_comm (M : StrictRingSystem B) {m n : ℕ} (h : m ≤ n) :
    𝟙 (M.level n) ≫ M.transition h =
      M.transition h ≫ (systemRestriction B h).map (𝟙 (M.level m)) := by
  let _ := ‹J.WEqualsLocallyBijective AddCommGrpCat.{w}›
  let _ := ‹HasSheafify J AddCommGrpCat.{w}›
  simp

/-- Compatible families compose componentwise.
Source: Zheng, Construction 4.1 (blueprint: lem-pur-system-level-left-extension).
Proof: substitute the two compatibility squares and use associativity and preservation
of composition by scalar restriction. -/
theorem strictRingSystem_comp_comm {M N P : StrictRingSystem B}
    (f : M.Hom N) (g : N.Hom P) {m n : ℕ} (h : m ≤ n) :
    (f.app n ≫ g.app n) ≫ P.transition h =
      M.transition h ≫ (systemRestriction B h).map (f.app m ≫ g.app m) := by
  let _ := ‹J.WEqualsLocallyBijective AddCommGrpCat.{w}›
  let _ := ‹HasSheafify J AddCommGrpCat.{w}›
  rw [Functor.map_comp, Category.assoc, g.comm h, ← Category.assoc, f.comm h,
    Category.assoc]

/-- Identity system map. Source: Zheng, Construction 4.1
(blueprint: lem-pur-system-level-left-extension). -/
def StrictRingSystem.id (M : StrictRingSystem B) : M.Hom M :=
  ⟨fun _ ↦ 𝟙 _, strictRingSystem_id_comm M⟩

/-- Composition of system maps. Source: Zheng, Construction 4.1
(blueprint: lem-pur-system-level-left-extension). -/
def StrictRingSystem.Hom.comp {M N P : StrictRingSystem B} (f : M.Hom N) (g : N.Hom P) :
    M.Hom P :=
  ⟨fun n ↦ f.app n ≫ g.app n, strictRingSystem_comp_comm f g⟩

/-- Category laws for the componentwise operations.
Source: Zheng, Construction 4.1 (blueprint: lem-pur-system-level-left-extension).
Proof: extensionality reduces all three laws to the corresponding laws at every level;
compatibility proofs are irrelevant. -/
theorem strictRingSystem_category_laws :
    (∀ (M N : StrictRingSystem B) (f : M.Hom N),
      M.id.comp f = f ∧ f.comp N.id = f) ∧
    (∀ (M N P Q : StrictRingSystem B) (f : M.Hom N) (g : N.Hom P) (h : P.Hom Q),
      (f.comp g).comp h = f.comp (g.comp h)) := by
  have ext {M N : StrictRingSystem B} (f g : M.Hom N) (h : f.app = g.app) : f = g := by
    cases f
    cases g
    cases h
    rfl
  constructor
  · intro M N f
    constructor
    · apply ext
      funext n
      exact Category.id_comp _
    · apply ext
      funext n
      exact Category.comp_id _
  · intro M N P Q f g h
    apply ext
    funext n
    exact Category.assoc _ _ _

/-- The category of the displayed strict systems. Source: Zheng, Construction 4.1
(blueprint: lem-pur-system-level-left-extension). -/
instance strictRingSystemCategory : Category (StrictRingSystem B) where
  Hom := StrictRingSystem.Hom
  id := StrictRingSystem.id (B := B)
  comp := StrictRingSystem.Hom.comp (B := B)
  id_comp := fun f ↦ (strictRingSystem_category_laws (B := B) |>.1 _ _ f).1
  comp_id := fun f ↦ (strictRingSystem_category_laws (B := B) |>.1 _ _ f).2
  assoc := fun f g h ↦ strictRingSystem_category_laws (B := B) |>.2 _ _ _ _ f g h

variable (B)

/-- Evaluation of the actual strict system. Source: Zheng, Construction 4.1
(blueprint: lem-pur-system-level-left-extension). -/
def systemEvaluation (n : ℕ) : StrictRingSystem B ⥤ systemLevel B n where
  obj M := M.level n
  map f := f.app n

/-- The additive structure is fixed by componentwise evaluation.
Source: Stacks 03DA; Zheng, Construction 4.1
(blueprint: lem-pur-system-level-left-extension). -/
def StrictRingSystem.AbelianNormalized (a : Abelian (StrictRingSystem B)) : Prop :=
  @_root_.id Prop (by
    letI := a
    exact ∀ n : ℕ, (systemEvaluation B n).Additive)

/-- Exactness of scalar restriction, with no flatness of the ring map.
Source: Stacks 03DA and 03DB (blueprint: lem-pur-system-level-left-extension).
Proof: the underlying abelian sheaf and all its maps are unchanged. Kernels and
sheafified cokernels therefore coincide with those before restriction. -/
theorem systemScalarRestriction_exact {R S : Sheaf J CommRingCat.{w}} (φ : R ⟶ S) :
    PreservesFiniteLimits (restrictScalars.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map φ)) ∧
    PreservesFiniteColimits (restrictScalars.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map φ)) := by
  let R' := (sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R
  let S' := (sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj S
  let F := restrictScalars.{w}
    ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map φ)
  have : PreservesFiniteColimits (toSheaf.{w} R') :=
    inferInstance
  have : PreservesFiniteColimits (toSheaf.{w} S') :=
    inferInstance
  have : PreservesFiniteLimits (F ⋙ toSheaf R') := by
    change PreservesFiniteLimits (toSheaf S')
    infer_instance
  have : PreservesFiniteColimits (F ⋙ toSheaf R') := by
    change PreservesFiniteColimits (toSheaf S')
    infer_instance
  exact ⟨preservesFiniteLimits_of_reflects_of_preserves F (toSheaf R'),
    preservesFiniteColimits_of_reflects_of_preserves F (toSheaf R')⟩

/-- Exact restriction preserves finite limits. Source: Stacks 03DA
(blueprint: lem-pur-system-level-left-extension). -/
instance systemScalarRestrictionLimits {R S : Sheaf J CommRingCat.{w}} (φ : R ⟶ S) :
    PreservesFiniteLimits (restrictScalars.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map φ)) :=
  (systemScalarRestriction_exact φ).1
/-- Exact restriction preserves finite colimits. Source: Stacks 03DA
(blueprint: lem-pur-system-level-left-extension). -/
instance systemScalarRestrictionColimits {R S : Sheaf J CommRingCat.{w}} (φ : R ⟶ S) :
    PreservesFiniteColimits (restrictScalars.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map φ)) :=
  (systemScalarRestriction_exact φ).2


variable {B}

private theorem system_hom_ext {M N : StrictRingSystem B} (f g : M ⟶ N)
    (h : ∀ n, f.app n = g.app n) : f = g := by
  cases f
  cases g
  congr 1
  funext n
  exact h n

@[instance_reducible]
private def system_hom_group (M N : StrictRingSystem B) : AddCommGroup (M ⟶ N) := by
  letI : Zero (M ⟶ N) := ⟨⟨fun _ ↦ 0, by intros; simp⟩⟩
  letI : Add (M ⟶ N) := ⟨fun f g ↦ ⟨fun n ↦ f.app n + g.app n, by
    intros
    simp only [Preadditive.add_comp, Preadditive.comp_add, Functor.map_add, f.comm, g.comm]⟩⟩
  letI : Neg (M ⟶ N) := ⟨fun f ↦ ⟨fun n ↦ -f.app n, by
    intros
    simp only [Preadditive.neg_comp, Preadditive.comp_neg, Functor.map_neg, f.comm]⟩⟩
  exact
    { nsmul := nsmulRec
      zsmul := zsmulRec
      add_assoc := fun f g h ↦ system_hom_ext _ _ (fun n ↦ add_assoc _ _ _)
      zero_add := fun f ↦ system_hom_ext _ _ (fun n ↦ zero_add _)
      add_zero := fun f ↦ system_hom_ext _ _ (fun n ↦ add_zero _)
      neg_add_cancel := fun f ↦ system_hom_ext _ _ (fun n ↦ neg_add_cancel _)
      add_comm := fun f g ↦ system_hom_ext _ _ (fun n ↦ add_comm _ _) }

@[instance_reducible]
private def system_preadditive : Preadditive (StrictRingSystem B) where
  homGroup := system_hom_group
  add_comp _ _ _ f g h := system_hom_ext _ _
    (fun n ↦ Preadditive.add_comp _ _ _ (f.app n) (g.app n) (h.app n))
  comp_add _ _ _ f g h := system_hom_ext _ _
    (fun n ↦ Preadditive.comp_add _ _ _ (f.app n) (g.app n) (h.app n))

private theorem system_desc_comm {K : Type} [SmallCategory K]
    {F : K ⥤ StrictRingSystem B} (c : Cocone F)
    (hc : ∀ n, IsColimit ((systemEvaluation B n).mapCocone c)) (s : Cocone F)
    {m n : ℕ} (h : m ≤ n) :
    (hc n).desc ((systemEvaluation B n).mapCocone s) ≫ s.pt.transition h =
      c.pt.transition h ≫ (systemRestriction B h).map
        ((hc m).desc ((systemEvaluation B m).mapCocone s)) := by
  apply (hc n).hom_ext
  intro j
  change (c.ι.app j).app n ≫ _ = (c.ι.app j).app n ≫ _
  erw [← Category.assoc, (hc n).fac ((systemEvaluation B n).mapCocone s) j]
  erw [← Category.assoc, (c.ι.app j).comm h, Category.assoc, ← Functor.map_comp,
    (hc m).fac ((systemEvaluation B m).mapCocone s) j]
  exact (s.ι.app j).comm h

private def system_isColimit {K : Type} [SmallCategory K]
    {F : K ⥤ StrictRingSystem B} (c : Cocone F)
    (hc : ∀ n, IsColimit ((systemEvaluation B n).mapCocone c)) : IsColimit c where
  desc s :=
    { app := fun n ↦ (hc n).desc ((systemEvaluation B n).mapCocone s)
      comm := system_desc_comm c hc s }
  fac s j := system_hom_ext _ _ (fun n ↦ (hc n).fac _ j)
  uniq s f hf := by
    apply system_hom_ext
    intro n
    apply (hc n).uniq ((systemEvaluation B n).mapCocone s) (f.app n)
    intro j
    exact congrArg (fun g : F.obj j ⟶ s.pt ↦ g.app n) (hf j)

private theorem system_lift_comm {K : Type} [SmallCategory K] [FinCategory K]
    {F : K ⥤ StrictRingSystem B} (c : Cone F)
    (hc : ∀ n, IsLimit ((systemEvaluation B n).mapCone c)) (s : Cone F)
    {m n : ℕ} (h : m ≤ n) :
    (hc n).lift ((systemEvaluation B n).mapCone s) ≫ c.pt.transition h =
      s.pt.transition h ≫ (systemRestriction B h).map
        ((hc m).lift ((systemEvaluation B m).mapCone s)) := by
  apply (isLimitOfPreserves (systemRestriction B h) (hc m)).hom_ext
  intro j
  change _ ≫ (systemRestriction B h).map ((c.π.app j).app m) =
    _ ≫ (systemRestriction B h).map ((c.π.app j).app m)
  erw [Category.assoc, ← (c.π.app j).comm h, ← Category.assoc,
    (hc n).fac ((systemEvaluation B n).mapCone s) j]
  erw [Category.assoc, ← Functor.map_comp,
    (hc m).fac ((systemEvaluation B m).mapCone s) j]
  exact (s.π.app j).comm h

private def system_isLimit {K : Type} [SmallCategory K] [FinCategory K]
    {F : K ⥤ StrictRingSystem B} (c : Cone F)
    (hc : ∀ n, IsLimit ((systemEvaluation B n).mapCone c)) : IsLimit c where
  lift s :=
    { app := fun n ↦ (hc n).lift ((systemEvaluation B n).mapCone s)
      comm := system_lift_comm c hc s }
  fac s j := system_hom_ext _ _ (fun n ↦ (hc n).fac _ j)
  uniq s f hf := by
    apply system_hom_ext
    intro n
    apply (hc n).uniq ((systemEvaluation B n).mapCone s) (f.app n)
    intro j
    exact congrArg (fun g : s.pt ⟶ F.obj j ↦ g.app n) (hf j)

private abbrev system_underlying (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (n : ℕ) :=
  toSheaf.{w} ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj (B.obj (op n)))

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}] in
private theorem system_underlying_restrict {m n : ℕ} (h : m ≤ n)
    {X Y : systemLevel B m} (f : X ⟶ Y) :
    (system_underlying B n).map ((systemRestriction B h).map f) =
      (system_underlying B m).map f := rfl

private theorem system_colimit_transition_naturality {K : Type}
    [SmallCategory K] [FinCategory K] (F : K ⥤ StrictRingSystem B)
    {m n : ℕ} (h : m ≤ n) {j k : K} (f : j ⟶ k) :
    (F.map f).app n ≫ ((F.obj k).transition h ≫
        (systemRestriction B h).map (colimit.ι (F ⋙ systemEvaluation B m) k)) =
      ((F.obj j).transition h ≫
        (systemRestriction B h).map (colimit.ι (F ⋙ systemEvaluation B m) j)) ≫ 𝟙 _ := by
  rw [Category.comp_id, ← Category.assoc, (F.map f).comm h,
    Category.assoc, ← Functor.map_comp]
  exact congrArg (fun g ↦ (F.obj j).transition h ≫ (systemRestriction B h).map g)
    (colimit.w (F ⋙ systemEvaluation B m) f)

private def system_colimit_transition {K : Type} [SmallCategory K] [FinCategory K]
    (F : K ⥤ StrictRingSystem B) {m n : ℕ} (h : m ≤ n) :
    colimit (F ⋙ systemEvaluation B n) ⟶
      (systemRestriction B h).obj (colimit (F ⋙ systemEvaluation B m)) :=
  colimit.desc (F ⋙ systemEvaluation B n)
    { pt := (systemRestriction B h).obj (colimit (F ⋙ systemEvaluation B m))
      ι :=
        { app := fun j ↦ (F.obj j).transition h ≫
            (systemRestriction B h).map (colimit.ι (F ⋙ systemEvaluation B m) j)
          naturality := fun _ _ f ↦ system_colimit_transition_naturality F h f } }

private theorem system_colimit_transition_fac {K : Type} [SmallCategory K] [FinCategory K]
    (F : K ⥤ StrictRingSystem B) {m n : ℕ} (h : m ≤ n) (j : K) :
    colimit.ι (F ⋙ systemEvaluation B n) j ≫ system_colimit_transition F h =
      (F.obj j).transition h ≫
        (systemRestriction B h).map (colimit.ι (F ⋙ systemEvaluation B m) j) := by
  apply colimit.ι_desc

private theorem system_colimit_transition_forget {K : Type} [SmallCategory K]
    [FinCategory K] (F : K ⥤ StrictRingSystem B) {m n : ℕ} (h : m ≤ n) (j : K) :
    (system_underlying B n).map (colimit.ι (F ⋙ systemEvaluation B n) j) ≫
        (system_underlying B n).map (system_colimit_transition F h) =
      (system_underlying B n).map ((F.obj j).transition h) ≫
        (system_underlying B m).map (colimit.ι (F ⋙ systemEvaluation B m) j) := by
  simpa only [Functor.map_comp, system_underlying_restrict] using
    congrArg (system_underlying B n).map (system_colimit_transition_fac F h j)

private theorem system_colimit_identity {K : Type} [SmallCategory K] [FinCategory K]
    (F : K ⥤ StrictRingSystem B) (n : ℕ)
    (U : Cᵒᵖ) (x : (colimit (F ⋙ systemEvaluation B n)).val.obj U) :
    (system_colimit_transition F (Nat.le_refl n)).val.app U x = x := by
  let R := (sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj (B.obj (op n))
  have : PreservesFiniteColimits (toSheaf.{w} R) :=
    inferInstance
  have he : (toSheaf R).map (system_colimit_transition F (Nat.le_refl n)) =
      𝟙 ((toSheaf R).obj (colimit (F ⋙ systemEvaluation B n))) := by
    apply (isColimitOfPreserves (toSheaf R)
      (colimit.isColimit (F ⋙ systemEvaluation B n))).hom_ext
    intro j
    change (toSheaf R).map (colimit.ι (F ⋙ systemEvaluation B n) j) ≫ _ =
      (toSheaf R).map (colimit.ι (F ⋙ systemEvaluation B n) j) ≫ _
    rw [← Functor.map_comp, system_colimit_transition_fac]
    ext V y
    change (colimit.ι (F ⋙ systemEvaluation B n) j).val.app V
        (((F.obj j).transition (Nat.le_refl n)).val.app V y) =
      (colimit.ι (F ⋙ systemEvaluation B n) j).val.app V y
    rw [(F.obj j).identity]
  exact congrArg (fun f : (toSheaf R).obj (colimit (F ⋙ systemEvaluation B n)) ⟶
    (toSheaf R).obj (colimit (F ⋙ systemEvaluation B n)) ↦ f.hom.app U x) he

private theorem system_colimit_compose {K : Type} [SmallCategory K] [FinCategory K]
    (F : K ⥤ StrictRingSystem B) {l m n : ℕ}
    (h : l ≤ m) (k : m ≤ n) (U : Cᵒᵖ)
    (x : (colimit (F ⋙ systemEvaluation B n)).val.obj U) :
    (system_colimit_transition F (h.trans k)).val.app U x =
      (system_colimit_transition F h).val.app U
        ((system_colimit_transition F k).val.app U x) := by
  let R (i : ℕ) :=
    (sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj (B.obj (op i))
  have : PreservesFiniteColimits (toSheaf.{w} (R n)) :=
    inferInstance
  have he : (toSheaf (R n)).map (system_colimit_transition F (h.trans k)) =
      (toSheaf (R n)).map (system_colimit_transition F k) ≫
        (toSheaf (R m)).map (system_colimit_transition F h) := by
    apply (isColimitOfPreserves (toSheaf (R n))
      (colimit.isColimit (F ⋙ systemEvaluation B n))).hom_ext
    intro j
    change (toSheaf (R n)).map (colimit.ι (F ⋙ systemEvaluation B n) j) ≫ _ =
      (toSheaf (R n)).map (colimit.ι (F ⋙ systemEvaluation B n) j) ≫ _
    rw [system_colimit_transition_forget, ← Category.assoc,
      system_colimit_transition_forget, Category.assoc,
      system_colimit_transition_forget]
    ext V y
    change (colimit.ι (F ⋙ systemEvaluation B l) j).val.app V
        (((F.obj j).transition (h.trans k)).val.app V y) =
      (colimit.ι (F ⋙ systemEvaluation B l) j).val.app V
        (((F.obj j).transition h).val.app V (((F.obj j).transition k).val.app V y))
    rw [(F.obj j).compose]
  exact congrArg (fun f : (toSheaf (R n)).obj (colimit (F ⋙ systemEvaluation B n)) ⟶
    (toSheaf (R l)).obj (colimit (F ⋙ systemEvaluation B l)) ↦ f.hom.app U x) he

private def system_colimit_object {K : Type} [SmallCategory K] [FinCategory K]
    (F : K ⥤ StrictRingSystem B) : StrictRingSystem B where
  level n := colimit (F ⋙ systemEvaluation B n)
  transition h := system_colimit_transition F h
  identity n U x := system_colimit_identity F n U x
  compose h k U x := system_colimit_compose F h k U x

private def system_colimit_cocone {K : Type} [SmallCategory K] [FinCategory K]
    (F : K ⥤ StrictRingSystem B) : Cocone F where
  pt := system_colimit_object F
  ι :=
    { app := fun j ↦
        { app := fun n ↦ colimit.ι (F ⋙ systemEvaluation B n) j
          comm := fun h ↦ system_colimit_transition_fac F h j }
      naturality := by
        intro j k f
        apply system_hom_ext
        intro n
        change (F.map f).app n ≫ colimit.ι (F ⋙ systemEvaluation B n) k =
          colimit.ι (F ⋙ systemEvaluation B n) j ≫ 𝟙 _
        have hh := colimit.w (F ⋙ systemEvaluation B n) f
        change (F.map f).app n ≫ colimit.ι (F ⋙ systemEvaluation B n) k = _ at hh
        simpa only [Category.comp_id] using hh }

private theorem system_limit_transition_naturality {K : Type}
    [SmallCategory K] [FinCategory K] (F : K ⥤ StrictRingSystem B)
    {m n : ℕ} (h : m ≤ n) {j k : K} (f : j ⟶ k) :
    𝟙 _ ≫ (limit.π (F ⋙ systemEvaluation B n) k ≫ (F.obj k).transition h) =
      (limit.π (F ⋙ systemEvaluation B n) j ≫ (F.obj j).transition h) ≫
        (systemRestriction B h).map ((F.map f).app m) := by
  rw [Category.id_comp, Category.assoc, ← (F.map f).comm h, ← Category.assoc]
  exact congrArg (fun g ↦ g ≫ (F.obj k).transition h)
    (limit.w (F ⋙ systemEvaluation B n) f).symm

private def system_limit_transition {K : Type} [SmallCategory K] [FinCategory K]
    (F : K ⥤ StrictRingSystem B) {m n : ℕ} (h : m ≤ n) :
    limit (F ⋙ systemEvaluation B n) ⟶
      (systemRestriction B h).obj (limit (F ⋙ systemEvaluation B m)) :=
  (isLimitOfPreserves (systemRestriction B h)
    (limit.isLimit (F ⋙ systemEvaluation B m))).lift
    { pt := limit (F ⋙ systemEvaluation B n)
      π :=
        { app := fun j ↦ limit.π (F ⋙ systemEvaluation B n) j ≫ (F.obj j).transition h
          naturality := fun _ _ f ↦ system_limit_transition_naturality F h f } }

private theorem system_limit_transition_fac {K : Type} [SmallCategory K] [FinCategory K]
    (F : K ⥤ StrictRingSystem B) {m n : ℕ} (h : m ≤ n) (j : K) :
    system_limit_transition F h ≫
        (systemRestriction B h).map (limit.π (F ⋙ systemEvaluation B m) j) =
      limit.π (F ⋙ systemEvaluation B n) j ≫ (F.obj j).transition h := by
  apply IsLimit.fac

private theorem system_limit_transition_forget {K : Type} [SmallCategory K]
    [FinCategory K] (F : K ⥤ StrictRingSystem B) {m n : ℕ} (h : m ≤ n) (j : K) :
    (system_underlying B n).map (system_limit_transition F h) ≫
        (system_underlying B m).map (limit.π (F ⋙ systemEvaluation B m) j) =
      (system_underlying B n).map (limit.π (F ⋙ systemEvaluation B n) j) ≫
        (system_underlying B n).map ((F.obj j).transition h) := by
  simpa only [Functor.map_comp, system_underlying_restrict] using
    congrArg (system_underlying B n).map (system_limit_transition_fac F h j)

private theorem system_limit_identity {K : Type} [SmallCategory K] [FinCategory K]
    (F : K ⥤ StrictRingSystem B) (n : ℕ)
    (U : Cᵒᵖ) (x : (limit (F ⋙ systemEvaluation B n)).val.obj U) :
    (system_limit_transition F (Nat.le_refl n)).val.app U x = x := by
  let R := (sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj (B.obj (op n))
  have he : (toSheaf R).map (system_limit_transition F (Nat.le_refl n)) =
      𝟙 ((toSheaf R).obj (limit (F ⋙ systemEvaluation B n))) := by
    apply (isLimitOfPreserves (toSheaf R)
      (limit.isLimit (F ⋙ systemEvaluation B n))).hom_ext
    intro j
    change _ ≫ (toSheaf R).map (limit.π (F ⋙ systemEvaluation B n) j) =
      _ ≫ (toSheaf R).map (limit.π (F ⋙ systemEvaluation B n) j)
    rw [system_limit_transition_forget]
    ext V y
    change ((F.obj j).transition (Nat.le_refl n)).val.app V
        ((limit.π (F ⋙ systemEvaluation B n) j).val.app V y) =
      (limit.π (F ⋙ systemEvaluation B n) j).val.app V y
    rw [(F.obj j).identity]
  exact congrArg (fun f : (toSheaf R).obj (limit (F ⋙ systemEvaluation B n)) ⟶
    (toSheaf R).obj (limit (F ⋙ systemEvaluation B n)) ↦ f.hom.app U x) he

private theorem system_limit_compose {K : Type} [SmallCategory K] [FinCategory K]
    (F : K ⥤ StrictRingSystem B) {l m n : ℕ}
    (h : l ≤ m) (k : m ≤ n) (U : Cᵒᵖ)
    (x : (limit (F ⋙ systemEvaluation B n)).val.obj U) :
    (system_limit_transition F (h.trans k)).val.app U x =
      (system_limit_transition F h).val.app U
        ((system_limit_transition F k).val.app U x) := by
  let R (i : ℕ) :=
    (sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj (B.obj (op i))
  have he : (toSheaf (R n)).map (system_limit_transition F (h.trans k)) =
      (toSheaf (R n)).map (system_limit_transition F k) ≫
        (toSheaf (R m)).map (system_limit_transition F h) := by
    apply (isLimitOfPreserves (toSheaf (R l))
      (limit.isLimit (F ⋙ systemEvaluation B l))).hom_ext
    intro j
    change _ ≫ (toSheaf (R l)).map (limit.π (F ⋙ systemEvaluation B l) j) =
      _ ≫ (toSheaf (R l)).map (limit.π (F ⋙ systemEvaluation B l) j)
    rw [system_limit_transition_forget, Category.assoc,
      system_limit_transition_forget,
      ← Category.assoc, system_limit_transition_forget]
    ext V y
    change ((F.obj j).transition (h.trans k)).val.app V
        ((limit.π (F ⋙ systemEvaluation B n) j).val.app V y) =
      ((F.obj j).transition h).val.app V
        (((F.obj j).transition k).val.app V
          ((limit.π (F ⋙ systemEvaluation B n) j).val.app V y))
    rw [(F.obj j).compose]
  exact congrArg (fun f : (toSheaf (R n)).obj (limit (F ⋙ systemEvaluation B n)) ⟶
    (toSheaf (R l)).obj (limit (F ⋙ systemEvaluation B l)) ↦ f.hom.app U x) he

private def system_limit_object {K : Type} [SmallCategory K] [FinCategory K]
    (F : K ⥤ StrictRingSystem B) : StrictRingSystem B where
  level n := limit (F ⋙ systemEvaluation B n)
  transition h := system_limit_transition F h
  identity n U x := system_limit_identity F n U x
  compose h k U x := system_limit_compose F h k U x

private def system_limit_cone {K : Type} [SmallCategory K] [FinCategory K]
    (F : K ⥤ StrictRingSystem B) : Cone F where
  pt := system_limit_object F
  π :=
    { app := fun j ↦
        { app := fun n ↦ limit.π (F ⋙ systemEvaluation B n) j
          comm := fun h ↦ (system_limit_transition_fac F h j).symm }
      naturality := by
        intro j k f
        apply system_hom_ext
        intro n
        change 𝟙 _ ≫ limit.π (F ⋙ systemEvaluation B n) k =
          limit.π (F ⋙ systemEvaluation B n) j ≫ (F.map f).app n
        have hh := (limit.w (F ⋙ systemEvaluation B n) f).symm
        change limit.π (F ⋙ systemEvaluation B n) k =
          limit.π (F ⋙ systemEvaluation B n) j ≫ (F.map f).app n at hh
        simpa only [Category.id_comp] using hh }

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

private theorem system_isIso {M N : StrictRingSystem B} (f : M ⟶ N)
    (hf : ∀ n, IsIso (f.app n)) : IsIso f := by
  have := hf
  let g : N ⟶ M :=
    { app := fun n ↦ inv (f.app n)
      comm := by
        intro m n h
        apply (cancel_mono ((systemRestriction B h).map (f.app m))).1
        simp only [Category.assoc]
        rw [← Functor.map_comp, IsIso.inv_hom_id, CategoryTheory.Functor.map_id,
          Category.comp_id, ← f.comm h, IsIso.inv_hom_id_assoc] }
  exact ⟨⟨g, system_hom_ext _ _ (fun n ↦ IsIso.hom_inv_id _),
    system_hom_ext _ _ (fun n ↦ IsIso.inv_hom_id _)⟩⟩

private theorem system_finiteLimits : HasFiniteLimits (StrictRingSystem B) :=
  ⟨fun _ _ _ ↦ ⟨fun F ↦ ⟨⟨system_limit_cone F,
    system_isLimit _ (fun n ↦ limit.isLimit (F ⋙ systemEvaluation B n))⟩⟩⟩⟩

private theorem system_finiteColimits : HasFiniteColimits (StrictRingSystem B) :=
  ⟨fun _ _ _ ↦ ⟨fun F ↦ ⟨⟨system_colimit_cocone F,
    system_isColimit _ (fun n ↦ colimit.isColimit (F ⋙ systemEvaluation B n))⟩⟩⟩⟩

private theorem system_evaluation_limits (n : ℕ) :
    PreservesFiniteLimits (systemEvaluation B n) := by
  constructor
  intro K _ _
  constructor
  intro F
  exact preservesLimit_of_preserves_limit_cone
    (system_isLimit (system_limit_cone F)
      (fun i ↦ limit.isLimit (F ⋙ systemEvaluation B i)))
    (limit.isLimit (F ⋙ systemEvaluation B n))

private theorem system_evaluation_colimits (n : ℕ) :
    PreservesFiniteColimits (systemEvaluation B n) := by
  constructor
  intro K _ _
  constructor
  intro F
  exact preservesColimit_of_preserves_colimit_cocone
    (system_isColimit (system_colimit_cocone F)
      (fun i ↦ colimit.isColimit (F ⋙ systemEvaluation B i)))
    (colimit.isColimit (F ⋙ systemEvaluation B n))

section AbelianComparison
universe ca cv da dv
variable {A : Type ca} [Category.{cv} A] [Preadditive A]
  [HasFiniteLimits A] [HasFiniteColimits A]
  {D : Type da} [Category.{dv} D] [Abelian D]

private theorem system_mappedComparison_isIso (E : A ⥤ D) [E.Additive]
    [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    {X Y : A} (f : X ⟶ Y) : IsIso (E.map (Abelian.coimageImageComparison f)) :=
  (Arrow.isIso_iff_isIso_of_isIso
    (Abelian.PreservesCoimageImageComparison.iso E f).hom).mpr inferInstance

private theorem system_abelian_of_comparison (P : Preadditive A → Prop)
    (hp : P (inferInstance : Preadditive A))
    (h : ∀ {X Y : A} (f : X ⟶ Y), IsIso (Abelian.coimageImageComparison f)) :
    ∃ a : Abelian A, P a.toPreadditive := by
  have {X Y : A} (f : X ⟶ Y) : IsIso (Abelian.coimageImageComparison f) := h f
  exact ⟨Abelian.ofCoimageImageComparisonIsIso, hp⟩

end AbelianComparison

private theorem system_foundation_exists :
    ∃ a : Abelian (StrictRingSystem B), StrictRingSystem.AbelianNormalized B a ∧
      ∀ n, PreservesFiniteLimits (systemEvaluation B n) ∧
        PreservesFiniteColimits (systemEvaluation B n) := by
  let := system_preadditive (B := B)
  have (n : ℕ) : (systemEvaluation B n).Additive := ⟨by intros; rfl⟩
  have : HasFiniteLimits (StrictRingSystem B) := system_finiteLimits
  have : HasFiniteColimits (StrictRingSystem B) := system_finiteColimits
  have (n : ℕ) : PreservesFiniteLimits (systemEvaluation B n) := system_evaluation_limits n
  have (n : ℕ) : PreservesFiniteColimits (systemEvaluation B n) := system_evaluation_colimits n
  have {M N : StrictRingSystem B} (f : M ⟶ N) :
      IsIso (Abelian.coimageImageComparison f) := by
    apply system_isIso
    intro n
    exact system_mappedComparison_isIso (A := StrictRingSystem B) (D := systemLevel B n)
      (systemEvaluation B n) f
  exact system_abelian_of_comparison (A := StrictRingSystem B)
    (fun p ↦ (letI := p; ∀ n, (systemEvaluation B n).Additive) ∧
      ∀ n, PreservesFiniteLimits (systemEvaluation B n) ∧
        PreservesFiniteColimits (systemEvaluation B n))
    ⟨fun _ ↦ inferInstance, fun _ ↦ ⟨inferInstance, inferInstance⟩⟩
    (fun _ ↦ inferInstance)

private theorem system_add_app (a : Abelian (StrictRingSystem B))
    (ha : StrictRingSystem.AbelianNormalized B a) {M N : StrictRingSystem B}
    (f g : M ⟶ N) (n : ℕ) :
    (letI := a; (f + g).app n) = f.app n + g.app n := by
  let := a
  have := ha n
  exact (systemEvaluation B n).map_add

private theorem system_preadditive_ext (a b : Abelian (StrictRingSystem B))
    (ha : StrictRingSystem.AbelianNormalized B a)
    (hb : StrictRingSystem.AbelianNormalized B b) : a.toPreadditive = b.toPreadditive := by
  apply Preadditive.ext
  funext M N
  apply AddCommGroup.ext
  funext f g
  apply system_hom_ext
  intro n
  exact (system_add_app a ha f g n).trans (system_add_app b hb f g n).symm

private theorem system_abelian_ext (a b : Abelian (StrictRingSystem B))
    (h : a.toPreadditive = b.toPreadditive) : a = b := by
  cases a
  cases b
  cases h
  rfl

variable (B)

/-- The unique componentwise abelian structure.
Source: Stacks 03DA and 03DB (blueprint: lem-pur-system-level-left-extension).
Proof: add linear maps componentwise. Restriction is additive, so the compatibility
condition is closed under addition. Componentwise finite cones and cocones give finite
limits and colimits preserved by evaluations. Evaluations jointly reflect isomorphisms,
so every coimage-image comparison is invertible by its component comparisons. Mathlib's
criterion gives the abelian structure. Normalized additive evaluations fix addition;
`AddCommGroup.ext` and `Preadditive.ext` give uniqueness of the preadditive structure.
All other abelian fields are Prop. -/
theorem strictRingSystem_abelian_exists :
    ∃! a : Abelian (StrictRingSystem B), StrictRingSystem.AbelianNormalized B a := by
  obtain ⟨a, ha, _⟩ := system_foundation_exists (B := B)
  refine ⟨a, ha, ?_⟩
  intro b hb
  exact system_abelian_ext b a (system_preadditive_ext b a hb ha)

/-- The abelian structure determined uniquely by componentwise addition.
Source: Stacks 03DA (blueprint: lem-pur-system-level-left-extension). -/
instance strictRingSystemAbelian : Abelian (StrictRingSystem B) :=
  (strictRingSystem_abelian_exists B).exists.choose

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- Evaluation is additive and exact.
Source: Stacks 03DA and 03DB (blueprint: lem-pur-system-level-left-extension).
Proof: use componentwise addition, kernels, finite biproducts and sheafified cokernels
from the preceding construction. Coverings do not change the level. -/
theorem systemEvaluation_exact (n : ℕ) :
    (systemEvaluation B n).Additive ∧ PreservesFiniteLimits (systemEvaluation B n) ∧
      PreservesFiniteColimits (systemEvaluation B n) := by
  exact ⟨(strictRingSystem_abelian_exists B).exists.choose_spec n,
    ((system_foundation_exists (B := B)).choose_spec.2 n).1,
    ((system_foundation_exists (B := B)).choose_spec.2 n).2⟩

/-- Additivity witness. Source: Stacks 03DA
(blueprint: lem-pur-system-level-left-extension). -/
instance systemEvaluationAdditive (n : ℕ) : (systemEvaluation B n).Additive :=
  (systemEvaluation_exact B n).1
/-- Finite-limit witness. Source: Stacks 03DA
(blueprint: lem-pur-system-level-left-extension). -/
instance systemEvaluationLimits (n : ℕ) : PreservesFiniteLimits (systemEvaluation B n) :=
  (systemEvaluation_exact B n).2.1
/-- Finite-colimit witness. Source: Stacks 03DA
(blueprint: lem-pur-system-level-left-extension). -/
instance systemEvaluationColimits (n : ℕ) : PreservesFiniteColimits (systemEvaluation B n) :=
  (systemEvaluation_exact B n).2.2

/-- Standard localization at a coefficient level; no restriction on cohomological bounds.
Source: Stacks 05RU (blueprint: lem-pur-system-level-left-extension). -/
instance systemRingHasDerived (R : Sheaf J CommRingCat.{w}) :
    HasDerivedCategory (ringedSiteModules.{w} (derivedChangeRingIndependentCoefficients J R)) :=
  HasDerivedCategory.standard _
/-- Standard localization of the strict abelian category.
Source: Stacks 05RU (blueprint: lem-pur-system-level-left-extension). -/
instance strictRingSystemHasDerived : HasDerivedCategory (StrictRingSystem B) :=
  HasDerivedCategory.standard _

/-- Exact derived evaluation, using the recorded ordinary derived category.
Source: Zheng, Construction 4.1 (blueprint: lem-pur-system-level-left-extension). -/
abbrev derivedSystemEvaluation (n : ℕ) := (systemEvaluation B n).mapDerivedCategory

/-- The actual selected coefficient sequence, including its composite ring maps.
Source: the subsequence construction extending Zheng 4.1
(blueprint: lem-pur-system-level-left-extension). -/
def selectedSystemRings (r : ℕ ↪o ℕ) : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w} :=
  r.toOrderHom.monotone.functor.op ⋙ B

/-- Restriction of strict systems to selected levels, on objects and maps.
Source: the subsequence construction extending Zheng 4.1
(blueprint: lem-pur-system-level-left-extension). -/
def systemSubsequence (r : ℕ ↪o ℕ) : StrictRingSystem B ⥤
    StrictRingSystem (selectedSystemRings B r) where
  obj M :=
    { level := fun n ↦ M.level (r n)
      transition := fun {_ _} h ↦ M.transition (r.monotone h)
      identity := fun n ↦ M.identity (r n)
      compose := fun h k ↦ M.compose (r.monotone h) (r.monotone k) }
  map f := { app := fun n ↦ f.app (r n), comm := fun h ↦ f.comm (r.monotone h) }

/-- Exactness of the actual restriction to a subsequence.
Source: Stacks 03DA and 03DB (blueprint: lem-pur-system-level-left-extension).
Proof: restriction just selects components; addition, kernels and cokernels are computed
at those components. -/
theorem systemSubsequence_exact (r : ℕ ↪o ℕ) :
    (systemSubsequence B r).Additive ∧ PreservesFiniteLimits (systemSubsequence B r) ∧
      PreservesFiniteColimits (systemSubsequence B r) := by
  have hadd : (systemSubsequence B r).Additive := by
    constructor
    intro M N f g
    apply system_hom_ext
    intro n
    change (systemEvaluation B (r n)).map (f + g) =
      (systemEvaluation (selectedSystemRings B r) n).map
        ((systemSubsequence B r).map f + (systemSubsequence B r).map g)
    rw [Functor.map_add, Functor.map_add]
    rfl
  refine ⟨hadd, ⟨?_⟩, ⟨?_⟩⟩
  · intro K _ _
    constructor
    intro F
    apply preservesLimit_of_preserves_limit_cone (limit.isLimit F)
    apply system_isLimit
    intro n
    exact isLimitOfPreserves (systemEvaluation B (r n)) (limit.isLimit F)
  · intro K _ _
    constructor
    intro F
    apply preservesColimit_of_preserves_colimit_cocone (colimit.isColimit F)
    apply system_isColimit
    intro n
    exact isColimitOfPreserves (systemEvaluation B (r n)) (colimit.isColimit F)

/-- Additivity of restriction. Source: Stacks 03DA
(blueprint: lem-pur-system-level-left-extension). -/
instance systemSubsequenceAdditive (r : ℕ ↪o ℕ) : (systemSubsequence B r).Additive :=
  (systemSubsequence_exact B r).1
/-- Finite-limit preservation. Source: Stacks 03DA
(blueprint: lem-pur-system-level-left-extension). -/
instance systemSubsequenceLimits (r : ℕ ↪o ℕ) : PreservesFiniteLimits (systemSubsequence B r) :=
  (systemSubsequence_exact B r).2.1
/-- Finite-colimit preservation. Source: Stacks 03DA
(blueprint: lem-pur-system-level-left-extension). -/
instance systemSubsequenceColimits (r : ℕ ↪o ℕ) : PreservesFiniteColimits (systemSubsequence B r) :=
  (systemSubsequence_exact B r).2.2

/-- Derived restriction to selected levels is the exact termwise restriction.
Source: Stacks 015F (blueprint: lem-pur-system-level-left-extension). -/
abbrev derivedSystemSubsequence (r : ℕ ↪o ℕ) := (systemSubsequence B r).mapDerivedCategory

/-- The first selected level above `m`. Every strictly increasing sequence of naturals
is unbounded, since `m ≤ r m`. Source: the subsequence construction extending Zheng 4.1
(blueprint: lem-pur-system-level-left-extension). -/
def systemNextSelected (r : ℕ ↪o ℕ) (m : ℕ) : ℕ :=
  Nat.find (⟨m, r.strictMono.id_le m⟩ : ∃ i, m ≤ r i)


/-- The selected index exists and is minimal.
Source: the subsequence extension of Zheng 4.1
(blueprint: lem-pur-system-level-left-extension).
Proof: apply the specification and minimality of Nat.find to m ≤ r m. -/
theorem systemNextSelected_spec (r : ℕ ↪o ℕ) (m : ℕ) :
    m ≤ r (systemNextSelected r m) ∧
      ∀ i : ℕ, m ≤ r i → systemNextSelected r m ≤ i := by
  dsimp only [systemNextSelected]
  exact ⟨Nat.find_spec (⟨m, r.strictMono.id_le m⟩ : ∃ i, m ≤ r i),
    fun i hi ↦ Nat.find_min' (⟨m, r.strictMono.id_le m⟩ : ∃ i, m ≤ r i) hi⟩

/-- The first selected index is monotone, including its constant intervals.
Source: the subsequence extension of Zheng 4.1
(blueprint: lem-pur-system-level-left-extension).
Proof: r(t(m+1)) ≥ m+1 ≥ m, so the minimality of t(m) gives the result. -/
theorem systemNextSelected_mono (r : ℕ ↪o ℕ) (m : ℕ) :
    systemNextSelected r m ≤ systemNextSelected r (m + 1) := by
  exact (systemNextSelected_spec r m).2 _
    ((Nat.le_succ m).trans (systemNextSelected_spec r (m + 1)).1)

/-- The first selected index of a composite selection is computed in two steps:
`t_{r∘s}(m) = t_s(t_r(m))`. Source: the subsequence extension of Zheng 4.1
(blueprint: lem-pur-system-level-left-extension), node proof step 12.
Proof: since `r` is strictly increasing, `m ≤ r j` iff `t_r(m) ≤ j` by the specification and
minimality of `t_r(m)`. Hence `m ≤ r (s i)` iff `t_r(m) ≤ s i` iff `t_s(t_r(m)) ≤ i`, so both
sides are the least such `i`. -/
theorem systemNextSelected_trans (r s : ℕ ↪o ℕ) (m : ℕ) :
    systemNextSelected (s.trans r) m = systemNextSelected s (systemNextSelected r m) := by
  apply Nat.le_antisymm
  · exact (systemNextSelected_spec (s.trans r) m).2 _
      ((systemNextSelected_spec r m).1.trans
        (r.monotone (systemNextSelected_spec s (systemNextSelected r m)).1))
  · apply (systemNextSelected_spec s (systemNextSelected r m)).2
    exact (systemNextSelected_spec r m).2 _
      (systemNextSelected_spec (s.trans r) m).1

/-- The actual iterated transition, as a natural transformation of evaluations.
Source: Zheng, Construction 4.1 (blueprint: lem-pur-system-level-left-extension). -/
def strictSystemTransition {m n : ℕ} (h : m ≤ n) :
    systemEvaluation B n ⟶ systemEvaluation B m ⋙ systemRestriction B h where
  app M := M.transition h
  naturality _ _ f := f.comm h

variable {B}


set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

section GeneralDerivedExtension
universe a av b bv dA dB
variable {A : Type a} [Category.{av} A] [Abelian A] [HasDerivedCategory.{dA} A]
  {D : Type b} [Category.{bv} D] [Abelian D] [HasDerivedCategory.{dB} D]
  (R : D ⥤ A) [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
  (resolving : CochainComplex A ℤ → Prop)

/-- An ordinary left extension and its total left derived pair, with the adjunction
normalized by the strict transpose. This packages the left-extension notion already
stated in the node; the right functor is always the actual evaluation or restriction.
Source: Zheng 4.1; Stacks 06XN, 0FND and 09T5
(blueprint: lem-pur-system-level-left-extension). -/
structure SystemDerivedLeftExtension where
  ordinary : A ⥤ D
  [additive : ordinary.Additive]
  ordinaryAdj : ordinary ⊣ R
  derived : DerivedCategory A ⥤ DerivedCategory D
  comparison : DerivedCategory.Q ⋙ derived ⟶
    ordinary.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
  universal : derived.IsLeftDerivedFunctor comparison (HomologicalComplex.quasiIso A (.up ℤ))
  pointwise : Functor.HasPointwiseLeftDerivedFunctor
    (ordinary.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
      (HomologicalComplex.quasiIso A (.up ℤ))
  computes : ∀ P, resolving P → IsIso (comparison.app P)
  [shift : derived.CommShift ℤ]
  triangulated : derived.IsTriangulated
  adjunction : derived ⊣ R.mapDerivedCategory
  transpose : ∀ (P : CochainComplex A ℤ) (K : CochainComplex D ℤ)
    (f : (ordinary.mapHomologicalComplex (.up ℤ)).obj P ⟶ K),
    adjunction.homEquiv (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj K)
      (comparison.app P ≫ DerivedCategory.Q.map f) =
        DerivedCategory.Q.map ((ordinaryAdj.mapHomologicalComplex (.up ℤ)).homEquiv P K f) ≫
          R.mapDerivedCategoryFactors.inv.app K

attribute [instance] SystemDerivedLeftExtension.additive SystemDerivedLeftExtension.shift
end GeneralDerivedExtension

variable [EssentiallySmall.{w} C]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The local pure tensor in the ordinary functor of the recorded derived-change model.
The scalar is first, as in the project's change-of-rings construction.
Source: Stacks 03EK and 03D7 (blueprint: lem-pur-system-level-left-extension). -/
def systemModelTmul {R S : Sheaf J CommRingCat.{w}} {φ : R ⟶ S}
    (D : DerivedChangeOfRingsCochainModel φ)
    (P : ringedSiteModules.{w} (derivedChangeRingIndependentCoefficients J R))
    (U : Cᵒᵖ) (c : S.obj.obj U) (x : P.val.obj U) : (D.E.obj P).val.obj U :=
  c • (eqToHom (D.obj_eq P).symm).val.app U
    ((toSheafify J (changeOfRingsPresheaf φ P).presheaf).app U
      (((ModuleCat.extendRestrictScalarsAdj (φ.hom.app U).hom).unit.app (P.val.obj U)) x))

/-- The recorded derived-change-of-rings model together with its actual scalar
adjunctions. The ordinary unit is fixed on local generators and the derived transpose
is fixed by the universal counit on complexes.
Source: Stacks 03D7, 06YY, 0FND and 09T5
(blueprint: lem-pur-system-level-left-extension). -/
structure SystemScalarModel {R S : Sheaf J CommRingCat.{w}} (φ : R ⟶ S) where
  model : DerivedChangeOfRingsCochainModel φ
  ordinaryAdj : model.E ⊣ restrictScalars.{w}
    ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map φ)
  unit_normalized : ∀ P U (x : P.val.obj U),
    (ordinaryAdj.unit.app P).val.app U x = systemModelTmul model P U 1 x
  adjunction : model.T ⊣ (restrictScalars.{w}
    ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map φ)).mapDerivedCategory
  transpose : ∀ P K (f : (model.E.mapHomologicalComplex (.up ℤ)).obj P ⟶ K),
    adjunction.homEquiv (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj K)
      (model.ε.app P ≫ DerivedCategory.Q.map f) =
      DerivedCategory.Q.map ((ordinaryAdj.mapHomologicalComplex (.up ℤ)).homEquiv P K f) ≫
        (restrictScalars.{w} ((sheafCompose J
          (forget₂ CommRingCat.{w} RingCat.{w})).map φ)).mapDerivedCategoryFactors.inv.app K

/-- The K-flat resolving predicate at one coefficient level.
Source: Stacks 06YN and 06YS (blueprint: lem-pur-system-level-left-extension). -/
abbrev systemLevelKFlat (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (n : ℕ)
    (P : CochainComplex (systemLevel B n) ℤ) : Prop :=
  CochainComplex.IsKFlatIndependentCoefficients (R := B.obj (op n)) P ∧
    ∀ i : ℤ, IsFlatOnSite (R := B.obj (op n)) (P.X i)

/-- A single strict representative that is flat-term K-flat at every level.
Source: Stacks 06YS and 0G7E (blueprint: lem-pur-system-level-left-extension). -/
def systemComponentwiseKFlat (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w})
    (P : CochainComplex (StrictRingSystem B) ℤ) : Prop :=
  ∀ n : ℕ, systemLevelKFlat B n
    (((systemEvaluation B n).mapHomologicalComplex (.up ℤ)).obj P)


/-- A scalar model for every actual coefficient map; these are universal derived pairs,
not unrelated evaluated objects. Source: Stacks 06YY
(blueprint: lem-pur-system-level-left-extension). -/
abbrev SystemScalarAssignment :=
  ∀ {R S : Sheaf J CommRingCat.{w}} (φ : R ⟶ S), SystemScalarModel φ

/-- Ordinary tensor along an actual transition. Source: Stacks 03EK
(blueprint: lem-pur-system-level-left-extension). -/
abbrev systemTensor (S : SystemScalarAssignment (J := J))
    (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) {m n : ℕ} (h : m ≤ n) :=
  (S (B.map (homOfLE h).op)).model.E

/-- Derived tensor along an actual transition, using the dependency's universal pair.
Source: Stacks 06YY (blueprint: lem-pur-system-level-left-extension). -/
abbrev systemDerivedTensor (S : SystemScalarAssignment (J := J))
    (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) {m n : ℕ} (h : m ≤ n) :=
  (S (B.map (homOfLE h).op)).model.T

/-- The scalar Hom correspondence, normalized on local tensor generators.
Source: Stacks 03D7 (blueprint: lem-pur-system-level-left-extension). -/
abbrev systemTensorAdj (S : SystemScalarAssignment (J := J))
    (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) {m n : ℕ} (h : m ≤ n) :=
  (S (B.map (homOfLE h).op)).ordinaryAdj

/-- The normalized derived scalar Hom correspondence.
Source: Stacks 07A6 and 0FND (blueprint: lem-pur-system-level-left-extension). -/
abbrev systemDerivedTensorAdj (S : SystemScalarAssignment (J := J))
    (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) {m n : ℕ} (h : m ≤ n) :=
  (S (B.map (homOfLE h).op)).adjunction

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Canonical tensor units and associators, fixed by their balanced formulas before
sheafification and by the universal counits on flat-term K-flat representatives.
Source: Stacks 03EK, 06YT and 0G7E
(blueprint: lem-pur-system-level-left-extension). -/
structure SystemTensorCoherence (S : SystemScalarAssignment (J := J)) where
  ordinaryUnit : ∀ (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (n : ℕ),
    systemTensor S B (Nat.le_refl n) ≅ 𝟭 (systemLevel B n)
  unit_normalized : ∀ B n P U c x,
    ((ordinaryUnit B n).hom.app P).val.app U
      (systemModelTmul (S (B.map (homOfLE (Nat.le_refl n)).op)).model P U c x) = c • x
  ordinaryAssoc : ∀ (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) {l m n : ℕ}
    (h : l ≤ m) (k : m ≤ n),
    systemTensor S B k ⋙ systemTensor S B h ≅ systemTensor S B (h.trans k)
  assoc_normalized : ∀ B {l m n : ℕ} (h : l ≤ m) (k : m ≤ n) P U c d x,
    ((ordinaryAssoc B h k).hom.app P).val.app U
      (systemModelTmul (S (B.map (homOfLE h).op)).model ((systemTensor S B k).obj P) U c
        (systemModelTmul (S (B.map (homOfLE k).op)).model P U d x)) =
      systemModelTmul (S (B.map (homOfLE (h.trans k)).op)).model P U
        (c * (B.map (homOfLE h).op).hom.app U d) x
  derivedUnit : ∀ (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (n : ℕ),
    systemDerivedTensor S B (Nat.le_refl n) ≅ 𝟭 (DerivedCategory (systemLevel B n))
  derivedUnit_rep : ∀ B n P, systemLevelKFlat B n P →
    (derivedUnit B n).hom.app (DerivedCategory.Q.obj P) =
      (S (B.map (homOfLE (Nat.le_refl n)).op)).model.ε.app P ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex (ordinaryUnit B n) (.up ℤ)).hom.app P)
  derivedAssoc : ∀ (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) {l m n : ℕ}
    (h : l ≤ m) (k : m ≤ n),
    systemDerivedTensor S B k ⋙ systemDerivedTensor S B h ≅
      systemDerivedTensor S B (h.trans k)
  derivedAssoc_rep : ∀ B {l m n : ℕ} (h : l ≤ m) (k : m ≤ n) P,
    systemLevelKFlat B n P →
    (derivedAssoc B h k).hom.app (DerivedCategory.Q.obj P) ≫
      (S (B.map (homOfLE (h.trans k)).op)).model.ε.app P =
    (systemDerivedTensor S B h).map ((S (B.map (homOfLE k).op)).model.ε.app P) ≫
      (S (B.map (homOfLE h).op)).model.ε.app
        (((systemTensor S B k).mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex (ordinaryAssoc B h k) (.up ℤ)).hom.app P)

/-- The two descriptions of the first selected level of a composite selection give the
same evaluated derived tensor; it transports the composite evaluation formula along
`systemNextSelected_trans`. Source: the subsequence extension of Zheng 4.1
(blueprint: lem-pur-system-level-left-extension), node proof step 12.
Proof: rewrite the index by `systemNextSelected_trans`; the two inequality proofs then
agree by proof irrelevance. -/
theorem systemSelectedTensor_trans (S : SystemScalarAssignment (J := J))
    (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (r s : ℕ ↪o ℕ) (m : ℕ)
    (P : DerivedCategory (StrictRingSystem (selectedSystemRings B (s.trans r)))) :
    (systemDerivedTensor S B (systemNextSelected_spec (s.trans r) m).1).obj
        ((derivedSystemEvaluation (selectedSystemRings B (s.trans r))
          (systemNextSelected (s.trans r) m)).obj P) =
      (systemDerivedTensor S B ((systemNextSelected_spec r m).1.trans
          (r.monotone (systemNextSelected_spec s (systemNextSelected r m)).1))).obj
        ((derivedSystemEvaluation (selectedSystemRings B (s.trans r))
          (systemNextSelected s (systemNextSelected r m))).obj P) := by
  let F (i : ℕ) (hi : m ≤ r (s i)) : DerivedCategory (systemLevel B m) :=
    (systemDerivedTensor S B hi).obj
      ((derivedSystemEvaluation (selectedSystemRings B (s.trans r)) i).obj P)
  change F _ _ = F _ _
  have h : (⟨systemNextSelected (s.trans r) m,
      (systemNextSelected_spec (s.trans r) m).1⟩ : {i : ℕ // m ≤ r (s i)}) =
      ⟨systemNextSelected s (systemNextSelected r m),
        (systemNextSelected_spec r m).1.trans
          (r.monotone (systemNextSelected_spec s (systemNextSelected r m)).1)⟩ :=
    Subtype.ext (systemNextSelected_trans r s m)
  exact congrArg (fun i : {i : ℕ // m ≤ r (s i)} ↦ F i.val i.property) h

/-- All ordinary and derived left extensions of strict semilinear systems, including
componentwise coproducts and cohomology, exact evaluation, the normalized transition
formula, and composition of subsequences. Every functor is a functor on the ordinary
unbounded localization of the actual strict abelian category.
Source: Zheng, Construction 4.1, p. 21, and its subsequence extension; Stacks 06XN and 09T5
(blueprint: lem-pur-system-level-left-extension). -/
structure SystemLevelLeftExtensionTheory where
  scalar : SystemScalarAssignment (J := J)
  tensor : SystemTensorCoherence scalar
  grothendieck : ∀ (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}),
    IsGrothendieckAbelian.{w} (StrictRingSystem B)
  [coproducts : ∀ (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}),
    HasCoproducts.{w} (StrictRingSystem B)]
  [derivedCoproducts : ∀ (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}),
    HasCoproducts.{w} (DerivedCategory (StrictRingSystem B))]
  [levelDerivedCoproducts : ∀ (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (n : ℕ),
    HasCoproducts.{w} (DerivedCategory (systemLevel B n))]
  evaluationCoproducts : ∀ (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) n (I : Type w),
    PreservesColimitsOfShape (Discrete I) (systemEvaluation B n)
  derivedEvaluationCoproducts : ∀ (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) n (I : Type w),
    PreservesColimitsOfShape (Discrete I) (derivedSystemEvaluation B n)
  cohomology : ∀ (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) n (q : ℤ),
    DerivedCategory.homologyFunctor (StrictRingSystem B) q ⋙ systemEvaluation B n ≅
      derivedSystemEvaluation B n ⋙ DerivedCategory.homologyFunctor (systemLevel B n) q
  detectsIso : ∀ (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w})
    {M N : DerivedCategory (StrictRingSystem B)} (f : M ⟶ N),
    IsIso f ↔ ∀ n : ℕ, IsIso ((derivedSystemEvaluation B n).map f)
  detectsBounds : ∀ (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w})
    (M : DerivedCategory (StrictRingSystem B)) (q : ℤ),
    (M.IsGE q ↔ ∀ n : ℕ, ((derivedSystemEvaluation B n).obj M).IsGE q) ∧
    (M.IsLE q ↔ ∀ n : ℕ, ((derivedSystemEvaluation B n).obj M).IsLE q)
  single : ∀ (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (n : ℕ),
    SystemDerivedLeftExtension (systemEvaluation B n) (systemLevelKFlat B n)
  singleBelow : ∀ (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) {m n : ℕ} (h : m ≤ n),
    (single B n).ordinary ⋙ systemEvaluation B m ≅ systemTensor scalar B h
  singleAbove : ∀ (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) m n, n < m → ∀ P,
    IsZero ((systemEvaluation B m).obj ((single B n).ordinary.obj P))
  singleTranspose : ∀ (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) {m n : ℕ} (h : m ≤ n) P M
    (f : (single B n).ordinary.obj P ⟶ M),
    (systemTensorAdj scalar B h).homEquiv P (M.level m)
      ((singleBelow B h).inv.app P ≫ (systemEvaluation B m).map f) =
      (single B n).ordinaryAdj.homEquiv P M f ≫ M.transition h
  singleDerivedBelow : ∀ (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) {m n : ℕ} (h : m ≤ n),
    (single B n).derived ⋙ derivedSystemEvaluation B m ≅ systemDerivedTensor scalar B h
  singleDerivedAbove : ∀ (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) m n, n < m → ∀ P,
    IsZero ((derivedSystemEvaluation B m).obj ((single B n).derived.obj P))
  transition : ∀ (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) {m n : ℕ} (h : m ≤ n),
    derivedSystemEvaluation B n ⟶
      derivedSystemEvaluation B m ⋙ (systemRestriction B h).mapDerivedCategory
  transition_rep : ∀ (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) {m n : ℕ} (h : m ≤ n) K,
    (transition B h).app (DerivedCategory.Q.obj K) ≫
      (systemRestriction B h).mapDerivedCategory.map
        ((systemEvaluation B m).mapDerivedCategoryFactors.hom.app K) ≫
      (systemRestriction B h).mapDerivedCategoryFactors.hom.app
        (((systemEvaluation B m).mapHomologicalComplex (.up ℤ)).obj K) =
      (systemEvaluation B n).mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map ((strictSystemTransition B h).mapHomologicalComplex (.up ℤ) |>.app K)
  transition_identity : ∀ (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) n M,
    ((systemDerivedTensorAdj scalar B (Nat.le_refl n)).homEquiv _ _).symm
      ((transition B (Nat.le_refl n)).app M) =
        (tensor.derivedUnit B n).hom.app ((derivedSystemEvaluation B n).obj M)
  singleDerivedTranspose : ∀ (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) {m n : ℕ} (h : m ≤ n) P M
    (f : (single B n).derived.obj P ⟶ M),
    (systemDerivedTensorAdj scalar B h).homEquiv P ((derivedSystemEvaluation B m).obj M)
      ((singleDerivedBelow B h).inv.app P ≫ (derivedSystemEvaluation B m).map f) =
      (single B n).adjunction.homEquiv P M f ≫ (transition B h).app M
  selected : ∀ (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (r : ℕ ↪o ℕ),
    SystemDerivedLeftExtension (systemSubsequence B r)
      (systemComponentwiseKFlat (selectedSystemRings B r))
  selectedEvaluation : ∀ (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) r n,
    derivedSystemSubsequence B r ⋙ derivedSystemEvaluation (selectedSystemRings B r) n ≅
      derivedSystemEvaluation B (r n)
  selectedEvaluation_rep : ∀ (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) r n K,
    (selectedEvaluation B r n).hom.app (DerivedCategory.Q.obj K) ≫
      (systemEvaluation B (r n)).mapDerivedCategoryFactors.hom.app K =
    (derivedSystemEvaluation (selectedSystemRings B r) n).map
      ((systemSubsequence B r).mapDerivedCategoryFactors.hom.app K) ≫
    (systemEvaluation (selectedSystemRings B r) n).mapDerivedCategoryFactors.hom.app
      (((systemSubsequence B r).mapHomologicalComplex (.up ℤ)).obj K)
  selectedBelow : ∀ (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) r m,
    (selected B r).ordinary ⋙ systemEvaluation B m ≅
      systemEvaluation (selectedSystemRings B r) (systemNextSelected r m) ⋙
        systemTensor scalar B (systemNextSelected_spec r m).1
  selectedTranspose : ∀ (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) r m P M
    (f : (selected B r).ordinary.obj P ⟶ M),
    (systemTensorAdj scalar B (systemNextSelected_spec r m).1).homEquiv
      (P.level (systemNextSelected r m)) (M.level m)
      ((selectedBelow B r m).inv.app P ≫ (systemEvaluation B m).map f) =
    (systemEvaluation (selectedSystemRings B r) (systemNextSelected r m)).map
      ((selected B r).ordinaryAdj.homEquiv P M f) ≫
        M.transition (systemNextSelected_spec r m).1
  selectedDerivedBelow : ∀ (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) r m,
    (selected B r).derived ⋙ derivedSystemEvaluation B m ≅
      derivedSystemEvaluation (selectedSystemRings B r) (systemNextSelected r m) ⋙
        systemDerivedTensor scalar B (systemNextSelected_spec r m).1
  selectedDerivedTranspose : ∀ (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) r m P M
    (f : (selected B r).derived.obj P ⟶ M),
    (systemDerivedTensorAdj scalar B (systemNextSelected_spec r m).1).homEquiv
      ((derivedSystemEvaluation (selectedSystemRings B r) (systemNextSelected r m)).obj P)
      ((derivedSystemEvaluation B m).obj M)
      ((selectedDerivedBelow B r m).inv.app P ≫ (derivedSystemEvaluation B m).map f) =
    (derivedSystemEvaluation (selectedSystemRings B r) (systemNextSelected r m)).map
      ((selected B r).adjunction.homEquiv P M f) ≫
    (selectedEvaluation B r (systemNextSelected r m)).hom.app M ≫
      (transition B (systemNextSelected_spec r m).1).app M
  selectedTransition : ∀ (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) r m N,
    ((systemDerivedTensorAdj scalar B (Nat.le_succ m)).homEquiv _ _).symm
      ((transition B (Nat.le_succ m)).app ((selected B r).derived.obj N)) =
    (systemDerivedTensor scalar B (Nat.le_succ m)).map
      ((selectedDerivedBelow B r (m + 1)).hom.app N) ≫
    (tensor.derivedAssoc B (Nat.le_succ m) (systemNextSelected_spec r (m + 1)).1).hom.app
      ((derivedSystemEvaluation (selectedSystemRings B r) (systemNextSelected r (m + 1))).obj N) ≫
    (tensor.derivedAssoc B (systemNextSelected_spec r m).1
      (r.monotone (systemNextSelected_mono r m))).inv.app
      ((derivedSystemEvaluation (selectedSystemRings B r) (systemNextSelected r (m + 1))).obj N) ≫
    (systemDerivedTensor scalar B (systemNextSelected_spec r m).1).map
      (((systemDerivedTensorAdj scalar (selectedSystemRings B r)
          (systemNextSelected_mono r m)).homEquiv _ _).symm
        ((transition (selectedSystemRings B r) (systemNextSelected_mono r m)).app N)) ≫
    (selectedDerivedBelow B r m).inv.app N
  restrictionComposition : ∀ (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) r s,
    derivedSystemSubsequence B r ⋙ derivedSystemSubsequence (selectedSystemRings B r) s ≅
      derivedSystemSubsequence B (s.trans r)
  restrictionComposition_rep : ∀ (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) r s K,
    (restrictionComposition B r s).hom.app (DerivedCategory.Q.obj K) ≫
      (systemSubsequence B (s.trans r)).mapDerivedCategoryFactors.hom.app K =
    (derivedSystemSubsequence (selectedSystemRings B r) s).map
      ((systemSubsequence B r).mapDerivedCategoryFactors.hom.app K) ≫
    (systemSubsequence (selectedSystemRings B r) s).mapDerivedCategoryFactors.hom.app
      (((systemSubsequence B r).mapHomologicalComplex (.up ℤ)).obj K)
  extensionComposition : ∀ (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) r s,
    (selected (selectedSystemRings B r) s).derived ⋙ (selected B r).derived ≅
      (selected B (s.trans r)).derived
  composition_mate : ∀ (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) r s P M
    (f : (selected B r).derived.obj ((selected (selectedSystemRings B r) s).derived.obj P) ⟶ M),
    (selected B (s.trans r)).adjunction.homEquiv P M
      ((extensionComposition B r s).inv.app P ≫ f) =
    (selected (selectedSystemRings B r) s).adjunction.homEquiv P
      ((derivedSystemSubsequence B r).obj M)
      ((selected B r).adjunction.homEquiv _ M f) ≫
        (restrictionComposition B r s).hom.app M
  extensionComposition_eval : ∀ (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) r s m P,
    (derivedSystemEvaluation B m).map ((extensionComposition B r s).hom.app P) ≫
      (selectedDerivedBelow B (s.trans r) m).hom.app P ≫
        eqToHom (systemSelectedTensor_trans scalar B r s m P) =
    (selectedDerivedBelow B r m).hom.app ((selected (selectedSystemRings B r) s).derived.obj P) ≫
      (systemDerivedTensor scalar B (systemNextSelected_spec r m).1).map
        ((selectedDerivedBelow (selectedSystemRings B r) s (systemNextSelected r m)).hom.app P) ≫
      (tensor.derivedAssoc B (systemNextSelected_spec r m).1
        (r.monotone (systemNextSelected_spec s (systemNextSelected r m)).1)).hom.app
        ((derivedSystemEvaluation (selectedSystemRings B (s.trans r))
          (systemNextSelected s (systemNextSelected r m))).obj P)

-- Unused-variable linting needlessly normalizes the entire extension schema here.
set_option linter.unusedVariables false in
/-- Derived left extensions of arbitrary strict semilinear ring-sheaf systems.
The nonnegative index n denotes the node's positive index n+1. All structure fields
are conclusions: no flatness of the coefficient maps, normalization, or boundedness
is an assumption. The ordinary and derived universal properties determine each left
extension, with its actual unit and counit; normalized Hom formulas specify all
coefficient comparisons and the selected transition, including repeated next indices.

Source: Zheng, Six Operations and Lefschetz--Verdier, Construction 4.1, printed p. 21;
the adic-stage paragraph of def-weil-exceptional-inverse-image in the main-20261015
blueprint, before taking inverse limits; Stacks Tags 03DA, 03DB, 06YS, 06YT, 06XN,
0FND and 09T5 (blueprint: lem-pur-system-level-left-extension).

Proof, following the node's ordinary-derived route (2026-10-18 repair):

1. Realize systems as modules on one small ringed site. Let $J$ be the ordered category of
positive integers with one arrow $m\to n$ for $m\le n$, and give $\mathcal C\times J$ the
coverings $\{(U_i,n)\to(U,n)\}$ coming from coverings of $U$ in $\mathcal C$. Pulling such a
covering back along $(V,m)\to(U,n)$ gives $\{(V\times_U U_i,m)\to(V,m)\}$, so the site axioms
hold. Define $\mathcal B(U,n)=B_n(U)$, with restriction along $(V,m)\to(U,n)$ induced by $B_n\to
B_m$ and restriction to $V$. The sheaf condition is exactly the sheaf condition at each level.
Consequently a $\mathcal B$-module sheaf is exactly a strict semilinear system, and a complex of
such sheaves is a strict complex of systems, including its maps. Apply
[lem-pur-ringed-site-grothendieck-abelian] to this small site and sheaf of commutative rings. This
proves that $\mathscr S(B)$ is Grothendieck abelian. By
[lem-weil-pbc-module-sheaves-colimits-forgetful], kernels are sectionwise, cokernels and colimits
are sheafified sectionwise constructions. Since coverings never change the level, these
constructions are the corresponding module-sheaf constructions at each level. Thus exactness,
coproducts, and cohomology of complexes are componentwise.

2. Small coproducts of short exact sequences in $\mathscr S(B)$ are exact: each coproduct is the
filtered colimit, over finite subsets of its indexing set, of finite direct sums, and filtered
colimits are exact by the Grothendieck property established in step 1. Hence termwise coproducts
preserve quasi-isomorphisms. They also give coproducts in the unbounded derived category. Indeed
for any family of complexes $K_i$ and target $M$, choose a K-injective resolution $M\to I$ using
[prop-pur-kinjective-resolutions-exist] on the product ringed site. By
[lem-weil-pbc-kinjective-hom-derived], morphisms from any complex to $I$ in the derived category
are chain maps modulo homotopy. A chain map $\bigoplus_i K_i\to I$ is exactly a family of chain
maps $K_i\to I$, and a homotopy is exactly a family of homotopies. Therefore
$\operatorname{Hom}_{D}(\bigoplus_i K_i,M)=\prod_i\operatorname{Hom}_{D}(K_i,M)$, with the
coprojections induced by those of complexes. This proof applies to every small indexing set,
including the empty set; it does not apply a countable-sum lemma to an arbitrary family.
Evaluation thus preserves these derived coproducts. Evaluations descend to exact triangulated
functors by [lem-weil-pbc-exact-functor-derived-factorization]. For a morphism $h$, every $e_n h$
is an isomorphism if and only if every $e_n\operatorname{Cone}(h)$ is acyclic, if and only if
$\operatorname{Cone}(h)$ is acyclic. Likewise $H^q(M)=0$ if and only if $H^q(e_nM)=0$ for every
$n$. This proves joint detection of isomorphisms and of either cohomological bound, with one
common bound for all levels.

3. Construct the underived evaluation adjunction. For a $B_n$-module sheaf $P$ put
$(E_nP)_m=B_m\otimes_{B_n}P$ for $m\le n$, and zero for $m>n$. Below $n$ use the
coefficient-map-induced tensor transitions; the transition out of the zero region is zero. On a
map use $1\otimes h$. Ordinary tensor/restriction adjunction is
[lem-weil-pbc-ringed-topoi-module-adjunction], applied to the identity topos and each map $B_n\to
B_m$. A map $h:P\to M_n$ determines at $m\le n$ the tensor-adjoint of
$P\xrightarrow{h}M_n\to\operatorname{Res}_{n,m}M_m$; above $n$ use zero. These components commute
with transitions because the transitions of $M$ compose. Conversely a system map $E_nP\to M$ has
these components by naturality from level $n$. Evaluation there is its inverse, so this gives a
bijection natural in $P,M$, hence $E_n\dashv e_n$. The unit is $P\cong B_n\otimes_{B_n}P$, and the
counit has at level $m\le n$ the adjoint of the transition $M_n\to\operatorname{Res}_{n,m}M_m$,
and zero above $n$. The same formulas degree by degree give the termwise adjunction on complexes.

4. Construct the underived subsequence adjunction. Unboundedness of $r$ makes $t(m)$ exist, and
strict increase gives $t(r(i))=i$ and $t(m)\le t(m+1)$. For a strict $B_r$-system $N$ set
$(E_rN)_m=B_m\otimes_{B_{r(a)}}N_a$, $a=t(m)$. When $b=t(m+1)$, take the transition adjunct to be
$B_m\otimes_{B_{r(b)}}N_b\to B_m\otimes_{B_{r(a)}}N_a$, obtained by tensoring the transition of
$N$ and using the ordinary tensor associator; when $a=b$ use the identity transition of $N_a$.
More generally use the same prescription for $m'\ge m$. It composes because $N$'s transitions
compose and both ways of multiplying three scalar factors give the same balanced tensor map. For a
map $h:N\to U_rM$, define $E_rN\to M$ at $m$ as the scalar adjunct of
$N_a\xrightarrow{h_a}M_{r(a)}\to\operatorname{Res}_{r(a),m}M_m$. Write $\tau^N_{j,i}$ and
$\tau^M_{v,u}$ for the iterated semilinear transitions. For $m'\ge m$, put $a'=t(m')$ and
$a=t(m)$. On a local pure tensor $c\otimes x$, $x\in N_{a'}$, both paths in the system-map square
give $c\,\tau^M_{r(a'),m}h_{a'}(x)$: the path through level $m$ gives
$c\,\tau^M_{r(a),m}h_a\tau^N_{a',a}(x)$, which is the same by
$h_a\tau^N_{a',a}=\tau^M_{r(a'),r(a)}h_{a'}$ and composition of $M$'s transitions. Pure tensors
generate the tensor presheaf and then its sheafification, so this proves the square on module
sheaves. Conversely evaluate a system map at $m=r(i)$, where $(E_rN)_{r(i)}=N_i$; its components
at other $m$ are forced by the arrow from $r(t(m))$ to $m$. These constructions are inverse and
natural, so $E_r\dashv U_r$. The unit is the identity under $U_rE_rN=N$. The counit has components
$B_m\otimes_{B_{r(t(m))}}M_{r(t(m))}\to M_m$ induced by the actual transitions. Evaluating this
counit at selected levels is the identity; applying it to $E_rN$ is the identity because
$t(r(t(m)))=t(m)$. These verify the two triangle identities. The construction is additive and
gives the termwise adjunction on complexes.

5. Obtain simultaneous K-flat representatives on the tower site of step 1. Evaluation on sheaves
of sets preserves finite limits, computed componentwise. Its right adjoint sends a sheaf $A$ to
the tower with value $A$ at $m\ge n$, terminal sheaf at $m<n$, identity transitions within each
region, and the unique boundary transition: a map into this tower is uniquely its component
$M_n\to A$. Thus evaluation is the inverse image of a morphism of topoi. It sends the tower ring
$\mathcal B$ to $B_n$, with identity structural ring map, so its module pullback is exactly $e_n$.
Apply [lem-pc-kflat-resolution] on the small ringed tower site to get $Q\to N$ K-flat with flat
terms and termwise surjective. By [lem-weil-pbc-ringed-pullback-preserves-kflat] applied to each
evaluation morphism, every $Q_n$ is K-flat over $B_n$ with flat terms. Since evaluation is exact,
every $Q_n\to N_n$ is a quasi-isomorphism. The same construction applies to $B_r$. In particular
every complex of systems has one strict representative with all these properties simultaneously;
independently chosen level resolutions are not being assembled.

6. For $E_n$ take the resolving class of flat-term K-flat $B_n$-complexes; it resolves every
complex by [lem-pc-kflat-resolution]. For $E_r$ take the class of strict system complexes whose
every component is flat-term K-flat; step 5 proves it resolves every complex. Both functors are
additive. Hence they preserve homotopies, shifts and cones termwise: a cone has terms $Y^k\oplus
X^{k+1}$ and a matrix differential, and additivity preserves this direct sum and each matrix
entry. Using [lem-pur-homotopy-category-triangulated], their composites from the homotopy
categories to the target derived categories are exact. If $s$ is a quasi-isomorphism between
objects of the relevant resolving class, every component of $E_ns$ or $E_rs$ is a change of rings
of a quasi-isomorphism between K-flat complexes (or $0\to0$). It is a quasi-isomorphism by
[lem-pur-derived-change-of-rings](1). Componentwise cohomology from step 1 makes this a
quasi-isomorphism of systems. Therefore [lem-pur-left-derived-from-kflat-class] gives
everywhere-defined exact functors $L_n=\mathbf L E_n$ and $L_r=\mathbf L E_r$, with natural
comparisons to $E_n$ and $E_r$ which are invertible on these resolving classes.

7. The exact functors $e_n$ and $U_r$ induce the termwise functors on derived categories by
[lem-weil-pbc-exact-functor-derived-factorization]. These are also their everywhere-defined right
derived functors by [lem-weil-pbc-exact-functor-derived-functor]. In the ind-system convention of
[lem-pc-derived-adjoint-functors], for a complex $K$ every quasi-isomorphism $K\to K'$ is carried
by $e_n$ or $U_r$ to a quasi-isomorphism, so every transition of the filtered system
$(F(K'))_{K\to K'}$ is an isomorphism in the target derived category. That system is therefore
essentially constant with value $F(K)$, the identity stage giving the representing cocone; this is
the right-hand existence hypothesis at every complex. To check the existence convention for
deriving adjoints explicitly, quasi-isomorphisms in either source homotopy category have a right
calculus of fractions and two-out-of-three by [lem-pur-quasi-isos-saturated-triangulated]. The
resolving classes and invariance verified in step 6 therefore satisfy
[lem-pur-resolving-class-essential-constancy]: the left-derived denominator pro-systems are
essentially constant at every complex, with invertible identity leg on the resolving classes. By
[lem-pur-left-derived-defined-pointwise-kan-bridge], these values and comparisons identify with
the left derived functors of step 6, including their specified comparison on representatives. All
hypotheses of [lem-pc-derived-adjoint-functors] now hold for each underived adjunction of steps 3
and 4. Consequently $L_n\dashv e_n$ and $L_r\dashv U_r$ on the ordinary unbounded derived
categories. This produces natural units and counits satisfying the triangle identities; it never
assumes that evaluation preserves K-injectives.

8. Fix the normalization of these adjunctions on representatives. By
[lem-weil-pbc-termwise-adjunction-homotopy] the termwise adjunctions of steps 3 and 4 induce the
Hom bijections on homotopy categories. Apply the explicit formula of
[lem-pc-pre-derived-adjoint-functors-general] with the exact right functor, its identity-stage
right-derived comparison, and the left-derived comparisons of step 7. For $P$ in the relevant
resolving class and a chain map $g:P\to R K$ ($E\dashv R$ means either pair), take the two
denominators to be identities. The formula says that the transpose of the class of $g$ is the
class of its strict transpose $EP\to K$, composed with $LE(QP)\cong Q(EP)$. In particular the
derived unit at $QP$ is represented by the strict unit $P\to REP$. For a resolution $p:P\to RK$,
the derived counit at $QK$ is represented by the strict transpose $EP\to K$, after identifying
$LE(RQK)\cong Q(EP)$ using $p$. Naturality extends these descriptions to all objects and
morphisms. Thus the adjunctions have the specific tensor-adjoint units and counits, rather than
merely some adjunction between the same functors.

9. For $P\in D(B_n)$ take a flat-term K-flat resolution $Q\to P$. Step 6 represents $L_nP$ by
$E_nQ$, so [lem-pur-derived-change-of-rings](2) gives $e_mL_nP=B_m\otimes^L_{B_n}P$ below $n$ and
zero above. For a system $N$ take the single strict resolution $Q\to N$ of step 5 for $B_r$. Then
$L_rN$ is represented by $E_rQ$ and $Q_a$ is flat-term K-flat for every $a$. Hence
$e_mL_rN=B_m\otimes^L_{B_{r(t(m))}}N_{t(m)}$, naturally in $N$. These are evaluations of one
derived functor with the comparison of step 6. On maps of representatives the component is
$1\otimes h_{t(m)}$; the natural comparison and localization define the action on arbitrary
derived morphisms. Moreover each component of $E_rQ$ is itself flat-term K-flat by
[lem-weil-pbc-ringed-pullback-preserves-kflat], for the identity topos and the indicated ring map.
Thus it is again an admissible representative for subsequent left extensions.

10. Write $a=t(m)$ and $b=t(m+1)$. On the same $Q$ the strict transition of $E_rQ$ is precisely
the tensor-adjoint of the selected transition $Q_b\to\operatorname{Res}_{B_{r(b)}\to B_{r(a)}}Q_a$
used in step 4. By [lem-weil-pbc-ringed-pullback-preserves-kflat], both $Q_b$ and
$B_{m+1}\otimes_{B_{r(b)}}Q_b$ are flat-term K-flat over their respective rings. Consequently the
ordinary chain isomorphism $$B_m\otimes_{B_{m+1}}(B_{m+1}\otimes_{B_{r(b)}}Q_b)\cong
B_m\otimes_{B_{r(b)}}Q_b$$ computes the derived associator. Explicitly $(c\otimes d)\otimes x$
maps to $c\overline d\otimes x$, with inverse inserting $1$ in the intermediate ring; these
balanced formulas sheafify by [def-pur-sheaf-tensor-product]. By the normalized scalar
transposition of [lem-pur-sheaf-ring-derived-coefficient-adjunction], the chain map induced from
$Q_b\to\operatorname{Res}Q_a$ represents exactly the specified derived adjoint structure map of
$N$. Its further scalar extension is therefore the arrow in the statement, including its source,
target and canonical associators. If $a=b$ it uses the identity of $Q_a$; if $a<b$ it uses the
actual iterated transition. This proves the transition formula, rather than testing equality of
arbitrary system morphisms by evaluations.

11. The left-extension terminology has its ordinary derived meaning here. For a singleton
inclusion or the selected-index inclusion $r$, the strict left extension is the functor $E_n$ or
$E_r$ of steps 3 and 4: its maps to a strict system are exactly the maps after restriction. Step 6
derives that functor, and step 7 gives its left-extension universal property on the ordinary
derived categories. The unit description of step 8 fixes the restriction-to-extension map in that
property. At $m$ the singleton comma category is empty for $m>n$ and has its sole object for $m\le
n$. For $r$ its objects are $i$ with $r(i)\ge m$, with arrows from larger to smaller indices; its
terminal object is $t(m)$. This accounts for the single tensor term in the formulas. None of this
identifies $D(\mathscr S(B))$ with a category of diagrams in the ordinary categories $D(B_n)$, nor
requires an enhanced section equivalence.

12. Let $s$ be a strictly increasing unbounded selection of $B_r$, put $a=t_r(m)$ and $c=t_s(a)$.
Then $r(s(i))\ge m$ if and only if $s(i)\ge a$, if and only if $i\ge c$, so $t_{r\circ s}(m)=c$.
Choose a strict componentwise flat-term K-flat resolution $Q\to N$ over $B_{r\circ s}$. Step 9
shows that $E_sQ$ is componentwise flat-term K-flat, so step 6 computes $L_rL_sN$ by $E_rE_sQ$.
The strict tensor associator identifies its $m$th component
$$B_m\otimes_{B_{r(a)}}(B_{r(a)}\otimes_{B_{r(s(c))}}Q_c)\cong B_m\otimes_{B_{r(s(c))}}Q_c.$$ This
gives a map of strict system complexes to $E_{r\circ s}Q$: each transition uses the same iterated
transition of $Q$, and the associator multiplies the same scalar factors on either path. Its
inverse inserts $1$; both formulas are balanced and sheafify by [def-pur-sheaf-tensor-product]. By
[lem-weil-pbc-ringed-pullback-preserves-kflat], these chain associators compute the corresponding
derived tensor associators. Thus the simultaneous representatives compute the proposed composite
comparison.

13. Define the composite comparison on all derived morphisms by adjunction. Both $L_rL_s$ and
$L_{r\circ s}$ are left adjoint to $U_sU_r=U_{r\circ s}$. Define the comparison to be the unique
map whose transpose is the unit of $L_{r\circ s}$ under the composite Hom adjunction, and its
inverse by the reverse prescription. The two composites transpose to the respective units, so are
identities. The bijections are natural, so this is a natural isomorphism preserving the adjunction
identifications, units and counits. On the simultaneous representatives of step 12, the normalized
transposes of step 8 show that this is exactly the tensor associator there: restriction to
selected indices is the identity and all other components are forced by the strict transitions.
The composite-unit and composite-counit formulas and compatibility of transposition with
composition are [lem-weil-pbc-mate-pasting](2). For three selections the two comparison paths
transpose to the same triple composite unit by that formula, so they agree; the identity selection
gives the identity unit and identity comparison. This proves composition compatibility in the
ordinary derived categories. Exactness and shift compatibility already follow from step 6; no
model-category suspension computation is needed. No flatness of coefficient maps, normalization,
or boundedness was introduced.

The tensor unit and associators are fixed on local pure tensors and on the universal
K-flat comparisons. The normalized transpose equations identify every displayed
comparison with the corresponding adjunction mate. The composition_mate equation states
compatibility with composition of restrictions, and extensionComposition_eval states the
evaluated compatibility with the canonical tensor associator of step 12, at the index
`t_{r∘s}(m) = t_s(t_r(m))` of systemNextSelected_trans; associativity for three selections
follows because both paths transpose to the same composite unit.
-/
theorem systemLevelLeftExtensionTheory : Nonempty (SystemLevelLeftExtensionTheory (J := J)) := by
  sorry

end SheafOfModules
