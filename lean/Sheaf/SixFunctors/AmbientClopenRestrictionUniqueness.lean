/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q55
-/
module

public import Sheaf.SixFunctors.IntegralSystemCanonicalBridge
public import Sheaf.AlgebraicGeometry.VaryingRingProperOpenArrows
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Paper.SemilinearDerivedSections
public import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
public import Sheaf.SixFunctors.OpenTensorNormalization
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Products.Basic
public import Sheaf.AlgebraicGeometry.ProEtaleClopenRingedModuleGluing
import all Sheaf.Paper.SequenceOpenScalars
import all Sheaf.AlgebraicGeometry.VaryingRingOperations
import all Sheaf.AlgebraicGeometry.ProEtaleClopenRingedModuleGluing
import Sheaf.AlgebraicGeometry.ProperOpenClopenProjector
import Sheaf.AlgebraicGeometry.TowerOpenBetaNormalization
import all Sheaf.AlgebraicGeometry.VaryingRingProperOpenPasting
import all Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Clopen restriction uniqueness in the ambient coefficient categories

Source: Stacks Project, more-etale.tex, Tag 0F7B (lemma-shriek-proper-and-open),
and sites.tex, Tag 04TS (lemma-mapping-property-glue). The pro-etale and simultaneous
semilinear formulation is the agent's explicit clopen construction
(blueprint: lem-sf-ambient-clopen-restriction-uniqueness).

`some n` means the single positive coefficient level n+1; `none` means the entire
semilinear system on the vertical sequence site. All categories and operations below
are dispatchers to the published constructions, rather than new module categories.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open WeilConjectures.IntegralSystemRealization

namespace AlgebraicGeometry.ProEtale.AmbientClopenRestriction

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Select the existing single-level or simultaneous system module category.
Source: Stacks 098K; Zheng 4.1
(blueprint: lem-sf-ambient-clopen-restriction-uniqueness). -/
abbrev Modules (m : Option ℕ) (X : Scheme.{u}) :=
  match m with
  | some n => StrictTower.Modules (scalarRings l E n) X
  | none => VaryingRing.Modules (scalarRings l E) (scalarTransitions l E) X

/-- The category structure is the published one in either case.
Source: Stacks 03DI; Zheng 4.1
(blueprint: lem-sf-ambient-clopen-restriction-uniqueness). -/
instance modulesCategory (m : Option ℕ) (X : Scheme.{u}) : Category (Modules l E m X) :=
  match m with
  | some _ => inferInstance
  | none => inferInstance

/-- Inherit the actual additive structure, without changing morphisms.
Source: Stacks 03DI; Zheng 4.1
(blueprint: lem-sf-ambient-clopen-restriction-uniqueness). -/
instance modulesPreadditive (m : Option ℕ) (X : Scheme.{u}) :
    Preadditive (Modules l E m X) :=
  match m with
  | some _ => inferInstance
  | none => inferInstance

/-- The zero object in either of the actual abelian coefficient categories.
Source: Stacks 03DI; Zheng 4.1
(blueprint: lem-sf-ambient-clopen-restriction-uniqueness). -/
instance modulesZero (m : Option ℕ) (X : Scheme.{u}) : HasZeroObject (Modules l E m X) :=
  match m with
  | some _ => inferInstance
  | none => inferInstance

/-- The published exact constant-coefficient inverse image.
Source: Stacks 09AE; Zheng 4.1
(blueprint: lem-sf-ambient-clopen-restriction-uniqueness). -/
abbrev pull (m : Option ℕ) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Modules l E m Y ⥤ Modules l E m X :=
  match m with
  | some n => StrictTower.modulePullback (scalarRings l E n) f
  | none => VaryingRing.pull (scalarRings l E) (scalarTransitions l E) f

/-- The specified ordinary extension by zero, on the whole system before evaluation.
Source: Stacks 03DI; Zheng 4.1
(blueprint: lem-sf-ambient-clopen-restriction-uniqueness). -/
abbrev extension (m : Option ℕ) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    Modules l E m U ⥤ Modules l E m X :=
  match m with
  | some n => StrictTower.moduleJ (scalarRings l E n) j
  | none => VaryingRing.extension (scalarRings l E) (scalarTransitions l E) j

/-- Reuse the specified ordinary open adjunction, including its unit normalization.
Source: Stacks 03DI; Zheng 4.1
(blueprint: lem-sf-ambient-clopen-restriction-uniqueness). -/
def openAdj (m : Option ℕ) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    extension l E m j ⊣ pull l E m j :=
  match m with
  | some n => StrictTower.moduleJAdj (scalarRings l E n) j
  | none => VaryingRing.moduleJAdj (scalarRings l E) (scalarTransitions l E) j

/-- The canonical unit-preserving pullback compositor, in its published orientation.
Source: Stacks 07A7 (blueprint: lem-sf-ambient-clopen-restriction-uniqueness). -/
def pullComp (m : Option ℕ) {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    pull l E m (f ≫ g) ≅ pull l E m g ⋙ pull l E m f :=
  match m with
  | some n => StrictTower.moduleGComp (scalarRings l E n) f g
  | none => VaryingRing.moduleGComp (scalarRings l E) (scalarTransitions l E) f g

/-- Underlying abelian section presheaves; the extra index is ignored at a fixed level.
Source: Stacks 04TS; Zheng 4.1
(blueprint: lem-sf-ambient-clopen-restriction-uniqueness). -/
def sections (m : Option ℕ) (X : Scheme.{u}) (n : ℕ) :
    Modules l E m X ⥤ X.ProEtᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  match m with
  | some _ => SheafOfModules.toSheaf _ ⋙ sheafToPresheaf _ _
  | none => SheafOfModules.toSheaf _ ⋙ sheafToPresheaf _ _ ⋙
      (Functor.whiskeringLeft _ _ AddCommGrpCat.{u + 1}).obj (Prod.sectR n X.ProEt).op

/-- The actual constant coefficient sheaf at the selected level.
Source: Stacks 0H7J (blueprint: lem-sf-ambient-clopen-restriction-uniqueness). -/
abbrev ringSections (m : Option ℕ) (X : Scheme.{u}) (n : ℕ) (T : X.ProEt) :=
  (StrictTower.coefficients (scalarRings l E (m.getD n)) X).obj.obj (op T)

/-- Scalar action on the underlying sections; evaluation keeps the actual module action.
Source: Stacks 03DI; Zheng 4.1
(blueprint: lem-sf-ambient-clopen-restriction-uniqueness). -/
def act (m : Option ℕ) (X : Scheme.{u}) (M : Modules l E m X) (n : ℕ) (T : X.ProEt) :
    ringSections l E m X n T → ((sections l E m X n).obj M).obj (op T) →
      ((sections l E m X n).obj M).obj (op T) :=
  match m with
  | some _ => @SMul.smul _ (M.val.obj (op T)) inferInstance
  | none => @SMul.smul _
      (((VaryingRing.eval (scalarRings l E) (scalarTransitions l E) X n).obj M).val.obj
        (op T)) inferInstance

/-- Pull a coefficient section to the actual pulled-back pro-etale test object.
Source: Stacks 0H7J, 09AE
(blueprint: lem-sf-ambient-clopen-restriction-uniqueness). -/
def scalarRestriction (m : Option ℕ) {X Y : Scheme.{u}} (j : Y ⟶ X)
    (n : ℕ) (T : X.ProEt) : ringSections l E m X n T →
      ringSections l E m Y n (Scheme.ProEt.clopenTestPiece j T) :=
  ((Scheme.proEtaleConstantDirectImageMap j CommRingCat.{u + 1}
    (scalarRings l E (m.getD n))).hom.app (op T))

/-- The actual adjacent semilinear transition on sections, before any derived operation.
Source: Zheng 4.1 (blueprint: lem-sf-ambient-clopen-restriction-uniqueness). -/
def transition (m : Option ℕ) (X : Scheme.{u})
    (M : Modules l E m X) (n : ℕ) (T : X.ProEt) :
    ((sections l E m X (n + 1)).obj M).obj (op T) →
      ((sections l E m X n).obj M).obj (op T) :=
  match m with
  | some _ => id
  | none => fun x ↦ (M.val.map (Prod.mkHom (homOfLE (Nat.le_succ n)) (𝟙 T)).op).hom x

/-- The inverse-image comparison used by restrictionSource.
Source: Stacks 07A7 (blueprint: lem-sf-ambient-clopen-restriction-uniqueness). -/
def restrictionPull (m : Option ℕ) {U V W Z : Scheme.{u}}
    (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    (h : k ≫ p = r ≫ i) :
    pull l E m k ≅ pull l E m (pullback.fst p i) ⋙
      pull l E m (StrictTower.squareLift k r p i h) :=
  ((pullComp l E m (StrictTower.squareLift k r p i h) (pullback.fst p i)).symm ≪≫
    eqToIso (congrArg (pull l E m) (pullback.lift_fst k r h))).symm

/-- The source identification used by restriction of a Hom: insert the b-open unit
and the inverse pullback compositor, then use s b = k.
Source: Stacks 03DI, 07A7
(blueprint: lem-sf-ambient-clopen-restriction-uniqueness). -/
def restrictionSource (m : Option ℕ) {U V W Z : Scheme.{u}}
    (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i)
    (F : Modules l E m (pullback p i)) :
    (pull l E m (StrictTower.squareLift k r p i h)).obj F ⟶
      (pull l E m k).obj ((extension l E m (pullback.fst p i)).obj F) :=
  (pull l E m (StrictTower.squareLift k r p i h)).map
      ((openAdj l E m (pullback.fst p i)).unit.app F) ≫
    (restrictionPull l E m k r p i h).inv.app
      ((extension l E m (pullback.fst p i)).obj F)

/-- The comparison between the two inverse-image routes in the cartesian b,q square.
Source: Stacks 07A7 (blueprint: lem-sf-ambient-clopen-restriction-uniqueness). -/
def cartesianPull (m : Option ℕ) {V W Z : Scheme.{u}} (p : V ⟶ Z) (i : W ⟶ Z) :
    pull l E m i ⋙ pull l E m (pullback.snd p i) ≅
      pull l E m p ⋙ pull l E m (pullback.fst p i) :=
  match m with
  | some n => (StrictTower.moduleSquareG (scalarRings l E n)
      (pullback.snd p i) (pullback.fst p i) i p pullback.condition.symm).symm
  | none => (VaryingRing.moduleSquareG (scalarRings l E) (scalarTransitions l E)
      (pullback.snd p i) (pullback.fst p i) i p pullback.condition.symm).symm

/-- The complete abelian clopen assertion for either concrete coefficient category.
The inverse's section isomorphisms are natural in both test objects and module maps;
for systems the separate compatibility below fixes the adjacent transitions too.
Source: Stacks 0F7B and 04TS
(blueprint: lem-sf-ambient-clopen-restriction-uniqueness). -/
def Assertion (m : Option ℕ) {U V W Z : Scheme.{u}}
    (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) : Prop :=
  ∃ (C : (pullback p i).Opens),
    Set.range C.ι = (Set.range (StrictTower.squareLift k r p i h))ᶜ ∧
    ∃ (e : Modules l E m (pullback p i) ≌
        Modules l E m U × Modules l E m C.toScheme),
      e.functor = (pull l E m (StrictTower.squareLift k r p i h)).prod'
        (pull l E m C.ι) ∧
      PreservesFiniteLimits e.functor ∧ PreservesFiniteColimits e.functor ∧
      PreservesFiniteLimits e.inverse ∧ PreservesFiniteColimits e.inverse ∧
      (∃ σ : ∀ (F : Modules l E m U × Modules l E m C.toScheme) (n : ℕ)
          (T : (pullback p i).ProEt),
          ((sections l E m (pullback p i) n).obj (e.inverse.obj F)).obj (op T) ≃+
            (((sections l E m U n).obj F.1).obj
                (op (Scheme.ProEt.clopenTestPiece (StrictTower.squareLift k r p i h) T)) ×
              ((sections l E m C.toScheme n).obj F.2).obj
                (op (Scheme.ProEt.clopenTestPiece C.ι T))),
        (∀ F n T a x,
          σ F n T (act l E m (pullback p i) (e.inverse.obj F) n T a x) =
            (act l E m U F.1 n
                (Scheme.ProEt.clopenTestPiece (StrictTower.squareLift k r p i h) T)
                (scalarRestriction l E m (StrictTower.squareLift k r p i h) n T a)
                (σ F n T x).1,
              act l E m C.toScheme F.2 n (Scheme.ProEt.clopenTestPiece C.ι T)
                (scalarRestriction l E m C.ι n T a) (σ F n T x).2)) ∧
        (∀ F n T T' (a : T' ⟶ T) x,
          σ F n T' (((sections l E m (pullback p i) n).obj (e.inverse.obj F)).map a.op x) =
            (((sections l E m U n).obj F.1).map
                ((Scheme.proEtaleBaseChange (StrictTower.squareLift k r p i h)).map a).op
                (σ F n T x).1,
              ((sections l E m C.toScheme n).obj F.2).map
                ((Scheme.proEtaleBaseChange C.ι).map a).op (σ F n T x).2)) ∧
        (∀ F H (a : F ⟶ H) n T x,
          σ H n T (((sections l E m (pullback p i) n).map (e.inverse.map a)).app (op T) x) =
            (((sections l E m U n).map a.1).app
                (op (Scheme.ProEt.clopenTestPiece (StrictTower.squareLift k r p i h) T))
                (σ F n T x).1,
              ((sections l E m C.toScheme n).map a.2).app
                (op (Scheme.ProEt.clopenTestPiece C.ι T)) (σ F n T x).2)) ∧
        (∀ F n T x,
            σ F n T (transition l E m (pullback p i) (e.inverse.obj F) n T x) =
              (transition l E m U F.1 n
                  (Scheme.ProEt.clopenTestPiece (StrictTower.squareLift k r p i h) T)
                  (σ F (n + 1) T x).1,
                transition l E m C.toScheme F.2 n (Scheme.ProEt.clopenTestPiece C.ι T)
                  (σ F (n + 1) T x).2))) ∧
      (IsIso (openAdj l E m (StrictTower.squareLift k r p i h)).unit ∧
        ∀ G, IsZero ((pull l E m C.ι).obj
          ((extension l E m (StrictTower.squareLift k r p i h)).obj G))) ∧
      (∃ π : 𝟭 (Modules l E m (pullback p i)) ⟶
          pull l E m (StrictTower.squareLift k r p i h) ⋙
            extension l E m (StrictTower.squareLift k r p i h),
        ∀ F, (pull l E m (StrictTower.squareLift k r p i h)).map (π.app F) =
            (openAdj l E m (StrictTower.squareLift k r p i h)).unit.app
              ((pull l E m (StrictTower.squareLift k r p i h)).obj F) ∧
          (pull l E m C.ι).map (π.app F) = 0) ∧
      IsIso (openAdj l E m (pullback.fst p i)).unit ∧
      IsIso (openAdj l E m k).unit ∧
      (∃ H : ∀ (F : Modules l E m (pullback p i)) (G : Modules l E m U),
          ((extension l E m (pullback.fst p i)).obj F ⟶ (extension l E m k).obj G) ≃
            ((pull l E m (StrictTower.squareLift k r p i h)).obj F ⟶ G),
        (∀ F G a, H F G a ≫ (openAdj l E m k).unit.app G =
          restrictionSource l E m k r p i h F ≫ (pull l E m k).map a) ∧
        (∀ F F' G G' (a : F' ⟶ F) (b : G ⟶ G') f,
          H F' G' ((extension l E m (pullback.fst p i)).map a ≫ f ≫
              (extension l E m k).map b) =
            (pull l E m (StrictTower.squareLift k r p i h)).map a ≫ H F G f ≫ b)) ∧
      (∀ F G (a b : (extension l E m (pullback.fst p i)).obj F ⟶
          (extension l E m k).obj G),
        (pull l E m k).map a = (pull l E m k).map b → a = b) ∧
      (∃ β : extension l E m i ⋙ pull l E m p ≅
          pull l E m (pullback.snd p i) ⋙ extension l E m (pullback.fst p i),
        ∀ M, (openAdj l E m (pullback.fst p i)).unit.app
              ((pull l E m (pullback.snd p i)).obj M) ≫
            (pull l E m (pullback.fst p i)).map (β.inv.app M) =
          (pull l E m (pullback.snd p i)).map ((openAdj l E m i).unit.app M) ≫
            (cartesianPull l E m p i).hom.app ((extension l E m i).obj M))

section

universe vC vD vA

variable {S : Type vC} [Category.{vD} S] {J : GrothendieckTopology S}
  (R : Sheaf J RingCat.{vA})

attribute [-instance] CategoryTheory.catToReflQuiver
attribute [local irreducible] Functor.leftAdjoint StrictTower.modulePullback

-- An explicit product retains its actual section pairs.
private def pairPresheaf (M N : SheafOfModules.{vA} R) : PresheafOfModules.{vA} R.obj :=
  { obj U := ModuleCat.of _ (M.val.obj U × N.val.obj U)
    map {U V} f := ModuleCat.ofHom
      (Y := (ModuleCat.restrictScalars (R.obj.map f).hom).obj
        (ModuleCat.of _ (M.val.obj V × N.val.obj V)))
      { toFun := fun x ↦ (M.val.map f x.1, N.val.map f x.2)
        map_add' := fun x y ↦ Prod.ext (map_add _ _ _) (map_add _ _ _)
        map_smul' := fun r x ↦ Prod.ext (M.val.map_smul f r x.1)
          (N.val.map_smul f r x.2) }
    map_id U := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change (M.val.map (𝟙 U) x.1, N.val.map (𝟙 U) x.2) = _
      simp only [PresheafOfModules.map_id]
      rfl
    map_comp f g := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      exact Prod.ext (M.val.map_comp_apply f g x.1) (N.val.map_comp_apply f g x.2) }


private theorem pairPresheaf_isSheaf (M N : SheafOfModules.{vA} R) :
    Presheaf.IsSheaf J (pairPresheaf R M N).presheaf := by
  let P := pairPresheaf R M N
  let c : BinaryFan M.val N.val := BinaryFan.mk
    (P := P)
    { app U := ModuleCat.ofHom (LinearMap.fst _ _ _)
      naturality f := by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        rfl }
    { app U := ModuleCat.ofHom (LinearMap.snd _ _ _)
      naturality f := by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        rfl }
  have hc : IsLimit c :=
    PresheafOfModules.evaluationJointlyReflectsLimits _ _ (fun U ↦ by
      refine
        { lift := fun d ↦ ModuleCat.ofHom
            ((d.π.app ⟨WalkingPair.left⟩).hom.prod (d.π.app ⟨WalkingPair.right⟩).hom)
          fac := ?_
          uniq := ?_ }
      · intro d i
        rcases i with ⟨i⟩
        cases i <;> rfl
      · intro d q hq
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        exact Prod.ext (ConcreteCategory.congr_hom (hq ⟨WalkingPair.left⟩) x)
          (ConcreteCategory.congr_hom (hq ⟨WalkingPair.right⟩) x))
  exact PresheafOfModules.isSheaf_of_isLimit hc (fun i ↦ by
    rcases i with ⟨i⟩
    cases i
    · exact M.isSheaf
    · exact N.isSheaf)

private def pairModule (M N : SheafOfModules.{vA} R) : SheafOfModules.{vA} R :=
  ⟨pairPresheaf R M N, pairPresheaf_isSheaf R M N⟩

private def pairFst (M N : SheafOfModules.{vA} R) : pairModule R M N ⟶ M where
  val.app U := ModuleCat.ofHom (LinearMap.fst _ _ _)
  val.naturality f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl

private def pairSnd (M N : SheafOfModules.{vA} R) : pairModule R M N ⟶ N where
  val.app U := ModuleCat.ofHom (LinearMap.snd _ _ _)
  val.naturality f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl

private def pairLift {M N P : SheafOfModules.{vA} R} (f : M ⟶ N) (g : M ⟶ P) :
    M ⟶ pairModule R N P where
  val.app U := ModuleCat.ofHom ((f.val.app U).hom.prod (g.val.app U).hom)
  val.naturality a := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact Prod.ext (PresheafOfModules.naturality_apply f.val a x)
      (PresheafOfModules.naturality_apply g.val a x)

private theorem moduleHom_ext {M N : SheafOfModules.{vA} R} {f g : M ⟶ N}
    (h : ∀ V x, f.val.app V x = g.val.app V x) : f = g := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  exact h V

private def pairFunctor : SheafOfModules.{vA} R × SheafOfModules.{vA} R ⥤
    SheafOfModules.{vA} R where
  obj M := pairModule R M.1 M.2
  map f := pairLift R (pairFst R _ _ ≫ f.1) (pairSnd R _ _ ≫ f.2)
  map_id M := by apply moduleHom_ext; intro V x; rfl
  map_comp f g := by apply moduleHom_ext; intro V x; rfl

end

attribute [instance] CategoryTheory.catToReflQuiver

private abbrev modelSite (m : Option ℕ) (X : Scheme.{u}) : Type (u + 1) :=
  match m with
  | some _ => X.ProEt
  | none => ℕ × X.ProEt

private instance modelSiteCategory (m : Option ℕ) (X : Scheme.{u}) :
    Category.{u} (modelSite m X) := by
  cases m <;> exact inferInstance

private abbrev modelTopology (m : Option ℕ) (X : Scheme.{u}) :
    GrothendieckTopology (modelSite m X) :=
  match m with
  | some _ => Scheme.ProEt.topology X
  | none => WeilConjectures.coefficientSequenceTopology
      (Scheme.ProEt.topology X)

private def modelRing (m : Option ℕ) (X : Scheme.{u}) :
    Sheaf (modelTopology m X) RingCat.{u + 1} :=
  match m with
  | some n => (sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (StrictTower.coefficients (scalarRings l E n) X)
  | none => VaryingRing.seqRing (scalarRings l E) (scalarTransitions l E) X

private abbrev Model (m : Option ℕ) (X : Scheme.{u}) :=
  SheafOfModules.{u + 1} (modelRing l E m X)

private def modelPush (m : Option ℕ) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Model l E m X ⥤ Model l E m Y :=
  match m with
  | some n => StrictTower.moduleDirectImage (scalarRings l E n) f
  | none => VaryingRing.push (scalarRings l E) (scalarTransitions l E) f

attribute [local instance] VaryingRing.openMapContinuous VaryingRing.prodOpenContinuous

private def modelRestriction (m : Option ℕ) {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] : Model l E m X ⥤ Model l E m U :=
  match m with
  | some n => SheafOfModules.pushforward
      (@inv _ _ _ _ (VaryingRing.openLevelTranspose j (scalarRings l E n))
        (VaryingRing.openLevelTranspose_isIso j (scalarRings l E n)))
  | none => SheafOfModules.pushforward
      (@inv _ _ _ _ (VaryingRing.openRingTranspose (scalarRings l E)
        (scalarTransitions l E) j)
        (VaryingRing.openRingTranspose_isIso (scalarRings l E) (scalarTransitions l E) j))

private def modelAdj (m : Option ℕ) {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] : modelRestriction l E m j ⊣ modelPush l E m j := by
  cases m with
  | some n => exact VaryingRing.openLevelAdj (scalarRings l E) j n
  | none => exact VaryingRing.openPullAdj (scalarRings l E) (scalarTransitions l E) j

private theorem modelLevelCounit_apply {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (n : ℕ) (M : Model l E (some n) U) (V : U.ProEt)
    (x : (((modelPush l E (some n) j ⋙ modelRestriction l E (some n) j).obj M).val.obj (op V))) :
    (((modelAdj l E (some n) j).counit.app M).val.app (op V)) x =
      M.val.map (Scheme.ProEt.clopenDiagonal j V).op x := by
  rfl

private theorem modelSystemCounit_apply {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (M : Model l E none U) (V : U.ProEt) (n : ℕ)
    (x : (((modelPush l E none j ⋙ modelRestriction l E none j).obj M).val.obj (op (n, V)))) :
    (((modelAdj l E none j).counit.app M).val.app (op (n, V))) x =
      M.val.map (Prod.mkHom (𝟙 n) (Scheme.ProEt.clopenDiagonal j V)).op x := by
  rfl

private def modelGlue (m : Option ℕ) {U X C : Scheme.{u}} (s : U ⟶ X) (c : C ⟶ X) :
    Model l E m U × Model l E m C ⥤ Model l E m X :=
  (modelPush l E m s).prod (modelPush l E m c) ⋙ pairFunctor (modelRing l E m X)

private def modelUnit (m : Option ℕ) {U X C : Scheme.{u}} (s : U ⟶ X) (c : C ⟶ X)
    [IsOpenImmersion s] [IsOpenImmersion c] :
    𝟭 (Model l E m X) ⟶
      (modelRestriction l E m s).prod' (modelRestriction l E m c) ⋙ modelGlue l E m s c where
  app M := pairLift _ ((modelAdj l E m s).unit.app M) ((modelAdj l E m c).unit.app M)
  naturality {M N} f := by
    apply moduleHom_ext
    intro V x
    exact Prod.ext
      (ConcreteCategory.congr_hom
        (congrArg (fun q ↦ q.val.app V) ((modelAdj l E m s).unit.naturality f)) x)
      (ConcreteCategory.congr_hom
        (congrArg (fun q ↦ q.val.app V) ((modelAdj l E m c).unit.naturality f)) x)

private def modelCounit (m : Option ℕ) {U X C : Scheme.{u}} (s : U ⟶ X) (c : C ⟶ X)
    [IsOpenImmersion s] [IsOpenImmersion c] :
    modelGlue l E m s c ⋙
      (modelRestriction l E m s).prod' (modelRestriction l E m c) ⟶
      𝟭 (Model l E m U × Model l E m C) where
  app M :=
    ((modelRestriction l E m s).map (pairFst _ _ _) ≫
        (modelAdj l E m s).counit.app M.1,
      (modelRestriction l E m c).map (pairSnd _ _ _) ≫
        (modelAdj l E m c).counit.app M.2)
  naturality {M N} f := by
    apply Prod.hom_ext
    · change (modelRestriction l E m s).map ((modelGlue l E m s c).map f) ≫
          ((modelRestriction l E m s).map (pairFst _ _ _) ≫
            (modelAdj l E m s).counit.app N.1) =
        ((modelRestriction l E m s).map (pairFst _ _ _) ≫
          (modelAdj l E m s).counit.app M.1) ≫ f.1
      rw [← Category.assoc, ← Functor.map_comp]
      have hp : (modelGlue l E m s c).map f ≫ pairFst _ _ _ =
          pairFst _ _ _ ≫ (modelPush l E m s).map f.1 := by
        apply moduleHom_ext
        intro V x
        rfl
      rw [hp, Functor.map_comp, Category.assoc]
      have hn := (modelAdj l E m s).counit.naturality f.1
      dsimp only [Functor.comp_map, Functor.id_map] at hn
      exact (congrArg (fun q ↦ (modelRestriction l E m s).map
        (pairFst _ _ _) ≫ q) hn).trans (Category.assoc _ _ _).symm
    · change (modelRestriction l E m c).map ((modelGlue l E m s c).map f) ≫
          ((modelRestriction l E m c).map (pairSnd _ _ _) ≫
            (modelAdj l E m c).counit.app N.2) =
        ((modelRestriction l E m c).map (pairSnd _ _ _) ≫
          (modelAdj l E m c).counit.app M.2) ≫ f.2
      rw [← Category.assoc, ← Functor.map_comp]
      have hp : (modelGlue l E m s c).map f ≫ pairSnd _ _ _ =
          pairSnd _ _ _ ≫ (modelPush l E m c).map f.2 := by
        apply moduleHom_ext
        intro V x
        rfl
      rw [hp, Functor.map_comp, Category.assoc]
      have hn := (modelAdj l E m c).counit.naturality f.2
      dsimp only [Functor.comp_map, Functor.id_map] at hn
      exact (congrArg (fun q ↦ (modelRestriction l E m c).map
        (pairSnd _ _ _) ≫ q) hn).trans (Category.assoc _ _ _).symm

private theorem moduleIso_of_sections {S : Type*} [Category S]
    {J : GrothendieckTopology S} {R : Sheaf J RingCat.{u + 1}}
    {M N : SheafOfModules.{u + 1} R} (f : M ⟶ N)
    (h : ∀ V, Function.Bijective (f.val.app V)) : IsIso f := by
  have (V : Sᵒᵖ) : IsIso (f.val.app V) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (h V)
  let e := PresheafOfModules.isoMk (fun V ↦ asIso (f.val.app V))
    (fun {_ _} a ↦ f.val.naturality a)
  have : IsIso f.val := by change IsIso e.hom; infer_instance
  have : IsIso ((SheafOfModules.forget R).map f) := by
    change IsIso f.val
    infer_instance
  exact isIso_of_reflects_iso f (SheafOfModules.forget R)

-- Evaluate the diagram site without transporting its coefficient ring along an equality.
attribute [local instance] VaryingRing.fixedEvalContinuous

private def sliceRing (X : Scheme.{u}) (n : ℕ) :
    Sheaf (Scheme.ProEt.topology X) RingCat.{u + 1} :=
  ((Prod.sectR n X.ProEt).sheafPushforwardContinuous RingCat.{u + 1}
    (Scheme.ProEt.topology X) (modelTopology none X)).obj (modelRing l E none X)

private def sliceModule {X : Scheme.{u}} (M : Model l E none X) (n : ℕ) :
    SheafOfModules.{u + 1} (sliceRing l E X n) :=
  (SheafOfModules.pushforward (F := Prod.sectR n X.ProEt) (𝟙 _)).obj M

private theorem clopenPair_bijective {U X C : Scheme.{u}}
    (R : Sheaf (Scheme.ProEt.topology X) RingCat.{u + 1})
    (s : U ⟶ X) (c : C ⟶ X) [IsOpenImmersion s] [IsOpenImmersion c]
    (hc : Set.range c = (Set.range s)ᶜ) (F : SheafOfModules.{u + 1} R) (H : X.ProEt) :
    Function.Bijective (fun x : F.val.obj (op H) ↦
      (F.val.map (Scheme.ProEt.clopenTestInclusion s H).op x,
        F.val.map (Scheme.ProEt.clopenTestInclusion c H).op x)) := by
  classical
  let Y : Bool → Scheme.{u} := Bool.rec U C
  let j : ∀ b, Y b ⟶ X := Bool.rec s c
  have hj : ∀ b : Bool, IsOpenImmersion (j b) := by
    intro b
    cases b <;> dsimp [j, Y] <;> infer_instance
  let : ∀ b : Bool, IsOpenImmersion (j b) := hj
  have hd : Pairwise (fun (b d : Bool) ↦ Disjoint
      (Set.range (fun x : Y b ↦ (j b).base x)) (Set.range (fun x : Y d ↦ (j d).base x))) := by
    intro b d hbd
    cases b <;> cases d
    · exact (hbd rfl).elim
    · change Disjoint (Set.range s) (Set.range c)
      rw [hc]
      exact disjoint_compl_right
    · change Disjoint (Set.range c) (Set.range s)
      rw [hc]
      exact disjoint_compl_left
    · exact (hbd rfl).elim
  have hcover (x : X) : ∃ b, x ∈ Set.range (fun z : Y b ↦ (j b).base z) := by
    by_cases hx : x ∈ Set.range s
    · exact ⟨false, hx⟩
    · exact ⟨true, by change x ∈ Set.range c; rwa [hc]⟩
  have hb := @Scheme.ProEt.clopenSections_bijective
    X Bool Y j hj hd hcover
    R F H
  constructor
  · intro x y hxy
    apply hb.1
    funext b
    cases b
    · exact congrArg Prod.fst hxy
    · exact congrArg Prod.snd hxy
  · intro x
    obtain ⟨z, hz⟩ := hb.2 (fun b ↦ match b with
      | false => x.1
      | true => x.2)
    exact ⟨z, Prod.ext (congrFun hz false) (congrFun hz true)⟩

private theorem modelUnit_isIso (m : Option ℕ) {U X C : Scheme.{u}}
    (s : U ⟶ X) (c : C ⟶ X) [IsOpenImmersion s] [IsClosedImmersion s]
    [IsOpenImmersion c] (hc : Set.range c = (Set.range s)ᶜ) :
    IsIso (modelUnit l E m s c) := by
  have hi (M : Model l E m X) : IsIso ((modelUnit l E m s c).app M) := by
    apply moduleIso_of_sections
    intro V
    cases m with
    | some n =>
      change Function.Bijective (fun x ↦
        (((VaryingRing.openLevelAdj (scalarRings l E) s n).unit.app M).val.app V x,
          ((VaryingRing.openLevelAdj (scalarRings l E) c n).unit.app M).val.app V x))
      have he : (fun x ↦
          (((VaryingRing.openLevelAdj (scalarRings l E) s n).unit.app M).val.app V x,
            ((VaryingRing.openLevelAdj (scalarRings l E) c n).unit.app M).val.app V x)) =
          (fun x ↦ (M.val.map (Scheme.ProEt.clopenTestInclusion s V.unop).op x,
            M.val.map (Scheme.ProEt.clopenTestInclusion c V.unop).op x)) := by
        funext x
        exact Prod.ext (VaryingRing.openLevelUnit (scalarRings l E) s n M V.unop x)
          (VaryingRing.openLevelUnit (scalarRings l E) c n M V.unop x)
      rw [he]
      exact StrictTower.clopen_section_decomposition (scalarRings l E n) s c hc M V.unop
    | none =>
      rcases V with ⟨n, V⟩
      change Function.Bijective (fun x ↦
        (((VaryingRing.openPullAdj (scalarRings l E) (scalarTransitions l E)
              s).unit.app M).val.app
              (op (n, V)) x,
          ((VaryingRing.openPullAdj (scalarRings l E) (scalarTransitions l E)
              c).unit.app M).val.app
              (op (n, V)) x))
      have he : (fun x ↦
          (((VaryingRing.openPullAdj (scalarRings l E) (scalarTransitions l E)
              s).unit.app M).val.app
              (op (n, V)) x,
            ((VaryingRing.openPullAdj (scalarRings l E) (scalarTransitions l E)
              c).unit.app M).val.app
              (op (n, V)) x)) =
          (fun x ↦
            (M.val.map (Prod.mkHom (𝟙 n) (Scheme.ProEt.clopenTestInclusion s V)).op x,
              M.val.map (Prod.mkHom (𝟙 n) (Scheme.ProEt.clopenTestInclusion c V)).op x)) := by
        funext x
        exact Prod.ext
          (VaryingRing.openPullUnit (scalarRings l E) (scalarTransitions l E) s M V n x)
          (VaryingRing.openPullUnit (scalarRings l E) (scalarTransitions l E) c M V n x)
      rw [he]
      exact clopenPair_bijective (sliceRing l E X n) s c hc (sliceModule l E M n) V
  exact NatIso.isIso_of_isIso_app _

private theorem crossEmpty {U X C : Scheme.{u}} (s : U ⟶ X) (c : C ⟶ X)
    [IsOpenImmersion s] (hd : Disjoint (Set.range s) (Set.range c)) (V : U.ProEt) :
    IsEmpty (Scheme.ProEt.clopenTestPiece c
      ((MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale s)).obj V)).left := by
  constructor
  intro z
  exact Set.disjoint_left.mp hd
    ⟨V.hom (pullback.fst (V.hom ≫ s) c z), rfl⟩
    ⟨pullback.snd (V.hom ≫ s) c z,
      congrArg (fun f ↦ f z) (pullback.condition (f := V.hom ≫ s) (g := c)).symm⟩

private theorem modelOffDiagonal_subsingleton (m : Option ℕ) {U X C : Scheme.{u}}
    (s : U ⟶ X) (c : C ⟶ X) [IsOpenImmersion s]
    (hd : Disjoint (Set.range s) (Set.range c)) (M : Model l E m C)
    (V : (modelSite m U)ᵒᵖ) :
    Subsingleton (((modelRestriction l E m s).obj
      ((modelPush l E m c).obj M)).val.obj V) := by
  cases m with
  | some n =>
    have hh := crossEmpty s c hd V.unop
    change IsEmpty ((Scheme.proEtaleBaseChange c).obj
      ((VaryingRing.openMap s).obj V.unop)).left at hh
    change Subsingleton (M.val.obj (op
      ((Scheme.proEtaleBaseChange c).obj ((VaryingRing.openMap s).obj V.unop))))
    exact @Scheme.ProEt.moduleSections_empty _ _ M _ hh
  | none =>
    rcases V with ⟨n, V⟩
    have hh := crossEmpty s c hd V
    change IsEmpty ((Scheme.proEtaleBaseChange c).obj
      ((VaryingRing.openMap s).obj V)).left at hh
    change Subsingleton (M.val.obj (op (n,
      (Scheme.proEtaleBaseChange c).obj ((VaryingRing.openMap s).obj V))))
    exact @Scheme.ProEt.moduleSections_empty _ (sliceRing l E C n)
      (sliceModule l E M n) _ hh

private theorem modelCounit_isIso (m : Option ℕ) {U X C : Scheme.{u}}
    (s : U ⟶ X) (c : C ⟶ X) [IsOpenImmersion s] [IsClosedImmersion s]
    [IsOpenImmersion c] (hc : Set.range c = (Set.range s)ᶜ) :
    IsIso (modelCounit l E m s c) := by
  have hdiag {Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
      (N : Model l E m Y) (V : (modelSite m Y)ᵒᵖ) :
      Function.Bijective (((modelAdj l E m j).counit.app N).val.app V) := by
    cases m with
    | some n =>
      have := Scheme.ProEt.clopenDiagonal_isIso j V.unop
      have hb := ConcreteCategory.bijective_of_isIso
        (N.val.presheaf.map (Scheme.ProEt.clopenDiagonal j V.unop).op)
      have he : (fun x ↦ (((modelAdj l E (some n) j).counit.app N).val.app V) x) =
          (fun x ↦ N.val.map (Scheme.ProEt.clopenDiagonal j V.unop).op x) := by
        funext x
        exact modelLevelCounit_apply l E j n N V.unop x
      exact (congrArg Function.Bijective he).mpr hb
    | none =>
      rcases V with ⟨n, V⟩
      have := Scheme.ProEt.clopenDiagonal_isIso j V
      have : IsIso (Prod.mkHom (𝟙 n) (Scheme.ProEt.clopenDiagonal j V)) :=
        (CategoryTheory.isIso_prod_iff _ _).mpr ⟨inferInstance, inferInstance⟩
      have hb := ConcreteCategory.bijective_of_isIso
        (N.val.presheaf.map (Prod.mkHom (𝟙 n) (Scheme.ProEt.clopenDiagonal j V)).op)
      have he : (fun x ↦ (((modelAdj l E none j).counit.app N).val.app (op (n, V))) x) =
          (fun x ↦ N.val.map
            (Prod.mkHom (𝟙 n) (Scheme.ProEt.clopenDiagonal j V)).op x) := by
        funext x
        exact modelSystemCounit_apply l E j N V n x
      exact (congrArg Function.Bijective he).mpr hb
  have hi (M : Model l E m U × Model l E m C) :
      IsIso ((modelCounit l E m s c).app M) := by
    have h₁ : IsIso (((modelCounit l E m s c).app M).1) := by
      apply moduleIso_of_sections
      intro V
      have hd : Disjoint (Set.range s) (Set.range c) := by
        rw [hc]; exact disjoint_compl_right
      have hs := modelOffDiagonal_subsingleton l E m s c hd M.2 V
      have hb := hdiag s M.1 V
      cases m <;> (
        change Function.Bijective (fun x : _ × _ ↦
          (((modelAdj l E _ s).counit.app M.1).val.app V) x.1)
        apply hb.comp
        exact ⟨fun x y h ↦ Prod.ext h (hs.elim _ _), fun x ↦ ⟨(x, 0), rfl⟩⟩)
    have h₂ : IsIso (((modelCounit l E m s c).app M).2) := by
      apply moduleIso_of_sections
      intro V
      have hd : Disjoint (Set.range c) (Set.range s) := by
        rw [hc]; exact disjoint_compl_left
      have hs := modelOffDiagonal_subsingleton l E m c s hd M.1 V
      have hb := hdiag c M.2 V
      cases m <;> (
        change Function.Bijective (fun x : _ × _ ↦
          (((modelAdj l E _ c).counit.app M.2).val.app V) x.2)
        apply hb.comp
        exact ⟨fun x y h ↦ Prod.ext (hs.elim _ _) h, fun x ↦ ⟨(0, x), rfl⟩⟩)
    exact ⟨⟨(inv (((modelCounit l E m s c).app M).1),
      inv (((modelCounit l E m s c).app M).2)),
      Prod.hom_ext (IsIso.hom_inv_id _) (IsIso.hom_inv_id _),
      Prod.hom_ext (IsIso.inv_hom_id _) (IsIso.inv_hom_id _)⟩⟩
  exact NatIso.isIso_of_isIso_app _

private def modelEquivalence (m : Option ℕ) {U X C : Scheme.{u}}
    (s : U ⟶ X) (c : C ⟶ X) [IsOpenImmersion s] [IsClosedImmersion s]
    [IsOpenImmersion c] (hc : Set.range c = (Set.range s)ᶜ) :
    Model l E m X ≌ Model l E m U × Model l E m C := by
  have := modelUnit_isIso l E m s c hc
  have := modelCounit_isIso l E m s c hc
  exact CategoryTheory.Equivalence.mk
    ((modelRestriction l E m s).prod' (modelRestriction l E m c))
    (modelGlue l E m s c) (asIso (modelUnit l E m s c))
    (asIso (modelCounit l E m s c))

private def modelPull (m : Option ℕ) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Model l E m Y ⥤ Model l E m X :=
  match m with
  | some n => StrictTower.modulePullback (scalarRings l E n) f
  | none => VaryingRing.pull (scalarRings l E) (scalarTransitions l E) f

private def modelPullAdj (m : Option ℕ) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    modelPull l E m f ⊣ modelPush l E m f :=
  match m with
  | some n => StrictTower.clopenModuleAdj (scalarRings l E n) f
  | none => VaryingRing.moduleAdj (scalarRings l E) (scalarTransitions l E) f

private def modelPullIso (m : Option ℕ) {U X : Scheme.{u}} (s : U ⟶ X)
    [IsOpenImmersion s] : modelRestriction l E m s ≅ modelPull l E m s :=
  (modelAdj l E m s).leftAdjointUniq (modelPullAdj l E m s)

private def pullEquivalence (m : Option ℕ) {U X C : Scheme.{u}}
    (s : U ⟶ X) (c : C ⟶ X) [IsOpenImmersion s] [IsClosedImmersion s]
    [IsOpenImmersion c] (hc : Set.range c = (Set.range s)ᶜ) :
    Model l E m X ≌ Model l E m U × Model l E m C :=
  (modelEquivalence l E m s c hc).changeFunctor
    (NatIso.ofComponents (G := (modelPull l E m s).prod' (modelPull l E m c))
      (fun M ↦ Iso.prod ((modelPullIso l E m s).app M) ((modelPullIso l E m c).app M))
      (fun f ↦ Prod.hom_ext ((modelPullIso l E m s).hom.naturality f)
        ((modelPullIso l E m c).hom.naturality f)))

private theorem openUnit_isIso (m : Option ℕ) {U X : Scheme.{u}}
    (s : U ⟶ X) [IsOpenImmersion s] : IsIso (openAdj l E m s).unit := by
  cases m with
  | some n => exact StrictTower.clopenModule_openUnit_isIso (scalarRings l E n) s
  | none =>
    exact VaryingRing.moduleJAdj_unit_isIso
      (scalarRings l E) (scalarTransitions l E) s

private def ambientEquivalence (m : Option ℕ) {U X C : Scheme.{u}}
    (s : U ⟶ X) (c : C ⟶ X) [IsOpenImmersion s] [IsClosedImmersion s]
    [IsOpenImmersion c] (hc : Set.range c = (Set.range s)ᶜ) :
    Modules l E m X ≌ Modules l E m U × Modules l E m C := by
  cases m with
  | some n => exact pullEquivalence l E (some n) s c hc
  | none => exact pullEquivalence l E none s c hc

private theorem ambientEquivalence_functor (m : Option ℕ) {U X C : Scheme.{u}}
    (s : U ⟶ X) (c : C ⟶ X) [IsOpenImmersion s] [IsClosedImmersion s]
    [IsOpenImmersion c] (hc : Set.range c = (Set.range s)ᶜ) :
    (ambientEquivalence l E m s c hc).functor =
      (pull l E m s).prod' (pull l E m c) := by
  cases m <;> rfl

private theorem extension_disjoint_zero (m : Option ℕ) {U X C : Scheme.{u}}
    (s : U ⟶ X) (c : C ⟶ X) [IsOpenImmersion s] [IsOpenImmersion c]
    (hd : Disjoint (Set.range s) (Set.range c)) (G : Modules l E m U) :
    IsZero ((pull l E m c).obj ((extension l E m s).obj G)) := by
  cases m with
  | some n => exact StrictTower.module_disjoint_extension (scalarRings l E n) s c hd G
  | none =>
    exact VaryingRing.module_disjoint_extension
      (scalarRings l E) (scalarTransitions l E) s c hd G

attribute [local irreducible] modelUnit modelCounit modelAdj modelPullIso

private def sectionIso (m : Option ℕ) {U X C : Scheme.{u}}
    (s : U ⟶ X) (c : C ⟶ X) [IsOpenImmersion s] [IsClosedImmersion s]
    [IsOpenImmersion c] (hc : Set.range c = (Set.range s)ᶜ)
    (F : Modules l E m U × Modules l E m C) (n : ℕ) (T : X.ProEt) :
    ((sections l E m X n).obj ((ambientEquivalence l E m s c hc).inverse.obj F)).obj
        (op T) ≃+
      (((sections l E m U n).obj F.1).obj (op (Scheme.ProEt.clopenTestPiece s T)) ×
        ((sections l E m C n).obj F.2).obj (op (Scheme.ProEt.clopenTestPiece c T))) := by
  cases m <;> (
    exact AddEquiv.refl _)

private theorem system_act (X : Scheme.{u}) (M : Modules l E none X) (n : ℕ)
    (T : X.ProEt) (a : ringSections l E none X n T)
    (x : ((sections l E none X n).obj M).obj (op T)) :
    act l E none X M n T a x = @SMul.smul ((VaryingRing.seqRing (scalarRings l E)
      (scalarTransitions l E) X).obj.obj (op (n, T)))
      (M.val.obj (op (n, T))) inferInstance a x := by
  exact WeilConjectures.SemilinearSections.evaluation_smul
    (Scheme.ProEt.topology X) (VaryingRing.coefficients (scalarRings l E) X)
    (VaryingRing.coefficientTransition (scalarRings l E) (scalarTransitions l E) X)
    n M (op T) a x

private theorem sectionIso_scalar (m : Option ℕ) {U X C : Scheme.{u}}
    (s : U ⟶ X) (c : C ⟶ X) [IsOpenImmersion s] [IsClosedImmersion s]
    [IsOpenImmersion c] (hc : Set.range c = (Set.range s)ᶜ)
    (F : Modules l E m U × Modules l E m C) (n : ℕ) (T : X.ProEt) (a) (x) :
    sectionIso l E m s c hc F n T
        (act l E m X ((ambientEquivalence l E m s c hc).inverse.obj F) n T a x) =
      (act l E m U F.1 n (Scheme.ProEt.clopenTestPiece s T)
          (scalarRestriction l E m s n T a) (sectionIso l E m s c hc F n T x).1,
        act l E m C F.2 n (Scheme.ProEt.clopenTestPiece c T)
          (scalarRestriction l E m c n T a) (sectionIso l E m s c hc F n T x).2) := by
  cases m with
  | none =>
    rw [system_act, system_act, system_act]
    dsimp only [sectionIso]
    rfl
  | some d =>
    have hm {Y : Scheme.{u}} (j : Y ⟶ X) :
        Scheme.proEtaleRingDirectImageMap j
            (StrictTower.coefficients (scalarRings l E d) X)
            (StrictTower.coefficients (scalarRings l E d) Y)
            (StrictTower.constantRingIso (scalarRings l E d) j) =
          Scheme.proEtaleConstantDirectImageMap j CommRingCat.{u + 1}
            (scalarRings l E d) :=
      ((Scheme.proEtaleSheafAdjunction j CommRingCat.{u + 1}).homEquiv _ _).apply_symm_apply _
    change
      (F.1.val.obj (op (Scheme.ProEt.clopenTestPiece s T)) ×
        F.2.val.obj (op (Scheme.ProEt.clopenTestPiece c T))) at x
    change
      ((Scheme.proEtaleRingDirectImageMap s
        (StrictTower.coefficients (scalarRings l E d) X)
        (StrictTower.coefficients (scalarRings l E d) U)
        (StrictTower.constantRingIso (scalarRings l E d) s)).hom.app (op T) a • x.1,
        (Scheme.proEtaleRingDirectImageMap c
          (StrictTower.coefficients (scalarRings l E d) X)
          (StrictTower.coefficients (scalarRings l E d) C)
          (StrictTower.constantRingIso (scalarRings l E d) c)).hom.app (op T) a • x.2) = _
    rw [hm s, hm c]
    rfl

private theorem sectionIso_transition (m : Option ℕ) {U X C : Scheme.{u}}
    (s : U ⟶ X) (c : C ⟶ X) [IsOpenImmersion s] [IsClosedImmersion s]
    [IsOpenImmersion c] (hc : Set.range c = (Set.range s)ᶜ)
    (F : Modules l E m U × Modules l E m C) (n : ℕ) (T : X.ProEt)
    (x : ((sections l E m X (n + 1)).obj
      ((ambientEquivalence l E m s c hc).inverse.obj F)).obj (op T)) :
    sectionIso l E m s c hc F n T
        (transition l E m X ((ambientEquivalence l E m s c hc).inverse.obj F) n T x) =
      (transition l E m U F.1 n (Scheme.ProEt.clopenTestPiece s T)
          (sectionIso l E m s c hc F (n + 1) T x).1,
        transition l E m C F.2 n (Scheme.ProEt.clopenTestPiece c T)
          (sectionIso l E m s c hc F (n + 1) T x).2) := by
  cases m with
  | some d => rfl
  | none =>
    change
      ((F.1.val.map (Prod.mkHom (homOfLE (Nat.le_succ n))
          ((Scheme.proEtaleBaseChange s).map (𝟙 T))).op).hom x.1,
        (F.2.val.map (Prod.mkHom (homOfLE (Nat.le_succ n))
          ((Scheme.proEtaleBaseChange c).map (𝟙 T))).op).hom x.2) =
      ((F.1.val.map (Prod.mkHom (homOfLE (Nat.le_succ n))
          (𝟙 (Scheme.ProEt.clopenTestPiece s T))).op).hom x.1,
        (F.2.val.map (Prod.mkHom (homOfLE (Nat.le_succ n))
          (𝟙 (Scheme.ProEt.clopenTestPiece c T))).op).hom x.2)
    rw [(Scheme.proEtaleBaseChange s).map_id T, (Scheme.proEtaleBaseChange c).map_id T]

section
universe vA uA vB uB vD uD vX uX
variable {A : Type uA} [Category.{vA} A] {B : Type uB} [Category.{vB} B]
  {D : Type uD} [Category.{vD} D] [HasZeroMorphisms D]
  {X : Type uX} [Category.{vX} X]

private theorem equivalence_finite (e : A ≌ B) :
    PreservesFiniteLimits e.functor ∧ PreservesFiniteColimits e.functor ∧
      PreservesFiniteLimits e.inverse ∧ PreservesFiniteColimits e.inverse := by
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

private def zeroTargetHom (a : A) (d : D) (b : A) (z : D) (hz : IsZero z) :
    ((a, d) ⟶ (b, z)) ≃ (a ⟶ b) where
  toFun f := f.1
  invFun f := (f, 0)
  left_inv _f := Prod.hom_ext rfl (hz.eq_zero_of_tgt _).symm
  right_inv _f := rfl

private def homToOpen {L : B ⥤ A} {R : A ⥤ B} (adj : L ⊣ R)
    [IsIso adj.unit] (Q : A ⥤ D) (e : A ≌ B × D)
    (he : e.functor = R.prod' Q) (hz : ∀ G, IsZero (Q.obj (L.obj G)))
    (F : A) (G : B) : (F ⟶ L.obj G) ≃ (R.obj F ⟶ G) := by
  let ff : (R.prod' Q).FullyFaithful := he ▸ e.fullyFaithfulFunctor
  exact ff.homEquiv |>.trans
    ((zeroTargetHom _ _ _ _ (hz G)).trans
      (Iso.homCongr (Iso.refl _) (asIso (adj.unit.app G)).symm))

private theorem homToOpen_formula {L : B ⥤ A} {R : A ⥤ B} (adj : L ⊣ R)
    [IsIso adj.unit] (Q : A ⥤ D) (e : A ≌ B × D)
    (he : e.functor = R.prod' Q) (hz : ∀ G, IsZero (Q.obj (L.obj G)))
    (F : A) (G : B) (f : F ⟶ L.obj G) :
    homToOpen adj Q e he hz F G f ≫ adj.unit.app G = R.map f := by
  dsimp [homToOpen, zeroTargetHom, Iso.homCongr, Functor.FullyFaithful.homEquiv]
  simp

private def squareHom {Ls : B ⥤ A} {Rs : A ⥤ B} (as_ : Ls ⊣ Rs)
    [IsIso as_.unit] (Q : A ⥤ D) (e : A ≌ B × D)
    (he : e.functor = Rs.prod' Q) (hz : ∀ G, IsZero (Q.obj (Ls.obj G)))
    {Lb : A ⥤ X} {Rb : X ⥤ A} (ab : Lb ⊣ Rb) [IsIso ab.unit]
    {Lk : B ⥤ X} {Rk : X ⥤ B} (ak : Lk ⊣ Rk)
    (t : Rk ≅ Rb ⋙ Rs) (F : A) (G : B) :
    (Lb.obj F ⟶ Lk.obj G) ≃ (Rs.obj F ⟶ G) :=
  (Iso.homCongr (Iso.refl _)
      (((conjugateIsoEquiv ak (as_.comp ab)).symm t).app G).symm).trans
    (ab.fullyFaithfulLOfIsIsoUnit.homEquiv.symm.trans
      (homToOpen as_ Q e he hz F G))

private theorem squareHom_formula {Ls : B ⥤ A} {Rs : A ⥤ B} (as_ : Ls ⊣ Rs)
    [IsIso as_.unit] (Q : A ⥤ D) (e : A ≌ B × D)
    (he : e.functor = Rs.prod' Q) (hz : ∀ G, IsZero (Q.obj (Ls.obj G)))
    {Lb : A ⥤ X} {Rb : X ⥤ A} (ab : Lb ⊣ Rb) [IsIso ab.unit]
    {Lk : B ⥤ X} {Rk : X ⥤ B} (ak : Lk ⊣ Rk)
    (t : Rk ≅ Rb ⋙ Rs) (F : A) (G : B) (f : Lb.obj F ⟶ Lk.obj G) :
    squareHom as_ Q e he hz ab ak t F G f ≫ ak.unit.app G =
      Rs.map (ab.unit.app F) ≫ t.inv.app (Lb.obj F) ≫ Rk.map f := by
  let c := (conjugateIsoEquiv ak (as_.comp ab)).symm t
  let ff := ab.fullyFaithfulLOfIsIsoUnit
  let g := ff.preimage (f ≫ c.inv.app G)
  have hg : Lb.map g = f ≫ c.inv.app G := ff.map_preimage _
  have hh := homToOpen_formula as_ Q e he hz F G g
  dsimp only [squareHom, Equiv.trans_apply, Iso.homCongr,
    Functor.FullyFaithful.homEquiv, Equiv.symm, Equiv.coe_fn_mk,
    Iso.refl_inv, Iso.symm_hom, Iso.app_inv]
  simp only [Category.id_comp]
  change homToOpen as_ Q e he hz F G g ≫ ak.unit.app G = _
  apply (cancel_mono (t.hom.app (Lk.obj G))).1
  have hu : ak.unit.app G ≫ t.hom.app (Lk.obj G) =
      as_.unit.app G ≫ Rs.map (ab.unit.app (Ls.obj G)) ≫
        Rs.map (Rb.map (c.hom.app G)) :=
    by
      simpa only [c, conjugateIsoEquiv, Equiv.symm, Equiv.coe_fn_mk,
        Adjunction.comp_unit_app, Functor.comp_map, Category.assoc] using
        (unit_conjugateEquiv_symm ak (as_.comp ab) t.hom G)
  have hn := ab.unit.naturality g
  dsimp only [Functor.id_map, Functor.comp_map] at hn
  rw [Category.assoc, hu, ← Category.assoc, ← Category.assoc, hh]
  rw [← Rs.map_comp, hn, Rs.map_comp, hg,
    Rb.map_comp, Rs.map_comp]
  simp only [Category.assoc]
  have ht := t.inv.naturality f
  dsimp only [Functor.comp_map] at ht
  rw [← Category.assoc (t.inv.app _) (Rk.map f), ← ht]
  simp only [← Rs.map_comp, ← Rb.map_comp, Iso.inv_hom_id_app,
    Category.comp_id, Category.assoc]


private theorem homEquiv_naturality {Lb : A ⥤ X} {Rk : X ⥤ B} {Lk : B ⥤ X}
    {Rs : A ⥤ B} (ak : Lk ⊣ Rk) [IsIso ak.unit]
    (H : ∀ F G, (Lb.obj F ⟶ Lk.obj G) ≃ (Rs.obj F ⟶ G))
    (c : ∀ F, Rs.obj F ⟶ Rk.obj (Lb.obj F))
    (hf : ∀ F G f, H F G f ≫ ak.unit.app G = c F ≫ Rk.map f)
    (hn : ∀ {F F'} (a : F' ⟶ F), c F' ≫ Rk.map (Lb.map a) = Rs.map a ≫ c F)
    {F F' : A} {G G' : B} (a : F' ⟶ F) (b : G ⟶ G')
    (f : Lb.obj F ⟶ Lk.obj G) :
    H F' G' (Lb.map a ≫ f ≫ Lk.map b) = Rs.map a ≫ H F G f ≫ b := by
  apply (cancel_mono (ak.unit.app G')).1
  have hu := ak.unit.naturality b
  dsimp only [Functor.id_map, Functor.comp_map] at hu
  calc
    H F' G' (Lb.map a ≫ f ≫ Lk.map b) ≫ ak.unit.app G' =
        c F' ≫ Rk.map (Lb.map a ≫ f ≫ Lk.map b) := hf _ _ _
    _ = (c F' ≫ Rk.map (Lb.map a)) ≫ Rk.map f ≫ Rk.map (Lk.map b) := by
      simp only [Functor.map_comp, Category.assoc]
    _ = Rs.map a ≫ (c F ≫ Rk.map f) ≫ Rk.map (Lk.map b) := by
      rw [hn a]
      simp only [Category.assoc]
    _ = Rs.map a ≫ (H F G f ≫ ak.unit.app G) ≫ Rk.map (Lk.map b) := by
      rw [hf F G f]
    _ = (Rs.map a ≫ H F G f ≫ b) ≫ ak.unit.app G' := by
      simp only [Category.assoc]
      rw [hu]

private theorem homEquiv_restriction_injective {Lb : A ⥤ X} {Rk : X ⥤ B}
    {Lk : B ⥤ X} {Rs : A ⥤ B} (ak : Lk ⊣ Rk) [IsIso ak.unit]
    (H : ∀ F G, (Lb.obj F ⟶ Lk.obj G) ≃ (Rs.obj F ⟶ G))
    (c : ∀ F, Rs.obj F ⟶ Rk.obj (Lb.obj F))
    (hf : ∀ F G f, H F G f ≫ ak.unit.app G = c F ≫ Rk.map f)
    (F : A) (G : B) (a b : Lb.obj F ⟶ Lk.obj G) (hab : Rk.map a = Rk.map b) :
    a = b := by
  apply (H F G).injective
  apply (cancel_mono (ak.unit.app G)).1
  rw [hf F G a, hf F G b, hab]


end

attribute [local irreducible] pullComp openAdj cartesianPull
attribute [local irreducible] Functor.leftAdjoint StrictTower.modulePullback

private theorem ambientBeta (m : Option ℕ) {V W Z : Scheme.{u}}
    (p : V ⟶ Z) (i : W ⟶ Z) [IsOpenImmersion i] [IsProper p] :
    ∃ β : extension l E m i ⋙ pull l E m p ≅
        pull l E m (pullback.snd p i) ⋙ extension l E m (pullback.fst p i),
      ∀ M, (openAdj l E m (pullback.fst p i)).unit.app
            ((pull l E m (pullback.snd p i)).obj M) ≫
          (pull l E m (pullback.fst p i)).map (β.inv.app M) =
        (pull l E m (pullback.snd p i)).map ((openAdj l E m i).unit.app M) ≫
          (cartesianPull l E m p i).hom.app ((extension l E m i).obj M) := by
  cases m with
    | some n =>
      let B := scalarRings l E n
      refine ⟨StrictTower.openBetaModule B (pullback.snd p i) (pullback.fst p i) i p
        pullback.condition.symm (IsPullback.of_hasPullback p i).flip, ?_⟩
      intro M
      have hh := (StrictTower.openBetaModule_normalized B
        (pullback.snd p i) (pullback.fst p i) i p
        pullback.condition.symm (IsPullback.of_hasPullback p i).flip).2 M
      rw [Adjunction.homEquiv_unit] at hh
      simpa only [cartesianPull, openAdj, Iso.symm_hom] using hh
    | none =>
      let R := scalarRings l E
      let φ := scalarTransitions l E
      let β := VaryingRing.moduleBeta R φ (pullback.snd p i) (pullback.fst p i) i p
        pullback.condition.symm (IsPullback.of_hasPullback p i).flip
      refine ⟨β, ?_⟩
      intro M
      have hh := ((VaryingRing.moduleJAdj R φ (pullback.fst p i )).homEquiv _ _).apply_symm_apply
        ((VaryingRing.pull R φ (pullback.snd p i)).map
            ((VaryingRing.moduleJAdj R φ i).unit.app M) ≫
          (VaryingRing.moduleSquareG R φ (pullback.snd p i) (pullback.fst p i) i p
            pullback.condition.symm).inv.app ((VaryingRing.extension R φ i).obj M))
      change (VaryingRing.moduleJAdj R φ (pullback.fst p i)).homEquiv _ _
        (β.inv.app M) = _ at hh
      rw [Adjunction.homEquiv_unit] at hh
      simpa only [cartesianPull, openAdj, Iso.symm_hom] using hh

private theorem restrictionSource_eq (m : Option ℕ) {U V W Z : Scheme.{u}}
    (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i)
    (F : Modules l E m (pullback p i)) :
    restrictionSource l E m k r p i h F =
      (pull l E m (StrictTower.squareLift k r p i h)).map
          ((openAdj l E m (pullback.fst p i)).unit.app F) ≫
        (restrictionPull l E m k r p i h).inv.app
          ((extension l E m (pullback.fst p i)).obj F) := by
  rfl

private def ambientHom (m : Option ℕ) {U V W Z : Scheme.{u}}
    (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i)
    (C : (pullback p i).Opens)
    (hc : Set.range C.ι = (Set.range (StrictTower.squareLift k r p i h))ᶜ)
    (F : Modules l E m (pullback p i)) (G : Modules l E m U) :
    ((extension l E m (pullback.fst p i)).obj F ⟶ (extension l E m k).obj G) ≃
      ((pull l E m (StrictTower.squareLift k r p i h)).obj F ⟶ G) := by
  have := openUnit_isIso l E m (StrictTower.squareLift k r p i h)
  have := openUnit_isIso l E m (pullback.fst p i)
  have hz (N : Modules l E m U) : IsZero ((pull l E m C.ι).obj
      ((extension l E m (StrictTower.squareLift k r p i h)).obj N)) := by
    apply extension_disjoint_zero l E m _ _ _ N
    rw [hc]
    exact disjoint_compl_right
  exact squareHom (openAdj l E m (StrictTower.squareLift k r p i h))
    (pull l E m C.ι) (ambientEquivalence l E m _ _ hc)
    (ambientEquivalence_functor l E m _ _ hc) hz
    (openAdj l E m (pullback.fst p i)) (openAdj l E m k)
    (restrictionPull l E m k r p i h) F G

private theorem ambientHom_formula (m : Option ℕ) {U V W Z : Scheme.{u}}
    (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i)
    (C : (pullback p i).Opens)
    (hc : Set.range C.ι = (Set.range (StrictTower.squareLift k r p i h))ᶜ)
    (F : Modules l E m (pullback p i)) (G : Modules l E m U)
    (a : (extension l E m (pullback.fst p i)).obj F ⟶ (extension l E m k).obj G) :
    ambientHom l E m k r p i h C hc F G a ≫ (openAdj l E m k).unit.app G =
      restrictionSource l E m k r p i h F ≫ (pull l E m k).map a := by
  have := openUnit_isIso l E m (StrictTower.squareLift k r p i h)
  have := openUnit_isIso l E m (pullback.fst p i)
  rw [restrictionSource_eq, Category.assoc]
  unfold ambientHom
  apply squareHom_formula

private theorem restrictionSource_naturality (m : Option ℕ) {U V W Z : Scheme.{u}}
    (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i)
    {F F' : Modules l E m (pullback p i)} (a : F' ⟶ F) :
    restrictionSource l E m k r p i h F' ≫
        (pull l E m k).map ((extension l E m (pullback.fst p i)).map a) =
      (pull l E m (StrictTower.squareLift k r p i h)).map a ≫
        restrictionSource l E m k r p i h F := by
  rw [restrictionSource_eq, restrictionSource_eq]
  rw [Category.assoc, ← (restrictionPull l E m k r p i h).inv.naturality]
  dsimp only [Functor.comp_map]
  have hn := (openAdj l E m (pullback.fst p i)).unit.naturality a
  dsimp only [Functor.id_map, Functor.comp_map] at hn
  rw [← Category.assoc, ← Functor.map_comp, ← hn, Functor.map_comp, Category.assoc]

attribute [local irreducible] ambientHom

private theorem ambientAssertion (m : Option ℕ) {U V W Z : Scheme.{u}}
    (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :
    Assertion l E m k r p i h := by
  let s := StrictTower.squareLift k r p i h
  let C : (pullback p i).Opens :=
    ⟨(Set.range s)ᶜ, s.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  have hc : Set.range C.ι = (Set.range s)ᶜ := Scheme.Opens.range_ι C
  let e := ambientEquivalence l E m s C.ι hc
  obtain ⟨he₁, he₂, he₃, he₄⟩ := equivalence_finite e
  refine ⟨C, hc, e, ambientEquivalence_functor l E m s C.ι hc,
    he₁, he₂, he₃, he₄, ?_, ?_, ?_,
    openUnit_isIso l E m _, openUnit_isIso l E m _, ?_, ?_, ?_⟩
  · refine ⟨sectionIso l E m s C.ι hc, sectionIso_scalar l E m s C.ι hc, ?_, ?_, ?_⟩
    · intro F n T T' a x
      cases m <;> rfl
    · intro F H a n T x
      cases m <;> rfl
    · exact sectionIso_transition l E m s C.ι hc
  · refine ⟨openUnit_isIso l E m s, ?_⟩
    intro G
    apply extension_disjoint_zero l E m s C.ι _ G
    rw [hc]
    exact disjoint_compl_right
  · cases m with
    | some n =>
      refine ⟨StrictTower.clopenModulePi (scalarRings l E n) s, ?_⟩
      intro F
      have hh := StrictTower.clopenModule_section_projector (scalarRings l E n) s C.ι hc
      simpa only [openAdj] using And.intro (hh.2.1 F) ((hh.2.2.1 F).2)
    | none =>
      refine ⟨VaryingRing.modulePi (scalarRings l E) (scalarTransitions l E) s, ?_⟩
      simpa only [openAdj] using
        VaryingRing.modulePi_components (scalarRings l E) (scalarTransitions l E) s C.ι hc
  · refine ⟨ambientHom l E m k r p i h C hc,
      ambientHom_formula l E m k r p i h C hc, ?_⟩
    intro F F' G G' a b f
    have := openUnit_isIso l E m k
    exact homEquiv_naturality (openAdj l E m k)
      (ambientHom l E m k r p i h C hc) (restrictionSource l E m k r p i h)
      (ambientHom_formula l E m k r p i h C hc)
      (fun a ↦ restrictionSource_naturality l E m k r p i h a) a b f
  · have := openUnit_isIso l E m k
    exact homEquiv_restriction_injective (openAdj l E m k)
      (ambientHom l E m k r p i h C hc) (restrictionSource l E m k r p i h)
      (ambientHom_formula l E m k r p i h C hc)
  · exact ambientBeta l E m p i

/-- Clopen geometry, exact restriction equivalence, its actual product section formula,
identity/zero projector, natural restriction Hom bijection and normalized ordinary beta.
Source: Stacks 0F7B (open-square geometry), 04TS (disjoint-open gluing), 03DI and
0F6Z (open extension and its unit)
(blueprint: lem-sf-ambient-clopen-restriction-uniqueness).

Proof:
1. Base change makes b open and q proper, hence separated. Identify V_W with p⁻¹(W)
   inside V; s is the inclusion of k(U). Proper-to-separated (01W6(2)) applied over W
   makes s proper, without assuming the structure maps separated.
2. A proper monomorphism is closed (04XV). Thus s is clopen, with complementary open C.
   Composition of finite-type maps (01T3) makes V_W finite type over the base field.
3. Apply lem-pur-clopen-ringed-module-gluing (04TS) to s(U),C and the coefficient ring
   sheaf. The inverse has the displayed product sections, and kernels and cokernels
   are detected on the pieces; both restriction and gluing are exact.
4. For systems perform this on every level: transition (x_U,x_C) maps to
   (τ_U x_U,τ_C x_C). Scalar restriction changes only the action, so this is semilinear.
   Componentwise maps, restriction units and projection counits commute with transitions
   by lem-coef-semilinear-derived-sections. Empty pieces and zero transitions are allowed.
5. In the product category G maps to (G,0). It is left adjoint to first projection.
   The specified open adjunction and unit-preserving uniqueness of left adjoints identify
   it with s_!. The component projection gives π_s=(1,0), naturally and compatibly in n.
6. Weakly-etale localization identifies each open site with a slice; extension restricted
   to that slice is the original presheaf. Module sheafification restriction preserves
   its unit (03DI,0F6Z,04B8), so b_! is fully faithful. Composite adjunction and the
   conjugate-iso unit equation identify b_!s_! with k_!, preserving the open unit.
7. Fully faithful b_!, then the product equivalence, give
   Hom_V(b_!F,k_!G)=Hom_V_W(F,s_!G)=Hom_U(s^*F,G).
   The inverse extends s_!h after π_s, then composes b_!s_!≅k_!. Restriction of this
   inverse is h; the other composite is identity by full faithfulness and product maps.
   All formulas commute with maps in F,G, proving naturality and restriction uniqueness.
8. Open-tensor normalization on the cartesian b,q,p,i square gives β. Its inverse is
   the b-open adjunct of q^* of the i-open unit under the specified pullback compositor.
   Exactness identifies degree-zero localization with this ordinary comparison.
   For systems this takes place on the entire diagram site before evaluation.
   Substitute F=q^*M into step 7; no derived-morphism faithfulness is asserted. -/
theorem ambientClopenRestrictionUniqueness
    (K : WeilConjectures.FiniteFieldDatum.{u}) (_hl : l ≠ K.p)
    (U V W Z : Over (Spec (.of K.k)))
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom]
    [LocallyOfFiniteType W.hom] [QuasiCompact W.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k.left] [IsOpenImmersion i.left]
    [QuasiCompact k.left] [QuasiCompact i.left] [IsProper r.left] [IsProper p.left]
    (h : k.left ≫ p.left = r.left ≫ i.left) :
    IsOpenImmersion (pullback.fst p.left i.left) ∧
    IsSeparated (pullback.snd p.left i.left) ∧
    IsOpenImmersion (StrictTower.squareLift k.left r.left p.left i.left h) ∧
    IsProper (StrictTower.squareLift k.left r.left p.left i.left h) ∧
    IsClosedImmersion (StrictTower.squareLift k.left r.left p.left i.left h) ∧
    LocallyOfFiniteType (pullback.snd p.left i.left ≫ W.hom) ∧
    QuasiCompact (pullback.snd p.left i.left ≫ W.hom) ∧
    ∀ m : Option ℕ, Assertion l E m k.left r.left p.left i.left h := by
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, ?_⟩
  intro m
  exact ambientAssertion l E m k.left r.left p.left i.left h

end AlgebraicGeometry.ProEtale.AmbientClopenRestriction
