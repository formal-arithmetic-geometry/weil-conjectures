/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C8
-/
module

public import Sheaf.AlgebraicGeometry.VaryingRingProperOpenArrows
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Ordinary coefficient evaluation of the clopen comparison

Source: Zheng, Construction 4.1 and Lemma 4.10; Stacks Project, Tags 09AE and 0F7B.
The evaluation used here first takes an ordinary system component, then makes a
constant tower concentrated in degree zero. Its faithfulness concerns ordinary
system morphisms only (blueprint: lem-sp-varying-ring-ordinary-clopen-evaluation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.VaryingRing
variable (R : ℕ → CommRingCat.{u + 1}) (φ : ∀ n : ℕ, R (n + 1) ⟶ R n)
attribute [local instance 2000] WeilConjectures.SemilinearSections.sequenceSmall
  StrictTower.towers_hasDerivedCategory Scheme.proEtaleRingModules_hasDerivedCategory

/-- The realization functor is fixed uniquely by its explicit construction.
Source: Zheng 4.1 (blueprint: lem-sp-varying-ring-ordinary-clopen-evaluation).
Proof: the displayed functor is a witness; the defining equality gives uniqueness. -/
theorem ordinaryRealization_existsUnique (n : ℕ) (X : Scheme.{u}) :
    ∃! E : Modules R φ X ⥤ StrictTower.Derived (R n) X,
      E = eval R φ X n ⋙ Functor.const ℕᵒᵖ ⋙
        DerivedCategory.singleFunctor (StrictTower.Towers (R n) X) 0 := by
  exact ⟨_, rfl, fun _ h ↦ h⟩

/-- An actual ordinary component, viewed as a degree-zero constant strict tower.
Source: Zheng 4.1 (blueprint: lem-sp-varying-ring-ordinary-clopen-evaluation). -/
def ordinaryRealization (n : ℕ) (X : Scheme.{u}) :
    Modules R φ X ⥤ StrictTower.Derived (R n) X :=
  (ordinaryRealization_existsUnique R φ n X).choose

/-- The realization retains exactly the explicit component/single construction.
Source: Zheng 4.1 (blueprint: lem-sp-varying-ring-ordinary-clopen-evaluation).
Proof: this is the equality in its proved unique specification. -/
theorem ordinaryRealization_eq (n : ℕ) (X : Scheme.{u}) :
    ordinaryRealization R φ n X = eval R φ X n ⋙ Functor.const ℕᵒᵖ ⋙
      DerivedCategory.singleFunctor (StrictTower.Towers (R n) X) 0 :=
  (ordinaryRealization_existsUnique R φ n X).choose_spec.1

attribute [local irreducible] ordinaryRealization moduleAlpha moduleGComp moduleJComp
  StrictTower.alpha StrictTower.G StrictTower.J StrictTower.gComp StrictTower.jComp
  Functor.leftAdjoint

/-- A square comparison records its four functors before its component equation.
Source: functoriality of the clopen comparison, Zheng 4.1
(blueprint: lem-sp-varying-ring-ordinary-clopen-evaluation). -/
structure OrdinarySquareComparison
    {A B C D A' B' C' D' : Type*}
    [Category A] [Category B] [Category C] [Category D]
    [Category A'] [Category B'] [Category C'] [Category D']
    {EA : A ⥤ A'} {EB : B ⥤ B'} {EC : C ⥤ C'} {ED : D ⥤ D'}
    {R₀ : C ⥤ A} {P₀ : D ⥤ B} {K : A ⥤ B} {I : C ⥤ D}
    {r : C' ⥤ A'} {p : D' ⥤ B'} {k : A' ⥤ B'} {i : C' ⥤ D'}
    (eR : R₀ ⋙ EA ≅ EC ⋙ r) (eP : P₀ ⋙ EB ≅ ED ⋙ p)
    (eK : K ⋙ EB ≅ EA ⋙ k) (eI : I ⋙ ED ≅ EC ⋙ i)
    (a : I ⋙ P₀ ⟶ R₀ ⋙ K) (a' : i ⋙ p ⟶ r ⋙ k) : Prop where
  equation (N : C) : EB.map (a.app N) ≫ eK.hom.app (R₀.obj N) ≫
      k.map (eR.hom.app N) =
    eP.hom.app (I.obj N) ≫ p.map (eI.hom.app N) ≫ a'.app (EC.obj N)

/-- The inverse-image comparisons for ordinary realization.
Source: Zheng 4.1 (blueprint: lem-sp-varying-ring-ordinary-clopen-evaluation). -/
abbrev OrdinaryPullComparison (n : ℕ) :=
  ∀ (X Y : Scheme.{u}) (f : X ⟶ Y),
    pull R φ f ⋙ ordinaryRealization R φ n X ≅
      ordinaryRealization R φ n Y ⋙ StrictTower.G (R n) f

/-- The open-extension comparisons for ordinary realization.
Source: Zheng 4.1 (blueprint: lem-sp-varying-ring-ordinary-clopen-evaluation). -/
abbrev OrdinaryOpenComparison (n : ℕ) :=
  ∀ (U X : Scheme.{u}) (j : U ⟶ X) [IsOpenImmersion j],
    extension R φ j ⋙ ordinaryRealization R φ n X ≅
      ordinaryRealization R φ n U ⋙ StrictTower.J (R n) j

/-- Pullback compositor normalization.
Source: Stacks 09AE (blueprint: lem-sp-varying-ring-ordinary-clopen-evaluation). -/
def OrdinaryPullComposition (n : ℕ) (gIso : OrdinaryPullComparison R φ n) : Prop :=
  ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (N : Modules R φ Z),
    (ordinaryRealization R φ n X).map ((moduleGComp R φ f g).hom.app N) ≫
        (gIso _ _ f).hom.app ((pull R φ g).obj N) ≫
        (StrictTower.G (R n) f).map ((gIso _ _ g).hom.app N) =
      (gIso _ _ (f ≫ g)).hom.app N ≫
        (StrictTower.gComp (R n) f g).hom.app ((ordinaryRealization R φ n Z).obj N)

/-- Extension compositor normalization.
Source: Stacks 09AE (blueprint: lem-sp-varying-ring-ordinary-clopen-evaluation). -/
def OrdinaryOpenComposition (n : ℕ) (jIso : OrdinaryOpenComparison R φ n) : Prop :=
  ∀ {U V X : Scheme.{u}} (i : U ⟶ V) (j : V ⟶ X)
    [IsOpenImmersion i] [IsOpenImmersion j] (N : Modules R φ U),
    (ordinaryRealization R φ n X).map ((moduleJComp R φ i j).hom.app N) ≫
        (jIso _ _ (i ≫ j)).hom.app N =
      (jIso _ _ j).hom.app ((extension R φ i).obj N) ≫
        (StrictTower.J (R n) j).map ((jIso _ _ i).hom.app N) ≫
        (StrictTower.jComp (R n) i j).hom.app ((ordinaryRealization R φ n U).obj N)

/-- Preservation of the single-square clopen arrow.
Source: Stacks 0F7B (blueprint: lem-sp-varying-ring-ordinary-clopen-evaluation). -/
def OrdinaryClopenComparison (n : ℕ) (gIso : OrdinaryPullComparison R φ n)
    (jIso : OrdinaryOpenComparison R φ n) : Prop :=
  ∀ {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i),
    OrdinarySquareComparison
      (EA := ordinaryRealization R φ n V) (EB := ordinaryRealization R φ n W)
      (EC := ordinaryRealization R φ n S) (ED := ordinaryRealization R φ n T)
      (R₀ := pull R φ r) (P₀ := pull R φ p)
      (K := extension R φ k) (I := extension R φ i)
      (r := StrictTower.G (R n) r) (p := StrictTower.G (R n) p)
      (k := StrictTower.J (R n) k) (i := StrictTower.J (R n) i)
      (gIso _ _ r) (gIso _ _ p) (jIso _ _ k) (jIso _ _ i)
      (moduleAlpha R φ k r p i h) (StrictTower.alpha (R n) k r p i h)


section ConstantSingle

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory (ℕᵒᵖ ⥤ C)] [HasDerivedCategory (ℕᵒᵖ ⥤ D)]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ C D).obj F)]
  [PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ C D).obj F)]

/-- Constant towers and the degree-zero embedding commute with exact functors.
Source: Zheng 4.1 (blueprint: lem-sp-varying-ring-ordinary-clopen-evaluation). -/
def ordinaryConstantSingleComparison :
    F ⋙ (Functor.const ℕᵒᵖ ⋙ DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ D) 0) ≅
      (Functor.const ℕᵒᵖ ⋙ DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ C) 0) ⋙
        ((Functor.whiskeringRight ℕᵒᵖ C D).obj F).mapDerivedCategory :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Functor.compConstIso ℕᵒᵖ F) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (((Functor.whiskeringRight ℕᵒᵖ C D).obj F).mapDerivedCategorySingleFunctor 0).symm ≪≫
    (Functor.associator _ _ _).symm

end ConstantSingle

/-- The actual inverse-image comparison, obtained from moduleEvalG and degree zero.
Source: Zheng 4.1 (blueprint: lem-sp-varying-ring-ordinary-clopen-evaluation). -/
def ordinaryPullComparison (n : ℕ) : OrdinaryPullComparison R φ n := by
  intro X Y f
  unfold StrictTower.G
  let C := Functor.const ℕᵒᵖ ⋙ DerivedCategory.singleFunctor (StrictTower.Towers (R n) X) 0
  let D := Functor.const ℕᵒᵖ ⋙ DerivedCategory.singleFunctor (StrictTower.Towers (R n) Y) 0
  let eX := eqToIso (ordinaryRealization_eq R φ n X)
  let eY := eqToIso (ordinaryRealization_eq R φ n Y)
  exact Functor.isoWhiskerLeft _ eX ≪≫ (Functor.associator _ _ C).symm ≪≫
    Functor.isoWhiskerRight (moduleEvalG R φ f n) C ≪≫
    Functor.associator _ _ C ≪≫
    Functor.isoWhiskerLeft _
      (ordinaryConstantSingleComparison (StrictTower.modulePullback (R n) f)) ≪≫
    (Functor.associator _ D _).symm ≪≫ Functor.isoWhiskerRight eY.symm _

section RecoverSingle

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]
  (F G : C ⥤ D) [F.Additive] [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]

/-- Recover an ordinary functor comparison through the fully faithful degree-zero embedding.
Source: Stacks 06YY (blueprint: lem-sp-varying-ring-ordinary-clopen-evaluation). -/
def ordinaryRecoverSingleIso (e : F.mapDerivedCategory ≅ G.mapDerivedCategory) : F ≅ G :=
  let h := (Functor.FullyFaithful.ofFullyFaithful
    (DerivedCategory.singleFunctor D 0)).whiskeringRight C
  h.preimageIso ((F.mapDerivedCategorySingleFunctor 0).symm ≪≫
      Functor.isoWhiskerLeft _ e ≪≫ G.mapDerivedCategorySingleFunctor 0)

end RecoverSingle

/-- The ordinary open comparison recovered from the specified derived open mate.
Source: Stacks 03DI (blueprint: lem-sp-varying-ring-ordinary-clopen-evaluation). -/
def ordinaryOpenEvaluation (n : ℕ) {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] :
    extension R φ j ⋙ eval R φ X n ≅ eval R φ U n ⋙ StrictTower.moduleJ (R n) j :=
  ordinaryRecoverSingleIso _ _
    (Functor.mapDerivedCategoryCompIso (extension R φ j) (eval R φ X n) ≪≫
      evalJ R φ j n ≪≫
      (Functor.mapDerivedCategoryCompIso (eval R φ U n) (StrictTower.moduleJ (R n) j)).symm)

/-- The actual open comparison, obtained from ordinary evaluation and degree zero.
Source: Stacks 03DI (blueprint: lem-sp-varying-ring-ordinary-clopen-evaluation). -/
def ordinaryOpenComparison (n : ℕ) : OrdinaryOpenComparison R φ n := by
  intro U X j _
  unfold StrictTower.J
  let C := Functor.const ℕᵒᵖ ⋙ DerivedCategory.singleFunctor (StrictTower.Towers (R n) X) 0
  let D := Functor.const ℕᵒᵖ ⋙ DerivedCategory.singleFunctor (StrictTower.Towers (R n) U) 0
  let eX := eqToIso (ordinaryRealization_eq R φ n X)
  let eU := eqToIso (ordinaryRealization_eq R φ n U)
  exact Functor.isoWhiskerLeft _ eX ≪≫ (Functor.associator _ _ C).symm ≪≫
    Functor.isoWhiskerRight (ordinaryOpenEvaluation R φ n j) C ≪≫
    Functor.associator _ _ C ≪≫
    Functor.isoWhiskerLeft _ (ordinaryConstantSingleComparison (StrictTower.moduleJ (R n) j)) ≪≫
    (Functor.associator _ D _).symm ≪≫ Functor.isoWhiskerRight eU.symm _

private theorem mate_of_unit {C D E F : Type*}
    [Category C] [Category D] [Category E] [Category F]
    {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
    {G : C ⥤ E} {H : D ⥤ F}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂)
    (α : TwoSquare G L₁ L₂ H) (β : TwoSquare R₁ H G R₂)
    (h : ∀ N : C, G.map (a₁.unit.app N) ≫ β.app (L₁.obj N) =
      a₂.unit.app (G.obj N) ≫ R₂.map (α.app N)) :
    mateEquiv a₁ a₂ α = β := by
  rw [← Equiv.eq_symm_apply]
  apply TwoSquare.ext
  intro N
  apply (a₂.homEquiv _ _).injective
  simpa only [Adjunction.homEquiv_unit, Functor.id_obj, Functor.comp_obj] using
    (h N).symm.trans (unit_mateEquiv_symm a₁ a₂ β N)

private abbrev ordinaryLevelAdj (n : ℕ) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    StrictTower.modulePullback (R n) f ⊣ StrictTower.moduleDirectImage (R n) f :=
  Scheme.proEtaleRingModuleAdjunction f (coefficients R Y n) (coefficients R X n)
    (StrictTower.constantRingIso (R n) f)

private theorem ordinaryLevelAdj_eq (n : ℕ) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ordinaryLevelAdj R n f = Scheme.proEtaleRingModuleAdjunction f
      (StrictTower.coefficients (R n) Y) (StrictTower.coefficients (R n) X)
      (StrictTower.constantRingIso (R n) f) := by
  dsimp only [ordinaryLevelAdj, coefficients, StrictTower.coefficients]
  generalize R n = A
  cases A
  rfl

private theorem ordinaryModuleEvalG_mate (n : ℕ) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    mateEquiv (moduleAdj R φ f) (ordinaryLevelAdj R n f)
      (TwoSquare.mk _ _ _ _ (moduleEvalG R φ f n).inv) =
      TwoSquare.mk _ _ _ _ (moduleEvalP R φ f n).hom := by
  apply mate_of_unit
  intro N
  apply (cancel_mono ((StrictTower.moduleDirectImage (R n) f).map
    ((moduleEvalG R φ f n).hom.app N))).1
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
  exact (moduleEvalG_existsUnique R φ f n).choose_spec.1 N

private theorem ordinaryModuleEvalP_apply (n : ℕ) {X Y : Scheme.{u}}
    (f : X ⟶ Y) (N : Modules R φ X) (U : Y.ProEt)
    (x : ((push R φ f).obj N).val.obj (op (n, U))) :
    ((moduleEvalP R φ f n).hom.app N).val.app (op U) x = x := by
  exact (moduleEvalP_existsUnique R φ f n).choose_spec.1 N U x

private theorem ordinaryLevelPush_map_apply (n : ℕ) {X Y : Scheme.{u}}
    (f : X ⟶ Y) {M N : StrictTower.Modules (R n) X} (a : M ⟶ N) (U : Y.ProEt)
    (x : ((StrictTower.moduleDirectImage (R n) f).obj M).val.obj (op U)) :
    (((StrictTower.moduleDirectImage (R n) f).map a).val.app (op U)) x =
      a.val.app (op ((Scheme.proEtaleBaseChange f).obj U)) x := by
  rfl

private theorem ordinaryEval_map_apply (n : ℕ) (X : Scheme.{u})
    {M N : Modules R φ X} (a : M ⟶ N) (U : X.ProEt)
    (x : M.val.obj (op (n, U))) :
    (((eval R φ X n).map a).val.app (op U)) x = a.val.app (op (n, U)) x := by
  rfl

private theorem ordinaryEval_obj_map_apply (n : ℕ) (X : Scheme.{u})
    (M : Modules R φ X) {U V : X.ProEt} (a : U ⟶ V)
    (x : M.val.obj (op (n, V))) :
    ((eval R φ X n).obj M).val.map a.op x =
      M.val.map (Prod.mkHom (𝟙 n) a).op x := by
  rfl

private theorem ordinaryLevelComp_apply (n : ℕ) {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (M : StrictTower.Modules (R n) X) (U : Z.ProEt)
    (x : ((StrictTower.moduleDirectImage (R n) f ⋙
      StrictTower.moduleDirectImage (R n) g).obj M).val.obj (op U)) :
    ((StrictTower.moduleRComp (R n) f g).hom.app M).val.app (op U) x =
      M.val.map ((MorphismProperty.Over.pullbackComp f g).hom.app U).op x := by
  exact (StrictTower.moduleRComp_existsUnique (R n) f g).choose_spec.1 M U x

private theorem ordinarySystemComp_apply {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (M : Modules R φ X) (n : ℕ) (U : Z.ProEt)
    (x : ((push R φ f ⋙ push R φ g).obj M).val.obj (op (n, U))) :
    ((modulePComp R φ f g).hom.app M).val.app (op (n, U)) x =
      M.val.map (Prod.mkHom (𝟙 n)
        ((MorphismProperty.Over.pullbackComp f g).hom.app U)).op x := by
  exact (modulePComp_existsUnique R φ f g).choose_spec.1 M n U x

attribute [local irreducible] moduleEvalP modulePComp StrictTower.moduleRComp constantSheaf
  WeilConjectures.SemilinearSections.rings

private theorem comparison_of_inverse {C : Type*} [Category C]
    {A B D E : C} (u : B ≅ E) (v : A ≅ D) (a : A ⟶ B) (b : D ⟶ E)
    (h : b ≫ u.inv = v.inv ≫ a) : a ≫ u.hom = v.hom ≫ b := by
  apply (cancel_epi v.inv).1
  rw [← Category.assoc, ← h]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
    Iso.inv_hom_id_assoc]

private lemma mateSquare
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    {L₃ L₄ : E ⥤ F} {R₃ R₄ : F ⥤ E}
    {G : C ⥤ E} {H : D ⥤ F}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a₃ : L₃ ⊣ R₃) (a₄ : L₄ ⊣ R₄)
    (q : TwoSquare G L₁ L₃ H) (r : TwoSquare G L₂ L₄ H)
    (s : L₄ ⟶ L₃) (t : L₂ ⟶ L₁)
    (h : (mateEquiv a₁ a₃ q).whiskerBottom (conjugateEquiv a₃ a₄ s) =
      (mateEquiv a₂ a₄ r).whiskerTop (conjugateEquiv a₁ a₂ t)) :
    q.whiskerRight s = r.whiskerLeft t := by
  apply (mateEquiv a₁ a₄).injective
  rw [mateEquiv_conjugateEquiv_vcomp, conjugateEquiv_mateEquiv_vcomp]
  exact h

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Ordinary component evaluation preserves the specified inverse-image compositor.
Source: Zheng, Construction 4.1 and Lemma 4.10
(blueprint: lem-sp-varying-ring-ordinary-clopen-evaluation).
Proof: take adjunction mates. The unit normalization identifies the evaluation
mate with the sectionwise identity comparison moduleEvalP. Both pushforward
compositors restrict sections along the same pullback-pasting map, so their
comparison holds on every section. Injectivity of the mate equivalence gives
its inverse-image counterpart; cancellation of the comparison isomorphisms
then gives the displayed orientation. -/
theorem ordinaryModuleEvalG_comp (n : ℕ) {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (N : Modules R φ Z) :
    (eval R φ X n).map ((moduleGComp R φ f g).hom.app N) ≫
        (moduleEvalG R φ f n).hom.app ((pull R φ g).obj N) ≫
        (StrictTower.modulePullback (R n) f).map ((moduleEvalG R φ g n).hom.app N) =
      (moduleEvalG R φ (f ≫ g) n).hom.app N ≫
        (StrictTower.moduleGComp (R n) f g).hom.app ((eval R φ Z n).obj N) := by
  let q := (TwoSquare.mk _ _ _ _ (moduleEvalG R φ g n).inv).vComp
    (TwoSquare.mk _ _ _ _ (moduleEvalG R φ f n).inv)
  have hc : q.whiskerRight (StrictTower.moduleGComp (R n) f g).hom =
      (TwoSquare.mk _ _ _ _ (moduleEvalG R φ (f ≫ g) n).inv).whiskerLeft
        (moduleGComp R φ f g).hom := by
    apply mateSquare ((moduleAdj R φ g).comp (moduleAdj R φ f))
      (moduleAdj R φ (f ≫ g))
      ((ordinaryLevelAdj R n g).comp (ordinaryLevelAdj R n f))
      (ordinaryLevelAdj R n (f ≫ g))
    dsimp only [q]
    rw [mateEquiv_hcomp, ordinaryModuleEvalG_mate, ordinaryModuleEvalG_mate,
      ordinaryModuleEvalG_mate]
    have hG : conjugateEquiv ((moduleAdj R φ g).comp (moduleAdj R φ f))
        (moduleAdj R φ (f ≫ g)) (moduleGComp R φ f g).hom =
        (modulePComp R φ f g).hom := by
      simpa only [moduleGComp, Iso.symm_hom] using
        (Adjunction.conjugateEquiv_leftAdjointCompIso_inv
          (moduleAdj R φ g) (moduleAdj R φ f) (moduleAdj R φ (f ≫ g))
          (modulePComp R φ f g))
    have hG' : conjugateEquiv ((ordinaryLevelAdj R n g).comp (ordinaryLevelAdj R n f))
        (ordinaryLevelAdj R n (f ≫ g)) (StrictTower.moduleGComp (R n) f g).hom =
        (StrictTower.moduleRComp (R n) f g).hom := by
      rw [ordinaryLevelAdj_eq, ordinaryLevelAdj_eq, ordinaryLevelAdj_eq]
      exact Adjunction.conjugateEquiv_leftAdjointCompIso_inv _ _ _ _
    rw [hG, hG']
    apply TwoSquare.ext
    intro M
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    ext x
    simp only [TwoSquare.whiskerBottom, TwoSquare.whiskerTop, TwoSquare.hComp,
      TwoSquare.mk, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
      Category.comp_id, SheafOfModules.comp_val, PresheafOfModules.comp_app,
      ModuleCat.comp_apply, TwoSquare.natTrans]
    obtain ⟨U⟩ := U
    let y := ((moduleEvalP R φ g n).hom.app ((push R φ f).obj M)).val.app (op U) x
    let a := ((StrictTower.moduleRComp (R n) f g).hom.app
      ((eval R φ X n).obj M)).val.app (op U)
    let b := ((moduleEvalP R φ (f ≫ g) n).hom.app M).val.app (op U)
    let c := ((eval R φ Z n).map ((modulePComp R φ f g).hom.app M)).val.app (op U)
    have hmap := ordinaryLevelPush_map_apply R n g
      ((moduleEvalP R φ f n).hom.app M) U y
    have hlevel := ordinaryLevelComp_apply R n f g ((eval R φ X n).obj M) U x
    have hsystem := ordinarySystemComp_apply R φ f g M n U x
    have hf := ordinaryModuleEvalP_apply R φ n f M
      ((Scheme.proEtaleBaseChange g).obj U) y
    have hg := ordinaryModuleEvalP_apply R φ n g ((push R φ f).obj M) U x
    have he := ordinaryEval_map_apply R φ n Z
      ((modulePComp R φ f g).hom.app M) U x
    have hfg := ordinaryModuleEvalP_apply R φ n (f ≫ g) M U (c x)
    let v : (Scheme.proEtaleBaseChange (f ≫ g)).obj U ⟶
        (Scheme.proEtaleBaseChange f).obj ((Scheme.proEtaleBaseChange g).obj U) := by
      set_option backward.isDefEq.respectTransparency false in
      set_option backward.isDefEq.respectTransparency.types false in
      exact (MorphismProperty.Over.pullbackComp.{u, u + 1}
        (T := Scheme.{u}) (P := @WeaklyEtale.{u}) (Q := ⊤) f g).hom.app U
    have hv := ordinaryEval_obj_map_apply R φ n X M v x
    exact (congrArg (fun z ↦ a z) hmap).trans
      ((congrArg (fun z ↦ a z) hf).trans
        ((congrArg (fun z ↦ a z) hg).trans
          (hlevel.trans (hv.trans (hsystem.symm.trans (he.symm.trans hfg.symm))))))
  have hm := congrArg (fun z ↦ z.app N) hc
  simp only [q, TwoSquare.whiskerRight, TwoSquare.whiskerLeft, TwoSquare.vComp,
    TwoSquare.mk, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Category.comp_id, TwoSquare.natTrans] at hm
  let u := (moduleEvalG R φ f n).app ((pull R φ g).obj N) ≪≫
    (StrictTower.modulePullback (R n) f).mapIso ((moduleEvalG R φ g n).app N)
  let v := (moduleEvalG R φ (f ≫ g) n).app N
  exact comparison_of_inverse u v
    ((eval R φ X n).map ((moduleGComp R φ f g).hom.app N))
    ((StrictTower.moduleGComp (R n) f g).hom.app ((eval R φ Z n).obj N)) hm

/-- Ordinary evaluation preserves the specified inverse-image and open-extension
comparisons and the single-square clopen arrow.
Source: Zheng, Construction 4.1 and Lemma 4.10; Stacks 09AE and 0F7B
(blueprint: lem-sp-varying-ring-ordinary-clopen-evaluation).
Proof: evaluate a system at n, embed the resulting module as a constant tower,
and apply the degree-zero embedding. The inverse-image comparison is moduleEvalG,
whiskered by the constant and single functors and their exact-functor comparisons.
The open comparison is its inverse open-adjunction mate. Evaluation and constant
embedding preserve that mate's unit normalization; exact localization preserves
the same unit, so this mate is invertible. For pullback composition take proper
adjunction mates: moduleEvalP is the identity on section carriers, and the two
pushforward compositors are restriction along the same pullback-pasting map.
Their equality on sections proves pull_comp by injectivity of the mate equivalence.
For open composition transpose once more: moduleJComp and the strict-tower jComp
are both conjugate to these pullback compositors. This proves open_comp.
For clopen, use the chosen pullback W ×_T S. Evaluation keeps the pullback lift
label, so the unit transpose defining moduleBeta evaluates to the strict-tower
beta. The canonical lift is clopen. On its image the projection is the open unit;
on its complement it is zero. Evaluation, constant embedding, and the single
functor keep these two maps. The two-component sheaf decomposition therefore
identifies the evaluated projector with the strict-tower pi. Substitute these
identifications into moduleAlpha and use the two compositor comparisons just
proved. The resulting equation is clopen. This calculation is on ordinary
systems and their degree-zero complexes; it uses no faithfulness of derived
evaluations and assumes no vertical or horizontal pasting law. -/
theorem ordinaryClopenEvaluation (n : ℕ) :
    ∃ (gIso : OrdinaryPullComparison R φ n) (jIso : OrdinaryOpenComparison R φ n),
      OrdinaryPullComposition R φ n gIso ∧ OrdinaryOpenComposition R φ n jIso ∧
        OrdinaryClopenComparison R φ n gIso jIso := by
  sorry

end AlgebraicGeometry.ProEtale.VaryingRing
