/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q64
-/
module

public import Sheaf.CategoryTheory.SystemRingedSequenceSite

/-! # Constant sequence modules with independent site universes

Source: Stacks Project, Tags 03DA and 0940; Zheng, Construction 4.1
(blueprint: def-coef-constant-sequence-equivalence).
The forward and inverse functors are constructed from strict systems, not chosen
from an existence theorem. The proved same-universe dependency is unchanged.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe c v r w
open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
namespace CategoryTheory.ConstantCompletion

variable {C : Type c} [Category.{v} C] [EssentiallySmall.{max c v r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})]
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (O : Sheaf J CommRingCat.{max c v r})

/-- The independentSystem construction with independent site and module universes.
Source: Stacks 03DA, 0940; Zheng 4.1
(blueprint: def-coef-constant-sequence-equivalence). -/
abbrev independentSystem :=
  SheafOfModules.StrictRingSystem.{c, v, max c v r} (J := J) ((Functor.const ℕᵒᵖ).obj O)

/-- The independentToTower construction with independent site and module universes.
Source: Stacks 03DA, 0940; Zheng 4.1
(blueprint: def-coef-constant-sequence-equivalence). -/
def independentToTower : independentSystem.{c, v, r} O ⥤ (ℕᵒᵖ ⥤ ringedSiteModules.{max c v r}
        ((sheafCompose J
      (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj O)) where
  obj M :=
    { obj n := M.level n.unop
      map h := M.transition (leOfHom h.unop)
      map_id n := by
        ext U x
        exact M.identity n.unop U x
      map_comp f g := by
        ext U x
        exact M.compose (leOfHom g.unop) (leOfHom f.unop) U x }
  map f :=
    { app n := f.app n.unop
      naturality := by
        intro n m h
        exact (f.comm (leOfHom h.unop)).symm }
  map_id M := rfl
  map_comp f g := rfl

/-- The independentFromTower construction with independent site and module universes.
Source: Stacks 03DA, 0940; Zheng 4.1
(blueprint: def-coef-constant-sequence-equivalence). -/
def independentFromTower : (ℕᵒᵖ ⥤ ringedSiteModules.{max c v r} ((sheafCompose J
      (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj O)) ⥤ independentSystem.{c, v,
        r} O where
  obj F :=
    { level n := F.obj (op n)
      transition h := F.map (homOfLE h).op
      identity n U x := by
        have h := congrArg (fun f ↦ f.val.app U) (F.map_id (op n))
        exact ConcreteCategory.congr_hom h x
      compose h k U x := by
        have h := congrArg (fun f ↦ f.val.app U)
          (F.map_comp (homOfLE k).op (homOfLE h).op)
        exact ConcreteCategory.congr_hom h x }
  map f :=
    { app n := f.app (op n)
      comm := by
        intro n m h
        exact (f.naturality (homOfLE h).op).symm }
  map_id F := rfl
  map_comp f g := rfl

set_option maxHeartbeats 800000 in
-- Identity coefficient restrictions require reducing the varying-ring system interface.
/-- The independentSystemTowerEquivalence construction with independent site and module universes.
Source: Stacks 03DA, 0940; Zheng 4.1
(blueprint: def-coef-constant-sequence-equivalence). -/
def independentSystemTowerEquivalence : independentSystem.{c, v, r} O ≌
    (ℕᵒᵖ ⥤ ringedSiteModules.{max c v r} ((sheafCompose J
      (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj O)) where
  functor := independentToTower.{c, v, r} O
  inverse := independentFromTower.{c, v, r} O
  unitIso := NatIso.ofComponents (fun M ↦
    { hom := { app n := 𝟙 _
               comm := by intros; ext U x; rfl }
      inv := { app n := 𝟙 _
               comm := by intros; ext U x; rfl }
      hom_inv_id := by
        apply SheafOfModules.strictRingSystem_hom_ext
        intro n
        change 𝟙 _ ≫ 𝟙 _ = 𝟙 _
        simp
      inv_hom_id := by
        apply SheafOfModules.strictRingSystem_hom_ext
        intro n
        change 𝟙 _ ≫ 𝟙 _ = 𝟙 _
        simp })
    (by
      intro M N f
      apply SheafOfModules.strictRingSystem_hom_ext
      intro n
      change f.app n ≫ 𝟙 _ = 𝟙 _ ≫ f.app n
      simp)
  counitIso := NatIso.ofComponents (fun F ↦ NatIso.ofComponents (fun n ↦ Iso.refl _)
    (by
      intro n m h
      change F.map _ ≫ 𝟙 _ = 𝟙 _ ≫ F.map h
      simp only [Category.comp_id, Category.id_comp])) (by intro M N f; ext n; exact rfl)
  functor_unitIso_comp M := by ext n; simp [independentToTower]

/-- The real constant-ring sequence equivalence, including its specified inverse.
Source: Stacks 03DA, 0940; Zheng 4.1
(blueprint: def-coef-constant-sequence-equivalence). -/
def independentConstantSequenceEquivalence :
    systemSequenceModules.{c, v, max c v r} ((Functor.const ℕᵒᵖ).obj O) ≌
      (ℕᵒᵖ ⥤ ringedSiteModules.{max c v r} ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj O)) :=
  (strictSystemSequenceEquivalence.{c, v, max c v r}
    ((Functor.const ℕᵒᵖ).obj O)).symm.trans (independentSystemTowerEquivalence.{c, v, r} O)

private theorem identityRestriction_hom_heq {R : Type w} [Ring R]
    (φ : R →+* R) (hφ : φ = RingHom.id R) (M N : ModuleCat.{w} R)
    (f : M ⟶ N) (g : M ⟶ (ModuleCat.restrictScalars φ).obj N)
    (h : ∀ x : M, f x = g x) : HEq f g := by
  subst φ
  apply heq_of_eq
  ext x
  exact h x

/-- Both explicit functors preserve sums.
Source: Stacks 03DA, 0940 (blueprint: def-coef-constant-sequence-equivalence).
Proof: the strict-system realization adds section maps componentwise; so do the
explicit forward and inverse tower functors. Their composites therefore add maps. -/
theorem independentConstantSequenceEquivalence_additive :
    (independentConstantSequenceEquivalence.{c, v, r} O).functor.Additive ∧
      (independentConstantSequenceEquivalence.{c, v, r} O).inverse.Additive := by
  have h : (independentConstantSequenceEquivalence.{c, v, r} O).functor.Additive := by
    constructor
    intro M N f g
    apply NatTrans.ext
    funext n
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    ext x
    rfl
  exact ⟨h, (independentConstantSequenceEquivalence.{c, v, r} O).inverse_additive⟩

/-- Constant sequence modules are literal towers, retaining their section objects,
vertical restrictions, horizontal restrictions and maps, at independent universes.
Source: Stacks 03DA, 0940; Zheng 4.1
(blueprint: def-coef-constant-sequence-equivalence).
Proof: compose strictSystemSequenceEquivalence with the equivalence taking a
constant-ring strict semilinear system to its levels and horizontal arrows.
Restriction along each identity ring map changes no module structure. The inverse
makes the levels and arrows of a tower into a strict system. Both round trips have
identity component maps, and both functors add maps componentwise. The sequence
site realization evaluates these levels, restrictions and arrows literally at
(n,U), so all four sectionwise characterizations follow. The coefficient universe
contains the objects and arrows; no equality of site universes is needed. -/
theorem independentConstantSequenceEquivalence_sections
    {C : Type c} [Category.{v} C] [EssentiallySmall.{max c v r} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})]
    [HasSheafify J AddCommGrpCat.{max c v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
    (O : Sheaf J CommRingCat.{max c v r}) :
      (∀ (M : systemSequenceModules.{c, v, max c v r} ((Functor.const ℕᵒᵖ).obj O))
        (n : ℕ) (U : Cᵒᵖ),
        HEq ((((independentConstantSequenceEquivalence.{c, v, r} O).functor.obj M).obj (op
        n)).val.obj U)
          (M.val.obj (op (n, U.unop)))) ∧
      (∀ (M : systemSequenceModules.{c, v, max c v r} ((Functor.const ℕᵒᵖ).obj O))
        (n : ℕ) {U V : Cᵒᵖ} (f : U ⟶ V),
        HEq ((((independentConstantSequenceEquivalence.{c, v, r} O).functor.obj M).obj (op
        n)).val.map f)
          (M.val.map (Prod.mkHom (𝟙 n) f.unop).op)) ∧
      (∀ (M : systemSequenceModules.{c, v, max c v r} ((Functor.const ℕᵒᵖ).obj O))
        {m n : ℕ} (h : m ≤ n) (U : Cᵒᵖ),
        HEq ((((independentConstantSequenceEquivalence.{c, v, r} O).functor.obj M).map (homOfLE
        h).op).val.app U)
          (M.val.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op)) ∧
      (∀ {M N : systemSequenceModules.{c, v, max c v r} ((Functor.const ℕᵒᵖ).obj O)}
        (f : M ⟶ N) (n : ℕ) (U : Cᵒᵖ),
        HEq ((((independentConstantSequenceEquivalence.{c, v, r} O).functor.map f).app (op
        n)).val.app U)
          (f.val.app (op (n, U.unop)))) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro M n U
    rfl
  · intro M n U V f
    rfl
  · intro M m n h U
    change HEq
      (sequenceSystemTransitionApp ((Functor.const ℕᵒᵖ).obj O) M h U)
      (M.val.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op)
    let φ := ((derivedChangeRingIndependentCoefficients
      (WeilConjectures.coefficientSequenceTopology J)
      (systemSequenceRing.{c, v, max c v r} ((Functor.const ℕᵒᵖ).obj O))).obj.map
        (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op).hom
    have hφ : φ = RingHom.id _ := by
      have hh := systemSequenceRing_horizontal ((Functor.const ℕᵒᵖ).obj O) h U
      dsimp only [Functor.const_obj_map] at hh
      exact congrArg (fun t ↦ t.hom) hh
    exact identityRestriction_hom_heq φ hφ _ _ _ _ (fun x ↦ rfl)
  · intro M N f n U
    rfl

/-- The explicit inverse also retains the level sections and all three kinds of maps.
Source: Stacks 03DA, 0940; Zheng 4.1
(blueprint: def-coef-constant-sequence-equivalence).
Proof: the inverse forms the strict system with levels F(n) and transitions F(h),
then realizes it on the sequence site. Its section at (n,U) is F(n)(U). Vertical
restrictions are those of F(n), horizontal restrictions are F(h), and module maps
are the corresponding components. The identity coefficient restrictions give HEq. -/
theorem independentConstantSequenceEquivalence_inverse_sections :
    (∀ (F : ℕᵒᵖ ⥤ ringedSiteModules.{max c v r} ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj O))
      (n : ℕ) (U : Cᵒᵖ),
      HEq (((independentConstantSequenceEquivalence.{c, v, r} O).inverse.obj F).val.obj
        (op (n, U.unop))) ((F.obj (op n)).val.obj U)) ∧
    (∀ (F : ℕᵒᵖ ⥤ ringedSiteModules.{max c v r} ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj O))
      (n : ℕ) {U V : Cᵒᵖ} (f : U ⟶ V),
      HEq (((independentConstantSequenceEquivalence.{c, v, r} O).inverse.obj F).val.map
        (Prod.mkHom (𝟙 n) f.unop).op) ((F.obj (op n)).val.map f)) ∧
    (∀ (F : ℕᵒᵖ ⥤ ringedSiteModules.{max c v r} ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj O))
      {m n : ℕ} (h : m ≤ n) (U : Cᵒᵖ),
      HEq (((independentConstantSequenceEquivalence.{c, v, r} O).inverse.obj F).val.map
        (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op)
        ((F.map (homOfLE h).op).val.app U)) ∧
    (∀ {F G : ℕᵒᵖ ⥤ ringedSiteModules.{max c v r} ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj O)}
      (f : F ⟶ G) (n : ℕ) (U : Cᵒᵖ),
      HEq (((independentConstantSequenceEquivalence.{c, v, r} O).inverse.map f).val.app
        (op (n, U.unop))) ((f.app (op n)).val.app U)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro F n U
    rfl
  · intro F n U V f
    apply heq_of_eq
    ext x
    change (F.obj (op n)).val.map f ((F.map (𝟙 (op n))).val.app U x) = _
    rw [F.map_id]
    rfl
  · intro F m n h U
    let φ := ((derivedChangeRingIndependentCoefficients
      (WeilConjectures.coefficientSequenceTopology J)
      (systemSequenceRing.{c, v, max c v r} ((Functor.const ℕᵒᵖ).obj O))).obj.map
        (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op).hom
    have hφ : φ = RingHom.id _ := by
      have hh := systemSequenceRing_horizontal ((Functor.const ℕᵒᵖ).obj O) h U
      dsimp only [Functor.const_obj_map] at hh
      exact congrArg (fun t ↦ t.hom) hh
    exact (identityRestriction_hom_heq φ hφ _ _ _ _ (by
      intro x
      change (F.map (homOfLE h).op).val.app U x =
        (F.obj (op m)).val.map (𝟙 U) ((F.map (homOfLE h).op).val.app U x)
      rw [PresheafOfModules.map_id]
      rfl)).symm
  · intro F G f n U
    rfl

end CategoryTheory.ConstantCompletion
