/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.SemilinearProperOpenMatePasting
public import WeilConjectures.SixFunctors.OpenTensorNormalization
public import WeilConjectures.AlgebraicGeometry.DiagramOpenClopenShiftModels
import Mathlib.CategoryTheory.Adjunction.Mates
import all WeilConjectures.SixFunctors.SemilinearProperOpenMatePasting
import all WeilConjectures.AlgebraicGeometry.VaryingRingOperations
import WeilConjectures.CategoryTheory.ConstantFiniteFreeSectionBasis
import Mathlib.Algebra.Category.ModuleCat.Descent
public import Mathlib.LinearAlgebra.Basis.Defs

/-! # Finite-free scalar naturality of the intrinsic proper/open mate

Source: Zheng, Section 5, Lemma 5.13 and Constructions 5.14--5.15, pp. 34--35;
Stacks 03CZ, 03DI, 0E8I and 0F7B. The scalar naturality argument is agent-formulated.
(blueprint: def-sf-system-finite-free-scalar-data).

The scalar functor is the localization of ordinary sheafified tensor, which is exact
under the compatible finite-free bases. All comparisons are constructed on whole systems.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures.SemilinearSections

attribute [local irreducible] Functor.leftAdjoint Functor.mapDerivedCategory
  Functor.rightDerivedFunctor constantSheaf systemMap
  AlgebraicGeometry.ProEtale.SemilinearProperOpen.coefficientMap

private def scalarPresheaf
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    [HasSheafify J AddCommGrpCat.{u + 1}]
    {R S : Sheaf J CommRingCat.{u + 1}} (φ : R ⟶ S) :
    SheafOfModules.{u + 1} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⥤
      PresheafOfModules.{u + 1} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S).obj
      where
  obj M := SheafOfModules.changeOfRingsPresheaf φ M
  map f :=
    { app U := (ModuleCat.extendScalars (φ.hom.app U).hom).map (f.val.app U)
      naturality := SheafOfModules.changeOfRingsHom_naturality φ _ f }
  map_id M := by
    apply PresheafOfModules.hom_ext
    intro U
    exact (ModuleCat.extendScalars (φ.hom.app U).hom).map_id _
  map_comp f g := by
    apply PresheafOfModules.hom_ext
    intro U
    exact (ModuleCat.extendScalars (φ.hom.app U).hom).map_comp _ _

private theorem scalarPresheaf_limits
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    [HasSheafify J AddCommGrpCat.{u + 1}]
    {R S : Sheaf J CommRingCat.{u + 1}} (φ : R ⟶ S)
    (hφ : ∀ U : Cᵒᵖ, (φ.hom.app U).hom.Flat) :
    PreservesFiniteLimits (scalarPresheaf φ) := by
  let F := scalarPresheaf φ
  let R' := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R
  let S' := (sheafCompose J (forget₂ CommRingCat RingCat)).obj S
  letI (U : Cᵒᵖ) : CommRing (R'.obj.obj U) :=
    inferInstanceAs (CommRing (R.obj.obj U))
  letI (U : Cᵒᵖ) : CommRing (S'.obj.obj U) :=
    inferInstanceAs (CommRing (S.obj.obj U))
  have he (U : Cᵒᵖ) : PreservesFiniteLimits (F ⋙ PresheafOfModules.evaluation S'.obj U) := by
    have := ModuleCat.preservesFiniteLimits_extendScalars_of_flat (hφ U)
    exact inferInstanceAs (PreservesFiniteLimits
      (SheafOfModules.evaluation R' U ⋙ ModuleCat.extendScalars (φ.hom.app U).hom))
  constructor
  intro I _ _
  constructor
  intro D
  apply preservesLimit_of_preserves_limit_cone (limit.isLimit D)
  apply PresheafOfModules.evaluationJointlyReflectsLimits
  intro U
  exact isLimitOfPreserves (F ⋙ PresheafOfModules.evaluation S'.obj U) (limit.isLimit D)

private theorem scalarModel_limits_of_flat
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    [HasSheafify J AddCommGrpCat.{u + 1}]
    {R S : Sheaf J CommRingCat.{u + 1}} (φ : R ⟶ S)
    [HasDerivedCategory.{u + 2} (SheafOfModules.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))]
    [HasDerivedCategory.{u + 2} (SheafOfModules.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))]
    (D : SheafOfModules.DerivedChangeOfRingsCochainModel φ)
    (hφ : ∀ U : Cᵒᵖ, (φ.hom.app U).hom.Flat) : PreservesFiniteLimits D.E := by
  let L := PresheafOfModules.sheafification.{u + 1}
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S).obj)
  let F := scalarPresheaf φ ⋙ L
  let e : D.E ≅ F := NatIso.ofComponents (fun M ↦ eqToIso (D.obj_eq M)) (by
    intro M N f
    change D.E.map f ≫ eqToHom (D.obj_eq N) =
      eqToHom (D.obj_eq M) ≫ SheafOfModules.changeOfRingsHom φ M f
    rw [D.map_eq]
    simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id])
  letI : PreservesFiniteLimits (scalarPresheaf φ) := scalarPresheaf_limits φ hφ
  have : PreservesFiniteLimits F := inferInstance
  exact preservesFiniteLimits_of_natIso e.symm

private theorem restriction_pushforward_square
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : C ⥤ D) [F.IsContinuous J K]
    {R S : Sheaf J RingCat.{u + 1}} {R' S' : Sheaf K RingCat.{u + 1}}
    (a : R ⟶ S) (b : R' ⟶ S')
    (p : R ⟶ (F.sheafPushforwardContinuous RingCat.{u + 1} J K).obj R')
    (q : S ⟶ (F.sheafPushforwardContinuous RingCat.{u + 1} J K).obj S')
    (h : a ≫ q = p ≫ (F.sheafPushforwardContinuous RingCat.{u + 1} J K).map b) :
    ∃ c : SheafOfModules.pushforward.{u + 1} q ⋙ SheafOfModules.restrictScalars a ≅
      SheafOfModules.restrictScalars b ⋙ SheafOfModules.pushforward p,
      ∀ (N : SheafOfModules.{u + 1} S') (V : C),
        HEq (fun x ↦ (c.hom.app N).val.app (op V) x)
          (fun x : N.val.obj (op (F.obj V)) ↦ x) := by
  let c : SheafOfModules.pushforward.{u + 1} q ⋙ SheafOfModules.restrictScalars a ≅
      SheafOfModules.restrictScalars b ⋙ SheafOfModules.pushforward p :=
    SheafOfModules.pushforwardComp (F := 𝟭 C) (G := F) a q ≪≫
      SheafOfModules.pushforwardCongr h ≪≫
        (SheafOfModules.pushforwardComp (F := F) (G := 𝟭 D) p b).symm
  exact ⟨c, fun _ _ ↦ HEq.rfl⟩

private theorem ringed_inverse_mate_iso
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {F : C ⥤ D} {G : D ⥤ C} [F.IsContinuous J K] [G.IsContinuous K J]
    (s : F ⊣ G)
    {RA RB : Sheaf J RingCat.{u + 1}} {SA SB : Sheaf K RingCat.{u + 1}}
    (a : SA ⟶ SB) (b : RA ⟶ RB)
    (pA : SA ⟶ (G.sheafPushforwardContinuous RingCat.{u + 1} K J).obj RA)
    (pB : SB ⟶ (G.sheafPushforwardContinuous RingCat.{u + 1} K J).obj RB)
    (h : a ≫ pB = pA ≫
      (G.sheafPushforwardContinuous RingCat.{u + 1} K J).map b)
    [IsIso (((s.sheafPushforwardContinuous (E := RingCat.{u + 1}) J K).homEquiv
      SA RA).symm pA)]
    [IsIso (((s.sheafPushforwardContinuous (E := RingCat.{u + 1}) J K).homEquiv
      SB RB).symm pB)]
    (q : SheafOfModules.pushforward.{u + 1} pB ⋙ SheafOfModules.restrictScalars a ≅
      SheafOfModules.restrictScalars b ⋙ SheafOfModules.pushforward pA)
    (hq : ∀ (N : SheafOfModules.{u + 1} RB) (V : D),
      HEq (fun x ↦ (q.hom.app N).val.app (op V) x)
        (fun x : N.val.obj (op (G.obj V)) ↦ x)) :
    IsIso ((mateEquiv
      (AlgebraicGeometry.ProEtale.VaryingRing.moduleAdjOfSiteAdj J K s pB)
      (AlgebraicGeometry.ProEtale.VaryingRing.moduleAdjOfSiteAdj J K s pA)).symm
        q.hom).natTrans := by
  let sh := s.sheafPushforwardContinuous (E := RingCat.{u + 1}) J K
  let dA := (sh.homEquiv SA RA).symm pA
  let dB := (sh.homEquiv SB RB).symm pB
  have ht : (F.sheafPushforwardContinuous RingCat.{u + 1} J K).map a ≫ dB = dA ≫ b := by
    apply (sh.homEquiv _ _).injective
    rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
    simpa only [dA, dB, Equiv.apply_symm_apply] using h
  have hi : b ≫ inv dB = inv dA ≫
      (F.sheafPushforwardContinuous RingCat.{u + 1} J K).map a := by
    apply (cancel_epi dA).mp
    simp only [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
    rw [← ht, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  obtain ⟨c, hc⟩ := restriction_pushforward_square F b a (inv dA) (inv dB) hi
  apply AlgebraicGeometry.ProEtale.VaryingRing.inverseMateIsoOfUnit _ _
    (SheafOfModules.restrictScalars a) (SheafOfModules.restrictScalars b) q.hom c
  intro N
  ext V x
  have hq' := congrFun (eq_of_heq (hq ((SheafOfModules.pushforward (inv dB)).obj N) V.unop))
    (((AlgebraicGeometry.ProEtale.VaryingRing.moduleAdjOfSiteAdj J K s pB).unit.app
      N).val.app V x)
  change (c.hom.app N).val.app (op (G.obj V.unop))
      ((q.hom.app ((SheafOfModules.pushforward (inv dB)).obj N)).val.app V
        (((AlgebraicGeometry.ProEtale.VaryingRing.moduleAdjOfSiteAdj J K s pB).unit.app
          N).val.app V x)) = _
  rw [hq']
  exact congrFun (eq_of_heq (hc N (G.obj V.unop)))
    (N.val.map (s.counit.app V.unop).op x)

namespace AlgebraicGeometry.ProEtale.SemilinearProperOpen.Scalar

variable (A B : ℕ → CommRingCat.{u + 1})
  (a : ∀ n : ℕ, A (n + 1) ⟶ A n) (b : ∀ n : ℕ, B (n + 1) ⟶ B n)
  (φ : ∀ n : ℕ, A n ⟶ B n)
  (hφ : ∀ n : ℕ, φ (n + 1) ≫ b n = a n ≫ φ n)

/-- The constant sheaf coefficient map at a single level. Source: Zheng 5.13
(blueprint: lem-sf-system-proper-open-scalar-square). -/
abbrev levelMap (X : Scheme.{u}) (n : ℕ) : coefficients A X n ⟶ coefficients B X n :=
  (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map (φ n)

include hφ in
/-- Compatibility of the actual constant sheaf maps. Source: Zheng 4.1, 5.13
Proof: apply the constant sheaf functor to hφ and use preservation of composition.
(blueprint: lem-sf-system-proper-open-scalar-square). -/
theorem levelCompatibility (X : Scheme.{u}) (n : ℕ) :
    levelMap A B φ X (n + 1) ≫ transition B b X n =
      transition A a X n ≫ levelMap A B φ X n :=
  by
    simpa only [levelMap, transition, ← Functor.map_comp] using
      congrArg ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map) (hφ n)

/-- The already constructed, unit-normalized scalar-extension calculus on the sequence site.
Source: Zheng 4.1; Stacks 06YY (blueprint: lem-sf-system-proper-open-scalar-square). -/
def calculus (X : Scheme.{u}) :=
  (Classical.choice (semilinearDerivedSections.{u + 1, u, u + 1}
    (ProEt.topology X) (coefficients A X) (transition A a X))).coefficientExtension
      (coefficients B X) (transition B b X) (levelMap A B φ X)
      (levelCompatibility A B a b φ hφ X)

/-- Ordinary extension is the existing sheafification of sectionwise tensor.
Source: Stacks 03CZ, 06YY (blueprint: lem-sf-system-proper-open-scalar-square). -/
abbrev E (X : Scheme.{u}) : Modules A a X ⥤ Modules B b X :=
  (calculus A B a b φ hφ X).scalar.model.E

/-- Ordinary coefficient restriction retains the section groups and quotient transitions.
Source: Stacks 03CZ (blueprint: lem-sf-system-proper-open-scalar-square). -/
abbrev restriction (X : Scheme.{u}) : Modules B b X ⥤ Modules A a X :=
  res (systemMap (ProEt.topology X) (coefficients A X) (transition A a X)
    (coefficients B X) (transition B b X) (levelMap A B φ X)
    (levelCompatibility A B a b φ hφ X))

/-- The existing normalized ordinary tensor/restriction adjunction.
Source: Stacks 03CZ (blueprint: lem-sf-system-proper-open-scalar-square). -/
def scalarAdj (X : Scheme.{u}) : E A B a b φ hφ X ⊣ restriction A B a b φ hφ X :=
  (calculus A B a b φ hφ X).scalar.ordinaryAdjunction

/-- The coefficient module uses precisely the given unital map, not another algebra action.
Source: Zheng 5.13, finite-free scalar argument
(blueprint: lem-sf-system-proper-open-scalar-square). -/
abbrev coefficientModule (n : ℕ) : ModuleCat (A n) :=
  (ModuleCat.restrictScalars (φ n).hom).obj (ModuleCat.of (B n) (B n))

/-- Compatible finite bases on the original ring sequence. Source: Zheng 5.13,
agent finite-free argument (blueprint: lem-sf-system-proper-open-scalar-square). -/
structure Bases (d : ℕ) where
  basis : ∀ n : ℕ, Module.Basis (Fin d) (A n) (coefficientModule A B φ n)
  transition : ∀ (n : ℕ) (j : Fin d), (b n).hom (basis (n + 1) j) = basis n j

/-- Compatible bases identify the underlying ordinary scalar extension with d copies,
so tensor is exact on the entire system category. Source: Zheng 5.13, agent argument
(blueprint: lem-sf-system-proper-open-scalar-square).
Proof: send the tuple (m_j) to the sum of m_j tensor e_j at every level. The inverse
uses the basis coordinates. Compatibility of bases makes both maps commute with all
transitions. Exactness is componentwise, and finite sums preserve short exact sequences. -/
theorem extension_exact (d : ℕ) (hd : 1 ≤ d) (e : Bases A B b φ d) (X : Scheme.{u}) :
    PreservesFiniteLimits (E A B a b φ hφ X) ∧
      PreservesFiniteColimits (E A B a b φ hφ X) := by
  have := hd
  let α := systemMap (ProEt.topology X) (coefficients A X) (transition A a X)
    (coefficients B X) (transition B b X) (levelMap A B φ X)
    (levelCompatibility A B a b φ hφ X)
  have hf (U : (ℕ × X.ProEt)ᵒᵖ) : (α.hom.app U).hom.Flat := by
    let n := U.unop.1
    letI : Algebra (A n) (B n) := (φ n).hom.toAlgebra
    letI : Module.Free (A n) (B n) := Module.Free.of_basis (e.basis n)
    letI : Module.Finite (A n) (B n) := Module.Finite.of_basis (e.basis n)
    obtain ⟨q, β, _⟩ := @constantFiniteFree_sectionBasis.{u + 1, u, u + 1}
      X.ProEt inferInstance (ProEt.topology X)
      (inferInstance : HasSheafify (ProEt.topology X) CommRingCat.{u + 1})
      (inferInstance : (ProEt.topology X).HasSheafCompose
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}))
      (inferInstance : HasSheafify (ProEt.topology X) AddCommGrpCat.{u + 1})
      (locallyBijective.{u + 1, u, u + 1} (ProEt.topology X))
      (A n) (B n) inferInstance inferInstance inferInstance
    have hα : α.hom.app U = (levelMap A B φ X n).hom.app (op U.unop.2) := by
      dsimp only [α]
      delta systemMap
      exact (systemMap_existsUnique (ProEt.topology X) (coefficients A X)
        (transition A a X) (coefficients B X) (transition B b X)
        (levelMap A B φ X) (levelCompatibility A B a b φ hφ X)).exists.choose_spec
          U.unop.1 (op U.unop.2)
    rw [hα]
    letI : Algebra ((coefficients A X n).obj.obj (op U.unop.2))
        ((coefficients B X n).obj.obj (op U.unop.2)) :=
      ((levelMap A B φ X n).hom.app (op U.unop.2)).hom.toAlgebra
    letI : Module.Free ((coefficients A X n).obj.obj (op U.unop.2))
        ((coefficients B X n).obj.obj (op U.unop.2)) :=
      Module.Free.of_basis (β (op U.unop.2))
    exact inferInstanceAs (Module.Flat ((coefficients A X n).obj.obj (op U.unop.2))
      ((coefficients B X n).obj.obj (op U.unop.2)))
  have hl : PreservesFiniteLimits (E A B a b φ hφ X) :=
    scalarModel_limits_of_flat α (calculus A B a b φ hφ X).scalar.model hf
  have hc : PreservesFiniteColimits (E A B a b φ hφ X) :=
    letI : (E A B a b φ hφ X).IsLeftAdjoint :=
      (scalarAdj A B a b φ hφ X).isLeftAdjoint
    inferInstance
  exact ⟨hl, hc⟩


variable (d : ℕ) (hd : 1 ≤ d) (e : Bases A B b φ d)

/-- Left exactness of the finite-free model. Source: Zheng 5.13, agent argument
(blueprint: lem-sf-system-proper-open-scalar-square). -/
abbrev extensionLimits (X : Scheme.{u}) : PreservesFiniteLimits (E A B a b φ hφ X) :=
  (extension_exact A B a b φ hφ d hd e X).1

/-- Right exactness of the finite-free model. Source: Zheng 5.13, agent argument
(blueprint: lem-sf-system-proper-open-scalar-square). -/
abbrev extensionColimits (X : Scheme.{u}) : PreservesFiniteColimits (E A B a b φ hφ X) :=
  (extension_exact A B a b φ hφ d hd e X).2

/-- Derived scalar extension on arbitrary unbounded systems, computed by the exact model.
Source: Zheng 5.13; Stacks 06YY (blueprint: lem-sf-system-proper-open-scalar-square). -/
def T (X : Scheme.{u}) : Derived A a X ⥤ Derived B b X :=
  letI := extensionLimits A B a b φ hφ d hd e X
  letI := extensionColimits A B a b φ hφ d hd e X
  (E A B a b φ hφ X).mapDerivedCategory

private theorem scalarRingSquare {X Y : Scheme.{u}} (f : X ⟶ Y) :
    let α (S : Scheme.{u}) := systemMap (ProEt.topology S)
      (coefficients A S) (transition A a S) (coefficients B S) (transition B b S)
      (levelMap A B φ S) (levelCompatibility A B a b φ hφ S)
    let L := sheafCompose (WeilConjectures.coefficientSequenceTopology (ProEt.topology Y))
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
    let K := sheafCompose (WeilConjectures.coefficientSequenceTopology (ProEt.topology X))
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
    L.map (α Y) ≫ L.map (coefficientMap B b f) =
      L.map (coefficientMap A a f) ≫
        ((siteMap f).sheafPushforwardContinuous RingCat.{u + 1}
          (WeilConjectures.coefficientSequenceTopology (ProEt.topology Y))
          (WeilConjectures.coefficientSequenceTopology (ProEt.topology X))).map
            (K.map (α X)) := by
  let α (S : Scheme.{u}) := systemMap (ProEt.topology S) (coefficients A S)
    (transition A a S) (coefficients B S) (transition B b S)
    (levelMap A B φ S) (levelCompatibility A B a b φ hφ S)
  have he : α Y ≫ coefficientMap B b f = coefficientMap A a f ≫
      ((siteMap f).sheafPushforwardContinuous CommRingCat.{u + 1}
        (WeilConjectures.coefficientSequenceTopology (ProEt.topology Y))
        (WeilConjectures.coefficientSequenceTopology (ProEt.topology X))).map (α X) := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    change (α Y).hom.app U ≫ (coefficientMap B b f).hom.app U =
      (coefficientMap A a f).hom.app U ≫ (α X).hom.app ((siteMap f).op.obj U)
    have hα (S : Scheme.{u}) (V : (ℕ × S.ProEt)ᵒᵖ) :
        (α S).hom.app V = (levelMap A B φ S V.unop.1).hom.app (op V.unop.2) := by
      dsimp only [α]
      delta systemMap
      exact (systemMap_existsUnique (ProEt.topology S) (coefficients A S)
        (transition A a S) (coefficients B S) (transition B b S)
        (levelMap A B φ S) (levelCompatibility A B a b φ hφ S)).exists.choose_spec
          V.unop.1 (op V.unop.2)
    have hB : (coefficientMap B b f).hom.app U =
        (proEtaleConstantDirectImageMap f CommRingCat.{u + 1} (B U.unop.1)).hom.app
          (op U.unop.2) := by
      delta coefficientMap
      exact eq_of_heq ((coefficientMap_existsUnique B b f).choose_spec.1 U.unop.1 U.unop.2)
    have hA : (coefficientMap A a f).hom.app U =
        (proEtaleConstantDirectImageMap f CommRingCat.{u + 1} (A U.unop.1)).hom.app
          (op U.unop.2) := by
      delta coefficientMap
      exact eq_of_heq ((coefficientMap_existsUnique A a f).choose_spec.1 U.unop.1 U.unop.2)
    rw [hα Y U, hα X ((siteMap f).op.obj U), hB, hA]
    exact congrArg (fun t ↦ t.hom.app (op U.unop.2))
      (AlgebraicGeometry.ProEtale.VaryingRing.constantMap_naturality f (φ U.unop.1))
  let L := sheafCompose (WeilConjectures.coefficientSequenceTopology (ProEt.topology Y))
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  let K := sheafCompose (WeilConjectures.coefficientSequenceTopology (ProEt.topology X))
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  have he' : L.map (α Y) ≫ L.map (coefficientMap B b f) =
      L.map (coefficientMap A a f) ≫
        ((siteMap f).sheafPushforwardContinuous RingCat.{u + 1}
          (WeilConjectures.coefficientSequenceTopology (ProEt.topology Y))
          (WeilConjectures.coefficientSequenceTopology (ProEt.topology X))).map
            (K.map (α X)) := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    exact congrArg (fun t ↦ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map t)
      (congrArg (fun t ↦ t.hom.app U) he)
  exact he'

set_option maxHeartbeats 1000000 in
-- The ringed-site comparison contains several dependent functor transports.
/-- The canonical ordinary restriction/direct-image identification is identity on sections.
Source: Stacks 03CZ, 03D7 (blueprint: lem-sf-system-proper-open-scalar-square).
Proof: both sides have the sections of N over the same fibre-product object, with
A action through φ. The coefficient square and hφ identify the actions and transitions.
Identity maps are mutually inverse and natural; their section formula gives uniqueness. -/
theorem restrictionPush_existsUnique {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃! c : push B b f ⋙ restriction A B a b φ hφ Y ≅
      restriction A B a b φ hφ X ⋙ push A a f,
      ∀ (N : Modules B b X) (n : ℕ) (V : Y.ProEt),
        HEq (fun x ↦ (c.hom.app N).val.app (op (n, V)) x)
          (fun x : N.val.obj (op (n, (proEtaleBaseChange f).obj V)) ↦ x) := by
  let α (S : Scheme.{u}) := systemMap (ProEt.topology S) (coefficients A S)
    (transition A a S) (coefficients B S) (transition B b S)
    (levelMap A B φ S) (levelCompatibility A B a b φ hφ S)
  let L := sheafCompose (WeilConjectures.coefficientSequenceTopology (ProEt.topology Y))
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  let K := sheafCompose (WeilConjectures.coefficientSequenceTopology (ProEt.topology X))
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  have he' := scalarRingSquare A B a b φ hφ f
  obtain ⟨c, hc⟩ := restriction_pushforward_square (siteMap f)
    (L.map (α Y)) (K.map (α X)) (L.map (coefficientMap A a f))
    (L.map (coefficientMap B b f)) he'
  refine ⟨c, fun N n V ↦ hc N (n, V), ?_⟩
  intro c' hc'
  apply Iso.ext
  apply NatTrans.ext
  funext N
  ext V x
  exact congrFun ((eq_of_heq (hc' N V.unop.1 V.unop.2)).trans
    (eq_of_heq (hc N V.unop)).symm) x

/-- Inverse image commutes with scalar tensor by uniqueness of the composed left adjoints.
This fixes the usual pure-tensor comparison through identity-on-sections restriction.
Source: Stacks 03CZ, 03D7 (blueprint: lem-sf-system-proper-open-scalar-square). -/
def ellOrdinary {X Y : Scheme.{u}} (f : X ⟶ Y) :
    E A B a b φ hφ Y ⋙ pull B b f ≅ pull A a f ⋙ E A B a b φ hφ X :=
  ((conjugateIsoEquiv ((scalarAdj A B a b φ hφ Y).comp (ordinaryAdj B b f))
    ((ordinaryAdj A a f).comp (scalarAdj A B a b φ hφ X))).symm
      (restrictionPush_existsUnique A B a b φ hφ f).choose).symm

set_option maxHeartbeats 1000000 in
-- Elaborate chosen adjoint comparisons without unfolding their construction.
private theorem scalar_open_restriction_mate_iso
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    IsIso ((mateEquiv (ordinaryAdj B b j) (ordinaryAdj A a j)).symm
      (restrictionPush_existsUnique A B a b φ hφ j).choose.hom).natTrans := by
  let α (S : Scheme.{u}) := systemMap (ProEt.topology S) (coefficients A S)
    (transition A a S) (coefficients B S) (transition B b S)
    (levelMap A B φ S) (levelCompatibility A B a b φ hφ S)
  let L := sheafCompose (WeilConjectures.coefficientSequenceTopology (ProEt.topology X))
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  let K := sheafCompose (WeilConjectures.coefficientSequenceTopology (ProEt.topology U))
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  let s := VaryingRing.prodAdj (VaryingRing.openAdj j)
  letI := VaryingRing.prodOpenContinuous j
  have hA : IsIso (((s.sheafPushforwardContinuous (E := RingCat.{u + 1})
      (WeilConjectures.coefficientSequenceTopology (ProEt.topology U))
      (WeilConjectures.coefficientSequenceTopology (ProEt.topology X))).homEquiv
        (L.obj (ringSystem A a X)) (K.obj (ringSystem A a U))).symm
        (L.map (coefficientMap A a j))) := by
    rw [coefficientMap_forget_eq]
    exact VaryingRing.openRingTranspose_isIso A a j
  have hB : IsIso (((s.sheafPushforwardContinuous (E := RingCat.{u + 1})
      (WeilConjectures.coefficientSequenceTopology (ProEt.topology U))
      (WeilConjectures.coefficientSequenceTopology (ProEt.topology X))).homEquiv
        (L.obj (ringSystem B b X)) (K.obj (ringSystem B b U))).symm
        (L.map (coefficientMap B b j))) := by
    rw [coefficientMap_forget_eq]
    exact VaryingRing.openRingTranspose_isIso B b j
  let cA := VaryingRing.moduleAdjOfSiteAdj
    (WeilConjectures.coefficientSequenceTopology (ProEt.topology U))
    (WeilConjectures.coefficientSequenceTopology (ProEt.topology X)) s
    (S := K.obj (ringSystem A a U)) (T := L.obj (ringSystem A a X))
    (L.map (coefficientMap A a j))
  let cB := VaryingRing.moduleAdjOfSiteAdj
    (WeilConjectures.coefficientSequenceTopology (ProEt.topology U))
    (WeilConjectures.coefficientSequenceTopology (ProEt.topology X)) s
    (S := K.obj (ringSystem B b U)) (T := L.obj (ringSystem B b X))
    (L.map (coefficientMap B b j))
  let q := (restrictionPush_existsUnique A B a b φ hφ j).choose
  have hi : IsIso ((mateEquiv cB cA).symm q.hom).natTrans :=
    ringed_inverse_mate_iso s (L.map (α X)) (K.map (α U))
      (L.map (coefficientMap A a j)) (L.map (coefficientMap B b j))
      (scalarRingSquare A B a b φ hφ j) q
      (fun N V ↦ (restrictionPush_existsUnique A B a b φ hφ j).choose_spec.1
        N V.1 V.2)
  exact inverse_mate_change_isIso (ordinaryAdj B b j) cB (ordinaryAdj A a j) cA q.hom

set_option maxHeartbeats 1000000 in
-- Elaborate chosen adjoint comparisons without unfolding their construction.
private theorem scalar_open_extension_mate_iso
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    IsIso ((mateEquiv (ordinaryOpenAdj A a j) (ordinaryOpenAdj B b j)).symm
      (ellOrdinary A B a b φ hφ j).inv).natTrans := by
  let q := (restrictionPush_existsUnique A B a b φ hφ j).choose
  have he : (ellOrdinary A B a b φ hφ j).inv =
      ((mateEquiv (scalarAdj A B a b φ hφ X) (scalarAdj A B a b φ hφ U)).symm
        ((mateEquiv (ordinaryAdj B b j) (ordinaryAdj A a j)).symm q.hom)).natTrans := by
    rw [iterated_mateEquiv_conjugateEquiv_symm]
    rfl
  rw [he, iterated_mateEquiv_conjugateEquiv_symm]
  haveI := scalar_open_restriction_mate_iso A B a b φ hφ j
  change IsIso ((conjugateEquiv
    ((ordinaryOpenAdj A a j).comp (scalarAdj A B a b φ hφ X))
    ((scalarAdj A B a b φ hφ U).comp (ordinaryOpenAdj B b j))).symm
    ((mateEquiv (ordinaryAdj B b j) (ordinaryAdj A a j)).symm q.hom).natTrans)
  infer_instance

/-- The termwise scalar shift, including the signed cochain differential.
Source: Stacks 06YY (blueprint: lem-sf-system-proper-open-scalar-square). -/
instance scalarShift (X : Scheme.{u}) : (T A B a b φ hφ d hd e X).CommShift ℤ :=
  letI := extensionLimits A B a b φ hφ d hd e X
  letI := extensionColimits A B a b φ hφ d hd e X
  inferInstanceAs ((E A B a b φ hφ X).mapDerivedCategory.CommShift ℤ)

/-- Localize the uniquely normalized ordinary inverse-image/tensor identification.
Source: Stacks 03CZ, 07A4 (blueprint: lem-sf-system-proper-open-scalar-square). -/
def ell {X Y : Scheme.{u}} (f : X ⟶ Y) :
    T A B a b φ hφ d hd e Y ⋙ P B b f ≅ P A a f ⋙ T A B a b φ hφ d hd e X :=
  letI := extensionLimits A B a b φ hφ d hd e X
  letI := extensionColimits A B a b φ hφ d hd e X
  letI := extensionLimits A B a b φ hφ d hd e Y
  letI := extensionColimits A B a b φ hφ d hd e Y
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (ellOrdinary A B a b φ hφ f) ≪≫
      Functor.mapDerivedCategoryCompIso _ _

/-- The scalar direct-image comparison is exactly the inverse-image adjunction mate.
Its transpose is ell followed by tensor of the proper counit.
Source: Zheng 5.13; Stacks 07A7 (blueprint: lem-sf-system-proper-open-scalar-square). -/
def chi {X Y : Scheme.{u}} (f : X ⟶ Y) :
    R A a f ⋙ T A B a b φ hφ d hd e Y ⟶ T A B a b φ hφ d hd e X ⋙ R B b f :=
  (mateEquiv (adj A a f) (adj B b f) (ell A B a b φ hφ d hd e f).hom).natTrans

/-- The inverse of open scalar balancing is the open-unit transpose, fixing its
normalization before evaluation. Source: Stacks 03DI, 0E8I
(blueprint: lem-sf-system-proper-open-scalar-square). -/
def betaInv {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    T A B a b φ hφ d hd e U ⋙ J B b j ⟶ J A a j ⋙ T A B a b φ hφ d hd e X :=
  ((mateEquiv (jAdj A a j) (jAdj B b j)).symm
    (ell A B a b φ hφ d hd e j).inv).natTrans

/-- Open scalar balancing is invertible. Source: Stacks 03DI, 0E8I
(blueprint: lem-sf-system-proper-open-scalar-square).
Proof: restriction to the open identifies the inverse mate with the identity on local
tensors. Open tensor normalization supplies the inverse, and the open adjunction
bijection proves the two identities, on the system site before localization. -/
theorem betaInv_isIso {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    IsIso (betaInv A B a b φ hφ d hd e j) := by
  letI := extensionLimits A B a b φ hφ d hd e U
  letI := extensionColimits A B a b φ hφ d hd e U
  letI := extensionLimits A B a b φ hφ d hd e X
  letI := extensionColimits A B a b φ hφ d hd e X
  haveI : IsIso ((mateEquiv (ordinaryOpenAdj A a j) (ordinaryOpenAdj B b j)).symm
      (TwoSquare.mk _ _ _ _ (ellOrdinary A B a b φ hφ j).symm.hom)).natTrans :=
    scalar_open_extension_mate_iso A B a b φ hφ j
  have hi := exact_inverse_mate_isIso (ordinaryOpenAdj A a j) (ordinaryOpenAdj B b j)
    (ellOrdinary A B a b φ hφ j).symm
  simpa only [betaInv, jAdj, J, T, P, ell, TwoSquare.mk,
    Functor.mapDerivedCategorySquareIso, Iso.symm_hom,
    Iso.trans_hom, Iso.trans_inv, Functor.mapDerivedCategoryNatIso_symm,
    Iso.symm_inv, Category.assoc] using hi

/-- Canonical open tensor balancing, with the new coefficient system as second factor.
Source: Stacks 0E8I (blueprint: lem-sf-system-proper-open-scalar-square). -/
def beta {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    J A a j ⋙ T A B a b φ hφ d hd e X ≅ T A B a b φ hφ d hd e U ⋙ J B b j :=
  (@asIso _ _ _ _ (betaInv A B a b φ hφ d hd e j)
    (betaInv_isIso A B a b φ hφ d hd e j)).symm

end AlgebraicGeometry.ProEtale.SemilinearProperOpen.Scalar
