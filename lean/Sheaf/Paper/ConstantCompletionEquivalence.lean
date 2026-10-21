/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q13
-/
module

public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Sheaf.Paper.FlatRingedIdealCompleteEquivalence
public import Sheaf.CategoryTheory.RingedKoszulSystem
public import Sheaf.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Sheaf.Paper.RingedSiteIdeal
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.CategoryTheory.Sites.Over
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.LocallyDerivedRingedIdealComplete
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import Sheaf.Algebra.Homology.KFlat
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Finiteness.Defs
import Sheaf.Paper.RingedTopoiTensorSections
import Sheaf.Algebra.Category.ModuleCat.Sheaf.ExtensionTensorComparison
import all Sheaf.CategoryTheory.RingedTowerPushforwardLimitComparison
import Mathlib.CategoryTheory.Adjunction.Whiskering
import Mathlib.CategoryTheory.Adjunction.Additive
import Sheaf.Paper.RingedTopoiDerivedPullback
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimit

import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
/-!
# Constant coefficients and their sheafwise adic completion

Source: Stacks Project, Tags 093M, 099I, 099L, 099M, 0A0E, 06YY and 0940
(blueprint: lem-weil-pbc-constant-completion-equivalence).

Positive exponents are indexed by `n : ℕ`, meaning `n+1`. All localizations below use
Mathlib's standard derived category. The extra names only specify the canonical objects,
strict towers and representative normalizations in this node; they introduce no replacement
for sheaves, tensor products, derived internal Hom or local completeness.
-/

@[expose] public noncomputable section

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

namespace CategoryTheory.ConstantCompletion

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
variable (A : Type u) [CommRing A] (I : Ideal A)

/-- The constant ring sheaf. Source: Stacks 099L
(blueprint: lem-weil-pbc-constant-completion-equivalence). -/
abbrev constant : Sheaf J CommRingCat.{u} :=
  (constantSheaf J CommRingCat.{u}).obj (CommRingCat.of A)

/-- The finite coefficient sheaf at exponent n+1. Source: Stacks 099L
(blueprint: lem-weil-pbc-constant-completion-equivalence). -/
abbrev finite (n : ℕ) : Sheaf J CommRingCat.{u} :=
  constant J (A ⧸ I ^ (n + 1))

/-- The quotient map of constant ring sheaves. Source: Stacks 099L
(blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def quotient (n : ℕ) : constant J A ⟶ finite J A I n :=
  (constantSheaf J CommRingCat.{u}).map (CommRingCat.ofHom (Ideal.Quotient.mk _))

/-- The finite quotient transition. Source: Stacks 099L
(blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def transition (n : ℕ) : finite J A I (n + 1) ⟶ finite J A I n :=
  (constantSheaf J CommRingCat.{u}).map
    (CommRingCat.ofHom (Ideal.Quotient.factorPow I (Nat.le_succ (n + 1))))

/-- The actual inverse sequence of finite constant ring sheaves. Source: Stacks 099L
(blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def finiteSystem : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{u} :=
  Functor.ofOpSequence (transition J A I)

/-- The sheafwise completion, as the limit of the specified sequence. Source: Stacks 093M
(blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def completed : Sheaf J CommRingCat.{u} := limit (finiteSystem J A I)

/-- The canonical finite projection. Source: Stacks 093M
(blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def projection (n : ℕ) : completed J A I ⟶ finite J A I n :=
  limit.π (finiteSystem J A I) (op n)

/-- Quotient maps form a cone. Source: Stacks 093M
(blueprint: lem-weil-pbc-constant-completion-equivalence).
Proof: both composites are the image under constant sheafification of the quotient map
A → A/I^(n+1); use factorPow_comp_mk and functoriality. -/
theorem quotient_step (n : ℕ) :
    ((Functor.const ℕᵒᵖ).obj (constant J A)).map (homOfLE (Nat.le_succ n)).op ≫
        quotient J A I n =
      quotient J A I (n + 1) ≫ (finiteSystem J A I).map (homOfLE (Nat.le_succ n)).op := by
  simp only [Functor.const_obj_map, finiteSystem,
    Functor.ofOpSequence_map_homOfLE_succ]
  change _ = (constantSheaf J CommRingCat).map _ ≫ (constantSheaf J CommRingCat).map _
  rw [← Functor.map_comp]
  congr 1

/-- The quotient cone, using the actual quotient maps. Source: Stacks 093M
(blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def quotientCone : Cone (finiteSystem J A I) where
  pt := constant J A
  π := NatTrans.ofOpSequence (quotient J A I) (quotient_step J A I)

/-- The canonical map from constant to completed coefficients. Source: Stacks 093M
(blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def coefficientMap : constant J A ⟶ completed J A I :=
  limit.lift _ (quotientCone J A I)

attribute [local irreducible] completed

variable {J A I}

/-- The existing category of module sheaves, with commutativity forgotten.
Source: Stacks 099L (blueprint: lem-weil-pbc-constant-completion-equivalence). -/
abbrev Mod (O : Sheaf J CommRingCat.{u}) := ringedSiteModules.{u} (siteModuleRings O)

/-- Cochain complexes of these module sheaves. Source: Stacks 099L
(blueprint: lem-weil-pbc-constant-completion-equivalence). -/
abbrev Cx (O : Sheaf J CommRingCat.{u}) := CochainComplex (Mod O) ℤ

/-- The standard derived localization, rather than an additional size hypothesis.
Source: Stacks 099L (blueprint: lem-weil-pbc-constant-completion-equivalence). -/
abbrev D (O : Sheaf J CommRingCat.{u}) :=
  @DerivedCategory (Mod O) _ _ (HasDerivedCategory.standard _)

/-- The standard localization functor. Source: Stacks 099L
(blueprint: lem-weil-pbc-constant-completion-equivalence). -/
abbrev Q (O : Sheaf J CommRingCat.{u}) : Cx O ⥤ D O :=
  @DerivedCategory.Q (Mod O) _ _ (HasDerivedCategory.standard _)

/-- Ordinary restriction of scalars, exactly Mathlib's functor. Source: Stacks 099I
(blueprint: lem-weil-pbc-constant-completion-equivalence). -/
abbrev res {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) : Mod B ⥤ Mod R :=
  SheafOfModules.restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)

/-- Exact derived restriction of scalars. Source: Stacks 099I
(blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def dres {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) : D B ⥤ D R :=
  letI := HasDerivedCategory.standard (Mod R)
  letI := HasDerivedCategory.standard (Mod B)
  siteDerivedRestrictScalars φ

/-- Constant global sections supplied by the sheafification unit. Source: Stacks 093M
(blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def constantSection (a : A) : ((constant J A).obj ⋙ forget CommRingCat).sections :=
  ⟨fun U ↦ (toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))).app U a,
    fun f ↦ ConcreteCategory.congr_hom
      ((toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))).naturality f) a |>.symm⟩

/-- Images of constant sections in a coefficient algebra. Source: Stacks 093M
(blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def algebraSection {O : Sheaf J CommRingCat.{u}} (φ : constant J A ⟶ O) (a : A) :
    (O.obj ⋙ forget CommRingCat).sections :=
  ⟨fun U ↦ φ.hom.app U ((constantSection (J := J) a).val U),
    fun f ↦ (ConcreteCategory.congr_hom (φ.hom.naturality f) _).symm.trans
      (congrArg (φ.hom.app _) ((constantSection (J := J) a).property f))⟩

/-- The kernel of a ring-sheaf map is a genuine ideal subsheaf with these sections.
Source: Stacks 093M (blueprint: lem-weil-pbc-constant-completion-equivalence).
Proof: ring-map kernels are ideals; naturality preserves them. A section whose image
vanishes on a covering sieve has zero image by separatedness of the target sheaf.
The sections formula determines the ideal subsheaf uniquely, by proof irrelevance. -/
theorem kernelIdeal_existsUnique {O S : Sheaf J CommRingCat.{u}} (q : O ⟶ S) :
    ∃! K : RingedSiteIdeal O,
      ∀ U : C, K.sections U = RingHom.ker (q.hom.app (op U)).hom := by
  let K : RingedSiteIdeal O :=
    { sections := fun U ↦ RingHom.ker (q.hom.app (op U)).hom
      restriction := by
        intro U V g a ha
        change q.hom.app (op V) (O.obj.map g.op a) = 0
        have h := ConcreteCategory.congr_hom (q.hom.naturality g.op) a
        change q.hom.app (op V) (O.obj.map g.op a) =
          S.obj.map g.op (q.hom.app (op U) a) at h
        rw [h, ha, map_zero]
      local_mem := by
        intro U a T hT ha
        change q.hom.app (op U) a = 0
        have hS : Presieve.IsSheaf J (S.obj ⋙ forget CommRingCat) :=
          (isSheaf_iff_isSheaf_of_type J _).mp
            ((sheafCompose J (forget CommRingCat)).obj S).property
        apply (hS.isSeparated T hT).ext
        intro V g hg
        change S.obj.map g.op (q.hom.app (op U) a) = S.obj.map g.op 0
        have h := ConcreteCategory.congr_hom (q.hom.naturality g.op) a
        change q.hom.app (op V) (O.obj.map g.op a) =
          S.obj.map g.op (q.hom.app (op U) a) at h
        rw [← h, map_zero]
        exact ha V g hg }
  refine ⟨K, fun _ ↦ rfl, ?_⟩
  intro L hL
  have h : L.sections = K.sections := funext hL
  have hext (M N : RingedSiteIdeal O) (h : M.sections = N.sections) : M = N := by
    cases M
    cases N
    dsimp only at h
    cases h
    rfl
  exact hext L K h

/-- The specified kernel ideal subsheaf, selected by its unique sections formula.
Source: Stacks 093M (blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def kernelIdeal {O S : Sheaf J CommRingCat.{u}} (q : O ⟶ S) : RingedSiteIdeal O :=
  (kernelIdeal_existsUnique q).exists.choose

/-- The existing local internal-Hom completeness predicate, at the standard localization.
Source: Stacks 0999, 099I (blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def IsComplete {O S : Sheaf J CommRingCat.{u}} (q : O ⟶ S) (M : D O) : Prop :=
  @IsLocallyDerivedRingedIdealComplete C _ J O
    (HasDerivedCategory.standard _)
    (fun _ ↦ HasDerivedCategory.standard _)
    (kernelIdeal q).module (kernelIdeal q).inclusion M

/-- Flatness and every canonical quotient identification for the sheafwise completion.
Source: Stacks 093M (blueprint: lem-weil-pbc-constant-completion-equivalence).
Proof: the constant-module section theorem gives flat A/I^n sections and surjective
transitions. The flat inverse-limit theorem makes the limit flat over A on each object;
flat sheafification makes it flat over the constant ring sheaf. The tensor-limit theorem
with the finite module A/I^n identifies the projection quotient with the constant finite
sheaf, sectionwise. Its kernel is generated by the images of I^n and its projection is
surjective. These identifications are the original projections, so respect transitions. -/
theorem flat_and_quotients (J : GrothendieckTopology C) (A : Type u) [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) :
    SheafOfModules.IsFlat
      ((res (coefficientMap J A I)).obj (SheafOfModules.unit
        (siteModuleRings (completed J A I)))) ∧
    (∀ (n : ℕ) (U : C),
      Function.Surjective ((projection J A I n).hom.app (op U)) ∧
      RingHom.ker ((projection J A I n).hom.app (op U)).hom =
        Ideal.span (Set.range (fun a : ↥(I ^ (n + 1)) ↦
          (algebraSection (coefficientMap J A I) a).val (op U)))) ∧
    (∀ (n : ℕ) (U : C),
      Function.Surjective ((quotient J A I n).hom.app (op U)) ∧
      RingHom.ker ((quotient J A I n).hom.app (op U)).hom =
        Ideal.span (Set.range (fun a : ↥(I ^ (n + 1)) ↦
          (constantSection (J := J) (a : A)).val (op U)))) := by
  sorry

section CoefficientIdeal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem extension_eq_of_span {R B : Sheaf J CommRingCat.{u}}
    (φ : R ⟶ B) (K : RingedSiteIdeal R) (L : RingedSiteIdeal B)
    (h : ∀ U, L.sections U =
      Ideal.span (Set.range (fun a : K.sections U ↦ φ.hom.app (op U) a))) :
    K.extension φ = L := by
  apply ((K.existsUnique_extension φ).unique ?_ ?_)
  · exact (K.existsUnique_extension φ).exists.choose_spec
  · intro U b
    constructor
    · intro hb
      refine ⟨⊤, J.top_mem _, ?_⟩
      intro V g _
      rw [← h V]
      exact L.restriction g b hb
    · rintro ⟨S, hS, hb⟩
      exact L.local_mem U b S hS (fun V g hg ↦ by rw [h V]; exact hb V g hg)

private theorem coefficientKernel_extension (A : Type u) [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) :
    (kernelIdeal (quotient J A I 0)).extension (coefficientMap J A I) =
      kernelIdeal (projection J A I 0) := by
  let φ := coefficientMap J A I
  let K := kernelIdeal (quotient J A I 0)
  let L := kernelIdeal (projection J A I 0)
  apply extension_eq_of_span φ K L
  intro U
  have hK : K.sections U = RingHom.ker ((quotient J A I 0).hom.app (op U)).hom :=
    (kernelIdeal_existsUnique (quotient J A I 0)).exists.choose_spec U
  have hL : L.sections U = RingHom.ker ((projection J A I 0).hom.app (op U)).hom :=
    (kernelIdeal_existsUnique (projection J A I 0)).exists.choose_spec U
  rw [hL, ((flat_and_quotients J A I).2.1 0 U).2]
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨a, rfl⟩
    apply Ideal.subset_span
    refine ⟨⟨(constantSection (J := J) a.val).val (op U), ?_⟩, rfl⟩
    rw [hK, ((flat_and_quotients J A I).2.2 0 U).2]
    exact Ideal.subset_span ⟨a, rfl⟩
  · apply Ideal.span_le.mpr
    rintro _ ⟨a, rfl⟩
    have ha : a.val ∈ Ideal.span (Set.range (fun b : ↥(I ^ (0 + 1)) ↦
        (constantSection (J := J) (b : A)).val (op U))) := by
      rw [← ((flat_and_quotients J A I).2.2 0 U).2, ← hK]
      exact a.property
    change φ.hom.app (op U) a.val ∈ _
    have hle : Ideal.span (Set.range (fun b : ↥(I ^ (0 + 1)) ↦
        (constantSection (J := J) (b : A)).val (op U))) ≤
        Ideal.comap (φ.hom.app (op U)).hom
          (Ideal.span (Set.range (fun b : ↥(I ^ (0 + 1)) ↦
            (algebraSection φ b).val (op U)))) := by
      apply Ideal.span_le.mpr
      rintro _ ⟨b, rfl⟩
      exact Ideal.subset_span ⟨b, rfl⟩
    exact hle ha

private theorem coefficientKernel_quotient (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) :
    (kernelIdeal (quotient J A I 0)).IsQuotientIso (coefficientMap J A I) := by
  let φ := coefficientMap J A I
  let K := kernelIdeal (quotient J A I 0)
  have he := coefficientKernel_extension (J := J) A I
  have hk (U : C) : K.sections U =
      RingHom.ker ((quotient J A I 0).hom.app (op U)).hom :=
    (kernelIdeal_existsUnique (quotient J A I 0)).exists.choose_spec U
  have hl (U : C) : (K.extension φ).sections U =
      RingHom.ker ((projection J A I 0).hom.app (op U)).hom := by
    rw [he]
    exact (kernelIdeal_existsUnique (projection J A I 0)).exists.choose_spec U
  have hc (U : C) (a : (constant J A).obj.obj (op U)) :
      (projection J A I 0).hom.app (op U) (φ.hom.app (op U) a) =
        (quotient J A I 0).hom.app (op U) a := by
    exact congrArg (fun f ↦ f.hom.app (op U) a)
      (limit.lift_π (quotientCone J A I) (op 0))
  constructor
  · intro U a
    rw [hl, hk]
    change (projection J A I 0).hom.app (op U) (φ.hom.app (op U) a) = 0 ↔
      (quotient J A I 0).hom.app (op U) a = 0
    rw [hc]
  · intro U b
    refine ⟨⊤, J.top_mem _, ?_⟩
    intro V g _
    obtain ⟨a, ha⟩ := ((flat_and_quotients J A I).2.2 0 V).1
      ((projection J A I 0).hom.app (op V) ((completed J A I).obj.map g.op b))
    refine ⟨a, ?_⟩
    rw [hl]
    change (projection J A I 0).hom.app (op V)
      ((completed J A I).obj.map g.op b - φ.hom.app (op V) a) = 0
    rw [map_sub, hc, ha, sub_self]
private theorem ideal_generated_global_sections
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) (I : RingedSiteIdeal R)
    (r : ℕ) (b : Fin r → (R.obj ⋙ CategoryTheory.forget CommRingCat).sections)
    (hs : ∀ U : C, I.sections U =
      Ideal.span (Set.range (fun i ↦ (b i).val (op U)))) :
    ∃ σ : I.module.GeneratingSections, ∃ e : σ.I ≃ Fin r,
      ∀ i : σ.I, SheafOfModules.sectionsMap I.inclusion (σ.s i) = b (e i) := by
  classical
  let s (i : ULift.{u} (Fin r)) : I.module.sections :=
    { val := fun U ↦ ⟨(b i.down).val U, by
        rw [hs]
        exact Ideal.subset_span ⟨i.down, rfl⟩⟩
      property := by
        intro U V f
        apply Subtype.ext
        exact (b i.down).property f }
  let π := I.module.freeHomEquiv.symm s
  have hπ : Epi π := by
    constructor
    intro M f g hfg
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    let x' : I.sections U.unop := x
    have hx : (x' : R.obj.obj U) ∈
        Ideal.span (Set.range (fun i ↦ (b i).val U)) := by
      rw [← hs]
      exact x'.property
    have hgen (i : ULift.{u} (Fin r)) :
        f.val.app U (s i |>.val U) = g.val.app U (s i |>.val U) := by
      have h := congrArg (fun k ↦
        (SheafOfModules.sectionsMap k (SheafOfModules.freeSection i)).val U) hfg
      dsimp only [π] at h
      have h' := h
      simp only [SheafOfModules.sectionsMap_comp,
        SheafOfModules.sectionsMap_freeHomEquiv_symm_freeSection] at h
      exact h
    have hind : ∀ (y : R.obj.obj U),
        y ∈ Ideal.span (Set.range (fun i ↦ (b i).val U)) →
        ∀ hy : y ∈ I.sections U.unop,
          f.val.app U ⟨y, hy⟩ = g.val.app U ⟨y, hy⟩ := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
          rcases hy with ⟨i, rfl⟩
          intro hi
          exact hgen ⟨i⟩
      | zero =>
          intro hzero
          change f.val.app U 0 = g.val.app U 0
          simp only [map_zero]
      | add y z hy hz ihy ihz =>
          intro hsum
          change f.val.app U (⟨y, by rw [hs]; exact hy⟩ +
              ⟨z, by rw [hs]; exact hz⟩) = _
          rw [map_add, ihy, ihz]
          exact (map_add (g.val.app U).hom _ _).symm
      | smul c y hy ih =>
          intro hprod
          change f.val.app U (c • ⟨y, by rw [hs]; exact hy⟩) = _
          rw [map_smul, ih]
          exact (map_smul (g.val.app U).hom c _).symm
    exact hind x'.val hx x'.property
  refine ⟨{ I := ULift.{u} (Fin r), s := s, epi := hπ }, Equiv.ulift, ?_⟩
  intro i
  rfl


private def overIdeal {R : Sheaf J CommRingCat.{u}} (K : RingedSiteIdeal R) (U : C) :
    RingedSiteIdeal (R.over U) where
  sections V := K.sections V.left
  restriction g a ha := K.restriction g.left a ha
  local_mem V a S hS ha :=
    K.local_mem V.left a (Sieve.overEquiv V S) ((J.mem_over_iff S).mp hS)
      (fun W g hg ↦ ha (Over.mk (g ≫ V.hom)) (Over.homMk g)
        ((Sieve.overEquiv_iff S g).mp hg))

private theorem ideal_finiteType_of_span {R : Sheaf J CommRingCat.{u}}
    (K : RingedSiteIdeal R) (r : ℕ)
    (b : Fin r → (R.obj ⋙ CategoryTheory.forget CommRingCat).sections)
    (hs : ∀ U : C, K.sections U = Ideal.span (Set.range (fun i ↦ (b i).val (op U)))) :
    SheafOfModules.IsFiniteType.{u, u, u} K.module := by
  let bs (U : C) (i : Fin r) :
      ((R.over U).obj ⋙ CategoryTheory.forget CommRingCat).sections :=
    { val := fun V ↦ (b i).val (op V.unop.left)
      property := fun f ↦ (b i).property ((Over.forget U).op.map f) }
  have hg (U : C) := ideal_generated_global_sections (R.over U) (overIdeal K U)
    r (bs U) (fun V ↦ hs V.left)
  let σ (U : C) : (K.module.over U).GeneratingSections := (hg U).choose
  have hσ (U : C) : (σ U).IsFiniteType := by
    obtain ⟨e, _⟩ := (hg U).choose_spec
    exact ⟨Finite.of_equiv (Fin r) e.symm⟩
  let q : SheafOfModules.LocalGeneratorsData.{u} K.module :=
    { I := C
      X := id
      coversTop := fun _ ↦ GrothendieckTopology.covering_of_eq_top J (by simp)
      generators := σ }
  constructor
  refine ⟨q, ?_⟩
  exact { isFiniteType := hσ }

private theorem span_subtype_images
    {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)
    (I : Ideal A) {ι : Type*} (a : ι → A) (ha : Ideal.span (Set.range a) = I) :
    Ideal.span (Set.range (fun x : I ↦ f x)) =
      Ideal.span (Set.range (fun i ↦ f (a i))) := by
  have h : Ideal.span (Set.range (fun x : I ↦ f x)) = Ideal.map f I := by
    unfold Ideal.map
    congr 1
    ext x
    simp only [Set.mem_range, Set.mem_image, SetLike.mem_coe]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, y.property, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
  rw [h, ← ha, Ideal.map_span]
  congr 1
  ext y
  simp only [Set.mem_image, Set.mem_range]
  constructor
  · rintro ⟨z, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨a i, ⟨i, rfl⟩, rfl⟩


private theorem coefficientKernel_finiteType (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) :
    SheafOfModules.IsFiniteType.{u, u, u} (kernelIdeal (quotient J A I 0)).module := by
  obtain ⟨r, a, ha⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    I.fg_of_isNoetherianRing
  apply ideal_finiteType_of_span (kernelIdeal (quotient J A I 0)) r
    (fun i ↦ constantSection (J := J) (a i))
  intro U
  have hk : (kernelIdeal (quotient J A I 0)).sections U =
      RingHom.ker ((quotient J A I 0).hom.app (op U)).hom :=
    (kernelIdeal_existsUnique (quotient J A I 0)).exists.choose_spec U
  rw [hk, ((flat_and_quotients J A I).2.2 0 U).2]
  let f : A →+* (constant J A).obj.obj (op U) :=
    ((toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))).app (op U)).hom
  exact span_subtype_images f (I ^ (0 + 1)) a
    (by simpa only [Nat.zero_add, pow_one] using ha)

end CoefficientIdeal

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Restriction along the canonical completion map gives the asserted equivalence.
Source: Stacks 099I and the opening of 099L
(blueprint: lem-weil-pbc-constant-completion-equivalence).
Proof: flat_and_quotients gives flatness and the quotient isomorphism modulo I. The
constant ideal is finite type since A is Noetherian. Apply the general flat ringed-ideal
complete equivalence. The kernel ideals in IsComplete are exactly I and I times the
completed ring by the preceding sections formulas. Its ambient functor is dres. -/
theorem equivalence (J : GrothendieckTopology C) (A : Type u) [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) :
    ∃ e : ObjectProperty.FullSubcategory (IsComplete (projection J A I 0)) ≌
        ObjectProperty.FullSubcategory (IsComplete (quotient J A I 0)),
      Nonempty (e.functor ⋙ ObjectProperty.ι (IsComplete (quotient J A I 0)) ≅
        ObjectProperty.ι (IsComplete (projection J A I 0)) ⋙ dres (coefficientMap J A I)) := by
  let := HasDerivedCategory.standard (Mod (constant J A))
  let := HasDerivedCategory.standard (Mod (completed J A I))
  let (U : C) := HasDerivedCategory.standard (Mod ((constant J A).over U))
  let (U : C) := HasDerivedCategory.standard (Mod ((completed J A I).over U))
  have h := flat_ringed_ideal_complete_equivalence
    (coefficientMap J A I) (kernelIdeal (quotient J A I 0))
    (coefficientKernel_finiteType (J := J) A I) (flat_and_quotients J A I).1
    (coefficientKernel_quotient (J := J) A I)
  rw [coefficientKernel_extension (J := J) A I] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Sectionwise scalar extension before sheafification, with the standard module maps. -/
private def scalarPresheaf {R S : Sheaf J CommRingCat.{u}} (φ : R ⟶ S) :
    Mod R ⥤ PresheafOfModules.{u} (siteModuleRings S).obj where
  obj := SheafOfModules.changeOfRingsPresheaf.{u, u, u} φ
  map f :=
    { app := fun U ↦ (ModuleCat.extendScalars (φ.hom.app U).hom).map (f.val.app U)
      naturality := SheafOfModules.changeOfRingsHom_naturality φ _ f }
  map_id M := by
    ext U : 1
    exact (ModuleCat.extendScalars (φ.hom.app U).hom).map_id _
  map_comp f g := by
    ext U : 1
    exact (ModuleCat.extendScalars (φ.hom.app U).hom).map_comp _ _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The ordinary scalar-extension map respects identities and composition.
Source: Stacks 06YY (blueprint: lem-weil-pbc-constant-completion-equivalence).
Proof: before sheafification these are the identity and composition laws of the
sectionwise extension-of-scalars functors. Sheafification preserves those equations. -/
theorem change_laws {R S : Sheaf J CommRingCat.{u}} (φ : R ⟶ S) :
    (∀ M : Mod R, SheafOfModules.changeOfRingsHom.{u, u, u} φ M (𝟙 M) = 𝟙 _) ∧
    (∀ (M N L : Mod R) (f : M ⟶ N) (g : N ⟶ L),
      SheafOfModules.changeOfRingsHom.{u, u, u} φ M (f ≫ g) =
        SheafOfModules.changeOfRingsHom.{u, u, u} φ M f ≫
          SheafOfModules.changeOfRingsHom.{u, u, u} φ N g) := by
  let F := scalarPresheaf φ ⋙
    PresheafOfModules.sheafification (𝟙 (siteModuleRings S).obj)
  exact ⟨fun M ↦ F.map_id M, fun _ _ _ f g ↦ F.map_comp f g⟩

/-- The additive ordinary scalar extension, with the recorded objects and maps.
Source: Stacks 06YY (blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def change {R S : Sheaf J CommRingCat.{u}} (φ : R ⟶ S) : Mod R ⥤ Mod S where
  obj := SheafOfModules.changeOfRings.{u, u, u} φ
  map := SheafOfModules.changeOfRingsHom.{u, u, u} φ _
  map_id := (change_laws φ).1
  map_comp f g := (change_laws φ).2 _ _ _ f g

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Ordinary scalar extension is additive.
Source: Stacks 06YY (blueprint: lem-weil-pbc-constant-completion-equivalence).
Proof: sectionwise scalar extension is additive by its ordinary module adjunction.
Module sheafification is additive by its adjunction to additive restriction and forgetful
functors. Their composite has exactly the objects and maps defining change. -/
theorem change_additive {R S : Sheaf J CommRingCat.{u}} (φ : R ⟶ S) :
    (change φ).Additive := by
  have (U : Cᵒᵖ) : (ModuleCat.extendScalars (φ.hom.app U).hom).Additive :=
    (ModuleCat.extendRestrictScalarsAdj (φ.hom.app U).hom).left_adjoint_additive
  have : (scalarPresheaf φ).Additive := by
    constructor
    intro M N f g
    ext U : 1
    exact (ModuleCat.extendScalars (φ.hom.app U).hom).map_add
  have : (PresheafOfModules.sheafification (𝟙 (siteModuleRings S).obj)).Additive :=
    (PresheafOfModules.sheafificationAdjunction (𝟙 (siteModuleRings S).obj)).left_adjoint_additive
  let F := scalarPresheaf φ ⋙
    PresheafOfModules.sheafification (𝟙 (siteModuleRings S).obj)
  constructor
  intro M N f g
  exact F.map_add

attribute [instance] change_additive

set_option genSizeOf false in
set_option genInjectivity false in
/-- The derived scalar-extension universal property and K-flat computation.
This packages an existing notion, with its universal comparison retained.
Source: Stacks 06YY (blueprint: lem-weil-pbc-constant-completion-equivalence). -/
structure DerivedExtension {R S : Sheaf J CommRingCat.{u}} (φ : R ⟶ S) where
  functor : D R ⥤ D S
  comparison : Q R ⋙ functor ⟶
    (change φ).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ Q S
  universal : functor.IsLeftDerivedFunctor comparison
    (HomologicalComplex.quasiIso (Mod R) (ComplexShape.up ℤ))
  computation : ∀ P : Cx R, P.IsAcyclicTensorKFlat → IsIso (comparison.app P)

/-- The recorded derived change-of-rings theorem supplies this universally specified pair.
Source: Stacks 06YY (blueprint: lem-weil-pbc-constant-completion-equivalence).
Proof: use derivedChangeOfRingsIndependentCoefficients with the standard localizations.
Identify its ordinary tensor witness with change on objects and maps. Compose its
homotopy counit with quotientCompQhIso and mapHomotopyCategoryFactors. The composite
localization universal property gives the complex-level universal property, and its
K-flat computation transports across those factorization isomorphisms. -/
theorem derivedExtension_exists {R S : Sheaf J CommRingCat.{u}} (φ : R ⟶ S) :
    Nonempty (DerivedExtension φ) := by
  let := HasDerivedCategory.standard (Mod R)
  let := HasDerivedCategory.standard (Mod S)
  obtain ⟨E, hobj, hmap, hpres, T, hpw, ε, huniv, htri, hcomp⟩ :=
    (SheafOfModules.nonempty_derivedChangeOfRingsCochainModel φ).some
  have hE : E = change φ := Functor.ext hobj (fun _ _ f ↦ hmap f)
  subst E
  exact ⟨{ functor := T
           comparison := ε
           universal := huniv
           computation := fun P hP ↦ hcomp P
             ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).2 hP) }⟩

/-- Select the universal derived pair, which is determined up to its unique normalized
natural isomorphism; no arbitrary tensor functor is chosen. Source: Stacks 06YY
(blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def derivedExtension {R S : Sheaf J CommRingCat.{u}} (φ : R ⟶ S) : DerivedExtension φ :=
  Classical.choice (derivedExtension_exists φ)

attribute [local irreducible] derivedExtension

/-- The specified derived extension of scalars. Source: Stacks 06YY
(blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def extend {R S : Sheaf J CommRingCat.{u}} (φ : R ⟶ S) : D R ⥤ D S :=
  (derivedExtension φ).functor

/-- Its universal computation comparison on complexes. Source: Stacks 06YY
(blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def extendComparison {R S : Sheaf J CommRingCat.{u}} (φ : R ⟶ S) :
    Q R ⋙ extend φ ⟶ (change φ).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ Q S :=
  (derivedExtension φ).comparison


/-- The scalar-extension insertion on sections, including the sheafification unit.
The target is the sheafification defining the actual scalar-extension tensor functor.
Source: Stacks 06YY (blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def tensorSection {R S : Sheaf J CommRingCat.{u}} (φ : R ⟶ S) (M : Mod R)
    (U : Cᵒᵖ) (s : S.obj.obj U) (m : M.val.obj U) : ((change φ).obj M).val.obj U :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 (siteModuleRings S).obj)).unit.app
      (SheafOfModules.changeOfRingsPresheaf.{u, u, u} φ M)).app U
        (s ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] m)

section ScalarTransitions
variable {R S T : Sheaf J CommRingCat.{u}}

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private def resCompIso (φ : R ⟶ S) (τ : S ⟶ T) (ψ : R ⟶ T) (h : φ ≫ τ = ψ) :
    res τ ⋙ res φ ≅ res ψ := by
  subst ψ
  refine NatIso.ofComponents (fun M ↦ ?_) ?_
  · refine { hom := { val := { app := fun U ↦ ?_, naturality := ?_ } }
             inv := { val := { app := fun U ↦ ?_, naturality := ?_ } }
             hom_inv_id := ?_
             inv_hom_id := ?_ }
    · exact ModuleCat.ofHom
        (X := ((res φ).obj ((res τ).obj M)).val.obj U)
        (Y := ((res (φ ≫ τ)).obj M).val.obj U)
        { toFun := fun m ↦ m
          map_add' := fun _ _ ↦ rfl
          map_smul' := fun _ _ ↦ rfl }
    · intros; ext; rfl
    · exact ModuleCat.ofHom
        (X := ((res (φ ≫ τ)).obj M).val.obj U)
        (Y := ((res φ).obj ((res τ).obj M)).val.obj U)
        { toFun := fun m ↦ m
          map_add' := fun _ _ ↦ rfl
          map_smul' := fun _ _ ↦ rfl }
    · intros; ext; rfl
    · ext; rfl
    · ext; rfl
  · intros; ext; rfl

private def transitionLift (φ : R ⟶ S) (τ : S ⟶ T) (ψ : R ⟶ T) (h : φ ≫ τ = ψ)
    (M : Mod R) : (change φ).obj M ⟶ (res τ).obj ((change ψ).obj M) :=
  (SheafOfModules.RingedTensor.tensorHomEquiv φ _ _).symm
    (SheafOfModules.RingedTensor.tensorHomEquiv ψ M _ (𝟙 _) ≫
      (resCompIso φ τ ψ h).inv.app ((change ψ).obj M))

private theorem transitionLift_one (φ : R ⟶ S) (τ : S ⟶ T) (ψ : R ⟶ T) (h : φ ≫ τ = ψ)
    (M : Mod R) (U : Cᵒᵖ) (m : M.val.obj U) :
    (transitionLift φ τ ψ h M).val.app U (tensorSection φ M U 1 m) =
      tensorSection ψ M U 1 m := by
  have hh := (SheafOfModules.RingedTensor.tensorHomEquiv φ _ _).apply_symm_apply
    (SheafOfModules.RingedTensor.tensorHomEquiv ψ M _ (𝟙 _) ≫
      (resCompIso φ τ ψ h).inv.app ((change ψ).obj M))
  subst ψ
  change (transitionLift φ τ (φ ≫ τ) rfl M).val.app U (tensorSection φ M U 1 m) = _
  exact congrArg (fun k ↦ k.val.app U m) hh

private theorem tensorSection_smul (φ : R ⟶ S) (M : Mod R)
    (U : Cᵒᵖ) (s : S.obj.obj U) (m : M.val.obj U) :
    tensorSection φ M U s m = s • tensorSection φ M U 1 m := by
  let η := (PresheafOfModules.sheafificationAdjunction (𝟙 (siteModuleRings S).obj)).unit.app
    (SheafOfModules.changeOfRingsPresheaf.{u, u, u} φ M)
  have h := (η.app U).hom.map_smul s
    ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] m)
  change η.app U ((s * 1) ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] m) = _ at h
  rw [mul_one] at h
  exact h

private theorem transitionLift_tmul (φ : R ⟶ S) (τ : S ⟶ T) (ψ : R ⟶ T)
    (h : φ ≫ τ = ψ) (M : Mod R) (U : Cᵒᵖ) (s : S.obj.obj U) (m : M.val.obj U) :
    (transitionLift φ τ ψ h M).val.app U (tensorSection φ M U s m) =
      tensorSection ψ M U (τ.hom.app U s) m := by
  rw [tensorSection_smul φ, map_smul, transitionLift_one,
    tensorSection_smul ψ M U (τ.hom.app U s)]
  rfl

private theorem tensorSection_map (φ : R ⟶ S) {M N : Mod R} (f : M ⟶ N)
    (U : Cᵒᵖ) (s : S.obj.obj U) (m : M.val.obj U) :
    ((change φ).map f).val.app U (tensorSection φ M U s m) =
      tensorSection φ N U s (f.val.app U m) := by
  let η := (PresheafOfModules.sheafificationAdjunction (𝟙 (siteModuleRings S).obj)).unit
  let k : SheafOfModules.changeOfRingsPresheaf.{u, u, u} φ M ⟶
      SheafOfModules.changeOfRingsPresheaf.{u, u, u} φ N :=
    { app := fun V ↦ (ModuleCat.extendScalars (φ.hom.app V).hom).map (f.val.app V)
      naturality := SheafOfModules.changeOfRingsHom_naturality φ M f }
  have h := congrArg (fun t ↦ t.app U
    (s ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] m)) (η.naturality k)
  change tensorSection φ N U s (f.val.app U m) =
    ((change φ).map f).val.app U (tensorSection φ M U s m) at h
  exact h.symm

private theorem restrictedTensor_hom_ext (φ : R ⟶ S) (M : Mod R) (N : Mod R)
    (f g : (res φ).obj ((change φ).obj M) ⟶ N)
    (h : ∀ U s m, f.val.app U (tensorSection φ M U s m) =
      g.val.app U (tensorSection φ M U s m)) : f = g := by
  apply (SheafOfModules.toSheaf (siteModuleRings R)).map_injective
  apply ((sheafificationAdjunction J AddCommGrpCat).homEquiv
    (SheafOfModules.changeOfRingsPresheaf.{u, u, u} φ M).presheaf
    ((SheafOfModules.toSheaf (siteModuleRings R)).obj N)).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  ext U z
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul s m => exact h U s m
  | add z w hz hw => simpa only [map_add] using congrArg₂ (· + ·) hz hw

private def scalarTransition (φ : R ⟶ S) (τ : S ⟶ T) (ψ : R ⟶ T) (h : φ ≫ τ = ψ) :
    change φ ⋙ res φ ⟶ change ψ ⋙ res ψ where
  app M := (res φ).map (transitionLift φ τ ψ h M) ≫
    (resCompIso φ τ ψ h).hom.app ((change ψ).obj M)
  naturality M N f := by
    apply restrictedTensor_hom_ext φ M
    intro U s m
    subst ψ
    change (transitionLift φ τ (φ ≫ τ) rfl N).val.app U
        (((change φ).map f).val.app U (tensorSection φ M U s m)) =
      ((change (φ ≫ τ)).map f).val.app U
        ((transitionLift φ τ (φ ≫ τ) rfl M).val.app U (tensorSection φ M U s m))
    rw [tensorSection_map, transitionLift_tmul, transitionLift_tmul, tensorSection_map]

private theorem scalarTransition_tmul (φ : R ⟶ S) (τ : S ⟶ T) (ψ : R ⟶ T)
    (h : φ ≫ τ = ψ) (M : Mod R) (U : Cᵒᵖ) (s : S.obj.obj U) (m : M.val.obj U) :
    ((scalarTransition φ τ ψ h).app M).val.app U (tensorSection φ M U s m) =
      tensorSection ψ M U (τ.hom.app U s) m := by
  subst ψ
  exact transitionLift_tmul φ τ (φ ≫ τ) rfl M U s m

private theorem resCompIso_hom_apply (φ : R ⟶ S) (τ : S ⟶ T) (ψ : R ⟶ T)
    (h : φ ≫ τ = ψ) (M : Mod T) (U : Cᵒᵖ) (m : M.val.obj U) :
    ((resCompIso φ τ ψ h).hom.app M).val.app U m = m := by
  subst ψ
  rfl

private theorem resCompIso_inv_apply (φ : R ⟶ S) (τ : S ⟶ T) (ψ : R ⟶ T)
    (h : φ ≫ τ = ψ) (M : Mod T) (U : Cᵒᵖ) (m : M.val.obj U) :
    ((resCompIso φ τ ψ h).inv.app M).val.app U m = m := by
  subst ψ
  rfl

end ScalarTransitions

section FiniteComparisons

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R B S : Sheaf J CommRingCat.{u}}

private theorem scalarLinear_of_kernel_span
    {R B S : Type u} [CommRing R] [CommRing B] [CommRing S]
    (φ : R →+* B) (q : R →+* S) (p : B →+* S)
    (h : p.comp φ = q) (hq : Function.Surjective q)
    (hk : RingHom.ker p = Ideal.span (φ '' (RingHom.ker q : Set R)))
    (M : ModuleCat B) (N : ModuleCat S)
    (f : (ModuleCat.restrictScalars φ).obj M ⟶ (ModuleCat.restrictScalars q).obj N)
    (b : B) (m : M) : f (b • m) = p b • f m := by
  have hz (d : B) (hd : d ∈ RingHom.ker p) : ∀ m : M, f (d • m) = 0 := by
    rw [hk] at hd
    change d ∈ Submodule.span B (φ '' (RingHom.ker q : Set R)) at hd
    induction hd using Submodule.span_induction with
    | mem d hd =>
      obtain ⟨a, ha, rfl⟩ := hd
      intro m
      have hf := f.hom.map_smul a m
      change f (φ a • m) = q a • f m at hf
      rw [show q a = 0 from ha, zero_smul] at hf
      exact hf
    | zero => intro m; simp only [zero_smul, map_zero]
    | add d e hd he ihd ihe =>
      intro m
      rw [add_smul, map_add, ihd, ihe, add_zero]
    | smul a d hd ih =>
      intro m
      change f ((a * d) • m) = 0
      rw [mul_comm a d, mul_smul]
      exact ih (a • m)
  obtain ⟨a, ha⟩ := hq (p b)
  have hφ (a : R) : p (φ a) = q a := congrArg (fun f : R →+* S ↦ f a) h
  have hd : b - φ a ∈ RingHom.ker p := by
    change p (b - φ a) = 0
    rw [map_sub, hφ, ha, sub_self]
  have he := hz (b - φ a) hd m
  rw [sub_smul, map_sub] at he
  rw [sub_eq_zero] at he
  rw [he]
  have hf := f.hom.map_smul a m
  change f (φ a • m) = q a • f m at hf
  exact hf.trans (congrArg (fun s : S ↦ s • f m) ha)

private def quotientRestrictionHomEquiv (φ : R ⟶ B) (q : R ⟶ S) (p : B ⟶ S)
    (h : φ ≫ p = q)
    (hq : ∀ U : Cᵒᵖ, Function.Surjective (q.hom.app U))
    (hk : ∀ U : Cᵒᵖ, RingHom.ker (p.hom.app U).hom =
      Ideal.span ((φ.hom.app U).hom '' (RingHom.ker (q.hom.app U).hom : Set _)))
    (M : Mod B) (N : Mod S) :
    ((res φ).obj M ⟶ (res q).obj N) ≃ (M ⟶ (res p).obj N) where
  toFun f :=
    { val :=
        { app := fun U ↦ ModuleCat.ofHom
            (X := M.val.obj U) (Y := ((res p).obj N).val.obj U)
            { toFun := fun m ↦ f.val.app U m
              map_add' := fun x y ↦ (f.val.app U).hom.map_add x y
              map_smul' := fun b m ↦ scalarLinear_of_kernel_span
                (φ.hom.app U).hom (q.hom.app U).hom (p.hom.app U).hom
                (congrArg (fun t : R ⟶ S ↦ (t.hom.app U).hom) h)
                (hq U) (hk U) (M.val.obj U) (N.val.obj U) (f.val.app U) b m }
          naturality := by
            intro U V i
            ext m
            exact congrArg (fun t ↦ t m) (f.val.naturality i) } }
  invFun g := (res φ).map g ≫ (resCompIso φ p q h).hom.app N
  left_inv f := by subst q; ext U m; rfl
  right_inv f := by subst q; ext U m; rfl

private def quotientTensorAdjunction (φ : R ⟶ B) (q : R ⟶ S) (p : B ⟶ S)
    (h : φ ≫ p = q)
    (hq : ∀ U : Cᵒᵖ, Function.Surjective (q.hom.app U))
    (hk : ∀ U : Cᵒᵖ, RingHom.ker (p.hom.app U).hom =
      Ideal.span ((φ.hom.app U).hom '' (RingHom.ker (q.hom.app U).hom : Set _))) :
    res φ ⋙ change q ⊣ res p :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun M N ↦ (SheafOfModules.RingedTensor.tensorHomEquiv q _ _).trans
        (quotientRestrictionHomEquiv φ q p h hq hk M N)
      homEquiv_naturality_left_symm := by
        intro M M' N f g
        change (SheafOfModules.RingedTensor.tensorHomEquiv q _ _).symm
          ((quotientRestrictionHomEquiv φ q p h hq hk M N).symm (f ≫ g)) = _
        have hh : (quotientRestrictionHomEquiv φ q p h hq hk M N).symm (f ≫ g) =
            (res φ).map f ≫ (quotientRestrictionHomEquiv φ q p h hq hk M' N).symm g := by
          subst q
          ext U m
          rfl
        rw [hh]
        have hn := (SheafOfModules.RingedTensor.tensorAdjunction q)
          |>.homEquiv_naturality_left_symm ((res φ).map f)
            ((quotientRestrictionHomEquiv φ q p h hq hk M' N).symm g)
        simp only [SheafOfModules.RingedTensor.tensorAdjunction,
          Adjunction.mkOfHomEquiv_homEquiv] at hn
        exact hn
      homEquiv_naturality_right := by
        intro M N N' f g
        change (quotientRestrictionHomEquiv φ q p h hq hk M N')
          (SheafOfModules.RingedTensor.tensorHomEquiv q _ _ (f ≫ g)) = _
        have hn := (SheafOfModules.RingedTensor.tensorAdjunction q).homEquiv_naturality_right f g
        simp only [SheafOfModules.RingedTensor.tensorAdjunction,
          Adjunction.mkOfHomEquiv_homEquiv] at hn
        rw [hn]
        rfl }

private theorem quotientTensorIso_exists (φ : R ⟶ B) (q : R ⟶ S) (p : B ⟶ S)
    (h : φ ≫ p = q)
    (hq : ∀ U : Cᵒᵖ, Function.Surjective (q.hom.app U))
    (hk : ∀ U : Cᵒᵖ, RingHom.ker (p.hom.app U).hom =
      Ideal.span ((φ.hom.app U).hom '' (RingHom.ker (q.hom.app U).hom : Set _))) :
    ∃! e : res φ ⋙ change q ≅ change p,
      ∀ (M : Mod B) (U : Cᵒᵖ) (s : S.obj.obj U) (m : M.val.obj U),
        (e.hom.app M).val.app U (tensorSection q ((res φ).obj M) U s m) =
          tensorSection p M U s m := by
  let adj₁ := quotientTensorAdjunction φ q p h hq hk
  let adj₂ := SheafOfModules.RingedTensor.tensorAdjunction p
  let e := Adjunction.leftAdjointUniq adj₁ adj₂
  have he (M : Mod B) (U : Cᵒᵖ) (m : M.val.obj U) :
      (e.hom.app M).val.app U (tensorSection q ((res φ).obj M) U 1 m) =
        tensorSection p M U 1 m := by
    have he := congrArg (fun t : M ⟶ (res p).obj ((change p).obj M) ↦ t.val.app U m)
      (Adjunction.homEquiv_leftAdjointUniq_hom_app adj₁ adj₂ M)
    change ((quotientRestrictionHomEquiv φ q p h hq hk M ((change p).obj M))
      (SheafOfModules.RingedTensor.tensorHomEquiv q ((res φ).obj M) _ (e.hom.app M))).val.app
        U m = _ at he
    change (e.hom.app M).val.app U (tensorSection q ((res φ).obj M) U 1 m) =
      tensorSection p M U 1 m at he
    exact he
  have ht (M : Mod B) (U : Cᵒᵖ) (s : S.obj.obj U) (m : M.val.obj U) :
      (e.hom.app M).val.app U (tensorSection q ((res φ).obj M) U s m) =
        tensorSection p M U s m := by
    rw [tensorSection_smul q, map_smul, he, tensorSection_smul p M U s m]
  refine ⟨e, ht, ?_⟩
  intro e' he'
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply (SheafOfModules.RingedTensor.tensorHomEquiv q ((res φ).obj M) _).injective
  ext U m
  exact (he' M U 1 m).trans (ht M U 1 m).symm

end FiniteComparisons

-- Subsequent proofs use the section formulas instead of reducing these constructions.
attribute [irreducible] resCompIso transitionLift scalarTransition
  quotientRestrictionHomEquiv quotientTensorAdjunction

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The finite comparison before localization, uniquely fixed on sheafified pure tensors.
Source: Stacks 099L, 06YY (blueprint: lem-weil-pbc-constant-completion-equivalence).
Proof: the finite quotients have the same kernel after extending the constant ideal.
Consequently restriction-linear maps to a finite-quotient module are completion-linear.
The two tensor functors are therefore left adjoints to the same restriction functor.
Uniqueness of left adjoints gives the comparison, and the adjunction unit gives its
pure-tensor formula. The formula on tensors with first factor one determines it uniquely. -/
theorem finiteComparison_existsUnique (J : GrothendieckTopology C) (A : Type u)
    [CommRing A] [IsNoetherianRing A] (I : Ideal A) (n : ℕ) :
    ∃! e : res (coefficientMap J A I) ⋙ change (quotient J A I n) ≅
        change (projection J A I n),
      ∀ (M : Mod (completed J A I)) (U : Cᵒᵖ)
        (s : (finite J A I n).obj.obj U) (m : M.val.obj U),
        (e.hom.app M).val.app U
          (tensorSection (quotient J A I n) ((res (coefficientMap J A I)).obj M) U s m) =
            tensorSection (projection J A I n) M U s m := by
  apply quotientTensorIso_exists (coefficientMap J A I) (quotient J A I n)
    (projection J A I n)
  · exact limit.lift_π (quotientCone J A I) (op n)
  · intro U
    exact ((flat_and_quotients J A I).2.2 n U.unop).1
  · intro U
    rw [← Ideal.map_span, Ideal.span_eq,
      ((flat_and_quotients J A I).2.2 n U.unop).2, Ideal.map_span, ← Set.range_comp']
    exact ((flat_and_quotients J A I).2.1 n U.unop).2


/-- The canonical finite comparison, with its pure-tensor normalization fixed uniquely.
Source: Stacks 099L (blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def finiteComparison (J : GrothendieckTopology C) (A : Type u) [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) (n : ℕ) :
    res (coefficientMap J A I) ⋙ change (quotient J A I n) ≅
      change (projection J A I n) :=
  (finiteComparison_existsUnique J A I n).exists.choose


/-- The standard computation square for exact restriction of scalars.
Source: Stacks 099I (blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def resFactors {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) :
    (res φ).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ Q R ≅ Q B ⋙ dres φ :=
  letI := HasDerivedCategory.standard (Mod R)
  letI := HasDerivedCategory.standard (Mod B)
  letI := (siteRestrictScalars_exact φ).1
  letI := (siteRestrictScalars_exact φ).2
  (res φ).mapDerivedCategoryFactors.symm

/-- Finite scalar comparison in D(S_n), normalized on every flat-term K-flat complex.
Source: Stacks 099L, 06YY (blueprint: lem-weil-pbc-constant-completion-equivalence).
Proof: a flat-term K-flat B-complex remains K-flat over R because B is R-flat.
Use finiteComparison on that representative. Its pure-tensor formula is natural and
independent of replacements by the universal derived-change-of-rings counits, giving
this natural isomorphism and the displayed computation square. -/
theorem finiteDerivedComparison (J : GrothendieckTopology C) (A : Type u) [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) (n : ℕ) :
    ∃ e : dres (coefficientMap J A I) ⋙ extend (quotient J A I n) ≅
        extend (projection J A I n),
      ∀ (P : Cx (completed J A I)), P.IsAcyclicTensorKFlat →
        (∀ q : ℤ, SheafOfModules.IsFlat (P.X q)) →
        (extend (quotient J A I n)).map
            ((resFactors (coefficientMap J A I)).inv.app P) ≫
          (extendComparison (quotient J A I n)).app
            (((res (coefficientMap J A I)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
          (Q (finite J A I n)).map
            ((NatIso.mapHomologicalComplex (finiteComparison J A I n)
              (ComplexShape.up ℤ)).hom.app P) =
        (e.hom.app ((Q (completed J A I)).obj P)) ≫
          (extendComparison (projection J A I n)).app P := by
  sorry

variable (J A I)

/-- The two coefficient sheaves, false for constant and true for completed coefficients.
Source: Stacks 099L (blueprint: lem-weil-pbc-constant-completion-equivalence). -/
abbrev coefficients (b : Bool) : Sheaf J CommRingCat.{u} :=
  if b then completed J A I else constant J A

/-- Their structural constant coefficient maps. Source: Stacks 099L
(blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def baseMap (b : Bool) : constant J A ⟶ coefficients J A I b :=
  match b with
  | false => 𝟙 _
  | true => coefficientMap J A I

/-- Their finite projections, the original quotient maps. Source: Stacks 099L
(blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def finiteMap (b : Bool) (n : ℕ) : coefficients J A I b ⟶ finite J A I n :=
  match b with
  | false => quotient J A I n
  | true => projection J A I n

/-- Finite reduction with the original coefficient action retained. Source: Stacks 099L
(blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def reduction (b : Bool) (n : ℕ) :
    Mod (coefficients J A I b) ⥤ Mod (coefficients J A I b) :=
  change (finiteMap J A I b n) ⋙ res (finiteMap J A I b n)

/-- The quotient transition is fixed uniquely by its sectionwise tensor formula.
Source: Stacks 099L, 06YY (blueprint: lem-weil-pbc-constant-completion-equivalence).
Proof: the finite quotient transition preserves the balanced tensor relations because
it commutes with the coefficient projections. Sheafify its map s tensor m ↦ bar(s) tensor m.
The formula is linear, commutes with restrictions and module maps, and determines it uniquely. -/
theorem reductionStep_existsUnique (b : Bool) (n : ℕ) :
    ∃! t : reduction J A I b (n + 1) ⟶ reduction J A I b n,
      ∀ (M : Mod (coefficients J A I b)) (U : Cᵒᵖ)
        (s : (finite J A I (n + 1)).obj.obj U) (m : M.val.obj U),
        (t.app M).val.app U (tensorSection (finiteMap J A I b (n + 1)) M U s m) =
          tensorSection (finiteMap J A I b n) M U
            ((transition J A I n).hom.app U s) m := by
  have h : finiteMap J A I b (n + 1) ≫ transition J A I n = finiteMap J A I b n := by
    cases b with
    | false =>
      simpa only [finiteMap, Functor.const_obj_map, Functor.const_obj_obj,
        Category.id_comp, finiteSystem,
        Functor.ofOpSequence_map_homOfLE_succ, Category.id_comp] using (quotient_step J A I n).symm
    | true =>
      change projection J A I (n + 1) ≫ transition J A I n = projection J A I n
      unfold projection completed
      simpa only [finiteSystem,
        Functor.ofOpSequence_map_homOfLE_succ] using
          limit.w (finiteSystem J A I) (homOfLE (Nat.le_succ n)).op
  let t := scalarTransition (finiteMap J A I b (n + 1)) (transition J A I n)
    (finiteMap J A I b n) h
  refine ⟨t, scalarTransition_tmul _ _ _ h, ?_⟩
  intro t' ht'
  apply NatTrans.ext
  funext M
  apply restrictedTensor_hom_ext (finiteMap J A I b (n + 1)) M
  intro U s m
  exact (ht' M U s m).trans (scalarTransition_tmul _ _ _ h M U s m).symm

/-- The actual finite quotient transition with its uniquely specified tensor formula.
Source: Stacks 099L (blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def reductionStep (b : Bool) (n : ℕ) :
    reduction J A I b (n + 1) ⟶ reduction J A I b n :=
  (reductionStep_existsUnique J A I b n).exists.choose

/-- The strict reduction tower, retaining all its transitions functorially.
Source: Stacks 099L, 099M (blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def reductionTower (b : Bool) : Mod (coefficients J A I b) ⥤
    (ℕᵒᵖ ⥤ Mod (coefficients J A I b)) :=
  (Functor.ofOpSequence (reductionStep J A I b)).flip

/-- The tower is additive, since every evaluation is additive scalar extension/restriction.
Source: Stacks 06YY (blueprint: lem-weil-pbc-constant-completion-equivalence).
Proof: evaluate the additive-functor identity at each tower index. The chosen tensor functor
and restriction of scalars are additive. Evaluation is jointly faithful. -/
theorem reductionTower_additive (b : Bool) : (reductionTower J A I b).Additive := by
  constructor
  intro M N f g
  apply NatTrans.ext
  funext n
  change (reduction J A I b n.unop).map (f + g) = _
  have : (reduction J A I b n.unop).Additive := by
    dsimp only [reduction, res]
    infer_instance
  exact Functor.map_add (reduction J A I b n.unop)

attribute [instance] reductionTower_additive

/-- The constant module tower functor. Source: Stacks 0940
(blueprint: lem-weil-pbc-constant-completion-equivalence). -/
abbrev constantTower (O : Sheaf J CommRingCat.{u}) : Mod O ⥤ (ℕᵒᵖ ⥤ Mod O) :=
  Functor.const ℕᵒᵖ

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The normalized scalar-extension unit, constructed before sheafification.
Its section maps are the ordinary module adjunction units followed by sheafification;
restriction and module-map naturality follow from the two presheaf unit equations. -/
private theorem scalarExtensionUnit_exists {R S : Sheaf J CommRingCat.{u}} (φ : R ⟶ S) :
    ∃ η : 𝟭 (Mod R) ⟶ change φ ⋙ res φ,
      ∀ (M : Mod R) (U : Cᵒᵖ) (m : M.val.obj U),
        (η.app M).val.app U m = tensorSection φ M U 1 m := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 (siteModuleRings S).obj)
  let q (M : Mod R) : M ⟶ (res φ).obj ((change φ).obj M) :=
    { val :=
      { app := fun U ↦
          (ModuleCat.extendRestrictScalarsAdj (φ.hom.app U).hom).unit.app (M.val.obj U) ≫
            (ModuleCat.restrictScalars (φ.hom.app U).hom).map
              ((adj.unit.app (SheafOfModules.changeOfRingsPresheaf.{u, u, u} φ M)).app U)
        naturality := by
          intro U V f
          ext m
          change tensorSection φ M V 1 (M.val.map f m) =
            ((change φ).obj M).val.map f (tensorSection φ M U 1 m)
          let η := adj.unit.app (SheafOfModules.changeOfRingsPresheaf.{u, u, u} φ M)
          have h := PresheafOfModules.naturality_apply η f
            ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] m)
          have ht := Classical.choose_spec (SheafOfModules.exists_changeOfRingsMap φ M f)
            1 m
          rw [map_one] at ht
          exact (congrArg (η.app V) ht.symm).trans h } }
  let η : 𝟭 (Mod R) ⟶ change φ ⋙ res φ :=
    { app := q
      naturality := by
        intro M N f
        ext U m
        let a : SheafOfModules.changeOfRingsPresheaf.{u, u, u} φ M ⟶
            SheafOfModules.changeOfRingsPresheaf.{u, u, u} φ N :=
          { app := fun V ↦ (ModuleCat.extendScalars (φ.hom.app V).hom).map (f.val.app V)
            naturality := SheafOfModules.changeOfRingsHom_naturality φ M f }
        have h := congrArg (fun t ↦ t.app U
          ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] m))
          (adj.unit.naturality a)
        change tensorSection φ N U 1 (f.val.app U m) =
          ((change φ).map f).val.app U (tensorSection φ M U 1 m)
        change (adj.unit.app (SheafOfModules.changeOfRingsPresheaf.{u, u, u} φ N)).app U
            ((ModuleCat.extendScalars (φ.hom.app U).hom).map (f.val.app U)
              ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] m)) =
          ((change φ).map f).val.app U (tensorSection φ M U 1 m) at h
        rw [ModuleCat.ExtendScalars.map_tmul] at h
        exact h }
  exact ⟨η, fun _ _ _ ↦ rfl⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The strict quotient unit is uniquely determined by m ↦ 1 tensor m at every level.
Source: Stacks 099M (blueprint: lem-weil-pbc-constant-completion-equivalence).
Proof: the scalar-extension units commute with quotient transitions since they preserve 1.
They are linear in the original coefficients and natural in M, so form a natural
transformation of strict towers. The section formula determines every component. -/
theorem reductionUnit_existsUnique (b : Bool) :
    ∃! η : constantTower J (coefficients J A I b) ⟶ reductionTower J A I b,
      ∀ (M : Mod (coefficients J A I b)) (n : ℕ) (U : Cᵒᵖ) (m : M.val.obj U),
        ((η.app M).app (op n)).val.app U m =
          tensorSection (finiteMap J A I b n) M U 1 m := by
  let ηn (n : ℕ) : 𝟭 (Mod (coefficients J A I b)) ⟶ reduction J A I b n :=
    (scalarExtensionUnit_exists J (finiteMap J A I b n)).choose
  have hη (n : ℕ) (M : Mod (coefficients J A I b)) (U : Cᵒᵖ) (m : M.val.obj U) :
      ((ηn n).app M).val.app U m = tensorSection (finiteMap J A I b n) M U 1 m :=
    (scalarExtensionUnit_exists J (finiteMap J A I b n)).choose_spec M U m
  have hstep (M : Mod (coefficients J A I b)) (n : ℕ) :
      ((Functor.const ℕᵒᵖ).obj M).map (homOfLE (Nat.le_succ n)).op ≫ (ηn n).app M =
        (ηn (n + 1)).app M ≫
          ((reductionTower J A I b).obj M).map (homOfLE (Nat.le_succ n)).op := by
    change 𝟙 M ≫ (ηn n).app M = (ηn (n + 1)).app M ≫
      ((Functor.ofOpSequence (reductionStep J A I b)).map
        (homOfLE (Nat.le_succ n)).op).app M
    rw [Category.id_comp, Functor.ofOpSequence_map_homOfLE_succ]
    ext U m
    change ((ηn n).app M).val.app U m =
      ((reductionStep J A I b n).app M).val.app U (((ηn (n + 1)).app M).val.app U m)
    rw [hη, hη]
    have ht := (reductionStep_existsUnique J A I b n).exists.choose_spec M U
      (1 : (finite J A I (n + 1)).obj.obj U) m
    simpa only [map_one, reductionStep] using ht.symm
  let η : constantTower J (coefficients J A I b) ⟶ reductionTower J A I b :=
    { app := fun M ↦ NatTrans.ofOpSequence (fun n ↦ (ηn n).app M) (hstep M)
      naturality := by
        intro M N f
        apply NatTrans.ext
        funext n
        exact (ηn n.unop).naturality f }
  refine ⟨η, fun M n U m ↦ hη n M U m, ?_⟩
  intro η' hη'
  apply NatTrans.ext
  funext M
  apply NatTrans.ext
  funext n
  ext U m
  exact (hη' M n.unop U m).trans (hη n.unop M U m).symm

/-- The actual strict quotient-tower unit. Source: Stacks 099M
(blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def reductionUnit (b : Bool) :
    constantTower J (coefficients J A I b) ⟶ reductionTower J A I b :=
  (reductionUnit_existsUnique J A I b).exists.choose

variable {J A I}


/-- The standard derived category of strict module towers. Source: Stacks 0940
(blueprint: lem-weil-pbc-constant-completion-equivalence). -/
abbrev TD (O : Sheaf J CommRingCat.{u}) :=
  @DerivedCategory (ℕᵒᵖ ⥤ Mod O) _ _ (HasDerivedCategory.standard _)

/-- Localization of strict tower complexes. Source: Stacks 0940
(blueprint: lem-weil-pbc-constant-completion-equivalence). -/
abbrev TQ (O : Sheaf J CommRingCat.{u}) :
    CochainComplex (ℕᵒᵖ ⥤ Mod O) ℤ ⥤ TD O :=
  @DerivedCategory.Q (ℕᵒᵖ ⥤ Mod O) _ _ (HasDerivedCategory.standard _)

/-- The degreewise limit functor on complexes, with an abstract coefficient category.
Source: Stacks 0940 (blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def complexLimitFunctor (M : Type*) [Category M] [Preadditive M]
    [HasLimitsOfShape ℕᵒᵖ M] [(lim : (ℕᵒᵖ ⥤ M) ⥤ M).PreservesZeroMorphisms] :
    CochainComplex (ℕᵒᵖ ⥤ M) ℤ ⥤ CochainComplex M ℤ :=
  (lim : (ℕᵒᵖ ⥤ M) ⥤ M).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The ordinary termwise limit of strict tower complexes. Source: Stacks 0940
(blueprint: lem-weil-pbc-constant-completion-equivalence). -/
abbrev ordinaryLimit (O : Sheaf J CommRingCat.{u}) :
    CochainComplex (ℕᵒᵖ ⥤ Mod O) ℤ ⥤ Cx O :=
  letI : (lim : (ℕᵒᵖ ⥤ Mod O) ⥤ Mod O).Additive :=
    Functor.additive_of_preserves_binary_products _
  complexLimitFunctor (Mod O)

set_option genSizeOf false in
set_option genInjectivity false in
/-- The total right derived strict-limit universal property and K-injective computation.
Source: Stacks 0940, 0941 (blueprint: lem-weil-pbc-constant-completion-equivalence). -/
structure StrictLimit (O : Sheaf J CommRingCat.{u}) where
  functor : TD O ⥤ D O
  comparison : ordinaryLimit O ⋙ Q O ⟶ TQ O ⋙ functor
  universal : functor.IsRightDerivedFunctor comparison
    (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ Mod O) (ComplexShape.up ℤ))
  computation : ∀ P : CochainComplex (ℕᵒᵖ ⥤ Mod O) ℤ,
    P.IsKInjective → IsIso (comparison.app P)

/-- The strict-tower theorem supplies this existing total derived functor and comparison.
Source: Stacks 0940 (blueprint: lem-weil-pbc-constant-completion-equivalence).
Proof: specialize ringedStrictTowerHomotopyLimit to O with commutativity retained and to
the standard localizations. Project its universal right-derived pair and its computation
on K-injective tower complexes. These are precisely the fields displayed here. -/
theorem strictLimit_exists (O : Sheaf J CommRingCat.{u}) : Nonempty (StrictLimit O) := by
  let := HasDerivedCategory.standard (Mod O)
  let := HasDerivedCategory.standard (ℕᵒᵖ ⥤ Mod O)
  obtain ⟨RF, η, huniv, hcomp, _⟩ :=
    ringedStrictTowerHomotopyLimit J (siteModuleRings O) (fun U a b ↦ @mul_comm (O.obj.obj U) _ a b)
  exact ⟨{ functor := RF
           comparison := η
           universal := huniv
           computation := hcomp }⟩

/-- Select the total derived strict limit by its universal comparison.
Source: Stacks 0940 (blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def strictLimit (O : Sheaf J CommRingCat.{u}) : StrictLimit O :=
  Classical.choice (strictLimit_exists O)

attribute [local irreducible] strictLimit

/-- Total right derived strict inverse limit, not a noncanonical triangulated cone.
Source: Stacks 0940 (blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def rlim (O : Sheaf J CommRingCat.{u}) : TD O ⥤ D O := (strictLimit O).functor

/-- Its universal comparison from ordinary termwise inverse limit.
Source: Stacks 0940 (blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def limitComparison (O : Sheaf J CommRingCat.{u}) :
    ordinaryLimit O ⋙ Q O ⟶ TQ O ⋙ rlim O := (strictLimit O).comparison

variable (J A I)

/-- The ordinary strict reduction-tower complex, on one fixed representative.
Source: Stacks 099M (blueprint: lem-weil-pbc-constant-completion-equivalence). -/
abbrev reductionComplex (b : Bool) (P : Cx (coefficients J A I b)) :=
  ((reductionTower J A I b).mapHomologicalComplex (ComplexShape.up ℤ)).obj P

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The degreewise universal limit map for an abstract tower functor and its unit.
The chain equation follows after each limit projection from naturality of the unit. -/
private theorem complexLimitUnit {M : Type*} [Category M] [Preadditive M]
    [HasLimitsOfShape ℕᵒᵖ M] (T : M ⥤ (ℕᵒᵖ ⥤ M)) [T.PreservesZeroMorphisms]
    [(lim : (ℕᵒᵖ ⥤ M) ⥤ M).PreservesZeroMorphisms]
    (η : Functor.const ℕᵒᵖ ⟶ T) (P : CochainComplex M ℤ) :
    ∃! f : P ⟶ (complexLimitFunctor M).obj ((T.mapHomologicalComplex (ComplexShape.up ℤ)).obj P),
      ∀ (q : ℤ) (n : ℕ), f.f q ≫ limit.π (T.obj (P.X q)) (op n) =
        (η.app (P.X q)).app (op n) := by
  let f : P ⟶
      (complexLimitFunctor M).obj
        ((T.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) :=
    { f := fun q ↦ limit.lift _
        { pt := P.X q
          π := η.app (P.X q) }
      comm' := by
        intro q q' h
        apply limit.hom_ext
        intro n
        rw [Category.assoc, Category.assoc]
        change limit.lift _ _ ≫
          limMap (((T.mapHomologicalComplex (ComplexShape.up ℤ)).obj P).d q q') ≫
            limit.π _ n = _
        rw [limMap_π, limit.lift_π_assoc]
        calc
          _ = P.d q q' ≫ (η.app (P.X q')).app n :=
            (congrArg (fun t ↦ t.app n)
              (η.naturality (P.d q q'))).symm
          _ = _ := congrArg (fun t ↦ P.d q q' ≫ t)
            (limit.lift_π (F := T.obj (P.X q'))
              { pt := P.X q', π := η.app (P.X q') } n).symm }
  refine ⟨f, ?_, ?_⟩
  · intro q n
    exact limit.lift_π _ _
  · intro g hg
    apply HomologicalComplex.hom_ext
    intro q
    apply limit.hom_ext
    intro n
    change g.f q ≫ limit.π (T.obj (P.X q)) n =
      limit.lift _ { pt := P.X q, π := η.app (P.X q) } ≫
        limit.π (T.obj (P.X q)) n
    rw [limit.lift_π]
    exact hg q n.unop


set_option backward.isDefEq.respectTransparency false in
/-- The ordinary limit unit is the unique chain map with the prescribed quotient components.
Source: Stacks 099M, 0940 (blueprint: lem-weil-pbc-constant-completion-equivalence).
Proof: at degree q use limit.lift on the strict quotient-unit cone. The differential
commutes with every projection by naturality of reductionUnit, hence with their limit.
Joint monicity of the projections proves uniqueness in every degree. -/
theorem ordinaryUnit_existsUnique (b : Bool) (P : Cx (coefficients J A I b)) :
    ∃! f : P ⟶ (ordinaryLimit (coefficients J A I b)).obj (reductionComplex J A I b P),
      ∀ (q : ℤ) (n : ℕ), f.f q ≫
        limit.π ((reductionComplex J A I b P).X q) (op n) =
          ((reductionUnit J A I b).app (P.X q)).app (op n) := by
  have : (lim : (ℕᵒᵖ ⥤ Mod (coefficients J A I b)) ⥤
      Mod (coefficients J A I b)).Additive :=
    Functor.additive_of_preserves_binary_products _
  exact complexLimitUnit (reductionTower J A I b) (reductionUnit J A I b) P

/-- The actual ordinary strict-limit unit, fixed by its quotient projections.
Source: Stacks 099M (blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def ordinaryUnit (b : Bool) (P : Cx (coefficients J A I b)) :
    P ⟶ (ordinaryLimit (coefficients J A I b)).obj (reductionComplex J A I b P) :=
  (ordinaryUnit_existsUnique J A I b P).exists.choose

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Precomposition by a fully faithful whiskering functor preserves the terminal
right-extension universal property. Construct its lifts by taking preimages. -/
private theorem kan_precomp
    {A B D H : Type*} [Category A] [Category B] [Category D] [Category H]
    (P : A ⥤ B) (Q : B ⥤ D) (T : D ⥤ H) (G : B ⥤ H) (ε : Q ⋙ T ⟶ G)
    [((Functor.whiskeringLeft A B H).obj P).Full]
    [((Functor.whiskeringLeft A B H).obj P).Faithful]
    [T.IsRightKanExtension ε] :
    T.IsRightKanExtension
      ((Functor.associator P Q T).hom ≫ Functor.whiskerLeft P ε) := by
  let K := (Functor.whiskeringLeft A B H).obj P
  let lift (s : Functor.RightExtension (P ⋙ Q) (P ⋙ G)) : s.left ⟶ T :=
    T.liftOfIsRightKanExtension ε s.left
      (K.preimage ((Functor.associator P Q s.left).inv ≫ s.hom))
  have fac (s : Functor.RightExtension (P ⋙ Q) (P ⋙ G)) :
      Functor.whiskerLeft (P ⋙ Q) (lift s) ≫
        ((Functor.associator P Q T).hom ≫ Functor.whiskerLeft P ε) = s.hom := by
    as_aux_lemma =>
      apply NatTrans.ext
      funext X
      have h := congrArg (fun t ↦ t.app (P.obj X))
        (T.liftOfIsRightKanExtension_fac ε s.left
          (K.preimage ((Functor.associator P Q s.left).inv ≫ s.hom)))
      have hp := congrArg (fun t ↦ t.app X)
        (K.map_preimage ((Functor.associator P Q s.left).inv ≫ s.hom))
      change (lift s).app (Q.obj (P.obj X)) ≫ (𝟙 _ ≫ ε.app (P.obj X)) = _
      rw [Category.id_comp]
      exact (h.trans hp).trans (Category.id_comp _)
  clear_value lift
  refine ⟨⟨IsTerminal.ofUniqueHom
    (fun s ↦ CostructuredArrow.homMk (lift s) (fac s)) ?_⟩⟩
  as_aux_lemma =>
    intro s m
    apply CostructuredArrow.hom_ext
    apply T.hom_ext_of_isRightKanExtension ε
    apply K.map_injective
    have h := CostructuredArrow.w m
    apply NatTrans.ext
    funext X
    have h' := congrArg (fun t ↦ t.app X) h
    have h'' := congrArg (fun t ↦ t.app X) (fac s)
    have hh := h'.trans h''.symm
    change m.left.app (Q.obj (P.obj X)) ≫ (𝟙 _ ≫ ε.app (P.obj X)) = _ at hh
    rw [Category.id_comp] at hh
    change _ = (lift s).app (Q.obj (P.obj X)) ≫ (𝟙 _ ≫ ε.app (P.obj X)) at hh
    rw [Category.id_comp] at hh
    exact hh

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Transport a right Kan extension across isomorphisms of its source diagram and target. -/
private theorem kan_change
    {A D H : Type*} [Category A] [Category D] [Category H]
    {Q Q' : A ⥤ D} {G G' : A ⥤ H} (T : D ⥤ H)
    (i : Q ≅ Q') (j : G ≅ G') (ε : Q ⋙ T ⟶ G)
    [T.IsRightKanExtension ε] :
    T.IsRightKanExtension (Functor.whiskerRight i.inv T ≫ ε ≫ j.hom) := by
  let Φ := Functor.rightExtensionEquivalenceOfIso₁ i G
  have ht := (IsTerminal.isTerminalIffObj Φ.functor
    (Functor.RightExtension.mk T ε)).1 (T.isUniversalOfIsRightKanExtension ε)
  have hε : T.IsRightKanExtension (Functor.whiskerRight i.inv T ≫ ε) := ⟨⟨ht⟩⟩
  exact (Functor.isRightKanExtension_iff_of_iso₂
    (Functor.whiskerRight i.inv T ≫ ε)
    (Functor.whiskerRight i.inv T ≫ ε ≫ j.hom) j (Iso.refl T) (by simp)).1 hε

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Transport a homotopy-level derived counit to complexes, with abstract categories.
The quotient comparison is invertible, so the transport preserves every computation
component that is already an isomorphism. -/
private theorem cochain_derived_counit
    {A₀ B₀ : Type*} [Category A₀] [Category B₀] [Abelian A₀] [Abelian B₀]
    [HasDerivedCategory A₀] [HasDerivedCategory B₀]
    (E : A₀ ⥤ B₀) [E.Additive]
    (T : DerivedCategory A₀ ⥤ DerivedCategory B₀)
    (ε : DerivedCategory.Qh ⋙ T ⟶ E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    [T.IsRightKanExtension ε] :
    ∃ β : DerivedCategory.Q ⋙ T ⟶
        E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q,
      T.IsRightKanExtension β ∧
        ∀ P : CochainComplex A₀ ℤ,
          IsIso (ε.app ((HomotopyCategory.quotient A₀ (.up ℤ)).obj P)) →
            IsIso (β.app P) := by
  let q := HomotopyCategory.quotient A₀ (.up ℤ)
  let H := E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh
  let α := (Functor.associator q DerivedCategory.Qh T).hom ≫ Functor.whiskerLeft q ε
  have : T.IsRightKanExtension α := kan_precomp q DerivedCategory.Qh T H ε
  let i := DerivedCategory.quotientCompQhIso A₀
  let j : q ⋙ H ≅ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (E.mapHomotopyCategoryFactors (.up ℤ)) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso B₀)
  let β : DerivedCategory.Q ⋙ T ⟶
      E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    Functor.whiskerRight i.inv T ≫ α ≫ j.hom
  refine ⟨β, kan_change T i j α, ?_⟩
  intro P hP
  have := hP
  dsimp [β, α]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem resolving_derived_cochain
    {M E : Type*} [Category M] [Abelian M] [HasDerivedCategory M]
    [Category E] [Abelian E] [HasDerivedCategory E]
    (T : M ⥤ E) [T.Additive] (S₀ : CochainComplex M ℤ → Prop)
    (hres₀ : ∀ P : CochainComplex M ℤ,
      ∃ (K : CochainComplex M ℤ) (f : K ⟶ P), S₀ K ∧ QuasiIso f)
    (hT : ∀ {P P' : CochainComplex M ℤ} (f : P ⟶ P'), S₀ P →
      S₀ P' → QuasiIso f →
        QuasiIso ((T.mapHomologicalComplex (.up ℤ)).map f)) :
    ∃ (LT : DerivedCategory M ⥤ DerivedCategory E)
      (β : DerivedCategory.Q ⋙ LT ⟶ T.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q),
      LT.IsLeftDerivedFunctor β (HomologicalComplex.quasiIso M (.up ℤ)) ∧
        ∀ P : CochainComplex M ℤ, S₀ P → IsIso (β.app P) := by
  let q := HomotopyCategory.quotient M (.up ℤ)
  let H := T.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh
  let S : Set (HomotopyCategory M (.up ℤ)) :=
    {X | ∃ P : CochainComplex M ℤ, S₀ P ∧ q.obj P = X}
  have hres (X : HomotopyCategory M (.up ℤ)) :
      ∃ (Y : HomotopyCategory M (.up ℤ)) (f : Y ⟶ X),
        Y ∈ S ∧ HomotopyCategory.quasiIso M (.up ℤ) f := by
    obtain ⟨P, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    obtain ⟨K, f, hK, hf⟩ := hres₀ P
    exact ⟨q.obj K, q.map f, ⟨K, hK, rfl⟩,
      (HomotopyCategory.quotient_map_mem_quasiIso_iff f).2 hf⟩
  have hinv (X Y : HomotopyCategory M (.up ℤ)) (f : X ⟶ Y)
      (hX : X ∈ S) (hY : Y ∈ S)
      (hf : HomotopyCategory.quasiIso M (.up ℤ) f) : IsIso (H.map f) := by
    obtain ⟨P, hP, rfl⟩ := hX
    obtain ⟨P', hP', rfl⟩ := hY
    obtain ⟨g, rfl⟩ := q.map_surjective f
    have hg := (HomotopyCategory.quotient_map_mem_quasiIso_iff g).1 hf
    have ht := hT g hP hP' hg
    change IsIso (DerivedCategory.Qh.map
      ((HomotopyCategory.quotient E (.up ℤ)).map
        ((T.mapHomologicalComplex (.up ℤ)).map g)))
    exact Localization.inverts DerivedCategory.Qh
      (HomotopyCategory.quasiIso E (.up ℤ)) _
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 ht)
  obtain ⟨_, LT, ε, hu, _, hc⟩ :=
    Functor.leftDerived_from_resolvingClass M (DerivedCategory E) H S hres hinv
  have : LT.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso M (.up ℤ)) := hu
  have : LT.IsRightKanExtension ε :=
    Functor.IsLeftDerivedFunctor.isRightKanExtension LT ε
      (HomotopyCategory.quasiIso M (.up ℤ))
  obtain ⟨β, hβ, hcomp⟩ := cochain_derived_counit T LT ε
  exact ⟨LT, β, ⟨hβ⟩, fun P hP ↦ hcomp P (hc (q.obj P) ⟨P, hP, rfl⟩)⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem change_preserves_kFlat_quasiIso
    {R S : Sheaf J CommRingCat.{u}}
    (φ : R ⟶ S) {P P' : Cx R} (f : P ⟶ P')
    (hP : P.IsAcyclicTensorKFlat) (hP' : P'.IsAcyclicTensorKFlat) (hf : QuasiIso f) :
    QuasiIso (((change φ).mapHomologicalComplex (.up ℤ)).map f) := by
  let := HasDerivedCategory.standard (Mod R)
  let := HasDerivedCategory.standard (Mod S)
  let d := derivedExtension φ
  have : IsIso (d.comparison.app P) := d.computation P hP
  have : IsIso (d.comparison.app P') := d.computation P' hP'
  have : IsIso ((Q R).map f) := (DerivedCategory.isIso_Q_map_iff_quasiIso (Mod R) f).2 hf
  have h := d.comparison.naturality f
  dsimp only [Functor.comp_map] at h
  apply (DerivedCategory.isIso_Q_map_iff_quasiIso (Mod S) _).1
  have : IsIso (d.comparison.app P ≫ (Q S).map
      (((change φ).mapHomologicalComplex (.up ℤ)).map f)) := by
    rw [← h]
    infer_instance
  exact IsIso.of_isIso_comp_left (d.comparison.app P) _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem derived_tower_unit
    {A₀ A₁ D₀ D₁ : Type*}
    [Category A₀] [Category A₁] [Category D₀] [Category D₁]
    (q : A₀ ⥤ D₀) (q' : A₁ ⥤ D₁) (W : MorphismProperty A₀)
    [q.IsLocalization W] {G T : A₀ ⥤ A₁} {F : A₁ ⥤ A₀}
    (ν : 𝟭 A₀ ⟶ G ⋙ F) (η : G ⟶ T) (DG LT : D₀ ⥤ D₁) (RF : D₁ ⥤ D₀)
    (α : q ⋙ DG ≅ G ⋙ q') (β : q ⋙ LT ⟶ T ⋙ q')
    [LT.IsLeftDerivedFunctor β W] (γ : F ⋙ q ⟶ q' ⋙ RF) :
    ∃ unit : 𝟭 D₀ ⟶ LT ⋙ RF,
      ∀ X, unit.app (q.obj X) ≫ RF.map (β.app X) =
        q.map (ν.app X ≫ F.map (η.app X)) ≫ γ.app (T.obj X) := by
  have : (DG ⋙ RF).IsLeftDerivedFunctor
      ((Functor.associator q DG RF).inv ≫ Functor.whiskerRight α.hom RF) W :=
    Functor.isLeftDerivedFunctor_of_inverts W _
      ((Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight α RF)
  let δ := (Functor.associator q DG RF).inv ≫ Functor.whiskerRight α.hom RF
  let θ := q.rightUnitor.hom ≫ q.leftUnitor.inv ≫ Functor.whiskerRight ν q ≫
    (Functor.associator G F q).hom ≫ Functor.whiskerLeft G γ ≫
      (Functor.associator G q' RF).inv
  let u := (DG ⋙ RF).leftDerivedLift δ W (𝟭 D₀) θ
  let t := LT.leftDerivedLift β W DG (α.hom ≫ Functor.whiskerRight η q')
  refine ⟨u ≫ Functor.whiskerRight t RF, ?_⟩
  intro X
  change (u.app (q.obj X) ≫ RF.map (t.app (q.obj X))) ≫ RF.map (β.app X) = _
  rw [Category.assoc, ← RF.map_comp,
    LT.leftDerived_fac_app β W DG (α.hom ≫ Functor.whiskerRight η q') X]
  change u.app (q.obj X) ≫ RF.map (α.hom.app X ≫ q'.map (η.app X)) = _
  have hu : u.app (q.obj X) ≫ RF.map (α.hom.app X) =
      q.map (ν.app X) ≫ γ.app (G.obj X) := by
    have hfac := (DG ⋙ RF).leftDerived_fac_app δ W (𝟭 D₀) θ X
    change u.app (q.obj X) ≫ (𝟙 _ ≫ RF.map (α.hom.app X)) =
      𝟙 _ ≫ 𝟙 _ ≫ q.map (ν.app X) ≫ 𝟙 _ ≫ γ.app (G.obj X) ≫ 𝟙 _ at hfac
    simpa only [Category.id_comp, Category.comp_id] using hfac
  rw [RF.map_comp, ← Category.assoc, hu]
  have hn := γ.naturality (η.app X)
  change q.map (F.map (η.app X)) ≫ γ.app (T.obj X) =
    γ.app (G.obj X) ≫ RF.map (q'.map (η.app X)) at hn
  rw [Category.assoc, ← hn, ← Category.assoc, ← q.map_comp]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem module_kFlat_resolution {R : Sheaf J CommRingCat.{u}} (P : Cx R) :
    ∃ (K : Cx R) (f : K ⟶ P), K.IsAcyclicTensorKFlat ∧ QuasiIso f := by
  obtain ⟨K, f, hK, _, hf, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients P
  exact ⟨K, f, (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat K).1 hK, hf⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem reductionTower_preserves_kFlat_quasiIso (b : Bool)
    {P P' : Cx (coefficients J A I b)} (f : P ⟶ P')
    (hP : P.IsAcyclicTensorKFlat) (hP' : P'.IsAcyclicTensorKFlat) (hf : QuasiIso f) :
    QuasiIso (((reductionTower J A I b).mapHomologicalComplex (.up ℤ)).map f) := by
  apply (HomologicalComplex.quasiIso_iff_evaluation _).2
  intro n
  have he := change_preserves_kFlat_quasiIso J (finiteMap J A I b n.unop) f hP hP' hf
  have := (siteRestrictScalars_exact (finiteMap J A I b n.unop)).1
  have := (siteRestrictScalars_exact (finiteMap J A I b n.unop)).2
  exact inferInstanceAs (QuasiIso
    (((res (finiteMap J A I b n.unop)).mapHomologicalComplex (.up ℤ)).map
      (((change (finiteMap J A I b n.unop)).mapHomologicalComplex (.up ℤ)).map f)))

/-- The canonical complex-limit unit, chosen by its unique projection formula. -/
private def towerOrdinaryUnit {M : Type*} [Category M] [Preadditive M]
    [HasLimitsOfShape ℕᵒᵖ M] (T : M ⥤ ℕᵒᵖ ⥤ M) [T.PreservesZeroMorphisms]
    [(lim : (ℕᵒᵖ ⥤ M) ⥤ M).PreservesZeroMorphisms]
    (η : Functor.const ℕᵒᵖ ⟶ T) (P : CochainComplex M ℤ) :
    P ⟶ (complexLimitFunctor M).obj ((T.mapHomologicalComplex (.up ℤ)).obj P) :=
  (complexLimitUnit T η P).exists.choose

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem derived_tower_presentation
    {M : Type*} [Category M] [Abelian M] [HasDerivedCategory M]
    [HasDerivedCategory (ℕᵒᵖ ⥤ M)] [HasLimitsOfShape ℕᵒᵖ M]
    [(lim : (ℕᵒᵖ ⥤ M) ⥤ M).Additive]
    (T : M ⥤ ℕᵒᵖ ⥤ M) [T.Additive]
    (η : (Functor.const ℕᵒᵖ : M ⥤ ℕᵒᵖ ⥤ M) ⟶ T)
    (S₀ : CochainComplex M ℤ → Prop)
    (hres : ∀ P : CochainComplex M ℤ,
      ∃ (K : CochainComplex M ℤ) (f : K ⟶ P), S₀ K ∧ QuasiIso f)
    (hT : ∀ {P P' : CochainComplex M ℤ} (f : P ⟶ P'), S₀ P → S₀ P' →
      QuasiIso f → QuasiIso ((T.mapHomologicalComplex (.up ℤ)).map f))
    (RF : DerivedCategory (ℕᵒᵖ ⥤ M) ⥤ DerivedCategory M)
    (γ : complexLimitFunctor M ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RF) :
    ∃ (LT : DerivedCategory M ⥤ DerivedCategory (ℕᵒᵖ ⥤ M))
      (β : DerivedCategory.Q ⋙ LT ⟶ T.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
      (unit : 𝟭 (DerivedCategory M) ⟶ LT ⋙ RF),
      LT.IsLeftDerivedFunctor β (HomologicalComplex.quasiIso M (.up ℤ)) ∧
      (∀ P : CochainComplex M ℤ, S₀ P → IsIso (β.app P)) ∧
      (∀ P : CochainComplex M ℤ,
        unit.app (DerivedCategory.Q.obj P) ≫ RF.map (β.app P) =
          DerivedCategory.Q.map (towerOrdinaryUnit T η P) ≫
            γ.app ((T.mapHomologicalComplex (.up ℤ)).obj P)) := by
  obtain ⟨LT, β, hu, hc⟩ := resolving_derived_cochain T S₀ hres hT
  have : LT.IsLeftDerivedFunctor β (HomologicalComplex.quasiIso M (.up ℤ)) := hu
  let G : M ⥤ ℕᵒᵖ ⥤ M := Functor.const ℕᵒᵖ
  let ηC := NatTrans.mapHomologicalComplex η (.up ℤ)
  let ν : 𝟭 (CochainComplex M ℤ) ⟶
      G.mapHomologicalComplex (.up ℤ) ⋙ complexLimitFunctor M :=
    { app := fun P ↦
        { f := fun q ↦ constLimAdj.unit.app (P.X q)
          comm' := fun i j _ ↦ (constLimAdj.unit.naturality (P.d i j)).symm }
      naturality := fun P P' f ↦ by
        ext q
        exact constLimAdj.unit.naturality (f.f q) }
  obtain ⟨unit, hunit⟩ := derived_tower_unit DerivedCategory.Q DerivedCategory.Q
    (HomologicalComplex.quasiIso M (.up ℤ))
    ν ηC
    G.mapDerivedCategory LT RF G.mapDerivedCategoryFactors β γ
  refine ⟨LT, β, unit, hu, hc, ?_⟩
  intro P
  have hord : ν.app P ≫
      (complexLimitFunctor M).map (ηC.app P) = towerOrdinaryUnit T η P := by
    apply (complexLimitUnit T η P).unique
    · intro q n
      change (limit.lift _ { pt := P.X q, π := 𝟙 _ } ≫
        limMap (η.app (P.X q))) ≫ limit.π _ (op n) = _
      rw [Category.assoc, limMap_π, limit.lift_π_assoc]
      change 𝟙 _ ≫ _ = _
      rw [Category.id_comp]
    · exact (complexLimitUnit T η P).exists.choose_spec
  have h := hunit P
  change unit.app (DerivedCategory.Q.obj P) ≫ RF.map (β.app P) =
    DerivedCategory.Q.map
      (ν.app P ≫
        (complexLimitFunctor M).map (ηC.app P)) ≫
      γ.app ((T.mapHomologicalComplex (.up ℤ)).obj P) at h
  rw [hord] at h
  exact h

/-- The universal derived-tower laws and the actual quotient-unit computation.
Naming this predicate keeps the dependent record small; its normalization is unchanged.
Source: Stacks 099M, 06YY, 0940
(blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def QuotientPresentationLaws (b : Bool)
    (tower : D (coefficients J A I b) ⥤ TD (coefficients J A I b))
    (comparison : Q (coefficients J A I b) ⋙ tower ⟶
      (reductionTower J A I b).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        TQ (coefficients J A I b))
    (unit : 𝟭 (D (coefficients J A I b)) ⟶ tower ⋙ rlim (coefficients J A I b)) : Prop :=
  tower.IsLeftDerivedFunctor comparison
      (HomologicalComplex.quasiIso (Mod (coefficients J A I b)) (ComplexShape.up ℤ)) ∧
    (∀ P : Cx (coefficients J A I b), P.IsAcyclicTensorKFlat →
      (∀ q : ℤ, SheafOfModules.IsFlat (P.X q)) → IsIso (comparison.app P)) ∧
    (∀ P : Cx (coefficients J A I b), P.IsAcyclicTensorKFlat →
      (∀ q : ℤ, SheafOfModules.IsFlat (P.X q)) →
        unit.app ((Q (coefficients J A I b)).obj P) ≫
          (rlim (coefficients J A I b)).map (comparison.app P) =
        (Q (coefficients J A I b)).map (ordinaryUnit J A I b P) ≫
          (limitComparison (coefficients J A I b)).app (reductionComplex J A I b P))

set_option genSizeOf false in
set_option genInjectivity false in
/-- A universal derived strict reduction tower with its prescribed completion unit.
The laws specify the actual quotient maps and total right derived strict inverse limit.
Source: Stacks 099M, 06YY, 0940
(blueprint: lem-weil-pbc-constant-completion-equivalence). -/
structure QuotientPresentation (b : Bool) where
  tower : D (coefficients J A I b) ⥤ TD (coefficients J A I b)
  comparison : Q (coefficients J A I b) ⋙ tower ⟶
    (reductionTower J A I b).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      TQ (coefficients J A I b)
  unit : 𝟭 (D (coefficients J A I b)) ⟶ tower ⋙ rlim (coefficients J A I b)
  laws : QuotientPresentationLaws J A I b tower comparison unit

section

attribute [local irreducible] HasDerivedCategory.standard

set_option backward.isDefEq.respectTransparency.types true in
/-- Strict diagram K-flat replacements and the universal derived limit supply this pair.
Source: Stacks 06YY, 0940, 099M
(blueprint: lem-weil-pbc-constant-completion-equivalence).
Proof: use a single flat-term K-flat representative for the entire reduction tower.
Each scalar extension preserves quasi-isomorphisms between such representatives, so the
resolving-class localization theorem gives the displayed universal tower and computation.
Apply total right derived limit to its strict quotient units. Their naturality and
invariance under quasi-isomorphisms descend the unit to D(O). The comparison square is
its construction, and determines it because every object has such a representative. -/
theorem quotientPresentation_exists (b : Bool) : Nonempty (QuotientPresentation J A I b) := by
  let O := coefficients J A I b
  let := HasDerivedCategory.standard (Mod O)
  let := HasDerivedCategory.standard (ℕᵒᵖ ⥤ Mod O)
  have : (lim : (ℕᵒᵖ ⥤ Mod O) ⥤ Mod O).Additive :=
    Functor.additive_of_preserves_binary_products _
  let hp :=
    derived_tower_presentation (M := Mod O) (reductionTower J A I b) (reductionUnit J A I b)
      (fun P ↦ P.IsAcyclicTensorKFlat) (module_kFlat_resolution J)
      (reductionTower_preserves_kFlat_quasiIso J A I b) (rlim O) (limitComparison O)
  let LT := hp.choose
  let β := hp.choose_spec.choose
  let unit := hp.choose_spec.choose_spec.choose
  have hlaws := hp.choose_spec.choose_spec.choose_spec
  refine ⟨{ tower := LT, comparison := β, unit := unit, laws := ⟨hlaws.1, ?_, ?_⟩ }⟩
  · intro P hP _
    exact hlaws.2.1 P hP
  · intro P _ _
    exact hlaws.2.2 P

end

/-- Choose the universally specified reduction tower and normalized unit.
Source: Stacks 099M (blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def quotientPresentation (b : Bool) : QuotientPresentation J A I b :=
  Classical.choice (quotientPresentation_exists J A I b)

attribute [local irreducible] quotientPresentation

/-- Quotient-tower derived completion, using total right derived inverse limit.
Source: Stacks 099M (blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def completion (b : Bool) : D (coefficients J A I b) ⥤ D (coefficients J A I b) :=
  (quotientPresentation J A I b).tower ⋙ rlim (coefficients J A I b)

/-- Its prescribed quotient-tower completion unit. Source: Stacks 099M
(blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def completionUnit (b : Bool) : 𝟭 (D (coefficients J A I b)) ⟶ completion J A I b :=
  (quotientPresentation J A I b).unit

/-- The existing strict Koszul presentation, for the images of the given generators.
Source: Stacks 0A0E (blueprint: lem-weil-pbc-constant-completion-equivalence). -/
abbrev KoszulPresentation (b : Bool) (r : ℕ) (a : Fin r → A) :=
  letI := HasDerivedCategory.standard (Mod (coefficients J A I b))
  letI := HasDerivedCategory.standard (ℕᵒᵖ ⥤ Mod (coefficients J A I b))
  RingedKoszulLimitPresentation (coefficients J A I b) r
    (fun i ↦ algebraSection (baseMap J A I b) (a i))

/-- Completion from the actual dual Koszul tensor tower with transitions (a_i,1).
Source: Stacks 0A0E (blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def koszulCompletion {b : Bool} {r : ℕ} {a : Fin r → A}
    (K : KoszulPresentation J A I b r a) : D (coefficients J A I b) ⥤
      D (coefficients J A I b) :=
  letI := HasDerivedCategory.standard (Mod (coefficients J A I b))
  letI := HasDerivedCategory.standard (ℕᵒᵖ ⥤ Mod (coefficients J A I b))
  K.completion

/-- The specified degree-zero Koszul unit in the standard localization.
Source: Stacks 0A0E (blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def koszulUnit {b : Bool} {r : ℕ} {a : Fin r → A}
    (K : KoszulPresentation J A I b r a) (M : D (coefficients J A I b)) :
    M ⟶ (koszulCompletion J A I K).obj M :=
  letI := HasDerivedCategory.standard (Mod (coefficients J A I b))
  letI := HasDerivedCategory.standard (ℕᵒᵖ ⥤ Mod (coefficients J A I b))
  K.unit M

/-- Koszul and finite-quotient completion are canonically identified, preserving the units;
their common functor is the reflector for the local internal-Hom completeness condition.
Source: Stacks 099L, 099M, 0A0E
(blueprint: lem-weil-pbc-constant-completion-equivalence).
Proof: apply the ringed Koszul reflector to the global generators, including the empty
list. For constant coefficients the Noetherian Koszul augmentation has pro-zero cone.
Exact constant sheafification and tensor by a fixed K-flat model preserve this property.
The strict-tower derived-limit theorem inverts the augmentation and identifies its unit
with the quotient unit. For completed coefficients, restrict to constant coefficients:
the finite reductions, strict Koszul tensors and units agree, and restriction identifies
total derived limits by the flat exact adjunction on strict towers. Conservativity
of exact restriction detects the augmentation isomorphism over the completion as well.
Transport the reflector property and the unit-isomorphism criterion across this
unit-preserving natural isomorphism. -/
theorem koszul_quotient_reflector [IsNoetherianRing A] (b : Bool) (r : ℕ) (a : Fin r → A)
    (ha : Ideal.span (Set.range a) = I) :
    ∃ K : KoszulPresentation J A I b r a,
      (∃ e : koszulCompletion J A I K ≅ completion J A I b,
        ∀ M : D (coefficients J A I b), koszulUnit J A I K M ≫ e.hom.app M =
          (completionUnit J A I b).app M) ∧
      (∀ M : D (coefficients J A I b),
        IsComplete (finiteMap J A I b 0) ((completion J A I b).obj M)) ∧
      (∀ (M L : D (coefficients J A I b)), IsComplete (finiteMap J A I b 0) L →
        Function.Bijective (fun f : (completion J A I b).obj M ⟶ L ↦
          (completionUnit J A I b).app M ≫ f)) ∧
      (∀ M : D (coefficients J A I b),
        IsIso ((completionUnit J A I b).app M) ↔ IsComplete (finiteMap J A I b 0) M) := by
  sorry

/-- Restriction identifies both completions and their specified units.
Source: Stacks 099L, 099M (blueprint: lem-weil-pbc-constant-completion-equivalence).
Proof: at the representative level finite reduction comparisons and dual Koszul tensor
comparisons preserve their strict transitions and degree-zero units. Restriction carries
K-injective strict tower resolutions to K-injective resolutions, since it is right
adjoint to flat exact extension of scalars. Apply limits and the universal comparisons.
This gives the natural isomorphism and the stated equality of the actual units. -/
theorem completion_restriction [IsNoetherianRing A] :
    ∃ e : dres (coefficientMap J A I) ⋙ completion J A I false ≅
        completion J A I true ⋙ dres (coefficientMap J A I),
      ∀ M : D (completed J A I),
        (completionUnit J A I false).app ((dres (coefficientMap J A I)).obj M) ≫
          e.hom.app M =
        (dres (coefficientMap J A I)).map ((completionUnit J A I true).app M) := by
  sorry

set_option backward.isDefEq.respectTransparency false in
/-- Restriction preserves the Koszul-to-quotient comparison itself and both units.
Source: Stacks 099M, 0A0E (blueprint: lem-weil-pbc-constant-completion-equivalence).
Proof: the finite Koszul complexes are finite sums of the chosen representative with
identical differentials and transitions after restriction. Their augmentations to the
finite quotients are identical as well. Apply the strict derived-limit restriction
comparison to this square of towers. The resulting square is the displayed equation.
Every augmentation preserves the degree-zero element 1, giving both unit equations.
Alternatively the reflector universal property determines this same square uniquely. -/
theorem koszul_quotient_restriction [IsNoetherianRing A] (r : ℕ) (a : Fin r → A)
    (ha : Ideal.span (Set.range a) = I) :
    ∃ (KR : KoszulPresentation J A I false r a) (KB : KoszulPresentation J A I true r a)
      (θR : koszulCompletion J A I KR ≅ completion J A I false)
      (θB : koszulCompletion J A I KB ≅ completion J A I true)
      (κ : dres (coefficientMap J A I) ⋙ koszulCompletion J A I KR ≅
        koszulCompletion J A I KB ⋙ dres (coefficientMap J A I))
      (χ : dres (coefficientMap J A I) ⋙ completion J A I false ≅
        completion J A I true ⋙ dres (coefficientMap J A I)),
      (∀ N : D (constant J A), koszulUnit J A I KR N ≫ θR.hom.app N =
        (completionUnit J A I false).app N) ∧
      (∀ M : D (completed J A I), koszulUnit J A I KB M ≫ θB.hom.app M =
        (completionUnit J A I true).app M) ∧
      (∀ M : D (completed J A I),
        koszulUnit J A I KR ((dres (coefficientMap J A I)).obj M) ≫ κ.hom.app M =
          (dres (coefficientMap J A I)).map (koszulUnit J A I KB M)) ∧
      (∀ M : D (completed J A I),
        (completionUnit J A I false).app ((dres (coefficientMap J A I)).obj M) ≫
          χ.hom.app M =
          (dres (coefficientMap J A I)).map ((completionUnit J A I true).app M)) ∧
      (∀ M : D (completed J A I),
        θR.hom.app ((dres (coefficientMap J A I)).obj M) ≫ χ.hom.app M =
          κ.hom.app M ≫ (dres (coefficientMap J A I)).map (θB.hom.app M)) := by
  obtain ⟨KR, ⟨θR, hR⟩, _⟩ := koszul_quotient_reflector J A I false r a ha
  obtain ⟨KB, ⟨θB, hB⟩, _⟩ := koszul_quotient_reflector J A I true r a ha
  obtain ⟨χ, hχ⟩ := completion_restriction J A I
  let F := dres (coefficientMap J A I)
  let κ : F ⋙ koszulCompletion J A I KR ≅ koszulCompletion J A I KB ⋙ F :=
    Functor.isoWhiskerLeft F θR ≪≫ χ ≪≫ Functor.isoWhiskerRight θB.symm F
  refine ⟨KR, KB, θR, θB, κ, χ, hR, hB, ?_, hχ, ?_⟩
  · intro M
    change koszulUnit J A I KR (F.obj M) ≫
      (θR.hom.app (F.obj M) ≫ χ.hom.app M ≫ F.map (θB.inv.app M)) = _
    rw [← Category.assoc, hR, ← Category.assoc, hχ, ← hB M, F.map_comp]
    simp only [Category.assoc, ← F.map_comp, θB.hom_inv_id_app, Category.comp_id]
    rfl
  · intro M
    change θR.hom.app (F.obj M) ≫ χ.hom.app M =
      (θR.hom.app (F.obj M) ≫ χ.hom.app M ≫ F.map (θB.inv.app M)) ≫
        F.map (θB.hom.app M)
    simp only [Category.assoc, ← F.map_comp, θB.inv_hom_id_app, F.map_id]
    exact congrArg (fun t ↦ θR.hom.app (F.obj M) ≫ t)
      (Category.comp_id (χ.hom.app M)).symm

variable {J A I}

/-- Levelwise restriction on strict module towers. Source: Stacks 0940
(blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def tres {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) :
    (ℕᵒᵖ ⥤ Mod B) ⥤ (ℕᵒᵖ ⥤ Mod R) :=
  (Functor.whiskeringRight ℕᵒᵖ (Mod B) (Mod R)).obj (res φ)

/-- Levelwise restriction is additive and exact, since evaluation computes these laws.
Source: Stacks 0940 (blueprint: lem-weil-pbc-constant-completion-equivalence).
Proof: evaluate at every tower index. Restriction is additive and exact on module sheaves
by siteRestrictScalars_exact, and finite limits and colimits of functors are pointwise. -/
theorem tres_exact {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) :
    (tres φ).Additive ∧ PreservesFiniteLimits (tres φ) ∧
      PreservesFiniteColimits (tres φ) := by
  have := (siteRestrictScalars_exact φ).1
  have := (siteRestrictScalars_exact φ).2
  change ((Functor.whiskeringRight ℕᵒᵖ (Mod B) (Mod R)).obj (res φ)).Additive ∧ _
  dsimp only [tres, res]
  refine ⟨inferInstance, ⟨fun K _ _ ↦ ?_⟩, ⟨fun K _ _ ↦ ?_⟩⟩ <;> infer_instance

/-- The additive structure of the specified levelwise restriction.
Source: Stacks 0940 (blueprint: lem-weil-pbc-constant-completion-equivalence). -/
instance tres_additive {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) :
    (tres φ).Additive := (tres_exact φ).1

/-- Finite limits for levelwise restriction.
Source: Stacks 0940 (blueprint: lem-weil-pbc-constant-completion-equivalence). -/
instance tres_finiteLimits {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) :
    PreservesFiniteLimits (tres φ) := (tres_exact φ).2.1

/-- Finite colimits for levelwise restriction.
Source: Stacks 0940 (blueprint: lem-weil-pbc-constant-completion-equivalence). -/
instance tres_finiteColimits {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) :
    PreservesFiniteColimits (tres φ) := (tres_exact φ).2.2

/-- Exact levelwise restriction induces restriction on the derived strict tower categories.
Source: Stacks 0940 (blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def tdres {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) : TD B ⥤ TD R :=
  letI := HasDerivedCategory.standard (ℕᵒᵖ ⥤ Mod R)
  letI := HasDerivedCategory.standard (ℕᵒᵖ ⥤ Mod B)
  letI := (siteRestrictScalars_exact φ).1
  letI := (siteRestrictScalars_exact φ).2
  (tres φ).mapDerivedCategory

/-- The exact levelwise restriction comparison on strict tower complexes.
Source: Stacks 0940 (blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def tresFactors {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) :
    (tres φ).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ TQ R ≅ TQ B ⋙ tdres φ :=
  letI := HasDerivedCategory.standard (ℕᵒᵖ ⥤ Mod R)
  letI := HasDerivedCategory.standard (ℕᵒᵖ ⥤ Mod B)
  letI := (siteRestrictScalars_exact φ).1
  letI := (siteRestrictScalars_exact φ).2
  (tres φ).mapDerivedCategoryFactors.symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The finite comparisons form a strict tower isomorphism, with all quotient transitions.
The normalization identifies each component with the S_n-linear comparison above.
Source: Stacks 099L, 06YY (blueprint: lem-weil-pbc-constant-completion-equivalence).
Proof: on s tensor m, transition then comparison and comparison then transition both give
bar(s) tensor m. Sheafification extends equality; naturality in M gives the functor
isomorphism of strict towers. The component formulas determine it uniquely. -/
theorem reductionTowerComparison_existsUnique (J : GrothendieckTopology C) (A : Type u)
    [CommRing A] [IsNoetherianRing A] (I : Ideal A) :
    ∃! e : res (coefficientMap J A I) ⋙ reductionTower J A I false ≅
        reductionTower J A I true ⋙ tres (coefficientMap J A I),
      ∀ (M : Mod (completed J A I)) (n : ℕ) (U : Cᵒᵖ)
        (x : ((change (quotient J A I n)).obj ((res (coefficientMap J A I)).obj M)).val.obj U),
        ((e.hom.app M).app (op n)).val.app U x =
          ((finiteComparison J A I n).hom.app M).val.app U x := by
  let φ := coefficientMap J A I
  have hφ (n : ℕ) : φ ≫ projection J A I n = quotient J A I n := by
    exact limit.lift_π (quotientCone J A I) (op n)
  let en (n : ℕ) : res φ ⋙ reduction J A I false n ≅
      reduction J A I true n ⋙ res φ :=
    Functor.isoWhiskerRight (finiteComparison J A I n) (res (quotient J A I n)) ≪≫
      Functor.isoWhiskerLeft (change (projection J A I n))
        (resCompIso φ (projection J A I n) (quotient J A I n) (hφ n)).symm
  have hen (n : ℕ) (M : Mod (completed J A I)) (U : Cᵒᵖ)
      (x : ((change (quotient J A I n)).obj ((res φ).obj M)).val.obj U) :
      ((en n).hom.app M).val.app U x =
        ((finiteComparison J A I n).hom.app M).val.app U x := by
    change ((resCompIso φ (projection J A I n) (quotient J A I n) (hφ n)).inv.app
      ((change (projection J A I n)).obj M)).val.app U
        (((finiteComparison J A I n).hom.app M).val.app U x) = _
    exact resCompIso_inv_apply φ (projection J A I n) (quotient J A I n) (hφ n)
      ((change (projection J A I n)).obj M) U
      (((finiteComparison J A I n).hom.app M).val.app U x)
  have hfinite (n : ℕ) (M : Mod (completed J A I)) (U : Cᵒᵖ)
      (s : (finite J A I n).obj.obj U) (m : M.val.obj U) :
      ((finiteComparison J A I n).hom.app M).val.app U
          (tensorSection (quotient J A I n) ((res φ).obj M) U s m) =
        tensorSection (projection J A I n) M U s m :=
    (finiteComparison_existsUnique J A I n).exists.choose_spec M U s m
  clear_value en
  have hstep (M : Mod (completed J A I)) (n : ℕ) :
      ((reductionTower J A I false).obj ((res φ).obj M)).map
          (homOfLE (Nat.le_succ n)).op ≫ (en n).hom.app M =
        (en (n + 1)).hom.app M ≫
          ((tres φ).obj ((reductionTower J A I true).obj M)).map
            (homOfLE (Nat.le_succ n)).op := by
    simp only [reductionTower, tres, Functor.whiskeringRight_obj_obj,
      Functor.comp_map, Functor.flip_obj_map,
      Functor.ofOpSequence_map_homOfLE_succ]
    apply restrictedTensor_hom_ext (quotient J A I (n + 1)) ((res φ).obj M)
    intro U s m
    change ((en n).hom.app M).val.app U
        (((reductionStep J A I false n).app ((res φ).obj M)).val.app U
          (tensorSection (quotient J A I (n + 1)) ((res φ).obj M) U s m)) =
      ((reductionStep J A I true n).app M).val.app U
        (((en (n + 1)).hom.app M).val.app U
          (tensorSection (quotient J A I (n + 1)) ((res φ).obj M) U s m))
    rw [hen, hen, hfinite]
    rw [show ((reductionStep J A I false n).app ((res φ).obj M)).val.app U
        (tensorSection (quotient J A I (n + 1)) ((res φ).obj M) U s m) =
      tensorSection (quotient J A I n) ((res φ).obj M) U
        ((transition J A I n).hom.app U s) m from
          (reductionStep_existsUnique J A I false n).exists.choose_spec _ U s m]
    rw [hfinite]
    exact ((reductionStep_existsUnique J A I true n).exists.choose_spec M U s m).symm
  let e : res φ ⋙ reductionTower J A I false ≅
      reductionTower J A I true ⋙ tres φ :=
    NatIso.ofComponents
      (fun M ↦ NatIso.ofComponents (fun n ↦ (en n.unop).app M)
        (fun f ↦ (NatTrans.ofOpSequence
          (F := (reductionTower J A I false).obj ((res φ).obj M))
          (G := (tres φ).obj ((reductionTower J A I true).obj M))
          (fun n ↦ (en n).hom.app M) (hstep M)).naturality f))
      (by
        intro M N f
        apply NatTrans.ext
        funext n
        exact (en n.unop).hom.naturality f)
  refine ⟨e, fun M n U x ↦ hen n M U x, ?_⟩
  intro e' he'
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply NatTrans.ext
  funext n
  ext U x
  exact (he' M n.unop U x).trans (hen n.unop M U x).symm

/-- The strict tower comparison with the prescribed S_n-linear finite components.
Source: Stacks 099L (blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def reductionTowerComparison (J : GrothendieckTopology C) (A : Type u) [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) :
    res (coefficientMap J A I) ⋙ reductionTower J A I false ≅
      reductionTower J A I true ⋙ tres (coefficientMap J A I) :=
  (reductionTowerComparison_existsUnique J A I).exists.choose

/-- Restricting before forming the strict quotient tower is additive.
Source: Stacks 06YY (blueprint: lem-weil-pbc-constant-completion-equivalence).
Proof: at every tower index the functor is scalar restriction followed by scalar
extension and restriction. All three maps preserve sums of module homomorphisms.
Equality after every evaluation is equality in the strict functor category. -/
theorem restrictionReduction_additive (J : GrothendieckTopology C) (A : Type u)
    [CommRing A] (I : Ideal A) :
    (res (coefficientMap J A I) ⋙ reductionTower J A I false).Additive := by
  have : (res (coefficientMap J A I)).Additive := inferInstance
  constructor
  intro M N f g
  change (reductionTower J A I false).map
    ((res (coefficientMap J A I)).map (f + g)) = _
  rw [Functor.map_add]
  exact Functor.map_add (reductionTower J A I false)

attribute [instance] restrictionReduction_additive

/-- Reducing and then restricting a completed-coefficient tower is additive.
Source: Stacks 06YY (blueprint: lem-weil-pbc-constant-completion-equivalence).
Proof: evaluate at every tower index. Scalar extension and both restrictions preserve
addition of module maps, so their composite does as well. -/
theorem reductionRestriction_additive (J : GrothendieckTopology C) (A : Type u)
    [CommRing A] (I : Ideal A) :
    (reductionTower J A I true ⋙ tres (coefficientMap J A I)).Additive := by
  infer_instance

attribute [instance] reductionRestriction_additive

/-- The completed strict reduction followed by restriction preserves zero maps.
Source: Stacks 06YY (blueprint: lem-weil-pbc-constant-completion-equivalence).
Proof: apply the additive identity of reductionRestriction_additive to the zero map. -/
theorem reductionRestriction_preservesZero (J : GrothendieckTopology C) (A : Type u)
    [CommRing A] (I : Ideal A) :
    (reductionTower J A I true ⋙ tres (coefficientMap J A I)).PreservesZeroMorphisms := by
  infer_instance

attribute [instance] reductionRestriction_preservesZero

-- Use the generic composite-functor instances while elaborating the remaining proofs.
-- Restore the exported instances at the end of the module.
attribute [-instance] restrictionReduction_additive reductionRestriction_additive
  reductionRestriction_preservesZero


/-- Apply the prescribed strict tower comparison termwise to complexes.
Source: Stacks 099L, 06YY (blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def reductionTowerComparisonComplex (J : GrothendieckTopology C) (A : Type u)
    [CommRing A] [IsNoetherianRing A] (I : Ideal A) :
    (res (coefficientMap J A I)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        (reductionTower J A I false).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      (reductionTower J A I true).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        (tres (coefficientMap J A I)).mapHomologicalComplex (ComplexShape.up ℤ) :=
  let liftIso {A₀ A₁ A₂ A₃ : Type (u + 1)}
      [Category.{u} A₀] [Category.{u} A₁] [Category.{u} A₂] [Category.{u} A₃]
      [Preadditive A₀] [Preadditive A₁] [Preadditive A₂] [Preadditive A₃]
      (F : A₀ ⥤ A₁) (G : A₁ ⥤ A₃) (H : A₀ ⥤ A₂) (K : A₂ ⥤ A₃)
      [F.Additive] [G.Additive] [H.Additive] [K.Additive] (e : F ⋙ G ≅ H ⋙ K) :
      F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          G.mapHomologicalComplex (ComplexShape.up ℤ) ≅
        H.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          K.mapHomologicalComplex (ComplexShape.up ℤ) :=
    Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (ComplexShape.up ℤ) ≪≫
      NatIso.mapHomologicalComplex e (ComplexShape.up ℤ) ≪≫
      (Functor.mapHomologicalComplexCompIso (Iso.refl (H ⋙ K)) (ComplexShape.up ℤ)).symm
  letI := reductionTower_additive J A I false
  letI := reductionTower_additive J A I true
  liftIso (res (coefficientMap J A I)) (reductionTower J A I false)
    (reductionTower J A I true) (tres (coefficientMap J A I))
    (reductionTowerComparison J A I)

/-- The representative computation square for a derived comparison of strict towers.
The functors are abstract here so that checking the equation never unfolds any concrete
scalar-restriction or reduction-tower construction. The four sides are the restriction
computation, the two derived-tower computations, and their strict comparison.
Source: Stacks 099L, 06YY
(blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def DerivedTowerComparisonFormula
    {A₀ A₁ A₂ A₃ A₄ A₅ A₆ A₇ : Type*}
    [Category A₀] [Category A₁] [Category A₂] [Category A₃]
    [Category A₄] [Category A₅] [Category A₆] [Category A₇]
    {qB : A₀ ⥤ A₄} {qR : A₁ ⥤ A₅} {tqB : A₂ ⥤ A₆} {tqR : A₃ ⥤ A₇}
    {rc : A₀ ⥤ A₁} {tc : A₂ ⥤ A₃} {dr : A₄ ⥤ A₅} {dt : A₆ ⥤ A₇}
    {tr : A₅ ⥤ A₇} {tb : A₄ ⥤ A₆} {redR : A₁ ⥤ A₃} {redB : A₀ ⥤ A₂}
    (α : rc ⋙ qR ≅ qB ⋙ dr) (βR : qR ⋙ tr ⟶ redR ⋙ tqR)
    (γ : rc ⋙ redR ≅ redB ⋙ tc) (δ : tc ⋙ tqR ≅ tqB ⋙ dt)
    (βB : qB ⋙ tb ⟶ redB ⋙ tqB) (e : dr ⋙ tr ≅ tb ⋙ dt) (P : A₀) : Prop :=
  tr.map (α.inv.app P) ≫ βR.app (rc.obj P) ≫ tqR.map (γ.hom.app P) ≫
      δ.hom.app (redB.obj P) = e.hom.app (qB.obj P) ≫ dt.map (βB.app P)

/-- The strict comparison descends through the universal derived-tower construction.
Source: Stacks 099L, 06YY (blueprint: lem-weil-pbc-constant-completion-equivalence).
Proof: restrict one flat-term K-flat B-representative, which remains K-flat by flatness
of the coefficient extension. Apply the strict tower comparison and both universal
computation counits. Their invariance under quasi-isomorphisms gives the derived natural
isomorphism, and the formula is exactly its normalized representative computation. -/
theorem derivedReductionTowerComparison (J : GrothendieckTopology C) (A : Type u)
    [CommRing A] [IsNoetherianRing A] (I : Ideal A) :
    ∃ e : dres (coefficientMap J A I) ⋙ (quotientPresentation J A I false).tower ≅
        (quotientPresentation J A I true).tower ⋙ tdres (coefficientMap J A I),
      ∀ P : Cx (completed J A I), P.IsAcyclicTensorKFlat →
        (∀ q : ℤ, SheafOfModules.IsFlat (P.X q)) →
        DerivedTowerComparisonFormula (resFactors (coefficientMap J A I))
          (quotientPresentation J A I false).comparison (reductionTowerComparisonComplex J A I)
          (tresFactors (coefficientMap J A I))
          (quotientPresentation J A I true).comparison e P := by
  sorry

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Ordinary inverse limits commute with scalar restriction by their coordinate maps.
Source: Stacks 0940 (blueprint: lem-weil-pbc-constant-completion-equivalence).
Proof: module restriction preserves limits, computed on underlying additive sheaves.
The limit comparison is invertible degreewise and commutes with differentials. Its
coordinate equations determine it uniquely, so this is a canonical chain isomorphism. -/
theorem limitRestriction_existsUnique {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) :
    ∃! e : ordinaryLimit B ⋙ (res φ).mapHomologicalComplex (ComplexShape.up ℤ) ≅
        (tres φ).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ ordinaryLimit R,
      ∀ (P : CochainComplex (ℕᵒᵖ ⥤ Mod B) ℤ) (q : ℤ) (n : ℕ),
        (e.hom.app P).f q ≫
          limit.π (((tres φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj P |>.X q) (op n) =
        (res φ).map (limit.π (P.X q) (op n)) := by
  have : PreservesLimitsOfSize.{u, u} (res φ) := siteRestrictScalars_preservesLimits φ
  have : PreservesLimitsOfSize.{0, 0} (res φ) := preservesLimitsOfSize_shrink (res φ)
  let liftIso {A₀ A₁ A₂ A₃ : Type (u + 1)}
      [Category.{u} A₀] [Category.{u} A₁] [Category.{u} A₂] [Category.{u} A₃]
      [Preadditive A₀] [Preadditive A₁] [Preadditive A₂] [Preadditive A₃]
      (F : A₀ ⥤ A₁) (G : A₁ ⥤ A₃) (H : A₀ ⥤ A₂) (K : A₂ ⥤ A₃)
      [F.Additive] [G.Additive] [H.Additive] [K.Additive] (e : F ⋙ G ≅ H ⋙ K) :
      F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          G.mapHomologicalComplex (ComplexShape.up ℤ) ≅
        H.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          K.mapHomologicalComplex (ComplexShape.up ℤ) :=
    Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (ComplexShape.up ℤ) ≪≫
      NatIso.mapHomologicalComplex e (ComplexShape.up ℤ) ≪≫
      (Functor.mapHomologicalComplexCompIso (Iso.refl (H ⋙ K)) (ComplexShape.up ℤ)).symm
  have liftIso_hom_f {A₀ A₁ A₂ A₃ : Type (u + 1)}
      [Category.{u} A₀] [Category.{u} A₁] [Category.{u} A₂] [Category.{u} A₃]
      [Preadditive A₀] [Preadditive A₁] [Preadditive A₂] [Preadditive A₃]
      (F : A₀ ⥤ A₁) (G : A₁ ⥤ A₃) (H : A₀ ⥤ A₂) (K : A₂ ⥤ A₃)
      [F.Additive] [G.Additive] [H.Additive] [K.Additive] (e : F ⋙ G ≅ H ⋙ K)
      (P : CochainComplex A₀ ℤ) (q : ℤ) :
      ((liftIso F G H K e).hom.app P).f q = e.hom.app (P.X q) := by
    dsimp only [liftIso, Iso.trans_hom, Iso.symm_hom,
      Functor.mapHomologicalComplexCompIso, NatIso.mapHomologicalComplex,
      NatTrans.mapHomologicalComplex, NatTrans.comp_app, HomologicalComplex.comp_f]
    simp only [Iso.refl_hom, Iso.refl_inv, NatTrans.id_app]
    exact (Category.id_comp _).trans (Category.comp_id _)
  have : (lim : (ℕᵒᵖ ⥤ Mod B) ⥤ Mod B).Additive :=
    Functor.additive_of_preserves_binary_products _
  have : (lim : (ℕᵒᵖ ⥤ Mod R) ⥤ Mod R).Additive :=
    Functor.additive_of_preserves_binary_products _
  let α : (lim : (ℕᵒᵖ ⥤ Mod B) ⥤ Mod B) ⋙ res φ ≅
      tres φ ⋙ (lim : (ℕᵒᵖ ⥤ Mod R) ⥤ Mod R) := preservesLimitNatIso (res φ)
  let e : ordinaryLimit B ⋙ (res φ).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      (tres φ).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ ordinaryLimit R :=
    liftIso (lim : (ℕᵒᵖ ⥤ Mod B) ⥤ Mod B) (res φ) (tres φ)
      (lim : (ℕᵒᵖ ⥤ Mod R) ⥤ Mod R) α
  have he (P : CochainComplex (ℕᵒᵖ ⥤ Mod B) ℤ) (q : ℤ) (n : ℕ) :
      (e.hom.app P).f q ≫
        limit.π (((tres φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj P |>.X q) (op n) =
      (res φ).map (limit.π (P.X q) (op n)) := by
    change ((liftIso _ _ _ _ α).hom.app P).f q ≫ _ = _
    rw [liftIso_hom_f]
    exact preservesLimitIso_hom_π (res φ) (P.X q) (op n)
  refine ⟨e, he, ?_⟩
  intro g hg
  apply Iso.ext
  apply NatTrans.ext
  funext P
  apply HomologicalComplex.hom_ext
  intro q
  apply limit.hom_ext
  intro n
  exact (hg P q n.unop).trans (he P q n.unop).symm

/-- The ordinary limit comparison fixed by its actual projections. Source: Stacks 0940
(blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def limitRestriction {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) :
    ordinaryLimit B ⋙ (res φ).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      (tres φ).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ ordinaryLimit R :=
  (limitRestriction_existsUnique φ).exists.choose

section ExactScalarExtension
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The proved extension-tensor comparison, selected once for each module. -/
private def extensionTensorComponent {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B)
    (M : Mod R) :
    (SheafOfModules.monoidalCategory R).tensorObj
      ((res φ).obj (SheafOfModules.unit (siteModuleRings B))) M ≅
        (res φ).obj ((change φ).obj M) :=
  (SheafOfModules.exists_extensionTensorComparison φ M).choose

/-- Its section formula is the original balanced tensor map. -/
private theorem extensionTensorComponent_pure {R B : Sheaf J CommRingCat.{u}}
    (φ : R ⟶ B) (M : Mod R) (U : Cᵒᵖ) (s : B.obj.obj U) (m : M.val.obj U) :
    (extensionTensorComponent φ M).hom.val.app U
        (SheafOfModules.RingedTensor.pure R
          ((res φ).obj (SheafOfModules.unit (siteModuleRings B))) M U s m) =
      tensorSection φ M U s m :=
  (SheafOfModules.exists_extensionTensorComparison φ M).choose_spec U s m

attribute [irreducible] extensionTensorComponent

/-- The pure-tensor comparison is natural in the module argument.
Source: Stacks 03EK; the component is exists_extensionTensorComparison. -/
private def extensionTensorIso {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) :
    letI := SheafOfModules.monoidalCategory R
    MonoidalCategory.tensorLeft ((res φ).obj (SheafOfModules.unit (siteModuleRings B))) ≅
      change φ ⋙ res φ := by
  letI := SheafOfModules.monoidalCategory R
  let N := (res φ).obj (SheafOfModules.unit (siteModuleRings B))
  refine NatIso.ofComponents (extensionTensorComponent φ) ?_
  intro M M' f
  apply SheafOfModules.RingedTensor.pure_hom_ext R N M
  intro U s m
  change (extensionTensorComponent φ M').hom.val.app U
      ((MonoidalCategory.whiskerLeft N f).val.app U
        (SheafOfModules.RingedTensor.pure R N M U s m)) =
    ((change φ).map f).val.app U
      ((extensionTensorComponent φ M).hom.val.app U
        (SheafOfModules.RingedTensor.pure R N M U s m))
  rw [← MonoidalCategory.id_tensorHom, SheafOfModules.RingedTensor.pure_map]
  change (extensionTensorComponent φ M').hom.val.app U
      (SheafOfModules.RingedTensor.pure R N M' U s (f.val.app U m)) = _
  rw [extensionTensorComponent_pure, extensionTensorComponent_pure]
  exact (tensorSection_map φ f U s m).symm

/-- Flatness of the target ring makes scalar extension exact.
Source: Stacks 03EK. Identify its restriction with tensoring by the flat target,
reflect finite limits through restriction, and use the extension adjunction for colimits. -/
private theorem change_exact {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B)
    (hflat : SheafOfModules.IsFlat
      ((res φ).obj (SheafOfModules.unit (siteModuleRings B)))) :
    PreservesFiniteLimits (change φ) ∧ PreservesFiniteColimits (change φ) := by
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  let N := (res φ).obj (SheafOfModules.unit (siteModuleRings B))
  have : PreservesFiniteLimits (MonoidalCategory.tensorRight N) := hflat.1
  have : PreservesFiniteLimits (MonoidalCategory.tensorLeft N) :=
    preservesFiniteLimits_of_natIso
      (BraidedCategory.tensorLeftIsoTensorRight N).symm
  have : PreservesFiniteLimits (change φ ⋙ res φ) :=
    preservesFiniteLimits_of_natIso (extensionTensorIso φ)
  have : (res φ).ReflectsIsomorphisms := siteRestrictScalars_reflectsIsomorphisms φ
  have : PreservesFiniteLimits (res φ) := (siteRestrictScalars_exact φ).1
  have : ReflectsFiniteLimits (res φ) :=
    { reflects := fun K _ _ ↦ reflectsLimitsOfShape_of_reflectsIsomorphisms }
  have hleft : PreservesFiniteLimits (change φ) :=
    preservesFiniteLimits_of_reflects_of_preserves (change φ) (res φ)
  have : PreservesColimitsOfSize.{0, 0} (change φ) :=
    (SheafOfModules.RingedTensor.tensorAdjunction φ).leftAdjoint_preservesColimits
  have hright : PreservesFiniteColimits (change φ) := inferInstance
  exact ⟨hleft, hright⟩

end ExactScalarExtension

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The exact restriction/limit square derives by the tower adjunction.
The abstract ring parameters prevent elaboration from unfolding a completion limit. -/
private theorem derivedLimitRestriction_of_flat {R B : Sheaf J CommRingCat.{u}}
    (φ : R ⟶ B) (hflat : SheafOfModules.IsFlat
      ((res φ).obj (SheafOfModules.unit (siteModuleRings B)))) :
    ∃ e : rlim B ⋙ dres φ ≅
        tdres φ ⋙ rlim R,
      ∀ P : CochainComplex (ℕᵒᵖ ⥤ Mod B) ℤ,
        (dres φ).map ((limitComparison B).app P) ≫
          e.hom.app ((TQ B).obj P) =
        (resFactors φ).inv.app
            ((ordinaryLimit B).obj P) ≫
          (Q R).map ((limitRestriction φ).hom.app P) ≫
          (limitComparison R).app
            (((tres φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
          (rlim R).map ((tresFactors φ).hom.app P) := by
  let := HasDerivedCategory.standard (Mod R)
  let := HasDerivedCategory.standard (Mod B)
  let := HasDerivedCategory.standard (ℕᵒᵖ ⥤ Mod R)
  let := HasDerivedCategory.standard (ℕᵒᵖ ⥤ Mod B)
  have : IsGrothendieckAbelian.{u} (ℕᵒᵖ ⥤ Mod B) := by
    have := smallModuleDiagrams_isGrothendieckAbelian J (siteModuleRings B)
      (ULiftHom.{u} (ULift.{u} ℕᵒᵖ))
    exact IsGrothendieckAbelian.of_equivalence
      (ULiftHomULiftCategory.equiv.{u, u} ℕᵒᵖ).congrLeft.symm
  have hex := change_exact φ hflat
  have : PreservesFiniteLimits (change φ) := hex.1
  have : PreservesFiniteColimits (change φ) := hex.2
  let E := (Functor.whiskeringRight ℕᵒᵖ (Mod R) (Mod B)).obj (change φ)
  have : E.Additive := inferInstance
  have : PreservesFiniteLimits E := ⟨fun K _ _ ↦ inferInstance⟩
  have : PreservesFiniteColimits E := ⟨fun K _ _ ↦ inferInstance⟩
  have : E.PreservesHomology := {}
  have adj : E ⊣ tres φ :=
    Adjunction.whiskerRight ℕᵒᵖ (SheafOfModules.RingedTensor.tensorAdjunction φ)
  have : (tres φ).PreservesKInjectiveComplexes := adj.preservesKInjectiveComplexes
  have : PreservesLimitsOfSize.{u, u} (res φ) := siteRestrictScalars_preservesLimits φ
  have : PreservesLimitsOfSize.{0, 0} (res φ) := preservesLimitsOfSize_shrink (res φ)
  have : (lim : (ℕᵒᵖ ⥤ Mod B) ⥤ Mod B).Additive :=
    Functor.additive_of_preserves_binary_products _
  have : (lim : (ℕᵒᵖ ⥤ Mod R) ⥤ Mod R).Additive :=
    Functor.additive_of_preserves_binary_products _
  let c : (lim : (ℕᵒᵖ ⥤ Mod B) ⥤ Mod B) ⋙ res φ ≅
      tres φ ⋙ (lim : (ℕᵒᵖ ⥤ Mod R) ⥤ Mod R) := preservesLimitNatIso (res φ)
  obtain ⟨e, he⟩ := towerComparison_existsLimitIso (res φ) (dres φ) (tdres φ)
    (rlim B) (rlim R) (resFactors φ).hom (tresFactors φ).hom
    (limitComparison B) (limitComparison R)
    (fun _ _ ↦ inferInstance) (fun _ _ ↦ inferInstance)
    (strictLimit B).computation
    (fun P hP ↦ by
      have := hP
      change IsIso ((limitComparison R).app
        (((tres φ).mapHomologicalComplex (.up ℤ)).obj P))
      exact (strictLimit R).computation _ inferInstance) c
  refine ⟨e, ?_⟩
  intro P
  have h := he P
  have hc : (NatTrans.mapHomologicalComplex c.hom (.up ℤ)).app P =
      (limitRestriction φ).hom.app P := by
    apply HomologicalComplex.hom_ext
    intro q
    apply limit.hom_ext
    intro n
    change c.hom.app (P.X q) ≫ limit.π _ n = _
    exact (preservesLimitIso_hom_π (res φ) (P.X q) n).trans
      ((limitRestriction_existsUnique φ).exists.choose_spec P q n.unop).symm
  rw [hc] at h
  apply (cancel_epi ((resFactors φ).hom.app ((ordinaryLimit B).obj P))).mp
  change (resFactors φ).hom.app ((ordinaryLimit B).obj P) ≫
      (dres φ).map ((limitComparison B).app P) ≫ e.hom.app ((TQ B).obj P) =
    (resFactors φ).hom.app ((ordinaryLimit B).obj P) ≫
      (resFactors φ).inv.app ((ordinaryLimit B).obj P) ≫
        (Q R).map ((limitRestriction φ).hom.app P) ≫
          (limitComparison R).app (((tres φ).mapHomologicalComplex (.up ℤ)).obj P) ≫
            (rlim R).map ((tresFactors φ).hom.app P)
  rw [Iso.hom_inv_id_app_assoc]
  exact h


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Restriction identifies total right derived limits of strict towers, canonically.
The comparison is normalized by the ordinary limit coordinate comparison and both
right-derived universal transformations. Source: Stacks 0940 and 0A07
(blueprint: lem-weil-pbc-constant-completion-equivalence).
Proof: extension of scalars is exact by flat_and_quotients, and restriction is its exact
right adjoint. This adjunction holds levelwise on strict towers, so the right-adjoint
K-injective theorem sends a K-injective tower resolution to one over the constant ring.
Ordinary limits agree by their coordinates. Apply the universal right-derived
comparisons to obtain the natural isomorphism and its displayed normalization. -/
theorem derivedLimitRestriction (J : GrothendieckTopology C) (A : Type u) [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) :
    ∃ e : rlim (completed J A I) ⋙ dres (coefficientMap J A I) ≅
        tdres (coefficientMap J A I) ⋙ rlim (constant J A),
      ∀ P : CochainComplex (ℕᵒᵖ ⥤ Mod (completed J A I)) ℤ,
        (dres (coefficientMap J A I)).map ((limitComparison (completed J A I)).app P) ≫
          e.hom.app ((TQ (completed J A I)).obj P) =
        (resFactors (coefficientMap J A I)).inv.app
            ((ordinaryLimit (completed J A I)).obj P) ≫
          (Q (constant J A)).map ((limitRestriction (coefficientMap J A I)).hom.app P) ≫
          (limitComparison (constant J A)).app
            (((tres (coefficientMap J A I)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
          (rlim (constant J A)).map ((tresFactors (coefficientMap J A I)).hom.app P) := by
  exact derivedLimitRestriction_of_flat (coefficientMap J A I)
    (flat_and_quotients J A I).1

/-- Forget a module sheaf to its underlying sheaf of sets.
Source: Stacks 03D2 (blueprint: lem-weil-pbc-constant-completion-equivalence). -/
abbrev underlying (O : Sheaf J CommRingCat.{u}) : Mod O ⥤ Sheaf J (Type u) :=
  SheafOfModules.toSheaf (siteModuleRings O) ⋙ sheafCompose J (forget AddCommGrpCat)

/-- A sheaf map with a fixed section formula is unique. -/
private theorem sheaf_map_existsUnique_of_formula {X Y : Sheaf J (Type u)}
    (q : X ⟶ Y) (f : ∀ U : Cᵒᵖ, X.obj.obj U → Y.obj.obj U)
    (hq : ∀ U x, q.hom.app U x = f U x) :
    ∃! q' : X ⟶ Y, ∀ U x, q'.hom.app U x = f U x := by
  refine ⟨q, hq, ?_⟩
  intro q' hq'
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply ConcreteCategory.hom_ext
  intro m
  exact (hq' U m).trans (hq U m).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The scalar-extension insertion is the unique underlying-sheaf map m ↦ 1 tensor m.
Source: Stacks 06YY (blueprint: lem-weil-pbc-constant-completion-equivalence).
Proof: the section formula commutes with restrictions by the pure-tensor formula for
changeOfRingsMap and naturality of the sheafification unit. Components determine the map. -/
theorem insertion_existsUnique {R S : Sheaf J CommRingCat.{u}} (φ : R ⟶ S) (M : Mod R) :
    ∃! q : (underlying R).obj M ⟶ (underlying S).obj ((change φ).obj M),
      ∀ (U : Cᵒᵖ) (m : M.val.obj U), q.hom.app U m = tensorSection φ M U 1 m := by
  let η := (scalarExtensionUnit_exists J φ).choose
  exact sheaf_map_existsUnique_of_formula
    ((underlying R).map (η.app M))
    (fun U m ↦ tensorSection φ M U 1 m)
    ((scalarExtensionUnit_exists J φ).choose_spec M)

/-- The actual scalar-extension insertion, including sheafification.
Source: Stacks 06YY (blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def insertion {R S : Sheaf J CommRingCat.{u}} (φ : R ⟶ S) (M : Mod R) :
    (underlying R).obj M ⟶ (underlying S).obj ((change φ).obj M) :=
  (insertion_existsUnique φ M).exists.choose

variable {C' : Type u} [SmallCategory C'] {J' : GrothendieckTopology C'}

set_option genSizeOf false in
set_option genInjectivity false in
/-- Algebraic lifts of a topos inverse image, coherently in all coefficient rings.
The existing AlgebraicInverseImage specifies every ring operation and module action on
all generalized sections. Naturality specifies its action on ring maps. The constant
comparison is natural in every commutative ring, fixing the canonical constant-object
identification, including its coefficient maps.
Source: Stacks 00YV, 03D2, 099L
(blueprint: lem-weil-pbc-constant-completion-equivalence). -/
structure InverseImageData (L : Sheaf J (Type u) ⥤ Sheaf J' (Type u)) where
  rings : Sheaf J CommRingCat.{u} ⥤ Sheaf J' CommRingCat.{u}
  algebra : ∀ O : Sheaf J CommRingCat.{u},
    SheafOfModules.AlgebraicInverseImage L O (rings.obj O)
  ring_naturality : ∀ {R S : Sheaf J CommRingCat.{u}} (φ : R ⟶ S),
    L.map ((sheafCompose J (forget CommRingCat)).map φ) ≫ (algebra S).ringUnderlying.hom =
      (algebra R).ringUnderlying.hom ≫
        (sheafCompose J' (forget CommRingCat)).map (rings.map φ)
  constants : constantSheaf J CommRingCat.{u} ⋙ rings ≅ constantSheaf J' CommRingCat.{u}

/-- Every geometric inverse image has these algebraic lifts and canonical constant maps.
Source: Stacks 00YV, 03D2, 099L
(blueprint: lem-weil-pbc-constant-completion-equivalence).
Proof: transport algebraic operations through finite products preserved by L. The
existing generalized-section equations define the transported ring and module actions.
Transport morphisms through the same underlying-sheaf isomorphisms. Since L is a left
adjoint and preserves the terminal object, it preserves coproducts of the terminal object
and hence constant sheaves. This gives the comparison naturally in every coefficient
ring, and its maps are the canonical constant-sheaf maps. -/
theorem inverseImageData_exists (L : Sheaf J (Type u) ⥤ Sheaf J' (Type u))
    (V : Sheaf J' (Type u) ⥤ Sheaf J (Type u)) (adj : L ⊣ V)
    [PreservesFiniteLimits L] : Nonempty (InverseImageData L) := by
  sorry

variable {L : Sheaf J (Type u) ⥤ Sheaf J' (Type u)} (F : InverseImageData L)

set_option backward.isDefEq.respectTransparency false in
/-- The inverse-image maps to finite coefficients form the canonical projection cone.
Source: Stacks 099L (blueprint: lem-weil-pbc-constant-completion-equivalence).
Proof: apply F.rings to projection naturality and use naturality of F.constants for
A/I^(n+2) → A/I^(n+1). These are exactly the displayed cone equations. -/
theorem pulledProjection_naturality (A : Type u) [CommRing A] (I : Ideal A)
    {m n : ℕᵒᵖ} (f : m ⟶ n) :
    ((Functor.const ℕᵒᵖ).obj (F.rings.obj (completed J A I))).map f ≫
        (F.rings.map (projection J A I n.unop) ≫
          (F.constants.app (CommRingCat.of (A ⧸ I ^ (n.unop + 1)))).hom) =
      (F.rings.map (projection J A I m.unop) ≫
        (F.constants.app (CommRingCat.of (A ⧸ I ^ (m.unop + 1)))).hom) ≫
          (finiteSystem J' A I).map f := by
  have hstep (k : ℕ) :
      ((Functor.const ℕᵒᵖ).obj (F.rings.obj (completed J A I))).map
          (homOfLE (Nat.le_succ k)).op ≫
        (F.rings.map (projection J A I k) ≫
          (F.constants.app (CommRingCat.of (A ⧸ I ^ (k + 1)))).hom) =
      (F.rings.map (projection J A I (k + 1)) ≫
          (F.constants.app (CommRingCat.of (A ⧸ I ^ (k + 1 + 1)))).hom) ≫
        (finiteSystem J' A I).map (homOfLE (Nat.le_succ k)).op := by
    simp only [Functor.const_obj_map, finiteSystem,
      Functor.ofOpSequence_map_homOfLE_succ]
    change F.rings.map (projection J A I k) ≫
        (F.constants.app (CommRingCat.of (A ⧸ I ^ (k + 1)))).hom =
      (F.rings.map (projection J A I (k + 1)) ≫
        (F.constants.app (CommRingCat.of (A ⧸ I ^ (k + 1 + 1)))).hom) ≫
          transition J' A I k
    have hnat := F.constants.hom.naturality
      (CommRingCat.ofHom (Ideal.Quotient.factorPow I (Nat.le_succ (k + 1))))
    change F.rings.map (transition J A I k) ≫
        (F.constants.app (CommRingCat.of (A ⧸ I ^ (k + 1)))).hom =
      (F.constants.app (CommRingCat.of (A ⧸ I ^ (k + 1 + 1)))).hom ≫
        transition J' A I k at hnat
    have hproj : projection J A I (k + 1) ≫ transition J A I k =
        projection J A I k := by
      unfold projection completed
      simpa only [finiteSystem, Functor.ofOpSequence_map_homOfLE_succ] using
        limit.w (finiteSystem J A I) (homOfLE (Nat.le_succ k)).op
    calc
      _ = F.rings.map (projection J A I (k + 1) ≫ transition J A I k) ≫
          (F.constants.app (CommRingCat.of (A ⧸ I ^ (k + 1)))).hom := by rw [hproj]
      _ = _ := by rw [F.rings.map_comp, Category.assoc, hnat, Category.assoc]
  exact (NatTrans.ofOpSequence
    (F := (Functor.const ℕᵒᵖ).obj (F.rings.obj (completed J A I)))
    (G := finiteSystem J' A I)
    (fun k ↦ F.rings.map (projection J A I k) ≫
      (F.constants.app (CommRingCat.of (A ⧸ I ^ (k + 1)))).hom) hstep).naturality f

attribute [local semireducible] completed

/-- The canonical map from the inverse image of the completed coefficient sheaf to the
completion on the second site, formed from its finite projections.
Source: Stacks 099L (blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def completedMap (A : Type u) [CommRing A] (I : Ideal A) :
    F.rings.obj (completed J A I) ⟶ completed J' A I :=
  limit.lift (finiteSystem J' A I)
    { pt := F.rings.obj (completed J A I)
      π :=
        { app := fun n ↦ F.rings.map (projection J A I n.unop) ≫
            (F.constants.app (CommRingCat.of (A ⧸ I ^ (n.unop + 1)))).hom
          naturality := fun {m n} f ↦ pulledProjection_naturality F A I (m := m) (n := n) f } }

attribute [local irreducible] completed

/-- Module inverse image followed by the existing sheafified scalar extension.
Source: Stacks 03D2, 06YY (blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def pull {R : Sheaf J CommRingCat.{u}} {S : Sheaf J' CommRingCat.{u}}
    (c : F.rings.obj R ⟶ S) : Mod R ⥤ Mod S :=
  (F.algebra R).modules ⋙ change c

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Addition transport and underlying naturality make the algebraic module lift additive.
Abstracting the lift avoids repeatedly reducing the full inverse-image data record. -/
private theorem algebraModules_additive {R : Sheaf J CommRingCat.{u}}
    {RI : Sheaf J' CommRingCat.{u}}
    (AI : SheafOfModules.AlgebraicInverseImage L R RI) : AI.modules.Additive := by
  constructor
  intro M N f g
  ext U x
  let e := AI.moduleUnderlying
  let y := (e.hom.app M).hom.app U x
  have hy : (e.inv.app M).hom.app U y = x :=
    congrFun (congrArg (fun t ↦ t.hom.app U) (e.hom_inv_id_app M)) x
  have hn (k : M ⟶ N) :
      (e.inv.app N).hom.app U ((L.map ((underlying R).map k)).hom.app U y) =
        (AI.modules.map k).val.app U x := by
    have hh := congrFun
      (congrArg (fun t ↦ t.hom.app U) (e.inv.naturality k)) y
    change _ = (AI.modules.map k).val.app U
      ((e.inv.app M).hom.app U y) at hh
    exact hh.trans (congrArg ((AI.modules.map k).val.app U) hy)
  have h := AI.moduleAdd N ((underlying R).obj M)
    ((underlying R).map f) ((underlying R).map g) ((underlying R).map (f + g))
    (fun _ _ ↦ rfl) U y
  exact (hn (f + g)).symm.trans
    (h.trans (congrArg₂ (fun (a b : (AI.modules.obj N).val.obj U) ↦ a + b)
      (hn f) (hn g)))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- This prescribed module pullback is additive.
Source: Stacks 03D2 (blueprint: lem-weil-pbc-constant-completion-equivalence).
Proof: the algebraic inverse-image lift preserves addition by its generalized-section
moduleAdd identity. The scalar-extension functor is additive, hence so is their composite. -/
theorem pull_additive {R : Sheaf J CommRingCat.{u}} {S : Sheaf J' CommRingCat.{u}}
    (c : F.rings.obj R ⟶ S) : (pull F c).Additive := by
  have := algebraModules_additive (F.algebra R)
  change ((F.algebra R).modules ⋙ change c).Additive
  infer_instance

attribute [instance] pull_additive

/-- Insertion after inverse image: u^(-1)M → u^(-1)M tensor S, with coefficient action
fixed by c. Source: Stacks 06YY
(blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def pullInsertion {R : Sheaf J CommRingCat.{u}} {S : Sheaf J' CommRingCat.{u}}
    (c : F.rings.obj R ⟶ S) (M : Mod R) :
    L.obj ((underlying R).obj M) ⟶ (underlying S).obj ((pull F c).obj M) :=
  (F.algebra R).moduleUnderlying.inv.app M ≫ insertion c ((F.algebra R).modules.obj M)

set_option genSizeOf false in
set_option genInjectivity false in
/-- A universally specified derived pullback with computation on flat-term K-flat models.
Source: Stacks 06YY, 0G7E (blueprint: lem-weil-pbc-constant-completion-equivalence). -/
structure DerivedPull {R : Sheaf J CommRingCat.{u}} {S : Sheaf J' CommRingCat.{u}}
    (c : F.rings.obj R ⟶ S) where
  functor : D R ⥤ D S
  comparison : Q R ⋙ functor ⟶ (pull F c).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ Q S
  universal : functor.IsLeftDerivedFunctor comparison
    (HomologicalComplex.quasiIso (Mod R) (ComplexShape.up ℤ))
  computation : ∀ P : Cx R, P.IsAcyclicTensorKFlat →
    (∀ q : ℤ, SheafOfModules.IsFlat (P.X q)) → IsIso (comparison.app P)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The recorded K-flat derived-pullback theorem supplies this universal derived pair.
Source: Stacks 06YY, 0G7E (blueprint: lem-weil-pbc-constant-completion-equivalence).
Proof: apply ringedTopoiDerivedPullback to the supplied geometric adjunction and algebraic
lift; pull has exactly its specified scalar-extension objects and maps. Flat-term K-flat
resolutions supply its resolving class. Transport the universal homotopy counit through
the quotient factorization to obtain the complex-level universal pair and computation. -/
theorem derivedPull_exists (V : Sheaf J' (Type u) ⥤ Sheaf J (Type u)) (adj : L ⊣ V)
    [PreservesFiniteLimits L] {R : Sheaf J CommRingCat.{u}} {S : Sheaf J' CommRingCat.{u}}
    (c : F.rings.obj R ⟶ S) : Nonempty (DerivedPull F c) := by
  let := HasDerivedCategory.standard (Mod R)
  let := HasDerivedCategory.standard (Mod S)
  have ho (M : Mod R) : (pull F c).obj M =
      SheafOfModules.changeOfRings c ((F.algebra R).modules.obj M) := rfl
  have hm {M N : Mod R} (f : M ⟶ N) : (pull F c).map f =
      eqToHom (ho M) ≫ SheafOfModules.changeOfRingsHom c
        ((F.algebra R).modules.obj M) ((F.algebra R).modules.map f) ≫
          eqToHom (ho N).symm := by
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl
  obtain ⟨T, ε, hu, _, _, hc, _⟩ :=
    SheafOfModules.ringedTopoiDerivedPullback L V adj (F.algebra R) c (pull F c) ho hm
  let : T.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso (Mod R) (.up ℤ)) := hu
  have : T.IsRightKanExtension ε :=
    Functor.IsLeftDerivedFunctor.isRightKanExtension T ε
      (HomotopyCategory.quasiIso (Mod R) (.up ℤ))
  obtain ⟨β, hβ, hcomp⟩ := cochain_derived_counit (pull F c) T ε
  exact ⟨{ functor := T
           comparison := β
           universal := ⟨hβ⟩
           computation := fun P hp hf ↦ hcomp P (hc P hp hf) }⟩

variable (V : Sheaf J' (Type u) ⥤ Sheaf J (Type u)) (adj : L ⊣ V)
variable [hL : PreservesFiniteLimits L]

/-- Choose the derived pullback with its universal comparison, not an arbitrary lift.
Source: Stacks 06YY (blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def derivedPull {R : Sheaf J CommRingCat.{u}} {S : Sheaf J' CommRingCat.{u}}
    (c : F.rings.obj R ⟶ S) : DerivedPull F c :=
  Classical.choice (derivedPull_exists F V adj c)

attribute [local irreducible] derivedPull

/-- The canonical constant-coefficient structural isomorphism.
Source: Stacks 099L (blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def constantMap (A : Type u) [CommRing A] : F.rings.obj (constant J A) ⟶ constant J' A :=
  (F.constants.app (CommRingCat.of A)).hom

/-- The unreduced scalar comparison on ordinary modules is fixed by scalar insertion.
This is exactly u^(-1)M → u^(-1)M tensor the completed coefficient ring after inverse image.
Source: Stacks 06YY, 099L (blueprint: lem-weil-pbc-constant-completion-equivalence).
Proof: the finite projections make the coefficient square commute. After identifying
inverse images of constant coefficients, define q by m ↦ 1 tensor m. It is linear over
the constant coefficient sheaf, and natural in M. Pure tensors generate after
sheafification, so the insertion equation determines q uniquely. -/
theorem ordinaryPullComparison_existsUnique (A : Type u) [CommRing A] (I : Ideal A) :
    ∃! q : res (coefficientMap J A I) ⋙ pull F (constantMap F A) ⟶
        pull F (completedMap F A I) ⋙ res (coefficientMap J' A I),
      ∀ M : Mod (completed J A I),
        pullInsertion F (constantMap F A) ((res (coefficientMap J A I)).obj M) ≫
            (underlying (constant J' A)).map (q.app M) =
          pullInsertion F (completedMap F A I) M := by
  sorry

/-- The prescribed unreduced ordinary scalar comparison. Source: Stacks 06YY, 099L
(blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def ordinaryPullComparison (A : Type u) [CommRing A] (I : Ideal A) :
    res (coefficientMap J A I) ⋙ pull F (constantMap F A) ⟶
      pull F (completedMap F A I) ⋙ res (coefficientMap J' A I) :=
  (ordinaryPullComparison_existsUnique F A I).exists.choose

/-- The representative square for a derived scalar comparison, with abstract ordinary
functors so complex-composition conversions are checked before specialization.
Source: Stacks 06YY, 099L
(blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def DerivedPullComparisonFormula
    {M₀ M₁ M₂ M₃ D₀ D₁ D₂ D₃ : Type*}
    [Category M₀] [Category M₁] [Category M₂] [Category M₃]
    [Preadditive M₀] [Preadditive M₁] [Preadditive M₂] [Preadditive M₃]
    [Category D₀] [Category D₁] [Category D₂] [Category D₃]
    (q₀ : CochainComplex M₀ ℤ ⥤ D₀) (q₁ : CochainComplex M₁ ℤ ⥤ D₁)
    (q₂ : CochainComplex M₂ ℤ ⥤ D₂) (q₃ : CochainComplex M₃ ℤ ⥤ D₃)
    (r : M₀ ⥤ M₁) (s : M₂ ⥤ M₃) (p : M₁ ⥤ M₃) (b : M₀ ⥤ M₂)
    [r.PreservesZeroMorphisms] [s.PreservesZeroMorphisms]
    [p.PreservesZeroMorphisms] [b.PreservesZeroMorphisms]
    {dr : D₀ ⥤ D₁} {ds : D₂ ⥤ D₃} {dp : D₁ ⥤ D₃} {db : D₀ ⥤ D₂}
    (α : r.mapHomologicalComplex (.up ℤ) ⋙ q₁ ≅ q₀ ⋙ dr)
    (βp : q₁ ⋙ dp ⟶ p.mapHomologicalComplex (.up ℤ) ⋙ q₃)
    (γ : r ⋙ p ⟶ b ⋙ s)
    (βb : q₀ ⋙ db ⟶ b.mapHomologicalComplex (.up ℤ) ⋙ q₂)
    (δ : s.mapHomologicalComplex (.up ℤ) ⋙ q₃ ≅ q₂ ⋙ ds)
    (e : dr ⋙ dp ⟶ db ⋙ ds) (P : CochainComplex M₀ ℤ) : Prop :=
  dp.map (α.inv.app P) ≫ βp.app ((r.mapHomologicalComplex (.up ℤ)).obj P) ≫
      q₃.map ((NatTrans.mapHomologicalComplex γ (.up ℤ)).app P) =
    e.app (q₀.obj P) ≫ ds.map (βb.app P) ≫
      δ.inv.app ((b.mapHomologicalComplex (.up ℤ)).obj P)

/-- The canonical derived scalar comparison, characterized on every flat-term K-flat
representative. Uniqueness makes it independent of resolving choices and gives its
coherence for identity and composite inverse images with the same insertion formula.
Source: Stacks 06YY, 099L (blueprint: lem-weil-pbc-constant-completion-equivalence).
Proof: restrict a flat-term K-flat B-model, using flatness of B over the constant ring.
Apply ordinaryPullComparison termwise, then the two universal computation maps. This
is invariant under resolution maps by the resolving-class derived-functor theorem, and
hence descends naturally to every derived object. The square determines it on a resolving
class, hence uniquely. For composite inverse images, both formulas send m to
(1 tensor (1 tensor m)), identified with 1 tensor m by ordinary tensor reassociation;
therefore uniqueness gives composition and identity coherence. -/
theorem derivedPullComparison_existsUnique (A : Type u) [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) :
    ∃! δ : dres (coefficientMap J A I) ⋙ (derivedPull F V adj (constantMap F A)).functor ⟶
        (derivedPull F V adj (completedMap F A I)).functor ⋙ dres (coefficientMap J' A I),
      ∀ P : Cx (completed J A I), P.IsAcyclicTensorKFlat →
        (∀ q : ℤ, SheafOfModules.IsFlat (P.X q)) →
        DerivedPullComparisonFormula (Q (completed J A I)) (Q (constant J A))
          (Q (completed J' A I)) (Q (constant J' A))
          (res (coefficientMap J A I)) (res (coefficientMap J' A I))
          (pull F (constantMap F A)) (pull F (completedMap F A I))
          (resFactors (coefficientMap J A I))
          (derivedPull F V adj (constantMap F A)).comparison
          (ordinaryPullComparison F A I)
          (derivedPull F V adj (completedMap F A I)).comparison
          (resFactors (coefficientMap J' A I)) δ P
        := by
  sorry

/-- The actual derived comparison with the specified K-flat scalar-insertion formula.
Source: Stacks 06YY, 099L (blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def derivedPullComparison (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) :
    dres (coefficientMap J A I) ⋙ (derivedPull F V adj (constantMap F A)).functor ⟶
      (derivedPull F V adj (completedMap F A I)).functor ⋙ dres (coefficientMap J' A I) :=
  (derivedPullComparison_existsUnique F V adj A I).exists.choose

include V adj hL in
/-- Ordinary constant-coefficient pullback commutes with finite reduction, normalized
by the two insertions. This fixes the canonical tensor reassociation in the quotient
coefficient category. Source: Stacks 06YY, 099L
(blueprint: lem-weil-pbc-constant-completion-equivalence).
Proof: inverse image preserves balanced generators and relations because it preserves
finite products and colimits. Both sides are the same quotient of u^(-1)M. The maps
send a generalized element m to the same class. These generate the tensor sheaf, giving
uniqueness, naturality in M, and compatibility with quotient ring maps. -/
theorem ordinaryFinitePull_existsUnique (A : Type u) [CommRing A] (I : Ideal A) (n : ℕ) :
    ∃! e : pull F (constantMap F A) ⋙ change (quotient J' A I n) ≅
        change (quotient J A I n) ⋙ pull F (constantMap F (A ⧸ I ^ (n + 1))),
      ∀ M : Mod (constant J A),
        pullInsertion F (constantMap F A) M ≫
            insertion (quotient J' A I n) ((pull F (constantMap F A)).obj M) ≫
            (underlying (finite J' A I n)).map (e.hom.app M) =
          L.map (insertion (quotient J A I n) M) ≫
            pullInsertion F (constantMap F (A ⧸ I ^ (n + 1)))
              ((change (quotient J A I n)).obj M) := by
  sorry

/-- The canonical ordinary finite pullback comparison, not an arbitrary isomorphism.
Source: Stacks 06YY, 099L (blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def ordinaryFinitePull (A : Type u) [CommRing A] (I : Ideal A) (n : ℕ) :
    pull F (constantMap F A) ⋙ change (quotient J' A I n) ≅
      change (quotient J A I n) ⋙ pull F (constantMap F (A ⧸ I ^ (n + 1))) :=
  (ordinaryFinitePull_existsUnique F V adj A I n).exists.choose

/-- The representative square for the derived finite-reduction comparison.
The ordinary tensor comparison is lifted with abstract functors before specialization.
Source: Stacks 06YY, 099L
(blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def FinitePullComparisonFormula
    {M₀ M₁ M₂ M₃ D₀ D₁ D₂ D₃ : Type*}
    [Category M₀] [Category M₁] [Category M₂] [Category M₃]
    [Preadditive M₀] [Preadditive M₁] [Preadditive M₂] [Preadditive M₃]
    [Category D₀] [Category D₁] [Category D₂] [Category D₃]
    (q₀ : CochainComplex M₀ ℤ ⥤ D₀) (q₁ : CochainComplex M₁ ℤ ⥤ D₁)
    (q₂ : CochainComplex M₂ ℤ ⥤ D₂) (q₃ : CochainComplex M₃ ℤ ⥤ D₃)
    (r : M₀ ⥤ M₁) (s : M₂ ⥤ M₃) (p : M₁ ⥤ M₃) (b : M₀ ⥤ M₂)
    [r.PreservesZeroMorphisms] [s.PreservesZeroMorphisms]
    [p.PreservesZeroMorphisms] [b.PreservesZeroMorphisms]
    {dr : D₀ ⥤ D₁} {ds : D₂ ⥤ D₃} {dp : D₁ ⥤ D₃} {db : D₀ ⥤ D₂}
    (α : q₀ ⋙ dr ⟶ r.mapHomologicalComplex (.up ℤ) ⋙ q₁)
    (β : q₁ ⋙ dp ⟶ p.mapHomologicalComplex (.up ℤ) ⋙ q₃)
    (γ : r ⋙ p ≅ b ⋙ s)
    (δ : q₀ ⋙ db ⟶ b.mapHomologicalComplex (.up ℤ) ⋙ q₂)
    (ε : q₂ ⋙ ds ⟶ s.mapHomologicalComplex (.up ℤ) ⋙ q₃)
    (e : dr ⋙ dp ≅ db ⋙ ds) (P : CochainComplex M₀ ℤ) : Prop :=
  dp.map (α.app P) ≫ β.app ((r.mapHomologicalComplex (.up ℤ)).obj P) ≫
      q₃.map ((NatIso.mapHomologicalComplex γ (.up ℤ)).hom.app P) =
    e.hom.app (q₀.obj P) ≫ ds.map (δ.app P) ≫
      ε.app ((b.mapHomologicalComplex (.up ℤ)).obj P)

/-- Derived constant pullback and finite reduction commute by the prescribed ordinary
comparison on every flat-term K-flat representative. Source: Stacks 06YY, 099L
(blueprint: lem-weil-pbc-constant-completion-equivalence).
Proof: ringed pullback and scalar extension preserve K-flat complexes with flat terms.
Consequently the two iterated derived functors are computed on the same representative.
Use ordinaryFinitePull there and descend through their universal computation counits.
The displayed square determines the resulting natural isomorphism uniquely. -/
theorem finitePull_existsUnique (A : Type u) [CommRing A] (I : Ideal A) (n : ℕ) :
    ∃! e : (derivedPull F V adj (constantMap F A)).functor ⋙ extend (quotient J' A I n) ≅
        extend (quotient J A I n) ⋙
          (derivedPull F V adj (constantMap F (A ⧸ I ^ (n + 1)))).functor,
      ∀ P : Cx (constant J A), P.IsAcyclicTensorKFlat →
        (∀ q : ℤ, SheafOfModules.IsFlat (P.X q)) →
        FinitePullComparisonFormula (Q (constant J A)) (Q (constant J' A))
          (Q (finite J A I n)) (Q (finite J' A I n))
          (pull F (constantMap F A)) (pull F (constantMap F (A ⧸ I ^ (n + 1))))
          (change (quotient J' A I n)) (change (quotient J A I n))
          (derivedPull F V adj (constantMap F A)).comparison
          (extendComparison (quotient J' A I n)) (ordinaryFinitePull F V adj A I n)
          (extendComparison (quotient J A I n))
          (derivedPull F V adj (constantMap F (A ⧸ I ^ (n + 1)))).comparison e P
        := by
  sorry

/-- The specified derived finite constant pullback comparison.
Source: Stacks 06YY, 099L (blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def finitePull (A : Type u) [CommRing A] (I : Ideal A) (n : ℕ) :
    (derivedPull F V adj (constantMap F A)).functor ⋙ extend (quotient J' A I n) ≅
      extend (quotient J A I n) ⋙
        (derivedPull F V adj (constantMap F (A ⧸ I ^ (n + 1)))).functor :=
  (finitePull_existsUnique F V adj A I n).exists.choose

/-- Completed pullback has the asserted finite comparison in D(A/I^(n+1)) on the second
site. Its inverse is exactly the finite reduction of the unreduced scalar comparison,
after the canonical constant-pullback tensor reassociation. Source: Stacks 099L, 06YY
(blueprint: lem-weil-pbc-constant-completion-equivalence).
Proof: choose one flat-term K-flat completed-coefficient model P. Both sides reduce to
the same quotient u^(-1)P/I^(n+1)u^(-1)P, by finiteComparison and inverse image exactness.
The scalar comparison sends p to 1 tensor p; finite reduction sends its image to the
same quotient class, inverse to the displayed comparison. Every construction commutes
with maps of models and with quotient transitions before localization, and therefore
after descent. The inverse equation fixes the natural isomorphism uniquely. -/
theorem completedFinitePull_existsUnique (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (n : ℕ) :
    ∃! e : (derivedPull F V adj (completedMap F A I)).functor ⋙
          dres (coefficientMap J' A I) ⋙ extend (quotient J' A I n) ≅
        dres (coefficientMap J A I) ⋙ extend (quotient J A I n) ⋙
          (derivedPull F V adj (constantMap F (A ⧸ I ^ (n + 1)))).functor,
      ∀ M : D (completed J A I),
        (extend (quotient J' A I n)).map ((derivedPullComparison F V adj A I).app M) =
          (finitePull F V adj A I n).hom.app ((dres (coefficientMap J A I)).obj M) ≫
            e.inv.app M := by
  sorry

/-- Pointwise application of a module pullback to a strict tower.
Source: Stacks 06YY (blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def pullTowers (A : Type u) [CommRing A] :
    (ℕᵒᵖ ⥤ Mod (constant J A)) ⥤ (ℕᵒᵖ ⥤ Mod (constant J' A)) :=
  (Functor.whiskeringRight ℕᵒᵖ (Mod (constant J A)) (Mod (constant J' A))).obj
    (pull F (constantMap F A))

include V adj hL in
/-- All finite pullback comparisons respect quotient transitions and quotient units,
as one isomorphism of strict towers with the specified insertion formula.
This formula also fixes the comparison for every topos morphism, so identity and
composition compatibility follow from its uniqueness and associativity of insertion.
Source: Stacks 099L, 06YY (blueprint: lem-weil-pbc-constant-completion-equivalence).
Proof: on inverse-image sections both composites send p to its class in
u^(-1)P/I^(n+1)u^(-1)P. A quotient transition sends that class to the class with the
reduced scalar. The equality holds on all sheafified pure tensors, hence on the module
sheaves, naturally in P. Inserting 1 gives exactly the quotient units. Thus these
are maps of strict towers, not unrelated levelwise isomorphisms. Their components
are the finite pullback comparisons by the same insertion normalization. -/
theorem pullbackTowerComparison_existsUnique (A : Type u) [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) :
    ∃! e : pull F (completedMap F A I) ⋙ reductionTower J' A I true ⋙
          tres (coefficientMap J' A I) ≅
        res (coefficientMap J A I) ⋙ reductionTower J A I false ⋙ pullTowers F A,
      ∀ (M : Mod (completed J A I)) (n : ℕ),
        pullInsertion F (completedMap F A I) M ≫
            insertion (projection J' A I n) ((pull F (completedMap F A I)).obj M) ≫
            (underlying (constant J' A)).map ((e.hom.app M).app (op n)) =
          L.map (insertion (quotient J A I n) ((res (coefficientMap J A I)).obj M)) ≫
            pullInsertion F (constantMap F A)
              ((reduction J A I false n).obj ((res (coefficientMap J A I)).obj M)) := by
  sorry

variable {C'' : Type u} [SmallCategory C''] {J'' : GrothendieckTopology C''}
variable {L₂ : Sheaf J' (Type u) ⥤ Sheaf J'' (Type u)}
variable (G : InverseImageData L₂) (H : InverseImageData (L ⋙ L₂))
variable (V₂ : Sheaf J'' (Type u) ⥤ Sheaf J' (Type u)) (adj₂ : L₂ ⊣ V₂)
variable [PreservesFiniteLimits L₂]

/-- Tensor insertion fixes the ordinary pullback composition comparison.
Source: Stacks 06YY (blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def IsPullComposition {R : Sheaf J CommRingCat.{u}} {S : Sheaf J' CommRingCat.{u}}
    {T : Sheaf J'' CommRingCat.{u}}
    (c : F.rings.obj R ⟶ S) (d : G.rings.obj S ⟶ T) (e : H.rings.obj R ⟶ T)
    (a : pull H e ≅ pull F c ⋙ pull G d) : Prop :=
  ∀ M : Mod R, pullInsertion H e M ≫ (underlying T).map (a.hom.app M) =
    L₂.map (pullInsertion F c M) ≫ pullInsertion G d ((pull F c).obj M)

/-- The derived composition comparison is the ordinary tensor comparison on K-flat models.
Source: Stacks 06YY, 0G7E (blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def IsDerivedPullComposition {R : Sheaf J CommRingCat.{u}}
    {S : Sheaf J' CommRingCat.{u}} {T : Sheaf J'' CommRingCat.{u}}
    (c : F.rings.obj R ⟶ S) (d : G.rings.obj S ⟶ T) (e : H.rings.obj R ⟶ T)
    (a : pull H e ≅ pull F c ⋙ pull G d)
    (α : (derivedPull H (V₂ ⋙ V) (adj.comp adj₂) e).functor ≅
      (derivedPull F V adj c).functor ⋙ (derivedPull G V₂ adj₂ d).functor) : Prop :=
  ∀ P : Cx R, P.IsAcyclicTensorKFlat → (∀ q : ℤ, SheafOfModules.IsFlat (P.X q)) →
    α.hom.app ((Q R).obj P) ≫
        (derivedPull G V₂ adj₂ d).functor.map
          ((derivedPull F V adj c).comparison.app P) ≫
        (derivedPull G V₂ adj₂ d).comparison.app
          (((pull F c).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) =
      (derivedPull H (V₂ ⋙ V) (adj.comp adj₂) e).comparison.app P ≫
        (Q T).map ((NatIso.mapHomologicalComplex a (ComplexShape.up ℤ)).hom.app P)

/-- The unreduced comparison is coherent for composite topos inverse images.
The composition isomorphisms are normalized by actual tensor insertions and their
K-flat computations. Consequently this also gives composition coherence for the finite
comparison, which is uniquely determined by its inverse equation.
Source: Stacks 099L, 06YY (blueprint: lem-weil-pbc-constant-completion-equivalence).
Proof: ordinary tensor associativity sends the twice-inserted element to 1 tensor m.
The coefficient maps for the composite agree after every finite projection, hence agree
by the limit universal property. This gives the two normalized ordinary isomorphisms.
All pullbacks preserve the flat-term K-flat resolving class, so these isomorphisms
descend to the displayed derived composition isomorphisms. On that class both sides of
the final equation insert 1 twice. Associativity identifies them, and localization
extends the equality to all derived objects. Uniqueness gives the finite coherence. -/
theorem pullback_composition (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) :
    ∃ (aR : pull H (constantMap H A) ≅
        pull F (constantMap F A) ⋙ pull G (constantMap G A))
      (aB : pull H (completedMap H A I) ≅
        pull F (completedMap F A I) ⋙ pull G (completedMap G A I))
      (αR : (derivedPull H (V₂ ⋙ V) (adj.comp adj₂) (constantMap H A)).functor ≅
        (derivedPull F V adj (constantMap F A)).functor ⋙
          (derivedPull G V₂ adj₂ (constantMap G A)).functor)
      (αB : (derivedPull H (V₂ ⋙ V) (adj.comp adj₂) (completedMap H A I)).functor ≅
        (derivedPull F V adj (completedMap F A I)).functor ⋙
          (derivedPull G V₂ adj₂ (completedMap G A I)).functor),
      IsPullComposition F G H (constantMap F A) (constantMap G A) (constantMap H A) aR ∧
      IsPullComposition F G H (completedMap F A I) (completedMap G A I)
        (completedMap H A I) aB ∧
      IsDerivedPullComposition F V adj G H V₂ adj₂
        (constantMap F A) (constantMap G A) (constantMap H A) aR αR ∧
      IsDerivedPullComposition F V adj G H V₂ adj₂
        (completedMap F A I) (completedMap G A I) (completedMap H A I) aB αB ∧
      (∀ M : D (completed J A I),
        (derivedPullComparison H (V₂ ⋙ V) (adj.comp adj₂) A I).app M ≫
            (dres (coefficientMap J'' A I)).map (αB.hom.app M) =
          αR.hom.app ((dres (coefficientMap J A I)).obj M) ≫
            (derivedPull G V₂ adj₂ (constantMap G A)).functor.map
              ((derivedPullComparison F V adj A I).app M) ≫
            (derivedPullComparison G V₂ adj₂ A I).app
              ((derivedPull F V adj (completedMap F A I)).functor.obj M)) := by
  sorry

/-- The identity inverse image gives the identity scalar comparison under its normalized
ordinary and derived identity identifications. Source: Stacks 099L, 06YY
(blueprint: lem-weil-pbc-constant-completion-equivalence).
Proof: the ordinary identity comparison multiplies 1 tensor m to m, fixing the stated
insertion equation. Descend termwise through the K-flat universal comparison to obtain
the derived identity isomorphisms. The scalar comparison inserts 1 and each identity
isomorphism removes it, so the final equality holds on the resolving class and hence
throughout the derived category. The inverse equation then gives the finite identity law. -/
theorem pullback_identity (F₀ : InverseImageData (𝟭 (Sheaf J (Type u))))
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) :
    ∃ (aR : pull F₀ (constantMap F₀ A) ≅ 𝟭 (Mod (constant J A)))
      (aB : pull F₀ (completedMap F₀ A I) ≅ 𝟭 (Mod (completed J A I)))
      (αR : (derivedPull F₀ (𝟭 _) Adjunction.id (constantMap F₀ A)).functor ≅
        𝟭 (D (constant J A)))
      (αB : (derivedPull F₀ (𝟭 _) Adjunction.id (completedMap F₀ A I)).functor ≅
        𝟭 (D (completed J A I))),
      (∀ M : Mod (constant J A), pullInsertion F₀ (constantMap F₀ A) M ≫
        (underlying (constant J A)).map (aR.hom.app M) = 𝟙 _) ∧
      (∀ M : Mod (completed J A I), pullInsertion F₀ (completedMap F₀ A I) M ≫
        (underlying (completed J A I)).map (aB.hom.app M) = 𝟙 _) ∧
      (∀ P : Cx (constant J A), P.IsAcyclicTensorKFlat →
        (∀ q : ℤ, SheafOfModules.IsFlat (P.X q)) →
        αR.hom.app ((Q (constant J A)).obj P) =
          (derivedPull F₀ (𝟭 _) Adjunction.id (constantMap F₀ A)).comparison.app P ≫
            (Q (constant J A)).map
              ((NatIso.mapHomologicalComplex aR (ComplexShape.up ℤ)).hom.app P)) ∧
      (∀ P : Cx (completed J A I), P.IsAcyclicTensorKFlat →
        (∀ q : ℤ, SheafOfModules.IsFlat (P.X q)) →
        αB.hom.app ((Q (completed J A I)).obj P) =
          (derivedPull F₀ (𝟭 _) Adjunction.id (completedMap F₀ A I)).comparison.app P ≫
            (Q (completed J A I)).map
              ((NatIso.mapHomologicalComplex aB (ComplexShape.up ℤ)).hom.app P)) ∧
      (∀ M : D (completed J A I),
        (derivedPullComparison F₀ (𝟭 _) Adjunction.id A I).app M ≫
            (dres (coefficientMap J A I)).map (αB.hom.app M) =
          αR.hom.app ((dres (coefficientMap J A I)).obj M)) := by
  sorry

attribute [instance] restrictionReduction_additive reductionRestriction_additive
  reductionRestriction_preservesZero

end CategoryTheory.ConstantCompletion
