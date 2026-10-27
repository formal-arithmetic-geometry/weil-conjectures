/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q41
-/
module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits

/-!
# Presheaf differential relations and their sheafified cokernel

Source: Stacks Project, Modules on Sites, Tag 08TP, lemma-differentials-sheafify,
its presheaf presentation and final sheafification step; Tag 03CY
(blueprint: lem-trf-differential-presheaf-relation-cokernel).

This module owns the presheaf-level data of the presentation: the relation labels,
the free symbol and relation module presheaves, and module sheafification along the ring
sheafification unit. They are built from Mathlib's `PresheafOfModules.freeObj` and
`PresheafOfModules.sheafification`. They are not imported from the module of the citer
lem-trf-sheafified-module-differentials-cokernel, whose proof uses this item: that would
close an import cycle. The relation source is the free module on the disjoint union of
the three label sets, hence the stated direct sum. The differential presheaf is Mathlib's
sectionwise Kähler module with its canonical semilinear restrictions.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits
open PresheafOfModules.DifferentialsConstruction

namespace CategoryTheory.DifferentialPresheafRelations

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

variable {C : Type u} [Category.{v} C]

/-- The three kinds of relation labels `(B × B) ⊔ ((B × B) ⊔ A)`, with their sectionwise
restriction maps.
Source: Stacks Project, Modules on Sites, Tag 08TP, displayed relation map
(blueprint: lem-trf-differential-presheaf-relation-cokernel). -/
def relationLabels (A B : Cᵒᵖ ⥤ CommRingCat.{max u v}) : Cᵒᵖ ⥤ Type (max u v) where
  obj U := (B.obj U × B.obj U) ⊕ ((B.obj U × B.obj U) ⊕ A.obj U)
  map f := TypeCat.ofHom (Sum.map (Prod.map (B.map f) (B.map f))
    (Sum.map (Prod.map (B.map f) (B.map f)) (A.map f)))
  map_id U := by
    ext x
    rcases x with ⟨a, b⟩ | (⟨a, b⟩ | h) <;> simp [Sum.map]
  map_comp f g := by
    ext x
    rcases x with ⟨a, b⟩ | (⟨a, b⟩ | h) <;> simp [Sum.map]

/-- The free module presheaf `F = B[B]` on the differential symbols `[b]`.
Source: Stacks Project, Modules on Sites, Tag 08TP
(blueprint: lem-trf-differential-presheaf-relation-cokernel). -/
noncomputable abbrev symbols (B : Cᵒᵖ ⥤ CommRingCat.{max u v}) :=
  PresheafOfModules.freeObj (R := B ⋙ forget₂ CommRingCat RingCat)
    (B ⋙ forget CommRingCat)

/-- The relation module presheaf `E`, the free module on the three relation label sets,
i.e. the direct sum of the two pair-relation free modules and the base-relation free module.
Source: Stacks Project, Modules on Sites, Tag 08TP
(blueprint: lem-trf-differential-presheaf-relation-cokernel). -/
noncomputable abbrev relations (A B : Cᵒᵖ ⥤ CommRingCat.{max u v}) :=
  PresheafOfModules.freeObj (R := B ⋙ forget₂ CommRingCat RingCat) (relationLabels A B)

/-- Ring-valued sheafification `B^#` of a commutative-ring presheaf, forgetting commutativity.
Source: Stacks Project, Modules on Sites, Tag 03CY
(blueprint: lem-trf-differential-presheaf-relation-cokernel). -/
noncomputable abbrev associatedRing (J : GrothendieckTopology C)
    (B : Cᵒᵖ ⥤ CommRingCat.{max u v}) : Sheaf J RingCat.{max u v} :=
  (sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj
    ((presheafToSheaf J CommRingCat.{max u v}).obj B)

/-- Module sheafification along the ring sheafification unit: the abelian sheafification
`M^#` of a module presheaf with its canonical `B^#`-module structure. The two local
bijectivity structures forget commutativity and have the same covering sieves.
Source: Stacks Project, Modules on Sites, Tag 03CY, lemma-sheafification-presheaf-modules
(blueprint: lem-trf-differential-presheaf-relation-cokernel). -/
noncomputable def associatedModules (J : GrothendieckTopology C)
    (B : Cᵒᵖ ⥤ CommRingCat.{max u v}) :
    PresheafOfModules.{max u v} (B ⋙ forget₂ CommRingCat RingCat) ⥤
      ringedSiteModules.{max u v} (associatedRing J B) :=
  let η := Functor.whiskerRight (CategoryTheory.toSheafify J B)
    (forget₂ CommRingCat.{max u v} RingCat.{max u v})
  letI : Presheaf.IsLocallyInjective J η :=
    ⟨fun x y h ↦ Presheaf.equalizerSieve_mem J (CategoryTheory.toSheafify J B) x y h⟩
  letI : Presheaf.IsLocallySurjective J η :=
    ⟨fun s ↦ Presheaf.imageSieve_mem J (CategoryTheory.toSheafify J B) s⟩
  PresheafOfModules.sheafification η

private theorem symbols_map
    (B : Cᵒᵖ ⥤ CommRingCat.{max u v}) {U V : Cᵒᵖ} (f : U ⟶ V) (b : B.obj U) :
    (symbols B).map f (ModuleCat.freeMk b) = ModuleCat.freeMk (B.map f b) :=
  ModuleCat.freeDesc_apply _ _

private noncomputable def relationMap
    {A B : Cᵒᵖ ⥤ CommRingCat.{max u v}} (φ : A ⟶ B) :
    relations A B ⟶ symbols B :=
  PresheafOfModules.freeObjDesc
    { app U := ↾fun x ↦ match x with
        | Sum.inl (a, b) =>
            ModuleCat.freeMk (a + b) - ModuleCat.freeMk a - ModuleCat.freeMk b
        | Sum.inr (Sum.inl (a, b)) =>
            ModuleCat.freeMk (a * b) - b • ModuleCat.freeMk a - a • ModuleCat.freeMk b
        | Sum.inr (Sum.inr a) => ModuleCat.freeMk (φ.app U a)
      naturality {U V} f := by
        ext x
        rcases x with ⟨a, b⟩ | (⟨a, b⟩ | a)
        · change ModuleCat.freeMk (B.map f a + B.map f b) -
              ModuleCat.freeMk (B.map f a) - ModuleCat.freeMk (B.map f b) =
            (symbols B).map f
              (ModuleCat.freeMk (a + b) - ModuleCat.freeMk a - ModuleCat.freeMk b)
          erw [map_sub, map_sub, symbols_map, symbols_map, symbols_map, map_add]
        · change ModuleCat.freeMk (B.map f a * B.map f b) -
              B.map f b • ModuleCat.freeMk (B.map f a) -
              B.map f a • ModuleCat.freeMk (B.map f b) =
            (symbols B).map f
              (ModuleCat.freeMk (a * b) - b • ModuleCat.freeMk a - a • ModuleCat.freeMk b)
          erw [map_sub, map_sub, PresheafOfModules.map_smul,
            PresheafOfModules.map_smul, symbols_map, symbols_map, symbols_map, map_mul]
          rfl
        · change ModuleCat.freeMk (φ.app V (A.map f a)) =
            (symbols B).map f (ModuleCat.freeMk (φ.app U a))
          rw [symbols_map]
          exact congrArg ModuleCat.freeMk (NatTrans.naturality_apply φ f a) }

private noncomputable def differentialMap
    {A B : Cᵒᵖ ⥤ CommRingCat.{max u v}} (φ : A ⟶ B) :
    symbols B ⟶ relativeDifferentials' φ :=
  PresheafOfModules.freeObjDesc
    { app U := ↾fun b ↦ (derivation' φ).d b
      naturality {U V} f := by
        ext b
        exact (derivation' φ).d_map f b }

private theorem relationMap_add
    {A B : Cᵒᵖ ⥤ CommRingCat.{max u v}} (φ : A ⟶ B) (U : Cᵒᵖ) (a b : B.obj U) :
    (relationMap φ).app U (ModuleCat.freeMk (Sum.inl (a, b))) =
      ModuleCat.freeMk (a + b) - ModuleCat.freeMk a - ModuleCat.freeMk b :=
  ModuleCat.freeDesc_apply _ _

private theorem relationMap_mul
    {A B : Cᵒᵖ ⥤ CommRingCat.{max u v}} (φ : A ⟶ B) (U : Cᵒᵖ) (a b : B.obj U) :
    (relationMap φ).app U (ModuleCat.freeMk (Sum.inr (Sum.inl (a, b)))) =
      ModuleCat.freeMk (a * b) - b • ModuleCat.freeMk a - a • ModuleCat.freeMk b :=
  ModuleCat.freeDesc_apply _ _

private theorem relationMap_base
    {A B : Cᵒᵖ ⥤ CommRingCat.{max u v}} (φ : A ⟶ B) (U : Cᵒᵖ) (a : A.obj U) :
    (relationMap φ).app U (ModuleCat.freeMk (Sum.inr (Sum.inr a))) =
      ModuleCat.freeMk (φ.app U a) :=
  ModuleCat.freeDesc_apply _ _

private theorem differentialMap_apply
    {A B : Cᵒᵖ ⥤ CommRingCat.{max u v}} (φ : A ⟶ B) (U : Cᵒᵖ) (b : B.obj U) :
    (differentialMap φ).app U (ModuleCat.freeMk b) = (derivation' φ).d b :=
  ModuleCat.freeDesc_apply _ _

private theorem relationMap_comp_differentialMap
    {A B : Cᵒᵖ ⥤ CommRingCat.{max u v}} (φ : A ⟶ B) :
    relationMap φ ≫ differentialMap φ = 0 := by
  ext1 U
  apply ModuleCat.free_hom_ext
  intro x
  change (differentialMap φ).app U ((relationMap φ).app U (ModuleCat.freeMk x)) = 0
  rcases x with ⟨a, b⟩ | (⟨a, b⟩ | a)
  · erw [relationMap_add φ U a b, map_sub, map_sub,
      differentialMap_apply φ U (a + b), differentialMap_apply φ U a,
      differentialMap_apply φ U b]
    rw [map_add]
    abel
  · erw [relationMap_mul φ U a b, map_sub, map_sub, map_smul, map_smul,
      differentialMap_apply φ U (a * b), differentialMap_apply φ U a,
      differentialMap_apply φ U b]
    rw [(derivation' φ).d_mul a b]
    abel
  · erw [relationMap_base φ U a, differentialMap_apply φ U (φ.app U a)]
    exact PresheafOfModules.Derivation'.d_app _ _

private noncomputable def coforkDerivation
    {A B : Cᵒᵖ ⥤ CommRingCat.{max u v}} (φ : A ⟶ B) (U : Cᵒᵖ)
    {N : ModuleCat.{max u v} (B.obj U)} (g : (symbols B).obj U ⟶ N)
    (h : (relationMap φ).app U ≫ g = 0) : N.Derivation (φ.app U) :=
  ModuleCat.Derivation.mk (fun b ↦ g (ModuleCat.freeMk b))
    (fun a b ↦ by
      have hh := ConcreteCategory.congr_hom h (ModuleCat.freeMk (Sum.inl (a, b)))
      change g ((relationMap φ).app U (ModuleCat.freeMk (Sum.inl (a, b)))) = 0 at hh
      erw [relationMap_add, map_sub, map_sub] at hh
      exact sub_eq_zero.mp (by simpa only [sub_sub] using hh))
    (fun a b ↦ by
      have hh := ConcreteCategory.congr_hom h
        (ModuleCat.freeMk (Sum.inr (Sum.inl (a, b))))
      change g ((relationMap φ).app U
        (ModuleCat.freeMk (Sum.inr (Sum.inl (a, b))))) = 0 at hh
      erw [relationMap_mul, map_sub, map_sub, map_smul, map_smul] at hh
      exact (sub_eq_zero.mp (by simpa only [sub_sub] using hh)).trans (add_comm _ _))
    (fun a ↦ by
      have hh := ConcreteCategory.congr_hom h (ModuleCat.freeMk (Sum.inr (Sum.inr a)))
      change g ((relationMap φ).app U
        (ModuleCat.freeMk (Sum.inr (Sum.inr a)))) = 0 at hh
      erw [relationMap_base] at hh
      exact hh)

private theorem coforkDerivation_d
    {A B : Cᵒᵖ ⥤ CommRingCat.{max u v}} (φ : A ⟶ B) (U : Cᵒᵖ)
    {N : ModuleCat.{max u v} (B.obj U)} (g : (symbols B).obj U ⟶ N)
    (h : (relationMap φ).app U ≫ g = 0) (b : B.obj U) :
    (coforkDerivation φ U g h).d b = g (ModuleCat.freeMk b) := rfl

private theorem differentialMap_d
    {A B : Cᵒᵖ ⥤ CommRingCat.{max u v}} (φ : A ⟶ B) (U : Cᵒᵖ) (b : B.obj U) :
    (differentialMap φ).app U (ModuleCat.freeMk b) =
      CommRingCat.KaehlerDifferential.d (f := φ.app U) b :=
  ModuleCat.freeDesc_apply _ _

private theorem sectionwise_zero
    {A B : Cᵒᵖ ⥤ CommRingCat.{max u v}} (φ : A ⟶ B) (U : Cᵒᵖ) :
    (relationMap φ).app U ≫ (differentialMap φ).app U = 0 :=
  congrArg (fun f ↦ f.app U) (relationMap_comp_differentialMap φ)

private noncomputable def sectionwiseIsColimit
    {A B : Cᵒᵖ ⥤ CommRingCat.{max u v}} (φ : A ⟶ B) (U : Cᵒᵖ) :
    IsColimit (CokernelCofork.ofπ ((differentialMap φ).app U) (sectionwise_zero φ U)) := by
  refine CokernelCofork.IsColimit.ofπ _ _
    (fun g h ↦ (coforkDerivation φ U g h).desc) ?_ ?_
  · intro N g h
    apply ModuleCat.free_hom_ext
    intro b
    exact (congrArg (fun x ↦ (coforkDerivation φ U g h).desc x)
      (differentialMap_d φ U b)).trans
        ((ModuleCat.Derivation.desc_d _ b).trans (coforkDerivation_d φ U g h b))
  · intro N g h m hm
    apply CommRingCat.KaehlerDifferential.ext
    intro b
    exact (congrArg (fun x ↦ m x) (differentialMap_d φ U b).symm).trans
      ((ConcreteCategory.congr_hom hm (ModuleCat.freeMk b)).trans
        ((ModuleCat.Derivation.desc_d _ b).trans (coforkDerivation_d φ U g h b)).symm)

private noncomputable def presheafIsColimit
    {A B : Cᵒᵖ ⥤ CommRingCat.{max u v}} (φ : A ⟶ B) :
    IsColimit (CokernelCofork.ofπ (differentialMap φ)
      (relationMap_comp_differentialMap φ)) := by
  apply PresheafOfModules.evaluationJointlyReflectsColimits
  intro U
  exact (CokernelCofork.isColimitMapCoconeEquiv _
    (PresheafOfModules.evaluation _ U)).symm (sectionwiseIsColimit φ U)

/-- The additivity, Leibniz, and base-ring relations present the sectionwise differential
presheaf, both before and after module sheafification. The last equality specifies the
value of the sheafified quotient on the original generators.

Source: Stacks Project, Modules on Sites, Tag 08TP, lemma-differentials-sheafify;
Tag 03CY, lemma-sheafification-presheaf-modules
(blueprint: lem-trf-differential-presheaf-relation-cokernel).

Proof plan:
1. Use the free basis of def-weil-pbc-free-module. Restrict each generator by
   `b[t] ↦ b|[t|]`. Ring restrictions preserve addition and multiplication, and the
   naturality of `φ` preserves the third relation, so the three linear maps assemble to `r`.
2. The universal property of def-weil-pbc-kahler-differentials gives restrictions on
   the sectionwise differential module carrying `d b` to `d (b|)`. Uniqueness proves
   their identity and composition laws. On free generators, this also proves naturality of `p`.
3. The image of `r.app U` is exactly the span of the three relation families. The
   quotient construction of differentials makes `p.app U` its cokernel. Apply
   lem-weil-pbc-presheaf-modules-colimits-sectionwise to obtain the presheaf cokernel.
4. By lem-pc-sites-module-sheafification-interface, `associatedModules` equips the
   abelian sheafification of every module presheaf with its canonical compatible
   `B`-sheafification action. Its adjunction identifies maps out of a sheafified module
   with presheaf-module maps into the target with scalars restricted along the ring unit.
5. If a sheaf-module map from the sheafification of `F` kills the sheafified relations,
   precompose with the unit, descend uniquely through the presheaf cokernel, and
   factor uniquely through the unit of `P`. These two uniqueness properties prove
   exactly the cokernel universal property after sheafification, including the zero composite.
6. The functorial unit identity `p^# η_F = η_P p`, evaluated on `[b]`, gives the final
   equality using the displayed value of `p.app U`.
-/
theorem differential_presheaf_relation_cokernel
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    {A B : Cᵒᵖ ⥤ CommRingCat.{max u v}} (φ : A ⟶ B) :
    ∃ (r : relations A B ⟶ symbols B)
      (p : symbols B ⟶ relativeDifferentials' φ),
      (∀ (U : Cᵒᵖ) (a b : B.obj U),
        r.app U (ModuleCat.freeMk (Sum.inl (a, b))) =
          ModuleCat.freeMk (a + b) - ModuleCat.freeMk a - ModuleCat.freeMk b) ∧
      (∀ (U : Cᵒᵖ) (f g : B.obj U),
        r.app U (ModuleCat.freeMk (Sum.inr (Sum.inl (f, g)))) =
          ModuleCat.freeMk (f * g) - g • ModuleCat.freeMk f - f • ModuleCat.freeMk g) ∧
      (∀ (U : Cᵒᵖ) (h : A.obj U),
        r.app U (ModuleCat.freeMk (Sum.inr (Sum.inr h))) = ModuleCat.freeMk (φ.app U h)) ∧
      (∀ (U : Cᵒᵖ) (b : B.obj U),
        p.app U (ModuleCat.freeMk b) = (derivation' φ).d b) ∧
      (∃ h : r ≫ p = 0, Nonempty (IsColimit (CokernelCofork.ofπ p h))) ∧
      (∀ U : Cᵒᵖ, ∃ h : r.app U ≫ p.app U = 0,
        Nonempty (IsColimit (CokernelCofork.ofπ (p.app U) h))) ∧
      (∃ h : (associatedModules J B).map r ≫ (associatedModules J B).map p = 0,
        Nonempty (IsColimit (CokernelCofork.ofπ ((associatedModules J B).map p) h))) ∧
      (∀ (U : Cᵒᵖ) (b : B.obj U),
        ((associatedModules J B).map p).val.app U
            ((CategoryTheory.toSheafify J (symbols B).presheaf).app U (ModuleCat.freeMk b)) =
          (CategoryTheory.toSheafify J (relativeDifferentials' φ).presheaf).app U
            ((derivation' φ).d b)) := by
  refine ⟨relationMap φ, differentialMap φ, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro U a b
    exact ModuleCat.freeDesc_apply _ _
  · intro U a b
    exact ModuleCat.freeDesc_apply _ _
  · intro U a
    exact ModuleCat.freeDesc_apply _ _
  · intro U b
    exact ModuleCat.freeDesc_apply _ _
  · exact ⟨relationMap_comp_differentialMap φ, ⟨presheafIsColimit φ⟩⟩
  · intro U
    exact ⟨sectionwise_zero φ U, ⟨sectionwiseIsColimit φ U⟩⟩
  · let F := associatedModules J B
    have : F.IsLeftAdjoint := by
      dsimp [F, associatedModules]
      infer_instance
    refine ⟨by rw [← F.map_comp, relationMap_comp_differentialMap, F.map_zero], ?_⟩
    exact ⟨CokernelCofork.mapIsColimit _ (presheafIsColimit φ) F⟩
  · intro U b
    have h := congrArg (fun t ↦ t.app U (ModuleCat.freeMk b))
      (CategoryTheory.toSheafify_naturality J
        ((PresheafOfModules.toPresheaf _).map (differentialMap φ)))
    change (CategoryTheory.toSheafify J (relativeDifferentials' φ).presheaf).app U
        ((differentialMap φ).app U (ModuleCat.freeMk b)) = _ at h
    exact h.symm.trans (congrArg
      ((CategoryTheory.toSheafify J (relativeDifferentials' φ).presheaf).app U)
      (differentialMap_apply φ U b))

end CategoryTheory.DifferentialPresheafRelations
