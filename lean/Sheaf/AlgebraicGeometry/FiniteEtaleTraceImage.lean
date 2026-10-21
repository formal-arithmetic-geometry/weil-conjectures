/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S2
-/
module

public import Sheaf.AlgebraicGeometry.FiniteEtaleTraceDefinitions
import Sheaf.AlgebraicGeometry.FiniteEtaleTraceSectionDescent
import Sheaf.AlgebraicGeometry.FiniteEtaleTraceSheetLifting
import Mathlib.CategoryTheory.Sites.Subsheaf
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.CategoryTheory.Category.ULift

/-! # Finite etale trace and integral sheaf image -/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {V S : Scheme.{u}} (p : V ⟶ S)
  (L : SheafOfModules.{u + 1} (traceFieldRing l E S))

private def traceSource :=
  (traceModuleDirectImage l E p).obj ((traceModulePullback l E p).obj L)

private def traceSection [IsFinite p] [Etale p] (B : S.ProEt)
    (s : (traceSource l E p L).val.obj (op (AsSmall.up.obj B))) :
    L.val.obj (op (AsSmall.up.obj B)) :=
  Classical.choose (finiteEtaleTrace_section_sum_descent l E p L B s).exists

private theorem traceSection_formula [IsFinite p] [Etale p] (B : S.ProEt)
    (s : (traceSource l E p L).val.obj (op (AsSmall.up.obj B)))
    (U : S.ProEt) (hU : Etale U.hom) (J : Type u) [Fintype J]
    (σ : TraceImageSplitting p U J) (C : S.ProEt) (a : C ⟶ B) (h : C ⟶ U)
    (t : J → L.val.obj (op (AsSmall.up.obj C)))
    (ht : ∀ j, traceImageSheetRestriction σ h j ((traceModulePullback l E p).obj L)
      ((traceSource l E p L).val.map (AsSmall.up.map a).op s) =
        traceImageSheetUnit l E p L σ h j (t j)) :
    L.val.map (AsSmall.up.map a).op (traceSection l E p L B s) = ∑ j, t j :=
  Classical.choose_spec (finiteEtaleTrace_section_sum_descent l E p L B s).exists
    U hU J σ C a h t ht

private theorem traceSection_ext [IsFinite p] [Etale p] (B : S.ProEt)
    (s : (traceSource l E p L).val.obj (op (AsSmall.up.obj B)))
    (r : L.val.obj (op (AsSmall.up.obj B)))
    (hr : ∀ (U : S.ProEt) (_ : Etale U.hom) (J : Type u) [Fintype J]
      (σ : TraceImageSplitting p U J) (C : S.ProEt) (a : C ⟶ B) (h : C ⟶ U)
      (t : J → L.val.obj (op (AsSmall.up.obj C))),
      (∀ j, traceImageSheetRestriction σ h j ((traceModulePullback l E p).obj L)
        ((traceSource l E p L).val.map (AsSmall.up.map a).op s) =
          traceImageSheetUnit l E p L σ h j (t j)) →
      L.val.map (AsSmall.up.map a).op r = ∑ j, t j) :
    r = traceSection l E p L B s :=
  (finiteEtaleTrace_section_sum_descent l E p L B s).unique hr
    (Classical.choose_spec (finiteEtaleTrace_section_sum_descent l E p L B s).exists)

private theorem traceSection_naturality [IsFinite p] [Etale p]
    {B C : S.ProEt} (a : C ⟶ B)
    (s : (traceSource l E p L).val.obj (op (AsSmall.up.obj B))) :
    L.val.map (AsSmall.up.map a).op (traceSection l E p L B s) =
      traceSection l E p L C ((traceSource l E p L).val.map (AsSmall.up.map a).op s) := by
  apply traceSection_ext l E p L C
    ((traceSource l E p L).val.map (AsSmall.up.map a).op s)
  intro U hU J inst σ D b h t ht
  have ht' : ∀ j,
      traceImageSheetRestriction σ h j ((traceModulePullback l E p).obj L)
        ((traceSource l E p L).val.map (AsSmall.up.map (b ≫ a)).op s) =
          traceImageSheetUnit l E p L σ h j (t j) := by
    intro j
    change traceImageSheetRestriction σ h j ((traceModulePullback l E p).obj L)
      ((traceSource l E p L).val.map
        (AsSmall.up.map b ≫ AsSmall.up.map a).op s) = _
    rw [op_comp, PresheafOfModules.map_comp_apply]
    exact ht j
  have hs := traceSection_formula l E p L B s U hU J σ D (b ≫ a) h t ht'
  change L.val.map (AsSmall.up.map b ≫ AsSmall.up.map a).op _ = _ at hs
  rw [op_comp, PresheafOfModules.map_comp_apply] at hs
  exact hs

private theorem traceSection_add [IsFinite p] [Etale p] (B : S.ProEt)
    (s s' : (traceSource l E p L).val.obj (op (AsSmall.up.obj B))) :
    traceSection l E p L B (s + s') =
      traceSection l E p L B s + traceSection l E p L B s' := by
  symm
  apply traceSection_ext
  intro U hU J inst σ C a h t ht
  classical
  let P := (traceModulePullback l E p).obj L
  let v : P.val.obj (op (AsSmall.up.obj ((proEtaleBaseChange p).obj C))) :=
    (traceSource l E p L).val.map (AsSmall.up.map a).op s
  let v' : P.val.obj (op (AsSmall.up.obj ((proEtaleBaseChange p).obj C))) :=
    (traceSource l E p L).val.map (AsSmall.up.map a).op s'
  have hb := (finiteEtaleTrace_sheet_lifting l E p L σ h).1
  choose t₁ ht₁ using fun j ↦ (hb j).surjective (traceImageSheetRestriction σ h j P v)
  choose t₂ ht₂ using fun j ↦ (hb j).surjective (traceImageSheetRestriction σ h j P v')
  have hcoord : ∀ j, t j = t₁ j + t₂ j := by
    intro j
    apply (hb j).injective
    dsimp only
    rw [show traceImageSheetUnit l E p L σ h j (t₁ j + t₂ j) =
      traceImageSheetUnit l E p L σ h j (t₁ j) +
        traceImageSheetUnit l E p L σ h j (t₂ j) by
          change (P.val.restrictₛₗ (AsSmall.up.map
            (traceImageSheetArrow σ h j)).op)
              ((((SheafOfModules.pullbackPushforwardAdjunction
                (traceFieldRingMap l E p)).unit.app L).val.app
                  (op (AsSmall.up.obj C))).hom (t₁ j + t₂ j)) = _
          rw [map_add, map_add]
          rfl]
    dsimp only at ht₁ ht₂
    rw [ht₁, ht₂, ← ht j]
    change (P.val.restrictₛₗ (AsSmall.up.map
      (traceImageSheetArrow σ h j)).op)
        (((traceSource l E p L).val.map (AsSmall.up.map a).op).hom (s + s')) = _
    rw [map_add, map_add]
    rfl
  rw [map_add, traceSection_formula l E p L B s U hU J σ C a h t₁
    (fun j ↦ (ht₁ j).symm),
    traceSection_formula l E p L B s' U hU J σ C a h t₂ (fun j ↦ (ht₂ j).symm)]
  simp only [hcoord, Finset.sum_add_distrib]

private theorem traceSection_smul [IsFinite p] [Etale p] (B : S.ProEt)
    (r : (traceFieldRing l E S).obj.obj (op (AsSmall.up.obj B)))
    (s : (traceSource l E p L).val.obj (op (AsSmall.up.obj B))) :
    traceSection l E p L B (r • s) = r • traceSection l E p L B s := by
  symm
  apply traceSection_ext
  intro U hU J inst σ C a h t ht
  classical
  let P := (traceModulePullback l E p).obj L
  let v : P.val.obj (op (AsSmall.up.obj ((proEtaleBaseChange p).obj C))) :=
    (traceSource l E p L).val.map (AsSmall.up.map a).op s
  let r' := (traceFieldRing l E S).obj.map (AsSmall.up.map a).op r
  have hb := (finiteEtaleTrace_sheet_lifting l E p L σ h).1
  choose t₁ ht₁ using fun j ↦ (hb j).surjective (traceImageSheetRestriction σ h j P v)
  have hcoord : ∀ j, t j = r' • t₁ j := by
    intro j
    apply (hb j).injective
    dsimp only
    rw [← ht j]
    have ht₁' := ht₁ j
    dsimp only at ht₁'
    have hu := congrArg
      (fun x : P.val.obj (op (AsSmall.up.obj (traceImageSheetObject σ h j))) ↦
        (traceFieldRing l E V).obj.map
        (AsSmall.up.map (traceImageSheetArrow σ h j)).op
          ((traceFieldRingMap l E p).hom.app (op (AsSmall.up.obj C)) r') • x) ht₁'
    calc
      _ = (traceFieldRing l E V).obj.map
          (AsSmall.up.map (traceImageSheetArrow σ h j)).op
            ((traceFieldRingMap l E p).hom.app (op (AsSmall.up.obj C)) r') •
              traceImageSheetRestriction σ h j P v := by
        unfold traceImageSheetRestriction
        rw [(traceSource l E p L).val.map_smul]
        change P.val.map _
          (((traceFieldRingMap l E p).hom.app (op (AsSmall.up.obj C)) r') • v) = _
        exact P.val.map_smul _ _ _
      _ = _ := by
        rw [← hu]
        unfold traceImageSheetUnit traceImageSheetRestriction
        rw [show (((SheafOfModules.pullbackPushforwardAdjunction
            (traceFieldRingMap l E p)).unit.app L).val.app
              (op (AsSmall.up.obj C))) (r' • t₁ j) =
            r' • (((SheafOfModules.pullbackPushforwardAdjunction
              (traceFieldRingMap l E p)).unit.app L).val.app
                (op (AsSmall.up.obj C))) (t₁ j) from
          ((((SheafOfModules.pullbackPushforwardAdjunction
            (traceFieldRingMap l E p)).unit.app L).val.app
              (op (AsSmall.up.obj C))).hom.map_smul r' (t₁ j))]
        let z : P.val.obj (op (AsSmall.up.obj ((proEtaleBaseChange p).obj C))) :=
          (((SheafOfModules.pullbackPushforwardAdjunction
            (traceFieldRingMap l E p)).unit.app L).val.app
              (op (AsSmall.up.obj C))) (t₁ j)
        change _ = P.val.map (AsSmall.up.map (traceImageSheetArrow σ h j)).op
          (((P.val.obj (op (AsSmall.up.obj ((proEtaleBaseChange p).obj C)))).smul
            ((traceFieldRingMap l E p).hom.app (op (AsSmall.up.obj C)) r')).hom z)
        exact (P.val.map_smul _ _ _).symm
  rw [L.val.map_smul, traceSection_formula l E p L B s U hU J σ C a h t₁
    (fun j ↦ (ht₁ j).symm)]
  simp only [hcoord, Finset.smul_sum, r']

private def traceMorphism [IsFinite p] [Etale p] : traceSource l E p L ⟶ L where
  val := PresheafOfModules.homMk
    { app X := AddCommGrpCat.ofHom (AddMonoidHom.mk'
        (traceSection l E p L (AsSmall.down.obj X.unop))
        (traceSection_add l E p L (AsSmall.down.obj X.unop)))
      naturality := fun {X Y} f ↦ by
        ext s
        exact (traceSection_naturality l E p L (AsSmall.down.map f.unop) s).symm }
    (fun X r s ↦ traceSection_smul l E p L (AsSmall.down.obj X.unop) r s)

private theorem traceMorphism_localSums [IsFinite p] [Etale p] :
    TraceImageLocalSums l E p L (traceMorphism l E p L) := by
  intro U hU J inst σ B h s t ht
  have hs := traceSection_formula l E p L B s U hU J σ B (𝟙 B) h t
    (by
      intro j
      have hi : (traceSource l E p L).val.map (AsSmall.up.map (𝟙 B)).op s = s := by
        change (traceSource l E p L).val.presheaf.map (AsSmall.up.map (𝟙 B)).op s = s
        rw [CategoryTheory.Functor.map_id, op_id, CategoryTheory.Functor.map_id]
        rfl
      rw [hi]
      exact ht j)
  have hi : L.val.map (AsSmall.up.map (𝟙 B)).op (traceSection l E p L B s) =
      traceSection l E p L B s := by
    change L.val.presheaf.map (AsSmall.up.map (𝟙 B)).op _ = _
    rw [CategoryTheory.Functor.map_id, op_id, CategoryTheory.Functor.map_id]
    rfl
  rw [hi] at hs
  exact hs

private theorem traceMorphism_unique [IsFinite p] [Etale p]
    (τ : traceSource l E p L ⟶ L) (hτ : TraceImageLocalSums l E p L τ) :
    τ = traceMorphism l E p L := by
  ext ⟨⟨B⟩⟩ s
  change τ.val.app (op (AsSmall.up.obj B)) s = traceSection l E p L B s
  apply traceSection_ext
  intro U hU J inst σ C a h t ht
  have hn := PresheafOfModules.naturality_apply τ.val (AsSmall.up.map a).op s
  rw [← hn]
  exact hτ U hU J σ C h _ t ht

private theorem submodule_saturation {C : Type (u + 1)} [SmallCategory C]
    (J : GrothendieckTopology C) (R : Sheaf J RingCat.{u + 1})
    (Q : SheafOfModules.{u + 1} R) (P : Q.val.Submodule) :
    ∃ N : Q.val.Submodule,
      Presheaf.IsSheaf J N.toPresheafOfModules.presheaf ∧
        ∀ (B : C) (s : Q.val.obj (op B)),
          s ∈ N.obj (op B) ↔
            ∃ T : Sieve B, T ∈ J B ∧
              ∀ (D : C) (a : D ⟶ B), T a → Q.val.map a.op s ∈ P.obj (op D) := by
  let G : Subfunctor (Q.val.presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
    { obj X := (P.obj X : Set (Q.val.obj X))
      map f := P.map f }
  let H := G.sheafify J
  let N : Q.val.Submodule :=
    { obj X :=
        { carrier := H.obj X
          zero_mem' := G.le_sheafify J X (P.obj X).zero_mem
          add_mem' := by
            intro x y hx hy
            apply J.superset_covering _ (J.intersection_covering hx hy)
            intro D a ha
            change Q.val.map a.op (x + y) ∈ P.obj (op D)
            rw [map_add]
            exact (P.obj (op D)).add_mem ha.1 ha.2
          smul_mem' := by
            intro r x hx
            apply J.superset_covering _ hx
            intro D a ha
            change Q.val.map a.op (r • x) ∈ P.obj (op D)
            rw [Q.val.map_smul]
            exact (P.obj (op D)).smul_mem _ ha }
      map f := H.map f }
  refine ⟨N, ?_, ?_⟩
  · apply (Presheaf.isSheaf_iff_isSheaf_forget J _
      (CategoryTheory.forget AddCommGrpCat.{u + 1})).mpr
    apply (isSheaf_iff_isSheaf_of_type J _).mpr
    exact G.sheafify_isSheaf ((isSheaf_iff_isSheaf_of_type J _).mp
      ((Presheaf.isSheaf_iff_isSheaf_forget J _
        (CategoryTheory.forget AddCommGrpCat.{u + 1})).mp Q.isSheaf))
  · intro B s
    constructor
    · intro hs
      exact ⟨G.sieveOfSection s, hs, fun _ _ ha ↦ ha⟩
    · rintro ⟨T, hT, ht⟩
      exact J.superset_covering ht hT

private def tracePointwiseImage
    (M : ((SheafOfModules.restrictScalars (traceIntegerToField l E V)).obj
      ((traceModulePullback l E p).obj L)).val.Submodule)
    (τ : traceSource l E p L ⟶ L) :
    ((SheafOfModules.restrictScalars (traceIntegerToField l E S)).obj L).val.Submodule where
  obj X :=
    { carrier := {s | ∃ m : M.obj
        (op (AsSmall.up.obj ((proEtaleBaseChange p).obj (AsSmall.down.obj X.unop)))),
          τ.val.app X m.val = s}
      zero_mem' := ⟨0, map_zero _⟩
      add_mem' := by
        rintro s t ⟨m, rfl⟩ ⟨n, rfl⟩
        exact ⟨m + n, map_add _ _ _⟩
      smul_mem' := by
        rintro r s ⟨m, rfl⟩
        let := coefficientExtensionNormedField l E
        let r' := (traceContinuousRingMap
          (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E)) p).hom.app X r
        refine ⟨r' • m, ?_⟩
        change τ.val.app X
          (((((traceModulePullback l E p).obj L).val.obj
            (op (AsSmall.up.obj ((proEtaleBaseChange p).obj
              (AsSmall.down.obj X.unop))))).smul
                ((traceIntegerToField l E V).hom.app
                  (op (AsSmall.up.obj ((proEtaleBaseChange p).obj
                    (AsSmall.down.obj X.unop)))) r')).hom m.val) =
          ((L.val.obj X).smul ((traceIntegerToField l E S).hom.app X r)).hom (τ.val.app X m.val)
        have hcoeff : (traceIntegerToField l E V).hom.app
            (op (AsSmall.up.obj ((proEtaleBaseChange p).obj
              (AsSmall.down.obj X.unop)))) r' =
            (traceFieldRingMap l E p).hom.app X ((traceIntegerToField l E S).hom.app X r) :=
          rfl
        erw [hcoeff]
        exact (τ.val.app X).hom.map_smul _ _ }
  map {X Y} f := by
    rintro s ⟨m, rfl⟩
    refine ⟨⟨_, M.map_mem
      (AsSmall.up.map ((proEtaleBaseChange p).map (AsSmall.down.map f.unop))).op m.property⟩,
      ?_⟩
    exact PresheafOfModules.naturality_apply τ.val f m.val

private theorem trace_local_image
    (M : ((SheafOfModules.restrictScalars (traceIntegerToField l E V)).obj
      ((traceModulePullback l E p).obj L)).val.Submodule)
    (τ : traceSource l E p L ⟶ L) :
    ∃ N : ((SheafOfModules.restrictScalars (traceIntegerToField l E S)).obj L).val.Submodule,
      Presheaf.IsSheaf (proEtaleModelTopology S) N.toPresheafOfModules.presheaf ∧
        ∀ (B : S.ProEt) (s : L.val.obj (op (AsSmall.up.obj B))),
          s ∈ N.obj (op (AsSmall.up.obj B)) ↔
            TraceImageLocalRepresentatives l E p L M τ B s := by
  obtain ⟨N, hN, hmem⟩ := submodule_saturation (proEtaleModelTopology S)
    (traceIntegerRing l E S)
    ((SheafOfModules.restrictScalars (traceIntegerToField l E S)).obj L)
    (tracePointwiseImage l E p L M τ)
  refine ⟨N, hN, ?_⟩
  intro B s
  rw [hmem]
  let e := AsSmall.equiv.{u, u + 1, u + 1} (C := S.ProEt)
  have : e.functor.IsDenseSubsite (ProEt.topology S) (proEtaleModelTopology S) :=
    inferInstanceAs (e.functor.IsDenseSubsite (ProEt.topology S)
      (e.inverse.inducedTopology (ProEt.topology S)))
  constructor
  · rintro ⟨T, hT, ht⟩
    let R := T.functorPushforward (AsSmall.down : proEtaleSiteModel S ⥤ S.ProEt)
    refine ⟨R, ?_, ?_⟩
    · exact (e.inverse.mem_inducedTopology_iff_of_isCoverDense (ProEt.topology S) T).mp hT
    · intro C a ha
      have ha' : T (AsSmall.up.map a) := by
        have hh : (T.functorPushforward
            (AsSmall.down : proEtaleSiteModel S ⥤ S.ProEt)).functorPullback
              AsSmall.down (AsSmall.up.map a) := ha
        rw [show AsSmall.down = (AsSmall.equiv.{u, u + 1, u + 1} (C := S.ProEt)).inverse from rfl,
          Sieve.functorPullback_functorPushforward_eq] at hh
        exact hh
      exact ht (AsSmall.up.obj C) (AsSmall.up.map a) ha'
  · rintro ⟨T, hT, ht⟩
    let R := T.functorPushforward (AsSmall.up : S.ProEt ⥤ proEtaleSiteModel S)
    refine ⟨R, ?_, ?_⟩
    · exact ((AsSmall.equiv.{u, u + 1, u + 1} (C := S.ProEt)).functor.functorPushforward_mem_iff
        (ProEt.topology S) (proEtaleModelTopology S)).mpr hT
    · intro C a ha
      have ha' : T (AsSmall.down.map a) := by
        have hh : (T.functorPushforward
            (AsSmall.up : S.ProEt ⥤ proEtaleSiteModel S)).functorPullback
              AsSmall.up (AsSmall.down.map a) := ha
        rw [show AsSmall.up = (AsSmall.equiv.{u, u + 1, u + 1} (C := S.ProEt)).functor from rfl,
          Sieve.functorPullback_functorPushforward_eq] at hh
        exact hh
      exact ht (AsSmall.down.obj C) (AsSmall.down.map a) ha'


/-- There is a unique rational-linear trace with the sheet-sum formula; its integral
sheaf image is an integral submodule sheaf and is the sheaf sum of the sheet submodules.
Source: blueprint main-20261015, sk-lem-stratified-lattice, "Pushing down by the trace"
(blueprint: lem-sfb-finite-etale-trace-image).

Proof:
1. The unique descended sum of each section defines traceSection. Its universal
sheet formula proves restriction compatibility. Bijective sheet units supply
coordinates for two inputs and a scalar multiple. Addition and diagonal scalar
action commute with the finite sums, so uniqueness of descent proves additivity
and linearity. The resulting natural linear maps form a sheaf-module morphism.
Its characterization at the identity gives local sums, and the universal formula
proves uniqueness of any morphism satisfying local sums.
2. Form the pointwise trace image of the integral submodule. The square formed by
integral-to-rational inclusions and projection precomposition commutes, giving
integral scalar closure. Saturate this submodule by local membership, using common
refinements for addition. Subfunctor sheafification proves the saturated object is
a sheaf. Transfer covering sieves through the existing small-model equivalence to
obtain exactly the stated local-representative predicate.
3. For a local trace representative, take the unique rational sheet coordinates,
restrict its submodule membership to each sheet, and use the local-sum formula.
Conversely the integral sheet-lifting theorem glues the given sheet tuple inside
the integral submodule; its trace is the sum. These are the two inclusions of the
local-sheet-sum description. Empty sheet sets are included in the proved gluing
lemma and give the zero sum.
-/
theorem finite_etale_trace_image (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] {V S : Scheme.{u}}
    (p : V ⟶ S) [IsFinite p] [Etale p]
    (L : SheafOfModules.{u + 1} (traceFieldRing l E S))
    (M : ((SheafOfModules.restrictScalars (traceIntegerToField l E V)).obj
      ((traceModulePullback l E p).obj L)).val.Submodule)
    (hM : Presheaf.IsSheaf (proEtaleModelTopology V) M.toPresheafOfModules.presheaf) :
    (∃! τ : (traceModuleDirectImage l E p).obj ((traceModulePullback l E p).obj L) ⟶ L,
      TraceImageLocalSums l E p L τ) ∧
      ∀ τ : (traceModuleDirectImage l E p).obj ((traceModulePullback l E p).obj L) ⟶ L,
        TraceImageLocalSums l E p L τ →
        ∃ N : ((SheafOfModules.restrictScalars (traceIntegerToField l E S)).obj L).val.Submodule,
          Presheaf.IsSheaf (proEtaleModelTopology S) N.toPresheafOfModules.presheaf ∧
            (∀ (B : S.ProEt) (s : L.val.obj (op (AsSmall.up.obj B))),
              s ∈ N.obj (op (AsSmall.up.obj B)) ↔
                TraceImageLocalRepresentatives l E p L M τ B s) ∧
            (∀ (U : S.ProEt) (_ : Etale U.hom) (J : Type u) [Fintype J]
              (σ : TraceImageSplitting p U J) (B : S.ProEt) (h : B ⟶ U)
              (s : L.val.obj (op (AsSmall.up.obj B))),
              s ∈ N.obj (op (AsSmall.up.obj B)) ↔
                TraceImageLocalSheetSum l E p L M σ h s) := by
  constructor
  · exact ⟨traceMorphism l E p L, traceMorphism_localSums l E p L,
      fun τ hτ ↦ traceMorphism_unique l E p L τ hτ⟩
  · intro τ hτ
    obtain ⟨N, hN, hmem⟩ := trace_local_image l E p L M τ
    refine ⟨N, hN, hmem, ?_⟩
    intro U hU J inst σ B h s
    rw [hmem]
    constructor
    · rintro ⟨R, hR, hr⟩
      refine ⟨R, hR, ?_⟩
      intro C a ha
      obtain ⟨m, hm⟩ := hr C a ha
      have hb := (finiteEtaleTrace_sheet_lifting l E p L σ (a ≫ h)).1
      choose t ht using fun j ↦ (hb j).surjective
        (traceImageSheetRestriction σ (a ≫ h) j ((traceModulePullback l E p).obj L) m.val)
      dsimp only at ht
      refine ⟨t, ?_, ?_⟩
      · exact (hτ U hU J σ C (a ≫ h) m.val t (fun j ↦ (ht j).symm)).symm.trans hm
      · intro j
        erw [ht j]
        exact M.map_mem (AsSmall.up.map (traceImageSheetArrow σ (a ≫ h) j)).op m.property
    · rintro ⟨R, hR, hr⟩
      refine ⟨R, hR, ?_⟩
      intro C a ha
      obtain ⟨t, ht, htM⟩ := hr C a ha
      obtain ⟨m, hm⟩ := (finiteEtaleTrace_sheet_lifting l E p L σ (a ≫ h)).2 M hM t htM
      exact ⟨m, (hτ U hU J σ C (a ≫ h) m.val t hm).trans ht⟩

end AlgebraicGeometry.Scheme
