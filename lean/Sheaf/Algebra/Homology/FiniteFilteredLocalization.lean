/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q03
-/
module

public import Sheaf.CategoryTheory.FiniteFiltrationInduction
public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import Mathlib.CategoryTheory.Localization.Triangulated
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.Algebra.Group.TransferInstance
import Sheaf.Paper.FiniteFilteredGradedExactness

/-!
# Finite filtered objects and their bounded-below localization

Source: Stacks Project, Derived Categories, Sections 13.13 and 13.20, Tags 05S2,
05TW, 05TY and 015Q (blueprint: def-trf-finite-filtered-localization).

`none` allows all finite filtrations, with bounds depending on the object.
`some (a,b)` requires the fixed interval `Fᵃ = ⊤`, `Fᵇ⁺¹ = ⊥`.
The Boolean parameter selects all objects or the full subcategory of filtered injectives.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe w v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The additive subgroup of maps preserving all filtration steps.
Source: Stacks, Homology, Tag 0121
(blueprint: def-trf-finite-filtered-localization). -/
def filteredHomSubgroup (K L : FilteredObject C) : AddSubgroup (K.obj ⟶ L.obj) where
  carrier := fun f ↦ ∀ p : ℤ, ∃ l : (K.filtration.step p : C) ⟶
    (L.filtration.step p : C), l ≫ (L.filtration.step p).arrow =
      (K.filtration.step p).arrow ≫ f
  zero_mem' := fun p ↦ ⟨0, by simp⟩
  add_mem' := by
    intro f g hf hg p
    obtain ⟨f', hf'⟩ := hf p
    obtain ⟨g', hg'⟩ := hg p
    exact ⟨f' + g', by simp [hf', hg', Preadditive.comp_add]⟩
  neg_mem' := by
    intro f hf p
    obtain ⟨f', hf'⟩ := hf p
    exact ⟨-f', by simp [hf']⟩

/-- The existing filtered morphisms identified with their additive subgroup.
Source: Stacks, Tag 0121 (blueprint: def-trf-finite-filtered-localization). -/
def filteredHomEquiv (K L : FilteredObject C) :
    (K ⟶ L) ≃ filteredHomSubgroup K L where
  toFun f := ⟨f.hom, f.preserves⟩
  invFun f := ⟨f.val, f.property⟩
  left_inv f := by cases f; rfl
  right_inv f := by cases f; rfl

/-- Addition of filtered maps is addition of underlying maps.
Source: Stacks, Derived Categories, Section 13.13
(blueprint: def-trf-finite-filtered-localization). -/
instance filteredObjectPreadditive : Preadditive (FilteredObject C) where
  homGroup K L := (filteredHomEquiv K L).addCommGroup
  add_comp := by
    intro K L M f g h
    apply (filteredHomEquiv K M).injective
    apply Subtype.ext
    exact Preadditive.add_comp _ _ _ f.hom g.hom h.hom
  comp_add := by
    intro K L M f g h
    apply (filteredHomEquiv K M).injective
    apply Subtype.ext
    exact Preadditive.comp_add _ _ _ f.hom g.hom h.hom

/-- Finite decreasing filtrations, optionally in a prescribed interval, optionally with
injective graded objects. No uniform bound is imposed across terms of a complex.
Source: Stacks, Tags 0121, 05TW and 015Q
(blueprint: def-trf-finite-filtered-localization). -/
def finiteFilteredProperty (B : Option (ℤ × ℤ)) (inj : Bool) :
    ObjectProperty (FilteredObject C) := fun K ↦
  K.filtration.IsFinite ∧
    (∀ a b : ℤ, B = some (a, b) →
      K.filtration.step a = ⊤ ∧ K.filtration.step (b + 1) = ⊥) ∧
    (∀ p : ℤ, inj = true → Injective (K.filtration.gradedPiece p))

/-- The full additive category of finite filtered objects (`inj = false`) or filtered
injective objects (`inj = true`), with optional fixed filtration bounds.
Source: Stacks, Tags 0121 and 015Q
(blueprint: def-trf-finite-filtered-localization). -/
abbrev FiniteFilteredObjects (C : Type u) [Category.{v} C] [Abelian C]
    (B : Option (ℤ × ℤ)) (inj : Bool) :=
  (finiteFilteredProperty (C := C) B inj).FullSubcategory

variable (C)

/-- The inclusion of filtered injectives into finite filtered objects.
Source: Stacks, Tag 015Q (blueprint: def-trf-finite-filtered-localization). -/
def filteredInjectiveInclusion (B : Option (ℤ × ℤ)) :
    FiniteFilteredObjects C B true ⥤ FiniteFilteredObjects C B false :=
  ObjectProperty.ιOfLE (fun K h ↦ ⟨h.1, h.2.1, fun _ hfalse ↦ by cases hfalse⟩)

/-- The inclusion preserves addition, as both full subcategories use underlying addition.
Source: Stacks, Tag 015Q (blueprint: def-trf-finite-filtered-localization). -/
instance filteredInjectiveInclusion_additive (B : Option (ℤ × ℤ)) :
    (filteredInjectiveInclusion C B).Additive where
  map_add := rfl

private theorem restrictionSteps_arrow {K L : FilteredObject C} (f : K ⟶ L) (p : ℤ) :
    FilteredObject.restrictionSteps f p ≫ (L.filtration.step p).arrow =
      (K.filtration.step p).arrow ≫ f.hom :=
  Classical.choose_spec (f.preserves p)

private theorem gradedMapSteps_π {K L : FilteredObject C} (f : K ⟶ L) (p : ℤ) :
    cokernel.π (Subobject.ofLE _ _ (K.filtration.F_succ_le p)) ≫
        FilteredObject.gradedMapSteps f p =
      FilteredObject.restrictionSteps f p ≫
        cokernel.π (Subobject.ofLE _ _ (L.filtration.F_succ_le p)) := by
  simpa [FilteredObject.gradedMapSteps] using
    (Classical.choose_spec (FilteredObject.exists_gradedMap_steps K L f p))

/-- Graded maps preserve identities.
Source: Stacks, Tags 0121 and 012K.
Proof: the identity on the graded cokernel has the required composite with its
projection; the cokernel universal property makes it the canonical graded map.
(blueprint: def-trf-finite-filtered-localization). -/
theorem filteredGraded_map_id (B : Option (ℤ × ℤ)) (inj : Bool) (p : ℤ)
    (K : FiniteFilteredObjects C B inj) :
    FilteredObject.gradedMapSteps (𝟙 K.obj) p = 𝟙 _ := by
  have hr : FilteredObject.restrictionSteps (𝟙 K.obj) p =
      𝟙 (K.obj.filtration.step p : C) := by
    apply (cancel_mono (K.obj.filtration.step p).arrow).1
    rw [restrictionSteps_arrow]
    change (K.obj.filtration.step p).arrow ≫ 𝟙 _ = _
    simp
  apply (cancel_epi (cokernel.π
    (Subobject.ofLE _ _ (K.obj.filtration.antitone_step (by omega))))).1
  erw [gradedMapSteps_π, hr, Category.id_comp, Category.comp_id]

/-- Graded maps preserve composition.
Source: Stacks, Tags 0121 and 012K.
Proof: compose the two restriction squares and then the two cokernel squares.
Uniqueness of factorization through the monic inclusions and uniqueness of
cokernel descent identify this composite with the graded map of the composite.
(blueprint: def-trf-finite-filtered-localization). -/
theorem filteredGraded_map_comp (B : Option (ℤ × ℤ)) (inj : Bool) (p : ℤ)
    {K L M : FiniteFilteredObjects C B inj} (f : K ⟶ L) (g : L ⟶ M) :
    FilteredObject.gradedMapSteps (f ≫ g).hom p =
      FilteredObject.gradedMapSteps f.hom p ≫ FilteredObject.gradedMapSteps g.hom p := by
  have hr : FilteredObject.restrictionSteps (f ≫ g).hom p =
      FilteredObject.restrictionSteps f.hom p ≫ FilteredObject.restrictionSteps g.hom p := by
    apply (cancel_mono (M.obj.filtration.step p).arrow).1
    simp only [Category.assoc, restrictionSteps_arrow]
    rw [← Category.assoc, restrictionSteps_arrow, Category.assoc]
    rfl
  apply (cancel_epi (cokernel.π
    (Subobject.ofLE _ _ (K.obj.filtration.antitone_step (by omega))))).1
  erw [gradedMapSteps_π, hr, Category.assoc, ← gradedMapSteps_π,
    ← Category.assoc, ← gradedMapSteps_π, Category.assoc]

/-- Forget the filtration (`none`) or take a graded piece (`some p`).
The graded map is the existing canonical map on the cokernels of successive steps.
Source: Stacks, Tags 0121 and 015Q
(blueprint: def-trf-finite-filtered-localization). -/
def filteredEvaluation (B : Option (ℤ × ℤ)) (inj : Bool) (p : Option ℤ) :
    FiniteFilteredObjects C B inj ⥤ C :=
  match p with
  | none =>
    { obj := fun K ↦ K.obj.obj
      map := fun f ↦ f.hom.hom }
  | some p =>
    { obj := fun K ↦ K.obj.filtration.gradedPiece p
      map := fun f ↦ FilteredObject.gradedMapSteps f.hom p
      map_id := filteredGraded_map_id C B inj p
      map_comp := filteredGraded_map_comp C B inj p }

/-- Forgetting and taking graded pieces are additive functors.
Source: Stacks, Section 13.13 and Tag 015Q.
Proof: restrictions of a sum are sums by uniqueness through monic inclusions.
Passing this equality through the cokernel projections proves additivity of the
graded map. The forgetful case is the definition of addition on filtered maps.
(blueprint: def-trf-finite-filtered-localization). -/
theorem filteredEvaluation_additive (B : Option (ℤ × ℤ)) (inj : Bool) (p : Option ℤ) :
    (filteredEvaluation C B inj p).Additive := by
  cases p with
  | none => exact { map_add := rfl }
  | some p =>
    constructor
    intro K L f g
    have hadd : ((f + g).hom).hom = f.hom.hom + g.hom.hom := rfl
    have hr : FilteredObject.restrictionSteps (f + g).hom p =
        FilteredObject.restrictionSteps f.hom p + FilteredObject.restrictionSteps g.hom p := by
      apply (cancel_mono (L.obj.filtration.step p).arrow).1
      rw [Preadditive.add_comp, restrictionSteps_arrow, restrictionSteps_arrow,
        restrictionSteps_arrow, hadd, Preadditive.comp_add]
    change FilteredObject.gradedMapSteps (f + g).hom p =
      FilteredObject.gradedMapSteps f.hom p + FilteredObject.gradedMapSteps g.hom p
    apply (cancel_epi (cokernel.π
      (Subobject.ofLE _ _ (K.obj.filtration.antitone_step (by omega))))).1
    rw [Preadditive.comp_add, gradedMapSteps_π, gradedMapSteps_π, gradedMapSteps_π,
      hr, Preadditive.add_comp]

attribute [instance] filteredEvaluation_additive

private def filteredSum (K L : FilteredObject C) : FilteredObject C where
  obj := K.obj ⊞ L.obj
  filtration :=
    { F := fun p ↦ Subobject.mk (biprod.map (K.filtration.step p).arrow
        (L.filtration.step p).arrow)
      F_succ_le := fun p ↦ Subobject.mk_le_mk_of_comm
        (biprod.map (Subobject.ofLE _ _ (K.filtration.F_succ_le p))
          (Subobject.ofLE _ _ (L.filtration.F_succ_le p))) (by ext <;> simp) }

private def filteredSumFst (K L : FilteredObject C) : filteredSum C K L ⟶ K :=
  ⟨biprod.fst, fun p ↦ ⟨(Subobject.underlyingIso _).hom ≫ biprod.fst, by
    dsimp [filteredSum]
    rw [← Subobject.underlyingIso_hom_comp_eq_mk]
    simp only [Category.assoc, biprod.map_fst]⟩⟩

private def filteredSumSnd (K L : FilteredObject C) : filteredSum C K L ⟶ L :=
  ⟨biprod.snd, fun p ↦ ⟨(Subobject.underlyingIso _).hom ≫ biprod.snd, by
    dsimp [filteredSum]
    rw [← Subobject.underlyingIso_hom_comp_eq_mk]
    simp only [Category.assoc, biprod.map_snd]⟩⟩

private def filteredSumInl (K L : FilteredObject C) : K ⟶ filteredSum C K L :=
  ⟨biprod.inl, fun p ↦ ⟨biprod.inl ≫ (Subobject.underlyingIso _).inv, by
    dsimp [filteredSum]
    rw [Category.assoc, Subobject.underlyingIso_arrow, biprod.inl_map]⟩⟩

private def filteredSumInr (K L : FilteredObject C) : L ⟶ filteredSum C K L :=
  ⟨biprod.inr, fun p ↦ ⟨biprod.inr ≫ (Subobject.underlyingIso _).inv, by
    dsimp [filteredSum]
    rw [Category.assoc, Subobject.underlyingIso_arrow, biprod.inr_map]⟩⟩

private theorem filteredSum_top (K L : FilteredObject C) (p : ℤ)
    (hK : K.filtration.step p = ⊤) (hL : L.filtration.step p = ⊤) :
    (filteredSum C K L).filtration.step p = ⊤ := by
  have : IsIso (K.filtration.step p).arrow := (Subobject.isIso_arrow_iff_eq_top _).2 hK
  have : IsIso (L.filtration.step p).arrow := (Subobject.isIso_arrow_iff_eq_top _).2 hL
  have : IsIso (biprod.map (K.filtration.step p).arrow (L.filtration.step p).arrow) :=
    (biprod.mapIso (asIso (K.filtration.step p).arrow)
      (asIso (L.filtration.step p).arrow)).isIso_hom
  exact Subobject.mk_eq_top_of_isIso _

private theorem filteredSum_bot (K L : FilteredObject C) (p : ℤ)
    (hK : K.filtration.step p = ⊥) (hL : L.filtration.step p = ⊥) :
    (filteredSum C K L).filtration.step p = ⊥ := by
  apply Subobject.mk_eq_bot_iff_zero.2
  have hK' : K.filtration.F p = ⊥ := hK
  have hL' : L.filtration.F p = ⊥ := hL
  have hzK : (K.filtration.F p).arrow = 0 :=
    Subobject.mk_eq_bot_iff_zero.mp ((Subobject.mk_arrow _).trans hK')
  have hzL : (L.filtration.F p).arrow = 0 :=
    Subobject.mk_eq_bot_iff_zero.mp ((Subobject.mk_arrow _).trans hL')
  simp only [hzK, hzL]
  apply biprod.hom_ext <;> simp

private theorem filteredSum_finite (K L : FilteredObject C)
    (hK : K.filtration.IsFinite) (hL : L.filtration.IsFinite) :
    (filteredSum C K L).filtration.IsFinite := by
  obtain ⟨a, b, ha, hb⟩ := hK
  obtain ⟨c, d, hc, hd⟩ := hL
  refine ⟨min a c, max b d, filteredSum_top C K L _ ?_ ?_,
    filteredSum_bot C K L _ ?_ ?_⟩
  · exact top_unique (ha ▸ K.filtration.antitone_step (min_le_left _ _))
  · exact top_unique (hc ▸ L.filtration.antitone_step (min_le_right _ _))
  · exact bot_unique (hb ▸ K.filtration.antitone_step (le_max_left _ _))
  · exact bot_unique (hd ▸ L.filtration.antitone_step (le_max_right _ _))

private theorem filteredSum_property (B : Option (ℤ × ℤ)) (inj : Bool)
    (K L : FiniteFilteredObjects C B inj) :
    finiteFilteredProperty B false (filteredSum C K.obj L.obj) := by
  refine ⟨filteredSum_finite C _ _ K.property.1 L.property.1, ?_, fun _ h ↦ by cases h⟩
  intro a b h
  exact ⟨filteredSum_top C _ _ _ (K.property.2.1 a b h).1 (L.property.2.1 a b h).1,
    filteredSum_bot C _ _ _ (K.property.2.1 a b h).2 (L.property.2.1 a b h).2⟩

private theorem filteredSum_injective (B : Option (ℤ × ℤ)) (inj : Bool)
    (K L : FiniteFilteredObjects C B inj) (p : ℤ)
    (hK : Injective (K.obj.filtration.gradedPiece p))
    (hL : Injective (L.obj.filtration.gradedPiece p)) :
    Injective ((filteredSum C K.obj L.obj).filtration.gradedPiece p) := by
  let S : FiniteFilteredObjects C B false :=
    ⟨filteredSum C K.obj L.obj, filteredSum_property C B inj K L⟩
  let K' : FiniteFilteredObjects C B false :=
    ⟨K.obj, K.property.1, K.property.2.1, fun _ h ↦ by cases h⟩
  let L' : FiniteFilteredObjects C B false :=
    ⟨L.obj, L.property.1, L.property.2.1, fun _ h ↦ by cases h⟩
  let π₁ : S ⟶ K' := ⟨filteredSumFst C K.obj L.obj⟩
  let π₂ : S ⟶ L' := ⟨filteredSumSnd C K.obj L.obj⟩
  let ι₁ : K' ⟶ S := ⟨filteredSumInl C K.obj L.obj⟩
  let ι₂ : L' ⟶ S := ⟨filteredSumInr C K.obj L.obj⟩
  let E := filteredEvaluation C B false (some p)
  have hid : π₁ ≫ ι₁ + π₂ ≫ ι₂ = 𝟙 S := by
    apply ObjectProperty.hom_ext
    apply (filteredHomEquiv _ _).injective
    apply Subtype.ext
    exact biprod.total
  have he : E.map π₁ ≫ E.map ι₁ + E.map π₂ ≫ E.map ι₂ = 𝟙 (E.obj S) := by
    rw [← E.map_comp, ← E.map_comp, ← E.map_add, hid, E.map_id]
  let : Injective (E.obj K') := hK
  let : Injective (E.obj L') := hL
  refine ⟨fun {X Y} g f hf ↦ ?_⟩
  let h₁ := Injective.factorThru (g ≫ E.map π₁) f
  let h₂ := Injective.factorThru (g ≫ E.map π₂) f
  refine ⟨h₁ ≫ E.map ι₁ + h₂ ≫ E.map ι₂, ?_⟩
  dsimp [h₁, h₂]
  rw [Preadditive.comp_add, ← Category.assoc, Injective.comp_factorThru,
    ← Category.assoc, Injective.comp_factorThru, Category.assoc, Category.assoc,
    ← Preadditive.comp_add, he]
  change g ≫ 𝟙 _ = g
  exact Category.comp_id g

open ZeroObject in
private def filteredZero : FilteredObject C where
  obj := 0
  filtration := { F := fun _ ↦ ⊥, F_succ_le := fun _ ↦ le_rfl }

open ZeroObject in
private def finiteFilteredZero (B : Option (ℤ × ℤ)) (inj : Bool) :
    FiniteFilteredObjects C B inj :=
  ⟨filteredZero C, by
    have hs : Subsingleton (Subobject (0 : C)) :=
      Subobject.subsingleton_of_isZero (isZero_zero C)
    refine ⟨⟨0, 0, hs.elim _ _, rfl⟩, fun _ _ _ ↦ ⟨hs.elim _ _, rfl⟩, ?_⟩
    intro p _
    apply IsZero.injective
    exact IsZero.of_epi (cokernel.π _) ((isZero_zero C).of_iso Subobject.botCoeIsoZero)⟩

open ZeroObject in
private theorem finiteFiltered_terminal (B : Option (ℤ × ℤ)) (inj : Bool) :
    HasTerminal (FiniteFilteredObjects C B inj) := by
  apply IsTerminal.hasTerminal (X := finiteFilteredZero C B inj)
  apply IsTerminal.ofUniqueHom (fun _ ↦ 0)
  intro K f
  apply ObjectProperty.hom_ext
  apply (filteredHomEquiv _ _).injective
  apply Subtype.ext
  exact (isZero_zero C).eq_of_tgt _ _

private theorem finiteFiltered_binaryProduct (B : Option (ℤ × ℤ)) (inj : Bool)
    (K L : FiniteFilteredObjects C B inj) : HasBinaryProduct K L := by
  let S : FiniteFilteredObjects C B inj := ⟨filteredSum C K.obj L.obj, by
    refine ⟨(filteredSum_property C B inj K L).1,
      (filteredSum_property C B inj K L).2.1, ?_⟩
    intro p h
    exact filteredSum_injective C B inj K L p (K.property.2.2 p h) (L.property.2.2 p h)⟩
  let π₁ : S ⟶ K := ⟨filteredSumFst C K.obj L.obj⟩
  let π₂ : S ⟶ L := ⟨filteredSumSnd C K.obj L.obj⟩
  let ι₁ : K ⟶ S := ⟨filteredSumInl C K.obj L.obj⟩
  let ι₂ : L ⟶ S := ⟨filteredSumInr C K.obj L.obj⟩
  have h₁₁ : ι₁ ≫ π₁ = 𝟙 K := by
    apply ObjectProperty.hom_ext
    apply (filteredHomEquiv _ _).injective
    apply Subtype.ext
    exact biprod.inl_fst
  have h₂₂ : ι₂ ≫ π₂ = 𝟙 L := by
    apply ObjectProperty.hom_ext
    apply (filteredHomEquiv _ _).injective
    apply Subtype.ext
    exact biprod.inr_snd
  have h₁₂ : ι₁ ≫ π₂ = 0 := by
    apply ObjectProperty.hom_ext
    apply (filteredHomEquiv _ _).injective
    apply Subtype.ext
    exact biprod.inl_snd
  have h₂₁ : ι₂ ≫ π₁ = 0 := by
    apply ObjectProperty.hom_ext
    apply (filteredHomEquiv _ _).injective
    apply Subtype.ext
    exact biprod.inr_fst
  have hid : π₁ ≫ ι₁ + π₂ ≫ ι₂ = 𝟙 S := by
    apply ObjectProperty.hom_ext
    apply (filteredHomEquiv _ _).injective
    apply Subtype.ext
    exact biprod.total
  refine ⟨⟨BinaryFan.mk π₁ π₂, BinaryFan.isLimitMk (X := K) (Y := L) (W := S)
    (fun s ↦ (show s.pt ⟶ S from s.fst ≫ ι₁) + (show s.pt ⟶ S from s.snd ≫ ι₂))
    ?_ ?_ ?_⟩⟩
  · intro s
    simp only [Preadditive.add_comp, Category.assoc, h₁₁, h₂₁, comp_zero, add_zero]
    erw [Category.comp_id]
  · intro s
    simp only [Preadditive.add_comp, Category.assoc, h₁₂, h₂₂, comp_zero, zero_add]
    erw [Category.comp_id]
  · intro s m h₁ h₂
    calc
      m = m ≫ (π₁ ≫ ι₁ + π₂ ≫ ι₂) := by rw [hid, Category.comp_id]
      _ = (show s.pt ⟶ S from s.fst ≫ ι₁) + (show s.pt ⟶ S from s.snd ≫ ι₂) := by
        rw [Preadditive.comp_add, ← Category.assoc, ← Category.assoc, h₁, h₂]

/-- These full subcategories have finite products. The products are the ordinary
finite direct sums with the direct-sum filtration, including the empty sum.
Source: Stacks, Section 13.13 and Tag 015Q.
Proof: take finite biproducts of the underlying objects and their filtration steps.
The inclusions of the summed steps are monic. Common lower and upper bounds for
finitely many finite filtrations give finiteness; prescribed bounds are retained.
Their graded objects are the finite sums of the original graded objects. Finite
sums of injectives are injective. The componentwise projections and lifts satisfy
the product universal property in the full subcategory.
(blueprint: def-trf-finite-filtered-localization). -/
theorem finiteFiltered_hasFiniteProducts (B : Option (ℤ × ℤ)) (inj : Bool) :
    HasFiniteProducts (FiniteFilteredObjects C B inj) := by
  have := finiteFiltered_terminal C B inj
  have : ∀ {K L : FiniteFilteredObjects C B inj}, HasBinaryProduct K L :=
    fun {K L} ↦ finiteFiltered_binaryProduct C B inj K L
  have := hasBinaryProducts_of_hasLimit_pair (C := FiniteFilteredObjects C B inj)
  exact hasFiniteProducts_of_has_binary_and_terminal

attribute [instance] finiteFiltered_hasFiniteProducts

/-- The zero object supplied by the empty product in a preadditive category.
Source: Stacks, Section 13.13 (blueprint: def-trf-finite-filtered-localization). -/
instance finiteFiltered_hasZeroObject (B : Option (ℤ × ℤ)) (inj : Bool) :
    HasZeroObject (FiniteFilteredObjects C B inj) :=
  hasZeroObject_of_hasTerminal_object

/-- Finite biproducts supplied by finite products and addition of filtered maps.
Source: Stacks, Section 13.13 (blueprint: def-trf-finite-filtered-localization). -/
instance finiteFiltered_hasFiniteBiproducts (B : Option (ℤ × ℤ)) (inj : Bool) :
    HasFiniteBiproducts (FiniteFilteredObjects C B inj) :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- Binary biproducts from the existing finite biproduct structure.
Source: Stacks, Section 13.13 (blueprint: def-trf-finite-filtered-localization). -/
instance finiteFiltered_hasBinaryBiproducts (B : Option (ℤ × ℤ)) (inj : Bool) :
    HasBinaryBiproducts (FiniteFilteredObjects C B inj) :=
  hasBinaryBiproducts_of_finite_biproducts (FiniteFilteredObjects C B inj)

/-- `K_F⁺(C)`: bounded-below complexes of finite filtered objects modulo filtered homotopy.
For `inj = true` this is `K⁺(Iᶠ)`; chain homotopies take values in the filtered category.
Source: Stacks, Tags 05TW, 05TY and 015Q
(blueprint: def-trf-finite-filtered-localization). -/
abbrev FiniteFilteredHomotopyPlus (B : Option (ℤ × ℤ)) (inj : Bool) :=
  HomotopyCategory.Plus (FiniteFilteredObjects C B inj)

/-- The filtered quasi-isomorphisms are precisely maps inducing quasi-isomorphisms
on every graded complex, using the canonical graded functors on homotopy categories.
Source: Stacks, Tags 05S2 and 05TY
(blueprint: def-trf-finite-filtered-localization). -/
def finiteFilteredQuasiIso (B : Option (ℤ × ℤ)) :
    MorphismProperty (FiniteFilteredHomotopyPlus C B false) := fun _ _ f ↦
  ∀ p : ℤ, HomotopyCategory.Plus.quasiIso C
    ((filteredEvaluation C B false (some p)).mapHomotopyCategoryPlus.map f)

private def filteredAcyclic (B : Option (ℤ × ℤ)) :
    ObjectProperty (FiniteFilteredHomotopyPlus C B false) := fun K ↦
  ∀ p : ℤ, (HomotopyCategory.Plus.subcategoryAcyclic C).inverseImage
    (filteredEvaluation C B false (some p)).mapHomotopyCategoryPlus K

private instance filteredAcyclic_closed (B : Option (ℤ × ℤ)) :
    (filteredAcyclic C B).IsClosedUnderIsomorphisms where
  of_iso e h p := ((HomotopyCategory.Plus.subcategoryAcyclic C).inverseImage
    (filteredEvaluation C B false (some p)).mapHomotopyCategoryPlus).prop_of_iso e (h p)

open ZeroObject in
private instance filteredAcyclic_zero (B : Option (ℤ × ℤ)) :
    (filteredAcyclic C B).ContainsZero where
  exists_zero := ⟨0, isZero_zero _, fun p ↦
    ((HomotopyCategory.Plus.subcategoryAcyclic C).inverseImage
      (filteredEvaluation C B false (some p)).mapHomotopyCategoryPlus).prop_zero⟩

private instance filteredAcyclic_shift (B : Option (ℤ × ℤ)) :
    (filteredAcyclic C B).IsStableUnderShift ℤ where
  isStableUnderShiftBy n := ⟨fun K h p ↦
    ((HomotopyCategory.Plus.subcategoryAcyclic C).inverseImage
      (filteredEvaluation C B false (some p)).mapHomotopyCategoryPlus).le_shift n K (h p)⟩

private instance filteredAcyclic_triangulated (B : Option (ℤ × ℤ)) :
    (filteredAcyclic C B).IsTriangulated where
  toIsTriangulatedClosed₂ := .mk' (fun T hT h₁ h₃ p ↦
    ((HomotopyCategory.Plus.subcategoryAcyclic C).inverseImage
      (filteredEvaluation C B false (some p)).mapHomotopyCategoryPlus).ext_of_isTriangulatedClosed₂
      T hT (h₁ p) (h₃ p))

private theorem finiteFilteredQuasiIso_eq_trW (B : Option (ℤ × ℤ)) :
    finiteFilteredQuasiIso C B = (filteredAcyclic C B).trW := by
  ext K L f
  obtain ⟨M, g, h, hT⟩ := Pretriangulated.distinguished_cocone_triangle f
  have he := (filteredAcyclic C B).trW_iff_of_distinguished _ hT
  change (filteredAcyclic C B).trW f ↔ _ at he
  rw [he]
  change (∀ p : ℤ, HomotopyCategory.Plus.quasiIso C
    ((filteredEvaluation C B false (some p)).mapHomotopyCategoryPlus.map f)) ↔ _
  simp only [filteredAcyclic]
  apply forall_congr'
  intro p
  rw [HomotopyCategory.Plus.quasiIso_eq_subcategoryAcyclic_trW,
    ← ObjectProperty.inverseImage_trW_iff]
  exact ((HomotopyCategory.Plus.subcategoryAcyclic C).inverseImage
    (filteredEvaluation C B false (some p)).mapHomotopyCategoryPlus).trW_iff_of_distinguished _ hT

/-- Filtered quasi-isomorphisms admit a left calculus of fractions.
Source: Stacks, Section 13.13, construction of the filtered derived category.
Proof: the cone of a filtered quasi-isomorphism is graded acyclic. Graded acyclic
objects form a triangulated subcategory because grading is additive and preserves
mapping-cone triangles. Thus filtered quasi-isomorphisms are exactly the Verdier
class of that subcategory, which has the calculus of fractions. All mapping cones
remain bounded below and, for fixed bounds, retain the same filtration interval.
(blueprint: def-trf-finite-filtered-localization). -/
theorem finiteFilteredQuasiIso_leftFractions (B : Option (ℤ × ℤ)) :
    (finiteFilteredQuasiIso C B).HasLeftCalculusOfFractions := by
  rw [finiteFilteredQuasiIso_eq_trW]
  infer_instance

attribute [instance] finiteFilteredQuasiIso_leftFractions

/-- The graded quasi-isomorphisms are compatible with the standard cone triangulation.
Source: Stacks, Section 13.13, Tag 05S2.
Proof: grading commutes with shifts and cones. Its acyclic objects are triangulated,
and the cone criterion identifies their Verdier class with graded quasi-isomorphisms.
The triangulated-subcategory localization criterion gives the claimed compatibility.
(blueprint: def-trf-finite-filtered-localization). -/
theorem finiteFilteredQuasiIso_triangulation (B : Option (ℤ × ℤ)) :
    (finiteFilteredQuasiIso C B).IsCompatibleWithTriangulation := by
  rw [finiteFilteredQuasiIso_eq_trW]
  infer_instance

attribute [instance] finiteFilteredQuasiIso_triangulation

/-- `DF⁺(C)`, constructed by formally inverting graded quasi-isomorphisms in `K_F⁺(C)`.
Its triangulation is the standard triangulated localization, not an arbitrary structure.
Source: Stacks, Tags 05S2 and 015Q
(blueprint: def-trf-finite-filtered-localization). -/
abbrev FiniteFilteredDerivedPlus (B : Option (ℤ × ℤ)) :=
  (finiteFilteredQuasiIso C B).Localization

/-- The canonical filtered localization functor.
Source: Stacks, Tags 05S2 and 015Q
(blueprint: def-trf-finite-filtered-localization). -/
abbrev finiteFilteredQh (B : Option (ℤ × ℤ)) :
    FiniteFilteredHomotopyPlus C B false ⥤ FiniteFilteredDerivedPlus C B :=
  (finiteFilteredQuasiIso C B).Q

/-- The canonical functor `K⁺(Iᶠ) → DF⁺(C)`, induced by inclusion and localization.
Source: Stacks, Tag 015Q (blueprint: def-trf-finite-filtered-localization). -/
def filteredInjectiveComparison (B : Option (ℤ × ℤ)) :
    FiniteFilteredHomotopyPlus C B true ⥤ FiniteFilteredDerivedPlus C B :=
  (filteredInjectiveInclusion C B).mapHomotopyCategoryPlus ⋙ finiteFilteredQh C B

/-- The comparison commutes with the standard cochain shifts using the inclusion
and localization shift comparisons.
Source: Stacks, Tag 015Q (blueprint: def-trf-finite-filtered-localization). -/
instance filteredInjectiveComparison_commShift (B : Option (ℤ × ℤ)) :
    (filteredInjectiveComparison C B).CommShift ℤ :=
  inferInstanceAs (((filteredInjectiveInclusion C B).mapHomotopyCategoryPlus ⋙
    finiteFilteredQh C B).CommShift ℤ)

private theorem filteredEvaluation_acyclic (B : Option (ℤ × ℤ))
    (K : CochainComplex (FiniteFilteredObjects C B false) ℤ)
    (hK : ∀ p : ℤ,
      (((filteredEvaluation C B false (some p)).mapHomologicalComplex (.up ℤ)).obj K).Acyclic) :
    (((filteredEvaluation C B false none).mapHomologicalComplex (.up ℤ)).obj K).Acyclic := by
  intro n
  let i := (ComplexShape.up ℤ).prev n
  let j := (ComplexShape.up ℤ).next n
  let u : (K.X i).obj ⟶ (K.X n).obj := (K.d i n).hom
  let v : (K.X n).obj ⟶ (K.X j).obj := (K.d n j).hom
  have huv : u.hom ≫ v.hom = 0 := by
    exact congrArg (fun f ↦ f.hom.hom) (K.d_comp_d i n j)
  have hgr (p : ℤ) : (ShortComplex.mk (FilteredObject.gradedMapSteps u p)
      (FilteredObject.gradedMapSteps v p)
      (FilteredObject.gradedMapSteps_comp u v huv p)).Exact := by
    exact hK p n
  exact (FilteredObject.finite_filtered_graded_exactness u v huv
    (K.X i).property.1 (K.X n).property.1 (K.X j).property.1 hgr).2.2.1

private theorem filteredEvaluation_acyclic_homotopy (B : Option (ℤ × ℤ))
    (K : FiniteFilteredHomotopyPlus C B false) (hK : filteredAcyclic C B K) :
    HomotopyCategory.Plus.subcategoryAcyclic C
      ((filteredEvaluation C B false none).mapHomotopyCategoryPlus.obj K) := by
  obtain ⟨L, hL⟩ := HomotopyCategory.quotient_obj_surjective K.obj
  have hgr (p : ℤ) :
      (((filteredEvaluation C B false (some p)).mapHomologicalComplex (.up ℤ)).obj L).Acyclic := by
    have hp := hK p
    change HomotopyCategory.subcategoryAcyclic C
      (((filteredEvaluation C B false (some p)).mapHomotopyCategory (.up ℤ)).obj K.obj) at hp
    rw [← hL] at hp
    exact (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).mp hp
  change HomotopyCategory.subcategoryAcyclic C
    (((filteredEvaluation C B false none).mapHomotopyCategory (.up ℤ)).obj K.obj)
  rw [← hL]
  exact (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).mpr
    (filteredEvaluation_acyclic C B L hgr)

variable [HasDerivedCategory.{w} C]

/-- Forgetting and grading invert filtered quasi-isomorphisms after ordinary localization.
Source: Stacks, Tags 05S2 and 015Q.
Proof: for grading this is the defining condition on the map. For forgetting, a
filtered acyclic cone is acyclic: in each degree its finite filtration is exhaustive
and separated, and exactness of every graded complex implies exactness of the
underlying complex. The ordinary derived localization therefore inverts the map.
(blueprint: def-trf-finite-filtered-localization). -/
theorem filteredEvaluation_inverts (B : Option (ℤ × ℤ)) (p : Option ℤ) :
    (finiteFilteredQuasiIso C B).IsInvertedBy
      ((filteredEvaluation C B false p).mapHomotopyCategoryPlus ⋙
        DerivedCategory.Plus.Qh) := by
  intro K L f hf
  apply Localization.inverts DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso C)
  cases p with
  | some p => exact hf p
  | none =>
    obtain ⟨M, g, h, hT⟩ := Pretriangulated.distinguished_cocone_triangle f
    have hm : filteredAcyclic C B M := by
      have hw : (filteredAcyclic C B).trW f := by
        rw [← finiteFilteredQuasiIso_eq_trW]
        exact hf
      exact ((filteredAcyclic C B).trW_iff_of_distinguished _ hT).mp hw
    rw [HomotopyCategory.Plus.quasiIso_eq_subcategoryAcyclic_trW]
    exact ((HomotopyCategory.Plus.subcategoryAcyclic C).trW_iff_of_distinguished _
      ((filteredEvaluation C B false none).mapHomotopyCategoryPlus.map_distinguished _ hT)).mpr
        (filteredEvaluation_acyclic_homotopy C B M hm)

/-- The canonical forgetful or graded functor `DF⁺(C) → D⁺(C)`, defined by localization
of the corresponding operation on filtered complexes.
Source: Stacks, Tags 05S2 and 015Q
(blueprint: def-trf-finite-filtered-localization). -/
def finiteFilteredDerivedEvaluation (B : Option (ℤ × ℤ)) (p : Option ℤ) :
    FiniteFilteredDerivedPlus C B ⥤ DerivedCategory.Plus C :=
  Localization.Construction.lift
    ((filteredEvaluation C B false p).mapHomotopyCategoryPlus ⋙
      DerivedCategory.Plus.Qh) (filteredEvaluation_inverts C B p)

end CategoryTheory
