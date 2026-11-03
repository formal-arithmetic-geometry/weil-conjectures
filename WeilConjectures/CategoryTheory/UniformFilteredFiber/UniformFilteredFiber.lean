/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.UniformFilteredCone.UniformFilteredCone

import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
/-! # Uniform filtered shifts and mapping fibers

Source: Stacks Project, Derived Categories, Sections 13.9 and 13.13.
Shift each subcomplex inclusion to define the filtration. Its cokernel comparison
identifies every grade with the shifted grade. The fiber is Cone(f)[-1], with its
actual shifted cone filtration. Its projection, null-homotopy and lift through a
supplied null-homotopy are compatible with every step. The canonical graded
projection is a quasi-isomorphism when the target is graded acyclic, by rotating
the ordinary cone triangle. These constructions retain the same fixed interval
and each of the four cochain conditions.
(blueprint: lem-trf-uniform-filtered-fiber).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe v u
namespace CategoryTheory
open Limits
variable {C : Type u} [Category.{v} C] [Abelian C]
namespace UniformFilteredFiber

/-- Shift the actual monic subcomplex inclusions.
Source: Stacks, Sections 13.9 and 13.13; proved by the displayed component and
universal-property identities. (blueprint: lem-trf-uniform-filtered-fiber). -/
def shift (K : FilteredObject (CochainComplex C ℤ)) (r : ℤ) :
    FilteredObject (CochainComplex C ℤ) where
  obj := K.obj⟦r⟧
  filtration :=
    { F := fun p ↦ Subobject.mk ((shiftFunctor _ r).map (K.filtration.F p).arrow)
      F_succ_le := fun p ↦ Subobject.mk_le_mk_of_comm
        ((shiftFunctor _ r).map (Subobject.ofLE _ _ (K.filtration.F_succ_le p)))
        (by rw [← Functor.map_comp, Subobject.ofLE_arrow]) }

/-- Identify a shifted filtration step with the shift of the original step.
Source: Stacks, Sections 13.9 and 13.13; proved by the displayed component and
universal-property identities. (blueprint: lem-trf-uniform-filtered-fiber). -/
def stepIso (K : FilteredObject (CochainComplex C ℤ)) (r p : ℤ) :
    ((shift K r).filtration.F p : CochainComplex C ℤ) ≅
      (K.filtration.F p : CochainComplex C ℤ)⟦r⟧ :=
  Subobject.underlyingIso _

/-- The step comparison commutes with successive inclusions.
Source: Stacks, Sections 13.9 and 13.13; proved by the displayed component and
universal-property identities. (blueprint: lem-trf-uniform-filtered-fiber). -/
theorem stepIso_next (K : FilteredObject (CochainComplex C ℤ)) (r p : ℤ) :
    Subobject.ofLE _ _ ((shift K r).filtration.F_succ_le p) ≫ (stepIso K r p).hom =
      (stepIso K r (p + 1)).hom ≫
        (shiftFunctor _ r).map (Subobject.ofLE _ _ (K.filtration.F_succ_le p)) := by
  apply (cancel_mono ((shiftFunctor _ r).map (K.filtration.F p).arrow)).1
  rw [Category.assoc, stepIso, Subobject.underlyingIso_hom_comp_eq_mk,
    Category.assoc, ← Functor.map_comp, Subobject.ofLE_arrow]
  rw [stepIso, Subobject.underlyingIso_hom_comp_eq_mk]
  exact Subobject.ofLE_arrow _

/-- The cokernel comparison identifies a shifted grade with the shifted original grade.
Source: Stacks, Sections 13.9 and 13.13; proved by the displayed component and
universal-property identities. (blueprint: lem-trf-uniform-filtered-fiber). -/
def gradeIso (K : FilteredObject (CochainComplex C ℤ)) (r p : ℤ) :
    (shift K r).filtration.gr p ≅ (K.filtration.gr p)⟦r⟧ :=
  cokernel.mapIso _ _ (stepIso K r (p + 1)) (stepIso K r p) (stepIso_next K r p) ≪≫
    (PreservesCokernel.iso (shiftFunctor _ r)
      (Subobject.ofLE _ _ (K.filtration.F_succ_le p))).symm

/-- The graded comparison intertwines the canonical cokernel projections.
Source: Stacks, Sections 13.9 and 13.13; proved by the displayed component and
universal-property identities. (blueprint: lem-trf-uniform-filtered-fiber). -/
theorem gradeIso_fac (K : FilteredObject (CochainComplex C ℤ)) (r p : ℤ) :
    cokernel.π (Subobject.ofLE _ _ ((shift K r).filtration.F_succ_le p)) ≫
      (gradeIso K r p).hom = (stepIso K r p).hom ≫
        (shiftFunctor _ r).map (cokernel.π (Subobject.ofLE _ _ (K.filtration.F_succ_le p))) := by
  simp only [gradeIso, Iso.trans_hom, cokernel.mapIso_hom, cokernel.map, ← Category.assoc,
    cokernel.π_desc]
  simp [Category.assoc, PreservesCokernel.iso_inv, π_comp_cokernelComparison]

/-- A full filtration step stays full after shift.
Source: Stacks, Sections 13.9 and 13.13; proved by the displayed component and
universal-property identities. (blueprint: lem-trf-uniform-filtered-fiber). -/
theorem top (K : FilteredObject (CochainComplex C ℤ)) (r p : ℤ)
    (h : K.filtration.F p = ⊤) : (shift K r).filtration.F p = ⊤ := by
  have : IsIso (K.filtration.F p).arrow := (Subobject.isIso_arrow_iff_eq_top _).2 h
  exact Subobject.mk_eq_top_of_isIso _

/-- A zero filtration step stays zero after shift.
Source: Stacks, Sections 13.9 and 13.13; proved by the displayed component and
universal-property identities. (blueprint: lem-trf-uniform-filtered-fiber). -/
theorem bot (K : FilteredObject (CochainComplex C ℤ)) (r p : ℤ)
    (h : K.filtration.F p = ⊥) : (shift K r).filtration.F p = ⊥ := by
  apply Subobject.mk_eq_bot_iff_zero.2
  have hz : (K.filtration.F p).arrow = 0 :=
    Subobject.mk_eq_bot_iff_zero.mp ((Subobject.mk_arrow _).trans h)
  simp only [hz, Functor.map_zero]

/-- Each of the four cochain conditions is stable under a shift.
Source: Stacks, Sections 13.9 and 13.13; proved by the displayed component and
universal-property identities. (blueprint: lem-trf-uniform-filtered-fiber). -/
theorem condition (K : CochainComplex C ℤ) (r : ℤ)
    (P : ObjectProperty (CochainComplex C ℤ)) (hP : IsUniformCochainCondition P)
    (h : P K) : P (K⟦r⟧) := by
  rcases hP with rfl | rfl | rfl | rfl
  · trivial
  · exact (CochainComplex.plus C).le_shift r K h
  · exact (CochainComplex.minus C).le_shift r K h
  · exact ⟨(CochainComplex.plus C).le_shift r K h.1,
      (CochainComplex.minus C).le_shift r K h.2⟩

/-- Shifts retain uniform finiteness, the prescribed interval, and the cochain condition.
Source: Stacks, Sections 13.9 and 13.13; proved by the displayed component and
universal-property identities. (blueprint: lem-trf-uniform-filtered-fiber). -/
theorem property (B : Option (ℤ × ℤ)) (P : ObjectProperty (CochainComplex C ℤ))
    (hP : IsUniformCochainCondition P) (K : UniformFilteredComplexes C B P) (r : ℤ) :
    uniformFilteredProperty B P (shift K.obj r) := by
  obtain ⟨a, b, ha, hb⟩ := K.property.1
  exact ⟨⟨a, b, top _ r a ha, bot _ r b hb⟩,
    fun a b hB ↦ ⟨top _ r a (K.property.2.1 a b hB).1,
      bot _ r (b + 1) (K.property.2.1 a b hB).2⟩,
    condition _ r P hP K.property.2.2⟩

open CochainComplex CochainComplex.HomComplex

/-- The standard projection from the shifted cone to its source.
Source: Stacks, Sections 13.9 and 13.13; proved by the displayed component and
universal-property identities. (blueprint: lem-trf-uniform-filtered-fiber). -/
def fiberProjection {K L : CochainComplex C ℤ} (f : K ⟶ L) :
    (mappingCone f)⟦(-1 : ℤ)⟧ ⟶ K :=
  -Cocycle.homOf ((mappingCone.fst f).leftShift (-1) 0 (by omega))

/-- The projection has the ordinary first cone component in the shifted degree.
Source: Stacks, Sections 13.9 and 13.13; proved by the displayed component and
universal-property identities. (blueprint: lem-trf-uniform-filtered-fiber). -/
theorem fiberProjection_f {K L : CochainComplex C ℤ} (f : K ⟶ L) (n : ℤ) :
    (fiberProjection f).f n =
      ((mappingCone f).shiftFunctorObjXIso (-1) n (n + -1) (by omega)).hom ≫
        (mappingCone.fst f).1.v (n + -1) n (by omega) := by
  simp [fiberProjection, Cocycle.homOf, Cochain.leftShift, Cocycle.leftShift]

/-- The fiber projection followed by the original map is null-homotopic.
Source: Stacks, Sections 13.9 and 13.13; proved by the displayed component and
universal-property identities. (blueprint: lem-trf-uniform-filtered-fiber). -/
def fiberNullHomotopy {K L : CochainComplex C ℤ} (f : K ⟶ L) :
    Homotopy (fiberProjection f ≫ f) 0 :=
  (Cochain.equivHomotopy _ _).symm
    ⟨-(mappingCone.snd f).leftShift (-1) (-1) (by omega), by
      simp only [δ_neg, Cochain.ofHom_comp, fiberProjection, Cochain.ofHom_neg,
        Cocycle.cochain_ofHom_homOf_eq_coe, Cocycle.leftShift_coe, Cochain.neg_comp]
      rw [Cochain.δ_leftShift _ (-1) (-1) 0 (by omega) 1 (by omega)]
      simp [mappingCone.δ_snd, Cochain.leftShift_comp_zero_cochain]⟩


/-- The fiber projection commutes with the map of a commutative square.
Source: Stacks, Sections 13.9 and 13.13; proved by the displayed component and
universal-property identities. (blueprint: lem-trf-uniform-filtered-fiber). -/
theorem fiberProjection_naturality {K L K' L' : CochainComplex C ℤ}
    (f : K ⟶ L) (g : K' ⟶ L') (a : K ⟶ K') (b : L ⟶ L')
    (h : f ≫ b = a ≫ g) :
    (mappingCone.map f g a b h)⟦(-1 : ℤ)⟧' ≫ fiberProjection g =
      fiberProjection f ≫ a := by
  ext n
  have he (i j : ℤ) (hij : i + 1 = j) :
      (mappingCone.map f g a b h).f i ≫ (mappingCone.fst g).1.v i j hij =
        (mappingCone.fst f).1.v i j hij ≫ a.f j := by
    subst j
    exact UniformFilteredCone.coneMap_fst f g a b h i
  simp only [HomologicalComplex.comp_f, fiberProjection_f, shiftFunctor_map_f']
  change (mappingCone.map f g a b h).f (n + -1) ≫
      (𝟙 _) ≫ (mappingCone.fst g).1.v (n + -1) n (by omega) =
    ((𝟙 _) ≫ (mappingCone.fst f).1.v (n + -1) n (by omega)) ≫ a.f n
  rw [Category.id_comp, Category.id_comp]
  exact he (n + -1) n (by omega)


/-- The actual filtered mapping fiber is the shifted filtered cone.
Source: Stacks, Sections 13.9 and 13.13; proved by the displayed component and
universal-property identities. (blueprint: lem-trf-uniform-filtered-fiber). -/
def fiber (K L : FilteredObject (CochainComplex C ℤ)) (f : K ⟶ L) :
    FilteredObject (CochainComplex C ℤ) := shift (UniformFilteredCone.filteredCone f) (-1)

/-- Identify a fiber filtration step with the fiber of the restricted map.
Source: Stacks, Sections 13.9 and 13.13; proved by the displayed component and
universal-property identities. (blueprint: lem-trf-uniform-filtered-fiber). -/
def fiberStepIso {K L : FilteredObject (CochainComplex C ℤ)} (f : K ⟶ L) (p : ℤ) :
    ((fiber K L f).filtration.F p : CochainComplex C ℤ) ≅
      (mappingCone (FilteredObject.restrictionSteps f p))⟦(-1 : ℤ)⟧ :=
  stepIso (UniformFilteredCone.filteredCone f) (-1) p ≪≫
    (shiftFunctor _ (-1)).mapIso (UniformFilteredCone.coneStepIso f p)

/-- The step comparison identifies its inclusion with the shifted cone step map.
Source: Stacks, Sections 13.9 and 13.13; proved by the displayed component and
universal-property identities. (blueprint: lem-trf-uniform-filtered-fiber). -/
theorem fiberStepIso_fac {K L : FilteredObject (CochainComplex C ℤ)} (f : K ⟶ L) (p : ℤ) :
    (fiberStepIso f p).hom ≫
      (shiftFunctor _ (-1)).map (UniformFilteredCone.coneStep f p) =
        ((fiber K L f).filtration.F p).arrow := by
  dsimp only [fiberStepIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [Category.assoc, ← Functor.map_comp]
  change (stepIso (UniformFilteredCone.filteredCone f) (-1) p).hom ≫
    (shiftFunctor _ (-1)).map
      ((Subobject.underlyingIso (UniformFilteredCone.coneStep f p)).hom ≫
        UniformFilteredCone.coneStep f p) = _
  rw [Subobject.underlyingIso_hom_comp_eq_mk]
  exact Subobject.underlyingIso_hom_comp_eq_mk _

/-- The inverse step comparison gives the shifted cone step inclusion.
Source: Stacks, Sections 13.9 and 13.13; proved by the displayed component and
universal-property identities. (blueprint: lem-trf-uniform-filtered-fiber). -/
theorem fiberStepIso_inv_fac {K L : FilteredObject (CochainComplex C ℤ)}
    (f : K ⟶ L) (p : ℤ) : (fiberStepIso f p).inv ≫
      ((fiber K L f).filtration.F p).arrow =
        (shiftFunctor _ (-1)).map (UniformFilteredCone.coneStep f p) := by
  rw [← fiberStepIso_fac f p, Iso.inv_hom_id_assoc]

/-- The ordinary projection on a restricted fiber factors the total projection.
Source: Stacks, Sections 13.9 and 13.13; proved by the displayed component and
universal-property identities. (blueprint: lem-trf-uniform-filtered-fiber). -/
theorem fiberProjectionStep_fac {K L : FilteredObject (CochainComplex C ℤ)}
    (f : K ⟶ L) (p : ℤ) :
    ((fiberStepIso f p).hom ≫ fiberProjection (FilteredObject.restrictionSteps f p)) ≫
        (K.filtration.F p).arrow =
      ((fiber K L f).filtration.F p).arrow ≫ fiberProjection f.hom := by
  rw [Category.assoc, ← fiberProjection_naturality _ _ _ _
    (UniformFilteredCone.restriction_arrow f p)]
  change (fiberStepIso f p).hom ≫
    (shiftFunctor _ (-1)).map (UniformFilteredCone.coneStep f p) ≫ _ = _
  rw [← Category.assoc, fiberStepIso_fac]

/-- The standard fiber projection preserves the actual subcomplex filtration.
Source: Stacks, Sections 13.9 and 13.13; proved by the displayed component and
universal-property identities. (blueprint: lem-trf-uniform-filtered-fiber). -/
def filteredFiberProjection {K L : FilteredObject (CochainComplex C ℤ)} (f : K ⟶ L) :
    fiber K L f ⟶ K :=
  ⟨fiberProjection f.hom, fun p ↦
    ⟨(fiberStepIso f p).hom ≫ fiberProjection (FilteredObject.restrictionSteps f p),
      fiberProjectionStep_fac f p⟩⟩

/-- The standard fiber null-homotopy commutes with every square.
Source: Stacks, Sections 13.9 and 13.13; proved by the displayed component and
universal-property identities. (blueprint: lem-trf-uniform-filtered-fiber). -/
theorem fiberNullHomotopy_naturality {K L K' L' : CochainComplex C ℤ}
    (f : K ⟶ L) (g : K' ⟶ L') (a : K ⟶ K') (b : L ⟶ L')
    (h : f ≫ b = a ≫ g) (n m : ℤ) :
    ((mappingCone.map f g a b h)⟦(-1 : ℤ)⟧').f n ≫
      (fiberNullHomotopy g).hom n m = (fiberNullHomotopy f).hom n m ≫ b.f m := by
  by_cases hnm : n + (-1) = m
  · subst m
    simp only [fiberNullHomotopy, Cochain.equivHomotopy, Equiv.symm, Equiv.coe_fn_mk,
      Cochain.leftShift,
      Cochain.neg_v, Cochain.mk_v, shiftFunctor_map_f', shiftFunctor_obj_X',
      shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom,
      Int.reduceNeg, Int.reduceMul, Int.reduceSub, Int.reduceDiv, Int.reduceAdd,
      Int.negOnePow_even 2 ⟨1, rfl⟩, one_smul, dite_true, Preadditive.comp_neg,
      Preadditive.neg_comp, neg_inj]
    change (mappingCone.map f g a b h).f (n + -1) ≫
        (𝟙 ((mappingCone g).X (n + -1))) ≫
          (mappingCone.snd g).v (n + -1) (n + -1) (add_zero _) =
      ((𝟙 ((mappingCone f).X (n + -1))) ≫
        (mappingCone.snd f).v (n + -1) (n + -1) (add_zero _)) ≫ b.f (n + -1)
    rw [Category.id_comp, Category.id_comp]
    exact UniformFilteredCone.coneMap_snd f g a b h (n + -1)
  · have hrel : ¬ (ComplexShape.up ℤ).Rel m n := by
      simp only [ComplexShape.up_Rel]
      omega
    rw [Homotopy.zero _ _ _ hrel, Homotopy.zero _ _ _ hrel]
    simp

/-- The standard fiber null-homotopy preserves every filtration step.
Source: Stacks, Sections 13.9 and 13.13; proved by the displayed component and
universal-property identities. (blueprint: lem-trf-uniform-filtered-fiber). -/
theorem filteredFiber_nullHomotopy {K L : FilteredObject (CochainComplex C ℤ)}
    (f : K ⟶ L) : UniformFilteredHomotopy (filteredFiberProjection f ≫ f) 0 := by
  refine ⟨fiberNullHomotopy f.hom, ?_⟩
  intro p n m
  refine ⟨(fiberStepIso f p).hom.f n ≫
    (fiberNullHomotopy (FilteredObject.restrictionSteps f p)).hom n m, ?_⟩
  rw [Category.assoc, ← fiberNullHomotopy_naturality _ _ _ _
    (UniformFilteredCone.restriction_arrow f p) n m, ← Category.assoc]
  change ((fiberStepIso f p).hom.f n ≫
    ((shiftFunctor _ (-1)).map (UniformFilteredCone.coneStep f p)).f n) ≫ _ = _
  rw [← HomologicalComplex.comp_f, fiberStepIso_fac]

/-- Identify a fiber grade with the shifted cone of the corresponding graded map.
Source: Stacks, Sections 13.9 and 13.13; proved by the displayed component and
universal-property identities. (blueprint: lem-trf-uniform-filtered-fiber). -/
def fiberGradeIso {K L : FilteredObject (CochainComplex C ℤ)} (f : K ⟶ L) (p : ℤ) :
    (fiber K L f).filtration.gr p ≅
      (mappingCone (FilteredObject.gradedMapSteps f p))⟦(-1 : ℤ)⟧ :=
  gradeIso (UniformFilteredCone.filteredCone f) (-1) p ≪≫
    (shiftFunctor _ (-1)).mapIso (UniformFilteredCone.filteredCone_gradeIso f p)

/-- The ordinary projection is unchanged by transport along equality of maps.
Source: Stacks, Sections 13.9 and 13.13; proved by the displayed component and
universal-property identities. (blueprint: lem-trf-uniform-filtered-fiber). -/
theorem fiberProjection_eqToIso {K L : CochainComplex C ℤ} (f g : K ⟶ L) (h : f = g) :
    (shiftFunctor _ (-1)).map (eqToIso (congrArg (fun φ ↦ mappingCone φ) h)).hom ≫
      fiberProjection g = fiberProjection f := by
  subst h
  simp

/-- Restriction of the filtered projection agrees with the ordinary step projection.
Source: Stacks, Sections 13.9 and 13.13; proved by the displayed component and
universal-property identities. (blueprint: lem-trf-uniform-filtered-fiber). -/
theorem filteredFiberProjection_restriction
    {K L : FilteredObject (CochainComplex C ℤ)} (f : K ⟶ L) (p : ℤ) :
    FilteredObject.restrictionSteps (filteredFiberProjection f) p =
      (fiberStepIso f p).hom ≫ fiberProjection (FilteredObject.restrictionSteps f p) := by
  apply (cancel_mono (K.filtration.F p).arrow).1
  rw [UniformFilteredCone.restriction_arrow]
  exact (fiberProjectionStep_fac f p).symm

/-- The fiber grade comparison intertwines its cokernel projection.
Source: Stacks, Sections 13.9 and 13.13; proved by the displayed component and
universal-property identities. (blueprint: lem-trf-uniform-filtered-fiber). -/
theorem fiberGradeIso_fac {K L : FilteredObject (CochainComplex C ℤ)}
    (f : K ⟶ L) (p : ℤ) :
    cokernel.π (Subobject.ofLE _ _ ((fiber K L f).filtration.F_succ_le p)) ≫
      (fiberGradeIso f p).hom = (fiberStepIso f p).hom ≫
        (shiftFunctor _ (-1)).map (cokernel.π (UniformFilteredCone.coneNext f p)) ≫
          (shiftFunctor _ (-1)).map (UniformFilteredCone.coneCokernelIso f p).hom := by
  dsimp only [fiberGradeIso, fiberStepIso, fiber, Iso.trans_hom, Functor.mapIso_hom]
  simp only [← Category.assoc]
  rw [gradeIso_fac, Category.assoc, ← Functor.map_comp,
    UniformFilteredCone.filteredCone_gradeIso_fac]
  simp only [Functor.map_comp, Category.assoc]

/-- The actual graded projection agrees with the ordinary projection under comparison.
Source: Stacks, Sections 13.9 and 13.13; proved by the displayed component and
universal-property identities. (blueprint: lem-trf-uniform-filtered-fiber). -/
theorem fiberGradeIso_projection
    {K L : FilteredObject (CochainComplex C ℤ)} (f : K ⟶ L) (p : ℤ) :
    FilteredObject.gradedMapSteps (filteredFiberProjection f) p =
      (fiberGradeIso f p).hom ≫ fiberProjection (FilteredObject.gradedMapSteps f p) := by
  apply (cancel_epi (cokernel.π
    (Subobject.ofLE _ _ ((fiber K L f).filtration.F_succ_le p)))).1
  have hπ : cokernel.π (Subobject.ofLE _ _ ((fiber K L f).filtration.F_succ_le p)) ≫
      FilteredObject.gradedMapSteps (filteredFiberProjection f) p =
        FilteredObject.restrictionSteps (filteredFiberProjection f) p ≫
          cokernel.π (Subobject.ofLE _ _ (K.filtration.F_succ_le p)) :=
    Classical.choose_spec (FilteredObject.exists_gradedMap_steps _ _ (filteredFiberProjection f) p)
  rw [hπ, filteredFiberProjection_restriction]
  rw [← Category.assoc _ (fiberGradeIso f p).hom, fiberGradeIso_fac]
  simp only [Category.assoc]
  apply congrArg ((fiberStepIso f p).hom ≫ ·)
  rw [← Category.assoc]
  rw [← Functor.map_comp, UniformFilteredCone.coneCokernelIso_fac,
    Functor.map_comp, Category.assoc, fiberProjection_eqToIso]
  · exact (fiberProjection_naturality _ _ _ _ _).symm
  · exact UniformFilteredCone.graded_eq_cokernel_map f p

/-- The explicit shift-by-one then shift-by-minus-one comparison.
Source: Stacks, Sections 13.9 and 13.13; proved by the displayed component and
universal-property identities. (blueprint: lem-trf-uniform-filtered-fiber). -/
def doubleShiftIso (K : CochainComplex C ℤ) : K⟦(1 : ℤ)⟧⟦(-1 : ℤ)⟧ ≅ K :=
  ((CochainComplex.shiftFunctorAdd' C 1 (-1) 0 (by omega)).symm ≪≫
    CochainComplex.shiftFunctorZero' C 0 rfl).app K

/-- The fiber projection is the shifted third cone arrow, with its rotation sign.
Source: Stacks, Sections 13.9 and 13.13; proved by the displayed component and
universal-property identities. (blueprint: lem-trf-uniform-filtered-fiber). -/
theorem fiberProjection_triangle {K L : CochainComplex C ℤ} (f : K ⟶ L) :
    fiberProjection f = -(mappingCone.triangle f).mor₃⟦(-1 : ℤ)⟧' ≫
      (doubleShiftIso K).hom := by
  ext n
  suffices he : (𝟙 ((mappingCone f).X (n + -1))) ≫
      (mappingCone.fst f).1.v (n + -1) n (by omega) =
        (mappingCone.fst f).1.v (n + -1) n (by omega) by
    convert he using 1 <;>
      simp [fiberProjection_f, mappingCone.triangle, Cocycle.homOf, Cocycle.rightShift,
        Cochain.rightShift, doubleShiftIso, CochainComplex.shiftFunctorAdd',
        CochainComplex.shiftFunctorZero', Cochain.v_comp_XIsoOfEq_hom, he]
  exact Category.id_comp _

/-- The ordinary fiber projection is a quasi-isomorphism if its target cone term is acyclic.
Source: Stacks, Sections 13.9 and 13.13; proved by the displayed component and
universal-property identities. (blueprint: lem-trf-uniform-filtered-fiber). -/
theorem fiberProjection_quasiIso {K L : CochainComplex C ℤ}
    (f : K ⟶ L) (hL : L.Acyclic) : QuasiIso (fiberProjection f) := by
  have hd : QuasiIso (mappingCone.triangle f).mor₃ := by
    rw [← HomologicalComplex.mem_quasiIso_iff,
      ← HomotopyCategory.quotient_map_mem_quasiIso_iff,
      HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
    apply ((HomotopyCategory.subcategoryAcyclic C).trW.cancel_right_of_respectsIso
      ((HomotopyCategory.quotient C (.up ℤ)).map (mappingCone.triangle f).mor₃)
      (((HomotopyCategory.quotient C (.up ℤ)).commShiftIso (1 : ℤ)).hom.app K)).1
    exact ObjectProperty.trW.mk' (HomotopyCategory.subcategoryAcyclic C)
      (Pretriangulated.rot_of_distTriang _
        (HomotopyCategory.mappingCone_triangleh_distinguished f))
      ((HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic L).2 hL)
  let d : mappingCone f ⟶ K⟦(1 : ℤ)⟧ := (mappingCone.triangle f).mor₃
  have : QuasiIso d := hd
  have he : fiberProjection f = d⟦(-1 : ℤ)⟧' ≫ (-doubleShiftIso K).hom := by
    rw [fiberProjection_triangle]
    simp only [Preadditive.neg_iso_hom, Preadditive.comp_neg]
    rfl
  rw [he]
  infer_instance

/-- A shift of an acyclic complex is acyclic.
Source: Stacks, Sections 13.9 and 13.13; proved by the displayed component and
universal-property identities. (blueprint: lem-trf-uniform-filtered-fiber). -/
theorem shifted_acyclic (K : CochainComplex C ℤ) (r : ℤ) (hK : K.Acyclic) :
    (K⟦r⟧).Acyclic := by
  intro n
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact (hK (r + n)).isZero_homology.of_iso
    ((CochainComplex.ShiftSequence.shiftIso C r n (r + n) rfl).app K)

/-- fiber_Shifts retain uniform finiteness, the prescribed interval, and the cochain condition.
Source: Stacks, Sections 13.9 and 13.13; proved by the displayed component and
universal-property identities. (blueprint: lem-trf-uniform-filtered-fiber). -/
theorem fiber_property (B : Option (ℤ × ℤ)) (P : ObjectProperty (CochainComplex C ℤ))
    (hP : IsUniformCochainCondition P) {K L : UniformFilteredComplexes C B P} (f : K ⟶ L) :
    uniformFilteredProperty B P (fiber K.obj L.obj f.hom) :=
  property B P hP
    ⟨UniformFilteredCone.filteredCone f.hom,
      UniformFilteredCone.filteredCone_property B P hP f⟩ (-1)

/-- The fiber of a graded quasi-isomorphism is graded acyclic.
Source: Stacks, Sections 13.9 and 13.13; proved by the displayed component and
universal-property identities. (blueprint: lem-trf-uniform-filtered-fiber). -/
theorem filteredFiber_acyclic {K L : FilteredObject (CochainComplex C ℤ)}
    (f : K ⟶ L) (hf : ∀ p : ℤ, QuasiIso (FilteredObject.gradedMapSteps f p)) :
    ∀ p : ℤ, ((fiber K L f).filtration.gr p).Acyclic := by
  intro p n
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  have hK := shifted_acyclic _ (-1) (UniformFilteredCone.filteredCone_acyclic f hf p)
  exact (hK n).isZero_homology.of_iso
    ((HomologicalComplex.homologyFunctor C (.up ℤ) n).mapIso
      (gradeIso (UniformFilteredCone.filteredCone f) (-1) p))

/-- The fiber projection is a graded quasi-isomorphism if the target is graded acyclic.
Source: Stacks, Sections 13.9 and 13.13; proved by the displayed component and
universal-property identities. (blueprint: lem-trf-uniform-filtered-fiber). -/
theorem filteredFiberProjection_quasiIso {K L : FilteredObject (CochainComplex C ℤ)}
    (f : K ⟶ L) (hL : ∀ p : ℤ, (L.filtration.gr p).Acyclic) :
    ∀ p : ℤ, QuasiIso (FilteredObject.gradedMapSteps (filteredFiberProjection f) p) := by
  intro p
  have : QuasiIso (fiberProjection (FilteredObject.gradedMapSteps f p)) :=
    fiberProjection_quasiIso _ (hL p)
  rw [fiberGradeIso_projection]
  infer_instance


end UniformFilteredFiber
end CategoryTheory
