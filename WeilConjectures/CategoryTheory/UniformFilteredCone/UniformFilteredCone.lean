/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.UniformFilteredHomotopy
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic

/-!
# Uniform filtered cones and their canonical associated-graded comparison

Source: Stacks Project, Derived Categories, Section 13.13, Tags 05S1--05S3.
The filtration steps are the actual mapping cones of restricted maps. Their
monic maps into the total cone define subobjects. The canonical graded cone
comparison is constructed from the cokernel universal property in each degree.
(blueprint: lem-trf-uniform-filtered-cone-grading).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe v u

namespace CategoryTheory

namespace UniformFilteredCone

open Limits CochainComplex CochainComplex.HomComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The cone map commutes with its first degreewise projection.
Source: Stacks, Section 13.13. The component formulas and universal-property
identities below prove the assertion.
(blueprint: lem-trf-uniform-filtered-cone-grading). -/
theorem coneMap_fst {K L K' L' : CochainComplex C ℤ}
    (f : K ⟶ L) (g : K' ⟶ L') (a : K ⟶ K') (b : L ⟶ L')
    (h : f ≫ b = a ≫ g) (n : ℤ) :
    (mappingCone.map f g a b h).f n ≫ (mappingCone.fst g).1.v n (n + 1) rfl =
      (mappingCone.fst f).1.v n (n + 1) rfl ≫ a.f (n + 1) := by
  apply mappingCone.ext_from _ (n + 1) n rfl <;> simp [mappingCone.map]

/-- The cone map commutes with its second degreewise projection.
Source: Stacks, Section 13.13. The component formulas and universal-property
identities below prove the assertion.
(blueprint: lem-trf-uniform-filtered-cone-grading). -/
theorem coneMap_snd {K L K' L' : CochainComplex C ℤ}
    (f : K ⟶ L) (g : K' ⟶ L') (a : K ⟶ K') (b : L ⟶ L')
    (h : f ≫ b = a ≫ g) (n : ℤ) :
    (mappingCone.map f g a b h).f n ≫ (mappingCone.snd g).v n n (add_zero n) =
      (mappingCone.snd f).v n n (add_zero n) ≫ b.f n := by
  apply mappingCone.ext_from _ (n + 1) n rfl <;> simp [mappingCone.map]

/-- Restrictions commute with the inclusions of filtration steps.
Source: Stacks, Section 13.13. The component formulas and universal-property
identities below prove the assertion.
(blueprint: lem-trf-uniform-filtered-cone-grading). -/
theorem restriction_arrow {K L : FilteredObject (CochainComplex C ℤ)}
    (f : K ⟶ L) (p : ℤ) :
    FilteredObject.restrictionSteps f p ≫ (L.filtration.F p).arrow =
      (K.filtration.F p).arrow ≫ f.hom := Classical.choose_spec (f.preserves p)

/-- The map from the cone of a restricted map to its total cone.
Source: Stacks, Section 13.13. The component formulas and universal-property
identities below prove the assertion.
(blueprint: lem-trf-uniform-filtered-cone-grading). -/
def coneStep {K L : FilteredObject (CochainComplex C ℤ)}
    (f : K ⟶ L) (p : ℤ) :
    mappingCone (FilteredObject.restrictionSteps f p) ⟶ mappingCone f.hom :=
  mappingCone.map _ _ (K.filtration.F p).arrow (L.filtration.F p).arrow
    (restriction_arrow f p)

/-- Restrictions commute with successive step inclusions.
Source: Stacks, Section 13.13. The component formulas and universal-property
identities below prove the assertion.
(blueprint: lem-trf-uniform-filtered-cone-grading). -/
theorem restriction_next {K L : FilteredObject (CochainComplex C ℤ)}
    (f : K ⟶ L) {p q : ℤ} (hpq : p ≤ q) :
    Subobject.ofLE _ _ (K.filtration.antitone_step hpq) ≫
        FilteredObject.restrictionSteps f p =
      FilteredObject.restrictionSteps f q ≫
        Subobject.ofLE _ _ (L.filtration.antitone_step hpq) := by
  apply (cancel_mono (L.filtration.F p).arrow).1
  rw [Category.assoc, restriction_arrow, ← Category.assoc, Subobject.ofLE_arrow,
    Category.assoc, Subobject.ofLE_arrow, restriction_arrow]

/-- The actual direct-sum filtered mapping cone.
Source: Stacks, Section 13.13. The component formulas and universal-property
identities below prove the assertion.
(blueprint: lem-trf-uniform-filtered-cone-grading). -/
def filteredCone {K L : FilteredObject (CochainComplex C ℤ)} (f : K ⟶ L) :
    FilteredObject (CochainComplex C ℤ) where
  obj := mappingCone f.hom
  filtration :=
    { F := fun p ↦ Subobject.mk (coneStep f p)
      F_succ_le := fun p ↦ Subobject.mk_le_mk_of_comm
        (mappingCone.map _ _ (Subobject.ofLE _ _ (K.filtration.F_succ_le p))
          (Subobject.ofLE _ _ (L.filtration.F_succ_le p))
          (restriction_next f (p := p) (q := p + 1) (by omega)).symm) (by
            dsimp only [coneStep]
            rw [← mappingCone.map_comp]
            simp only [Subobject.ofLE_arrow]) }

/-- A common whole-object filtration step remains whole on the cone.
Source: Stacks, Section 13.13. The component formulas and universal-property
identities below prove the assertion.
(blueprint: lem-trf-uniform-filtered-cone-grading). -/
theorem filteredCone_top {K L : FilteredObject (CochainComplex C ℤ)}
    (f : K ⟶ L) (p : ℤ) (hK : K.filtration.F p = ⊤) (hL : L.filtration.F p = ⊤) :
    (filteredCone f).filtration.F p = ⊤ := by
  have : IsIso (K.filtration.F p).arrow := (Subobject.isIso_arrow_iff_eq_top _).2 hK
  have : IsIso (L.filtration.F p).arrow := (Subobject.isIso_arrow_iff_eq_top _).2 hL
  change Subobject.mk (coneStep f p) = ⊤
  dsimp only [coneStep]
  exact Subobject.mk_eq_top_of_isIso _

/-- A common zero filtration step remains zero on the cone.
Source: Stacks, Section 13.13. The component formulas and universal-property
identities below prove the assertion.
(blueprint: lem-trf-uniform-filtered-cone-grading). -/
theorem filteredCone_bot {K L : FilteredObject (CochainComplex C ℤ)}
    (f : K ⟶ L) (p : ℤ) (hK : K.filtration.F p = ⊥) (hL : L.filtration.F p = ⊥) :
    (filteredCone f).filtration.F p = ⊥ := by
  change Subobject.mk (coneStep f p) = ⊥
  apply Subobject.mk_eq_bot_iff_zero.2
  have hzK : (K.filtration.F p).arrow = 0 :=
    Subobject.mk_eq_bot_iff_zero.mp ((Subobject.mk_arrow _).trans hK)
  have hzL : (L.filtration.F p).arrow = 0 :=
    Subobject.mk_eq_bot_iff_zero.mp ((Subobject.mk_arrow _).trans hL)
  ext n
  apply mappingCone.ext_from _ (n + 1) n rfl <;>
    simp [coneStep, mappingCone.map, hzK, hzL]

/-- Common extrema of two finite filtration intervals bound the cone.
Source: Stacks, Section 13.13. The component formulas and universal-property
identities below prove the assertion.
(blueprint: lem-trf-uniform-filtered-cone-grading). -/
theorem filteredCone_finite {K L : FilteredObject (CochainComplex C ℤ)}
    (f : K ⟶ L) (hK : K.filtration.IsFinite) (hL : L.filtration.IsFinite) :
    (filteredCone f).filtration.IsFinite := by
  obtain ⟨a, b, ha, hb⟩ := hK
  obtain ⟨c, d, hc, hd⟩ := hL
  refine ⟨min a c, max b d, filteredCone_top f _ ?_ ?_, filteredCone_bot f _ ?_ ?_⟩
  · exact top_unique (ha ▸ K.filtration.antitone_step (min_le_left _ _))
  · exact top_unique (hc ▸ L.filtration.antitone_step (min_le_right _ _))
  · exact bot_unique (hb ▸ K.filtration.antitone_step (le_max_left _ _))
  · exact bot_unique (hd ▸ L.filtration.antitone_step (le_max_right _ _))

/-- A cone of bounded-below complexes is bounded below.
Source: Stacks, Section 13.13. The component formulas and universal-property
identities below prove the assertion.
(blueprint: lem-trf-uniform-filtered-cone-grading). -/
theorem cone_plus {K L : CochainComplex C ℤ} (f : K ⟶ L)
    (hK : CochainComplex.plus C K) (hL : CochainComplex.plus C L) :
    CochainComplex.plus C (mappingCone f) := by
  obtain ⟨a, ha⟩ := hK
  obtain ⟨b, hb⟩ := hL
  refine ⟨min (a - 1) b, ?_⟩
  rw [CochainComplex.isStrictlyGE_iff]
  intro n hn
  rw [mappingCone.isZero_X_iff]
  constructor
  · exact (CochainComplex.isStrictlyGE_iff K a).1 ha (n + 1) (by omega)
  · exact (CochainComplex.isStrictlyGE_iff L b).1 hb n (by omega)

/-- A cone of bounded-above complexes is bounded above.
Source: Stacks, Section 13.13. The component formulas and universal-property
identities below prove the assertion.
(blueprint: lem-trf-uniform-filtered-cone-grading). -/
theorem cone_minus {K L : CochainComplex C ℤ} (f : K ⟶ L)
    (hK : CochainComplex.minus C K) (hL : CochainComplex.minus C L) :
    CochainComplex.minus C (mappingCone f) := by
  obtain ⟨a, ha⟩ := hK
  obtain ⟨b, hb⟩ := hL
  refine ⟨max a b, ?_⟩
  rw [CochainComplex.isStrictlyLE_iff]
  intro n hn
  rw [mappingCone.isZero_X_iff]
  constructor
  · exact (CochainComplex.isStrictlyLE_iff K a).1 ha (n + 1) (by omega)
  · exact (CochainComplex.isStrictlyLE_iff L b).1 hb n (by omega)

/-- All four cochain conditions are stable under mapping cones.
Source: Stacks, Section 13.13. The component formulas and universal-property
identities below prove the assertion.
(blueprint: lem-trf-uniform-filtered-cone-grading). -/
theorem cone_condition {K L : CochainComplex C ℤ} (f : K ⟶ L)
    (P : ObjectProperty (CochainComplex C ℤ)) (hP : IsUniformCochainCondition P)
    (hK : P K) (hL : P L) : P (mappingCone f) := by
  rcases hP with rfl | rfl | rfl | rfl
  · trivial
  · exact cone_plus f hK hL
  · exact cone_minus f hK hL
  · exact ⟨cone_plus f hK.1 hL.1, cone_minus f hK.2 hL.2⟩

/-- Cones retain uniform finiteness, fixed endpoints and the cochain condition.
Source: Stacks, Section 13.13. The component formulas and universal-property
identities below prove the assertion.
(blueprint: lem-trf-uniform-filtered-cone-grading). -/
theorem filteredCone_property
    (B : Option (ℤ × ℤ)) (P : ObjectProperty (CochainComplex C ℤ))
    (hP : IsUniformCochainCondition P) {K L : UniformFilteredComplexes C B P} (f : K ⟶ L) :
    uniformFilteredProperty B P (filteredCone f.hom) := by
  refine ⟨filteredCone_finite f.hom K.property.1 L.property.1, ?_,
    cone_condition f.hom.hom P hP K.property.2.2 L.property.2.2⟩
  intro a b hab
  exact ⟨filteredCone_top f.hom _ (K.property.2.1 a b hab).1 (L.property.2.1 a b hab).1,
    filteredCone_bot f.hom _ (K.property.2.1 a b hab).2 (L.property.2.1 a b hab).2⟩

/-- The canonical map from a cone to the cone of the induced quotient map.
Source: Stacks, Section 13.13. The component formulas and universal-property
identities below prove the assertion.
(blueprint: lem-trf-uniform-filtered-cone-grading). -/
def coneQuotientMap {K L K' L' : CochainComplex C ℤ}
    (f : K ⟶ L) (g : K' ⟶ L') (a : K ⟶ K') (b : L ⟶ L')
    (h : f ≫ b = a ≫ g) :
    mappingCone g ⟶ mappingCone (cokernel.map a b f g h.symm) :=
  mappingCone.map _ _ (cokernel.π a) (cokernel.π b) (by simp [cokernel.map])

/-- The quotient cone map annihilates the preceding cone map.
Source: Stacks, Section 13.13. The component formulas and universal-property
identities below prove the assertion.
(blueprint: lem-trf-uniform-filtered-cone-grading). -/
theorem coneQuotientMap_zero {K L K' L' : CochainComplex C ℤ}
    (f : K ⟶ L) (g : K' ⟶ L') (a : K ⟶ K') (b : L ⟶ L')
    (h : f ≫ b = a ≫ g) :
    mappingCone.map f g a b h ≫ coneQuotientMap f g a b h = 0 := by
  rw [coneQuotientMap, ← mappingCone.map_comp]
  ext n
  apply mappingCone.ext_from _ (n + 1) n rfl <;> simp [mappingCone.map]

/-- The cone of a cokernel square is the cokernel of its cone map.
Source: Stacks, Section 13.13. The component formulas and universal-property
identities below prove the assertion.
(blueprint: lem-trf-uniform-filtered-cone-grading). -/
def coneQuotientMap_isCokernel
    {K L K' L' : CochainComplex C ℤ}
    (f : K ⟶ L) (g : K' ⟶ L') (a : K ⟶ K') (b : L ⟶ L')
    (h : f ≫ b = a ≫ g) :
    IsColimit (CokernelCofork.ofπ (coneQuotientMap f g a b h)
      (coneQuotientMap_zero f g a b h)) := by
  apply HomologicalComplex.isColimitOfEval
  intro n
  refine (isColimitMapCoconeCoforkEquiv' (HomologicalComplex.eval C (.up ℤ) n)
    (coneQuotientMap_zero f g a b h)).symm ?_
  let m := mappingCone.map f g a b h
  let q := coneQuotientMap f g a b h
  have hq : m.f n ≫ q.f n = 0 :=
    congrArg (fun t ↦ t.f n) (coneQuotientMap_zero f g a b h)
  have : Epi q := by dsimp only [q, coneQuotientMap]; infer_instance
  apply CokernelCofork.IsColimit.ofπ'
  intro Z l hl
  have hk : a.f (n + 1) ≫ (mappingCone.inl g).v (n + 1) n (by omega) ≫ l = 0 := by
    have he := congrArg ((mappingCone.inl f).v (n + 1) n (by omega) ≫ ·) hl
    simpa [m, mappingCone.map, Category.assoc] using he
  have hl' : b.f n ≫ (mappingCone.inr g).f n ≫ l = 0 := by
    have he := congrArg ((mappingCone.inr f).f n ≫ ·) hl
    simpa [m, mappingCone.map, Category.assoc] using he
  let α := CokernelCofork.IsColimit.desc'
    (isColimitOfHasCokernelOfPreservesColimit
      (HomologicalComplex.eval C (.up ℤ) (n + 1)) a)
    ((mappingCone.inl g).v (n + 1) n (by omega) ≫ l) hk
  let β := CokernelCofork.IsColimit.desc'
    (isColimitOfHasCokernelOfPreservesColimit
      (HomologicalComplex.eval C (.up ℤ) n) b)
    ((mappingCone.inr g).f n ≫ l) hl'
  let φ := cokernel.map a b f g h.symm
  refine ⟨(mappingCone.fst φ).1.v n (n + 1) rfl ≫ α.1 +
    (mappingCone.snd φ).v n n (add_zero n) ≫ β.1, ?_⟩
  apply mappingCone.ext_from g (n + 1) n rfl
  · simpa [q, φ, coneQuotientMap, mappingCone.map, Category.assoc] using α.2
  · simpa [q, φ, coneQuotientMap, mappingCone.map, Category.assoc] using β.2

/-- The map of cones induced by successive filtration step inclusions.
Source: Stacks, Section 13.13. The component formulas and universal-property
identities below prove the assertion.
(blueprint: lem-trf-uniform-filtered-cone-grading). -/
def coneNext {K L : FilteredObject (CochainComplex C ℤ)} (f : K ⟶ L) (p : ℤ) :
    mappingCone (FilteredObject.restrictionSteps f (p + 1)) ⟶
      mappingCone (FilteredObject.restrictionSteps f p) :=
  mappingCone.map _ _ (Subobject.ofLE _ _ (K.filtration.F_succ_le p))
    (Subobject.ofLE _ _ (L.filtration.F_succ_le p))
    (restriction_next f (p := p) (q := p + 1) (by omega)).symm

/-- Successive cone step maps commute with their total inclusions.
Source: Stacks, Section 13.13. The component formulas and universal-property
identities below prove the assertion.
(blueprint: lem-trf-uniform-filtered-cone-grading). -/
theorem coneNext_fac {K L : FilteredObject (CochainComplex C ℤ)}
    (f : K ⟶ L) (p : ℤ) : coneNext f p ≫ coneStep f p = coneStep f (p + 1) := by
  dsimp only [coneNext, coneStep]
  rw [← mappingCone.map_comp]
  simp only [Subobject.ofLE_arrow]

/-- The subobject representative of a cone step is its stepwise cone.
Source: Stacks, Section 13.13. The component formulas and universal-property
identities below prove the assertion.
(blueprint: lem-trf-uniform-filtered-cone-grading). -/
def coneStepIso {K L : FilteredObject (CochainComplex C ℤ)} (f : K ⟶ L) (p : ℤ) :
    ((filteredCone f).filtration.F p : CochainComplex C ℤ) ≅
      mappingCone (FilteredObject.restrictionSteps f p) :=
  Subobject.underlyingIso (coneStep f p)

/-- The cone step identifications intertwine successive inclusions.
Source: Stacks, Section 13.13. The component formulas and universal-property
identities below prove the assertion.
(blueprint: lem-trf-uniform-filtered-cone-grading). -/
theorem coneStepIso_next {K L : FilteredObject (CochainComplex C ℤ)}
    (f : K ⟶ L) (p : ℤ) :
    Subobject.ofLE _ _ ((filteredCone f).filtration.F_succ_le p) ≫
        (coneStepIso f p).hom = (coneStepIso f (p + 1)).hom ≫ coneNext f p := by
  apply (cancel_mono (coneStep f p)).1
  simp only [Category.assoc, coneStepIso, Subobject.underlyingIso_hom_comp_eq_mk,
    coneNext_fac]
  exact Subobject.ofLE_arrow _

/-- The canonical graded map is the induced map of step cokernels.
Source: Stacks, Section 13.13. The component formulas and universal-property
identities below prove the assertion.
(blueprint: lem-trf-uniform-filtered-cone-grading). -/
theorem graded_eq_cokernel_map
    {K L : FilteredObject (CochainComplex C ℤ)} (f : K ⟶ L) (p : ℤ) :
    cokernel.map (Subobject.ofLE _ _ (K.filtration.F_succ_le p))
        (Subobject.ofLE _ _ (L.filtration.F_succ_le p))
        (FilteredObject.restrictionSteps f (p + 1)) (FilteredObject.restrictionSteps f p)
        (restriction_next f (p := p) (q := p + 1) (by omega)) =
      FilteredObject.gradedMapSteps f p := by
  apply (cancel_epi (cokernel.π (Subobject.ofLE _ _ (K.filtration.F_succ_le p)))).1
  rw [cokernel.map, cokernel.π_desc]
  exact (Classical.choose_spec (FilteredObject.exists_gradedMap_steps K L f p)).symm

/-- The cokernel of successive step cones is the cone of the graded map.
Source: Stacks, Section 13.13. The component formulas and universal-property
identities below prove the assertion.
(blueprint: lem-trf-uniform-filtered-cone-grading). -/
def coneCokernelIso {K L : FilteredObject (CochainComplex C ℤ)}
    (f : K ⟶ L) (p : ℤ) :
    cokernel (coneNext f p) ≅ mappingCone (FilteredObject.gradedMapSteps f p) := by
  let e : cokernel (coneNext f p) ≅
      mappingCone (cokernel.map (Subobject.ofLE _ _ (K.filtration.F_succ_le p))
        (Subobject.ofLE _ _ (L.filtration.F_succ_le p))
        (FilteredObject.restrictionSteps f (p + 1)) (FilteredObject.restrictionSteps f p)
        (restriction_next f (p := p) (q := p + 1) (by omega))) :=
    colimit.isoColimitCocone ⟨_, coneQuotientMap_isCokernel
      (FilteredObject.restrictionSteps f (p + 1)) (FilteredObject.restrictionSteps f p)
      (Subobject.ofLE _ _ (K.filtration.F_succ_le p))
      (Subobject.ofLE _ _ (L.filtration.F_succ_le p))
      (restriction_next f (p := p) (q := p + 1) (by omega)).symm⟩
  exact e ≪≫ eqToIso (congrArg (fun φ ↦ mappingCone φ) (graded_eq_cokernel_map f p))

/-- Grading the actual filtered cone gives the cone of the canonical graded map.
Source: Stacks, Section 13.13. The component formulas and universal-property
identities below prove the assertion.
(blueprint: lem-trf-uniform-filtered-cone-grading). -/
def filteredCone_gradeIso {K L : FilteredObject (CochainComplex C ℤ)}
    (f : K ⟶ L) (p : ℤ) :
    ((filteredCone f).filtration.gr p) ≅ mappingCone (FilteredObject.gradedMapSteps f p) :=
  cokernel.mapIso _ _ (coneStepIso f (p + 1)) (coneStepIso f p)
    (coneStepIso_next f p) ≪≫ coneCokernelIso f p

/-- The cone inclusion is a filtration-preserving chain map.
Source: Stacks, Section 13.13. The component formulas and universal-property
identities below prove the assertion.
(blueprint: lem-trf-uniform-filtered-cone-grading). -/
def filteredCone_inr {K L : FilteredObject (CochainComplex C ℤ)} (f : K ⟶ L) :
    L ⟶ filteredCone f :=
  ⟨mappingCone.inr f.hom, fun p ↦
    ⟨mappingCone.inr (FilteredObject.restrictionSteps f p) ≫ (coneStepIso f p).inv, by
      change _ ≫ (Subobject.mk (coneStep f p)).arrow = _
      dsimp only [coneStepIso]
      rw [Category.assoc, Subobject.underlyingIso_arrow]
      ext n
      simp [coneStep, mappingCone.map]⟩⟩

/-- Restricting the cone inclusion gives the stepwise cone inclusion.
Source: Stacks, Section 13.13. The component formulas and universal-property
identities below prove the assertion.
(blueprint: lem-trf-uniform-filtered-cone-grading). -/
theorem filteredCone_inr_restriction
    {K L : FilteredObject (CochainComplex C ℤ)} (f : K ⟶ L) (p : ℤ) :
    FilteredObject.restrictionSteps (filteredCone_inr f) p ≫ (coneStepIso f p).hom =
      mappingCone.inr (FilteredObject.restrictionSteps f p) := by
  apply (cancel_mono (coneStep f p)).1
  rw [Category.assoc, coneStepIso, Subobject.underlyingIso_hom_comp_eq_mk]
  change FilteredObject.restrictionSteps (filteredCone_inr f) p ≫
    ((filteredCone f).filtration.F p).arrow = _
  rw [restriction_arrow]
  ext n
  simp [coneStep, mappingCone.map, filteredCone_inr]

/-- The cone comparison intertwines the canonical cokernel projection.
Source: Stacks, Section 13.13. The component formulas and universal-property
identities below prove the assertion.
(blueprint: lem-trf-uniform-filtered-cone-grading). -/
theorem coneCokernelIso_fac
    {K L : FilteredObject (CochainComplex C ℤ)} (f : K ⟶ L) (p : ℤ) :
    cokernel.π (coneNext f p) ≫ (coneCokernelIso f p).hom =
      coneQuotientMap (FilteredObject.restrictionSteps f (p + 1))
        (FilteredObject.restrictionSteps f p)
        (Subobject.ofLE _ _ (K.filtration.F_succ_le p))
        (Subobject.ofLE _ _ (L.filtration.F_succ_le p))
        (restriction_next f (p := p) (q := p + 1) (by omega)).symm ≫
          (eqToIso (congrArg (fun φ ↦ mappingCone φ) (graded_eq_cokernel_map f p))).hom := by
  unfold coneCokernelIso
  simp only [Iso.trans_hom, ← Category.assoc]
  congr 1
  exact colimit.isoColimitCocone_ι_hom _ WalkingParallelPair.one

/-- Transport along equality of arrows preserves the cone inclusion.
Source: Stacks, Section 13.13. The component formulas and universal-property
identities below prove the assertion.
(blueprint: lem-trf-uniform-filtered-cone-grading). -/
theorem mappingCone_inr_eqToIso {K L : CochainComplex C ℤ} (f g : K ⟶ L)
    (h : f = g) : mappingCone.inr f ≫ (eqToIso (congrArg (fun φ ↦ mappingCone φ) h)).hom =
      mappingCone.inr g := by
  subst h
  simp

/-- The graded cone comparison intertwines its step projection.
Source: Stacks, Section 13.13. The component formulas and universal-property
identities below prove the assertion.
(blueprint: lem-trf-uniform-filtered-cone-grading). -/
theorem filteredCone_gradeIso_fac
    {K L : FilteredObject (CochainComplex C ℤ)} (f : K ⟶ L) (p : ℤ) :
    cokernel.π (Subobject.ofLE _ _ ((filteredCone f).filtration.F_succ_le p)) ≫
        (filteredCone_gradeIso f p).hom =
      (coneStepIso f p).hom ≫ cokernel.π (coneNext f p) ≫ (coneCokernelIso f p).hom := by
  simp only [filteredCone_gradeIso, Iso.trans_hom, cokernel.mapIso_hom, cokernel.map,
    cokernel.π_desc_assoc, Category.assoc]

/-- The graded cone comparison takes the graded inclusion to the cone inclusion.
Source: Stacks, Section 13.13. The component formulas and universal-property
identities below prove the assertion.
(blueprint: lem-trf-uniform-filtered-cone-grading). -/
theorem filteredCone_inr_graded
    {K L : FilteredObject (CochainComplex C ℤ)} (f : K ⟶ L) (p : ℤ) :
    FilteredObject.gradedMapSteps (filteredCone_inr f) p ≫ (filteredCone_gradeIso f p).hom =
      mappingCone.inr (FilteredObject.gradedMapSteps f p) := by
  apply (cancel_epi (cokernel.π (Subobject.ofLE _ _ (L.filtration.F_succ_le p)))).1
  have hπ : cokernel.π (Subobject.ofLE _ _ (L.filtration.F_succ_le p)) ≫
      FilteredObject.gradedMapSteps (filteredCone_inr f) p =
    FilteredObject.restrictionSteps (filteredCone_inr f) p ≫
      cokernel.π (Subobject.ofLE _ _ ((filteredCone f).filtration.F_succ_le p)) :=
    Classical.choose_spec (FilteredObject.exists_gradedMap_steps _ _ (filteredCone_inr f) p)
  rw [← Category.assoc, hπ,
    Category.assoc, filteredCone_gradeIso_fac, ← Category.assoc,
    filteredCone_inr_restriction, coneCokernelIso_fac]
  rw [← Category.assoc]
  have he : mappingCone.inr (FilteredObject.restrictionSteps f p) ≫
      coneQuotientMap (FilteredObject.restrictionSteps f (p + 1))
        (FilteredObject.restrictionSteps f p)
        (Subobject.ofLE _ _ (K.filtration.F_succ_le p))
        (Subobject.ofLE _ _ (L.filtration.F_succ_le p))
        (restriction_next f (p := p) (q := p + 1) (by omega)).symm =
      cokernel.π (Subobject.ofLE _ _ (L.filtration.F_succ_le p)) ≫
        mappingCone.inr (cokernel.map (Subobject.ofLE _ _ (K.filtration.F_succ_le p))
          (Subobject.ofLE _ _ (L.filtration.F_succ_le p))
          (FilteredObject.restrictionSteps f (p + 1)) (FilteredObject.restrictionSteps f p)
          (restriction_next f (p := p) (q := p + 1) (by omega))) := by
    ext n
    simp [coneQuotientMap, mappingCone.map]
  rw [he, Category.assoc, mappingCone_inr_eqToIso]
  exact graded_eq_cokernel_map f p

/-- The cone inclusion is a quasi-isomorphism if its source cone arrow has acyclic domain.
Source: Stacks, Section 13.6, cone triangle criterion.
(blueprint: lem-trf-uniform-filtered-cone-grading). -/
theorem cone_inr_quasiIso {K L : CochainComplex C ℤ} (f : K ⟶ L) (hK : K.Acyclic) :
    QuasiIso (mappingCone.inr f) := by
  rw [← HomologicalComplex.mem_quasiIso_iff,
    ← HomotopyCategory.quotient_map_mem_quasiIso_iff,
    HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
  exact ObjectProperty.trW.mk' (HomotopyCategory.subcategoryAcyclic C)
    (HomotopyCategory.mappingCone_triangleh_distinguished f)
    ((HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic K).2 hK)

/-- The filtered cone of a graded quasi-isomorphism is acyclic in every grade.
Source: Stacks, Section 13.13. Apply the canonical cone grading isomorphism and
ordinary cone criterion grade by grade.
(blueprint: lem-trf-uniform-filtered-cone-grading). -/
theorem filteredCone_acyclic {K L : FilteredObject (CochainComplex C ℤ)}
    (f : K ⟶ L) (hf : ∀ p : ℤ, QuasiIso (FilteredObject.gradedMapSteps f p)) :
    ∀ p : ℤ, ((filteredCone f).filtration.gr p).Acyclic := by
  intro p n
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  have hzero := (HomologicalComplex.exactAt_iff_isZero_homology _ _).1
    (((mappingCone.quasiIso_iff_acyclic (FilteredObject.gradedMapSteps f p)).1 (hf p)) n)
  exact hzero.of_iso
    ((HomologicalComplex.homologyFunctor C (.up ℤ) n).mapIso (filteredCone_gradeIso f p))

/-- The filtered cone inclusion is a graded quasi-isomorphism for a graded-acyclic domain.
Source: Stacks, Section 13.13. Its graded map is the ordinary cone inclusion,
up to the proved canonical comparison isomorphism.
(blueprint: lem-trf-uniform-filtered-cone-grading). -/
theorem filteredCone_inr_quasiIso {K L : FilteredObject (CochainComplex C ℤ)}
    (f : K ⟶ L) (hK : ∀ p : ℤ, (K.filtration.gr p).Acyclic) :
    ∀ p : ℤ, QuasiIso (FilteredObject.gradedMapSteps (filteredCone_inr f) p) := by
  intro p
  have : QuasiIso (mappingCone.inr (FilteredObject.gradedMapSteps f p)) :=
    cone_inr_quasiIso _ (hK p)
  have : QuasiIso (FilteredObject.gradedMapSteps (filteredCone_inr f) p ≫
      (filteredCone_gradeIso f p).hom) := by
    rw [filteredCone_inr_graded]
    infer_instance
  exact quasiIso_of_comp_right _ (filteredCone_gradeIso f p).hom

/-- The standard null-homotopy of the composite into a cone.
Source: Stacks, cone construction; the cochain is the left inclusion.
(blueprint: lem-trf-uniform-filtered-cone-grading). -/
def coneNullHomotopy {K L : CochainComplex C ℤ} (f : K ⟶ L) :
    Homotopy (f ≫ mappingCone.inr f) 0 :=
  (Cochain.equivHomotopy _ _).symm ⟨mappingCone.inl f, by simp⟩

/-- The standard cone null-homotopy is compatible with every commutative square.
Source: Stacks, cone construction. In the relevant degree its component is inl;
otherwise both components vanish. The cone map formula gives the identity.
(blueprint: lem-trf-uniform-filtered-cone-grading). -/
theorem coneNullHomotopy_naturality {K L K' L' : CochainComplex C ℤ}
    (f : K ⟶ L) (g : K' ⟶ L') (a : K ⟶ K') (b : L ⟶ L')
    (h : f ≫ b = a ≫ g) (n m : ℤ) :
    a.f n ≫ (coneNullHomotopy g).hom n m =
      (coneNullHomotopy f).hom n m ≫ (mappingCone.map f g a b h).f m := by
  by_cases hnm : n + (-1) = m
  · simp [coneNullHomotopy, Cochain.equivHomotopy, hnm, mappingCone.map]
  · simp [coneNullHomotopy, Cochain.equivHomotopy, hnm]

/-- The standard cone null-homotopy preserves every filtration step.
Source: Stacks, Section 13.13. Lift its stepwise component through the canonical
step-cone isomorphism; naturality supplies the required factorization.
(blueprint: lem-trf-uniform-filtered-cone-grading). -/
theorem filteredCone_nullHomotopy
    {K L : FilteredObject (CochainComplex C ℤ)} (f : K ⟶ L) :
    UniformFilteredHomotopy (f ≫ filteredCone_inr f) 0 := by
  refine ⟨coneNullHomotopy f.hom, ?_⟩
  intro p n m
  refine ⟨(coneNullHomotopy (FilteredObject.restrictionSteps f p)).hom n m ≫
    (coneStepIso f p).inv.f m, ?_⟩
  dsimp only [coneStepIso]
  change _ ≫ (Subobject.mk (coneStep f p)).arrow.f m = _
  rw [Category.assoc, ← HomologicalComplex.comp_f, Subobject.underlyingIso_arrow]
  exact (coneNullHomotopy_naturality _ _ _ _ (restriction_arrow f p) n m).symm

end UniformFilteredCone

end CategoryTheory
