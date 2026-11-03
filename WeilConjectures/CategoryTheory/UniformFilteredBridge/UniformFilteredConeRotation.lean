/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.UniformFilteredFiber.UniformFilteredFiber
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
/-! # Filtered cone rotation maps

Source: Stacks Project, Derived Categories, Sections 13.9 and 13.13, and the
cone multiplicative-system proof in Tag 05RG.

For q:fiber(f)→K, the inverse rotation map J:L→Cone(q) is the cone lift of
minus the shifted inclusion of L. The shifted left inclusion gamma satisfies
gamma q=id and delta(gamma)=-f alpha; hence -gamma inl(q) is the homotopy
between f J and inclusion(q).

For i:L→Cone(f), let beta be the shifted second cone cochain for i.
Its differential is -projection(i) i. The cocycle -beta fst(f) defines
v:fiber(i)→K, and beta snd(f) supplies v f homotopic to projection(i).
The projection equations show naturality with every square. Canonical fiber
and cone step comparisons then give actual filtered maps and homotopies.
(blueprint: lem-trf-uniform-filtered-cone-rotation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe v u
namespace CategoryTheory
open Limits CochainComplex CochainComplex.HomComplex UniformFilteredFiber
variable {C : Type u} [Category.{v} C] [Abelian C]
namespace UniformFilteredBridge
/-- The shifted left inclusion is a degree-zero cochain into the fiber.
Source: Stacks, Sections 13.9 and 13.13; its component identity is proved below.
(blueprint: lem-trf-uniform-filtered-cone-rotation). -/
def fiberLeftCochain {K L : CochainComplex C ℤ} (f : K ⟶ L) :
    Cochain K ((mappingCone f)⟦(-1 : ℤ)⟧) 0 :=
  (mappingCone.inl f).rightShift (-1) 0 (by omega)

/-- The shifted left inclusion is a degreewise section of the fiber projection.
Source: Stacks, Sections 13.9 and 13.13; its component identity is proved below.
(blueprint: lem-trf-uniform-filtered-cone-rotation). -/
theorem fiberLeftCochain_projection {K L : CochainComplex C ℤ} (f : K ⟶ L) :
    (fiberLeftCochain f).comp (Cochain.ofHom (fiberProjection f)) (zero_add 0) =
      Cochain.ofHom (𝟙 K) := by
  ext n
  simpa only [Cochain.comp_zero_cochain_v, Cochain.ofHom_v, HomologicalComplex.id_f,
    fiberLeftCochain, fiberProjection, mappingCocone.inl, mappingCocone.fst] using
    mappingCocone.inl_v_fst_f f n

/-- The inverse rotation map from L to the cone of the fiber projection.
Source: Stacks, Sections 13.9 and 13.13; its component identity is proved below.
(blueprint: lem-trf-uniform-filtered-cone-rotation). -/
def inverseRotateInclusion {K L : CochainComplex C ℤ} (f : K ⟶ L) :
    L ⟶ mappingCone (fiberProjection f) :=
  mappingCone.lift (fiberProjection f)
    (-((Cocycle.ofHom (mappingCone.inr f)).rightShift (-1) 1 (by omega))) 0 (by
      change δ 0 1 (0 : Cochain L K 0) +
        (-mappingCocone.inr f).1.comp (Cochain.ofHom (mappingCocone.fst f))
          (add_zero 1) = 0
      simp only [δ_zero, zero_add, Cocycle.coe_neg, Cochain.neg_comp, neg_eq_zero]
      ext n q hnq
      simpa only [Cochain.comp_zero_cochain_v, Cochain.zero_v, Cochain.ofHom,
        Cochain.ofHoms, Cochain.mk_v, eqToHom_refl, Category.comp_id] using
        mappingCocone.inr_v_fst_f f n q hnq)

/-- The differential of the shifted left inclusion is minus f times the shifted inclusion.
Source: Stacks, Sections 13.9 and 13.13; its component identity is proved below.
(blueprint: lem-trf-uniform-filtered-cone-rotation). -/
theorem fiberLeftCochain_differential {K L : CochainComplex C ℤ} (f : K ⟶ L) :
    δ 0 1 (fiberLeftCochain f) =
      -(Cochain.ofHom f).comp
        ((Cocycle.ofHom (mappingCone.inr f)).rightShift (-1) 1 (by omega)).1 (zero_add 1) := by
  dsimp only [fiberLeftCochain]
  rw [Cochain.δ_rightShift _ (-1) 0 1 (by omega) 0 (by omega), mappingCone.δ_inl]
  ext n
  simp [Cochain.rightShift, Cochain.zero_cochain_comp_v, Cocycle.rightShift,
    Category.assoc, Cochain.ofHom, Cochain.ofHoms, Cochain.mk_v,
    eqToHom_refl, Category.comp_id]

/-- The inverse rotation map commutes with f up to the canonical homotopy.
Source: Stacks, Sections 13.9 and 13.13; its component identity is proved below.
(blueprint: lem-trf-uniform-filtered-cone-rotation). -/
def inverseRotateHomotopy {K L : CochainComplex C ℤ} (f : K ⟶ L) :
    Homotopy (f ≫ inverseRotateInclusion f) (mappingCone.inr (fiberProjection f)) :=
  (Cochain.equivHomotopy _ _).symm
    ⟨-(fiberLeftCochain f).comp (mappingCone.inl (fiberProjection f)) (zero_add (-1)), by
      simp only [Cochain.ofHom_comp, inverseRotateInclusion, mappingCone.ofHom_lift,
        mappingCone.liftCochain, Cochain.zero_comp, add_zero,
        δ_neg, δ_zero_cochain_comp (fiberLeftCochain f)
          (mappingCone.inl (fiberProjection f)) 0 (by omega), mappingCone.δ_inl,
        fiberLeftCochain_differential, Cochain.neg_comp, Cochain.comp_neg,
        Int.negOnePow_neg, Int.negOnePow_one, Units.neg_smul, one_smul, neg_neg,
        Cocycle.coe_neg]
      rw [← Cochain.comp_assoc_of_second_is_zero_cochain]
      simp only [fiberLeftCochain_projection, Cochain.id_comp,
        Cochain.comp_assoc_of_first_is_zero_cochain]
      abel⟩


/-- The inverse rotation map commutes with every commutative square.
Source: Stacks, Sections 13.9 and 13.13; its component identity is proved below.
(blueprint: lem-trf-uniform-filtered-cone-rotation). -/
theorem inverseRotateInclusion_naturality {K L K' L' : CochainComplex C ℤ}
    (f : K ⟶ L) (g : K' ⟶ L') (a : K ⟶ K') (b : L ⟶ L')
    (h : f ≫ b = a ≫ g) :
    b ≫ inverseRotateInclusion g = inverseRotateInclusion f ≫
      mappingCone.map (fiberProjection f) (fiberProjection g)
        ((mappingCone.map f g a b h)⟦(-1 : ℤ)⟧') a
        (fiberProjection_naturality f g a b h).symm := by
  ext n
  simp only [HomologicalComplex.comp_f]
  apply mappingCone.ext_to (fiberProjection g) n (n + 1) rfl
  · simp only [Category.assoc, inverseRotateInclusion, mappingCone.lift_f_fst_v,
      UniformFilteredCone.coneMap_fst]
    rw [← Category.assoc, mappingCone.lift_f_fst_v]
    have hv {M N : CochainComplex C ℤ} (k : M ⟶ N) :
        ((Cocycle.ofHom (mappingCone.inr k)).rightShift (-1) 1 (by omega)).1.v
          n (n + 1) rfl = (mappingCone.inr k).f n ≫
            ((mappingCone k).shiftFunctorObjXIso (-1) (n + 1) n (by omega)).inv := by
      rw [Cocycle.rightShift_coe,
        Cochain.rightShift_v _ (-1) 1 (by omega) n (n + 1) rfl n (by omega),
        Cocycle.ofHom_coe, Cochain.ofHom_v]
    simp only [Cocycle.coe_neg, Cochain.neg_v, Preadditive.comp_neg,
      Preadditive.neg_comp, neg_inj, hv, shiftFunctor_map_f']
    have hi : (mappingCone.inr f).f n ≫ (mappingCone.map f g a b h).f n =
        b.f n ≫ (mappingCone.inr g).f n := by simp [mappingCone.map]
    rw [← Category.assoc, ← hi, Category.assoc]
    dsimp only [shiftFunctorObjXIso]
    rw [HomologicalComplex.XIsoOfEq_inv_naturality, ← Category.assoc]
  · simp [Category.assoc, inverseRotateInclusion, UniformFilteredCone.coneMap_snd]

/-- The inverse rotation homotopy commutes with every commutative square.
Source: Stacks, Sections 13.9 and 13.13; its component identity is proved below.
(blueprint: lem-trf-uniform-filtered-cone-rotation). -/
theorem inverseRotateHomotopy_naturality {K L K' L' : CochainComplex C ℤ}
    (f : K ⟶ L) (g : K' ⟶ L') (a : K ⟶ K') (b : L ⟶ L')
    (h : f ≫ b = a ≫ g) (n m : ℤ) :
    a.f n ≫ (inverseRotateHomotopy g).hom n m =
      (inverseRotateHomotopy f).hom n m ≫
        (mappingCone.map (fiberProjection f) (fiberProjection g)
          ((mappingCone.map f g a b h)⟦(-1 : ℤ)⟧') a
          (fiberProjection_naturality f g a b h).symm).f m := by
  by_cases hnm : n + (-1) = m
  · subst m
    simp [inverseRotateHomotopy, fiberLeftCochain, Cochain.equivHomotopy,
      Cochain.rightShift, mappingCone.map]
  · have hrel : ¬ (ComplexShape.up ℤ).Rel m n := by
      simp only [ComplexShape.up_Rel]
      omega
    rw [Homotopy.zero _ _ _ hrel, Homotopy.zero _ _ _ hrel]
    simp

/-- Transport the cone of a stepwise fiber projection to the cone of the actual restriction.
Source: Stacks, Sections 13.9 and 13.13; its component identity is proved below.
(blueprint: lem-trf-uniform-filtered-cone-rotation). -/
def coneFiberStepMap {K L : FilteredObject (CochainComplex C ℤ)}
    (f : K ⟶ L) (p : ℤ) :
    mappingCone (fiberProjection (FilteredObject.restrictionSteps f p)) ⟶
      mappingCone (FilteredObject.restrictionSteps (filteredFiberProjection f) p) :=
  mappingCone.map _ _ (fiberStepIso f p).inv (𝟙 _) (by
    rw [Category.comp_id]
    apply (cancel_epi (fiberStepIso f p).hom).1
    rw [Iso.hom_inv_id_assoc]
    exact (filteredFiberProjection_restriction f p).symm)

/-- The transported cone map factors the actual cone-step inclusion.
Source: Stacks, Sections 13.9 and 13.13; its component identity is proved below.
(blueprint: lem-trf-uniform-filtered-cone-rotation). -/
theorem coneFiberStepMap_fac {K L : FilteredObject (CochainComplex C ℤ)}
    (f : K ⟶ L) (p : ℤ) :
    coneFiberStepMap f p ≫ UniformFilteredCone.coneStep (filteredFiberProjection f) p =
      mappingCone.map (fiberProjection (FilteredObject.restrictionSteps f p))
        (fiberProjection f.hom)
        ((UniformFilteredCone.coneStep f p)⟦(-1 : ℤ)⟧') (K.filtration.F p).arrow
        (fiberProjection_naturality _ _ _ _
          (UniformFilteredCone.restriction_arrow f p)).symm := by
  dsimp only [coneFiberStepMap, UniformFilteredCone.coneStep]
  rw [← mappingCone.map_comp]
  congr 1
  · exact fiberStepIso_inv_fac f p
  · exact Category.id_comp _

/-- The inverse rotation map preserves every actual filtration step.
Source: Stacks, Sections 13.9 and 13.13; its component identity is proved below.
(blueprint: lem-trf-uniform-filtered-cone-rotation). -/
def filteredInverseRotateInclusion {K L : FilteredObject (CochainComplex C ℤ)}
    (f : K ⟶ L) : L ⟶ UniformFilteredCone.filteredCone (filteredFiberProjection f) :=
  ⟨inverseRotateInclusion f.hom, fun p ↦
    ⟨inverseRotateInclusion (FilteredObject.restrictionSteps f p) ≫
      coneFiberStepMap f p ≫
        (UniformFilteredCone.coneStepIso (filteredFiberProjection f) p).inv, by
      dsimp only [UniformFilteredCone.coneStepIso]
      change _ ≫ (Subobject.mk
        (UniformFilteredCone.coneStep (filteredFiberProjection f) p)).arrow = _
      rw [Category.assoc, Category.assoc, Subobject.underlyingIso_arrow,
        coneFiberStepMap_fac]
      exact (inverseRotateInclusion_naturality _ _ _ _
        (UniformFilteredCone.restriction_arrow f p)).symm⟩⟩

/-- The inverse rotation homotopy preserves every actual filtration step.
Source: Stacks, Sections 13.9 and 13.13; its component identity is proved below.
(blueprint: lem-trf-uniform-filtered-cone-rotation). -/
theorem filteredInverseRotateHomotopy {K L : FilteredObject (CochainComplex C ℤ)}
    (f : K ⟶ L) : UniformFilteredHomotopy (f ≫ filteredInverseRotateInclusion f)
      (UniformFilteredCone.filteredCone_inr (filteredFiberProjection f)) := by
  refine ⟨inverseRotateHomotopy f.hom, ?_⟩
  intro p n m
  refine ⟨(inverseRotateHomotopy (FilteredObject.restrictionSteps f p)).hom n m ≫
    (coneFiberStepMap f p).f m ≫
      (UniformFilteredCone.coneStepIso (filteredFiberProjection f) p).inv.f m, ?_⟩
  dsimp only [UniformFilteredCone.coneStepIso]
  change _ ≫ (Subobject.mk
    (UniformFilteredCone.coneStep (filteredFiberProjection f) p)).arrow.f m = _
  rw [Category.assoc, Category.assoc, ← HomologicalComplex.comp_f,
    Subobject.underlyingIso_arrow, ← HomologicalComplex.comp_f, coneFiberStepMap_fac]
  exact (inverseRotateHomotopy_naturality _ _ _ _
    (UniformFilteredCone.restriction_arrow f p) n m).symm

/-- The shifted second cone projection, a degree-minus-one cochain.
Source: Stacks, Sections 13.9 and 13.13; its component identity is proved below.
(blueprint: lem-trf-uniform-filtered-cone-rotation). -/
def fiberSecondCochain {K L : CochainComplex C ℤ} (f : K ⟶ L) :
    Cochain ((mappingCone f)⟦(-1 : ℤ)⟧) L (-1) :=
  (mappingCone.snd f).leftShift (-1) (-1) (by omega)

/-- The shifted second projection differentiates to minus the projection followed by f.
Source: Stacks, Sections 13.9 and 13.13; its component identity is proved below.
(blueprint: lem-trf-uniform-filtered-cone-rotation). -/
theorem fiberSecondCochain_differential {K L : CochainComplex C ℤ} (f : K ⟶ L) :
    δ (-1) 0 (fiberSecondCochain f) = -Cochain.ofHom (fiberProjection f ≫ f) := by
  have hf := δ_ofHomotopy (fiberNullHomotopy f)
  have he : Cochain.ofHomotopy (fiberNullHomotopy f) = -fiberSecondCochain f := by
    ext n m h
    simp [fiberNullHomotopy, Cochain.equivHomotopy, Cochain.ofHomotopy,
      fiberSecondCochain, h]
  rw [he, δ_neg, Cochain.ofHom_zero, sub_zero] at hf
  exact (neg_eq_iff_eq_neg).mp hf

/-- The ordinary rotation projection from the fiber of the cone inclusion to K.
Source: Stacks, Sections 13.9 and 13.13; its component identity is proved below.
(blueprint: lem-trf-uniform-filtered-cone-rotation). -/
def rotateProjection {K L : CochainComplex C ℤ} (f : K ⟶ L) :
    (mappingCone (mappingCone.inr f))⟦(-1 : ℤ)⟧ ⟶ K :=
  Cocycle.homOf ⟨-(fiberSecondCochain (mappingCone.inr f)).comp
    (mappingCone.fst f).1 (by omega), by
      rw [Cocycle.mem_iff _ 1 rfl, δ_neg,
        δ_comp _ _ (show (-1 : ℤ) + 1 = 0 by omega)
          0 2 1 (by omega) (by omega) (by omega)]
      simp only [Cocycle.δ_eq_zero, Cochain.comp_zero, fiberSecondCochain_differential,
        Int.negOnePow_one, Units.neg_smul, one_smul, zero_add, neg_neg,
        Cochain.neg_comp, neg_eq_zero, Cochain.ofHom_comp]
      rw [Cochain.comp_assoc_of_first_is_zero_cochain]
      have hz : (Cochain.ofHom (mappingCone.inr f)).comp (mappingCone.fst f).1
          (zero_add 1) = 0 := by
        ext n m h
        simpa only [Cochain.zero_cochain_comp_v, Cochain.ofHom, Cochain.ofHoms,
          Cochain.mk_v, eqToHom_refl, Category.comp_id, Cochain.zero_v] using
          mappingCone.inr_f_fst_v f n m h
      rw [hz, Cochain.comp_zero]⟩

/-- The ordinary rotation projection commutes with f up to the canonical homotopy.
Source: Stacks, Sections 13.9 and 13.13; its component identity is proved below.
(blueprint: lem-trf-uniform-filtered-cone-rotation). -/
def rotateProjectionHomotopy {K L : CochainComplex C ℤ} (f : K ⟶ L) :
    Homotopy (rotateProjection f ≫ f) (fiberProjection (mappingCone.inr f)) :=
  (Cochain.equivHomotopy _ _).symm
    ⟨(fiberSecondCochain (mappingCone.inr f)).comp (mappingCone.snd f) (add_zero (-1)), by
      simp only [Cochain.ofHom_comp, rotateProjection,
        Cocycle.cochain_ofHom_homOf_eq_coe, Cochain.neg_comp,
        δ_comp_zero_cochain (fiberSecondCochain (mappingCone.inr f))
          (mappingCone.snd f) 0 (by omega), mappingCone.δ_snd,
        fiberSecondCochain_differential, Cochain.comp_neg, Cochain.ofHom_comp,
        Cochain.neg_comp,
        Cochain.comp_assoc_of_first_is_zero_cochain,
        Cochain.comp_assoc_of_third_is_zero_cochain]
      have hz : (Cochain.ofHom (mappingCone.inr f)).comp (mappingCone.snd f)
          (zero_add 0) = Cochain.ofHom (𝟙 L) := by
        ext n
        simp
      rw [hz, Cochain.comp_id]
      abel⟩

/-- The shifted second projection commutes with every commutative square.
Source: Stacks, Sections 13.9 and 13.13; its component identity is proved below.
(blueprint: lem-trf-uniform-filtered-cone-rotation). -/
theorem fiberSecondCochain_naturality {K L K' L' : CochainComplex C ℤ}
    (f : K ⟶ L) (g : K' ⟶ L') (a : K ⟶ K') (b : L ⟶ L')
    (h : f ≫ b = a ≫ g) (n m : ℤ) (hnm : n + (-1) = m) :
    ((mappingCone.map f g a b h)⟦(-1 : ℤ)⟧').f n ≫
      (fiberSecondCochain g).v n m hnm =
        (fiberSecondCochain f).v n m hnm ≫ b.f m := by
  subst m
  simp only [fiberSecondCochain, Cochain.leftShift, Cochain.mk_v,
    shiftFunctor_map_f', shiftFunctor_obj_X', shiftFunctorObjXIso,
    HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, Int.reduceNeg, Int.reduceMul,
    Int.reduceSub, Int.reduceDiv, Int.reduceAdd, Int.negOnePow_even 2 ⟨1, rfl⟩,
    one_smul]
  change (mappingCone.map f g a b h).f (n + -1) ≫
      (𝟙 ((mappingCone g).X (n + -1))) ≫
        (mappingCone.snd g).v (n + -1) (n + -1) (add_zero _) =
    ((𝟙 ((mappingCone f).X (n + -1))) ≫
      (mappingCone.snd f).v (n + -1) (n + -1) (add_zero _)) ≫ b.f (n + -1)
  rw [Category.id_comp, Category.id_comp]
  exact UniformFilteredCone.coneMap_snd f g a b h (n + -1)

/-- The rotation projection is minus the composite of the two ordinary projections.
Source: Stacks, Sections 13.9 and 13.13; its component identity is proved below.
(blueprint: lem-trf-uniform-filtered-cone-rotation). -/
theorem rotateProjection_f {K L : CochainComplex C ℤ} (f : K ⟶ L) (n : ℤ) :
    (rotateProjection f).f n =
      -((fiberSecondCochain (mappingCone.inr f)).v n (n + -1) (by omega) ≫
        (mappingCone.fst f).1.v (n + -1) n (by omega)) := by
  simp only [rotateProjection, Cocycle.homOf_f, Cochain.neg_v]
  rw [Cochain.comp_v _ _ _ n (n + -1) n (by omega) (by omega)]

/-- The rotation homotopy is the composite of the second cone projections.
Source: Stacks, Sections 13.9 and 13.13; its component identity is proved below.
(blueprint: lem-trf-uniform-filtered-cone-rotation). -/
theorem rotateProjectionHomotopy_hom {K L : CochainComplex C ℤ}
    (f : K ⟶ L) (n m : ℤ) (hnm : n + (-1) = m) :
    (rotateProjectionHomotopy f).hom n m =
      (fiberSecondCochain (mappingCone.inr f)).v n m hnm ≫
        (mappingCone.snd f).v m m (add_zero m) := by
  simp only [rotateProjectionHomotopy, Cochain.equivHomotopy, Equiv.symm_mk,
    Equiv.coe_fn_mk, dif_pos hnm]
  rw [Cochain.comp_zero_cochain_v]

/-- The rotation projection commutes with every commutative square.
Source: Stacks, Sections 13.9 and 13.13; its component identity is proved below.
(blueprint: lem-trf-uniform-filtered-cone-rotation). -/
theorem rotateProjection_naturality {K L K' L' : CochainComplex C ℤ}
    (f : K ⟶ L) (g : K' ⟶ L') (a : K ⟶ K') (b : L ⟶ L')
    (h : f ≫ b = a ≫ g) :
    (mappingCone.map (mappingCone.inr f) (mappingCone.inr g) b
      (mappingCone.map f g a b h) (by ext n; simp [mappingCone.map]))⟦(-1 : ℤ)⟧' ≫
        rotateProjection g = rotateProjection f ≫ a := by
  ext n
  simp only [HomologicalComplex.comp_f, rotateProjection_f,
    Preadditive.comp_neg, Preadditive.neg_comp, neg_inj]
  rw [← Category.assoc, fiberSecondCochain_naturality]
  rw [Category.assoc]
  have he (i j : ℤ) (hij : i + 1 = j) :
      (mappingCone.map f g a b h).f i ≫ (mappingCone.fst g).1.v i j hij =
        (mappingCone.fst f).1.v i j hij ≫ a.f j := by
    subst j
    exact UniformFilteredCone.coneMap_fst f g a b h i
  rw [he, ← Category.assoc]

/-- The rotation homotopy commutes with every commutative square.
Source: Stacks, Sections 13.9 and 13.13; its component identity is proved below.
(blueprint: lem-trf-uniform-filtered-cone-rotation). -/
theorem rotateProjectionHomotopy_naturality
    {K L K' L' : CochainComplex C ℤ}
    (f : K ⟶ L) (g : K' ⟶ L') (a : K ⟶ K') (b : L ⟶ L')
    (h : f ≫ b = a ≫ g) (n m : ℤ) :
    ((mappingCone.map (mappingCone.inr f) (mappingCone.inr g) b
      (mappingCone.map f g a b h) (by ext n; simp [mappingCone.map]))⟦(-1 : ℤ)⟧').f n ≫
        (rotateProjectionHomotopy g).hom n m =
      (rotateProjectionHomotopy f).hom n m ≫ b.f m := by
  by_cases hnm : n + (-1) = m
  · subst m
    rw [rotateProjectionHomotopy_hom _ _ _ rfl,
      rotateProjectionHomotopy_hom _ _ _ rfl]
    rw [← Category.assoc, fiberSecondCochain_naturality]
    rw [Category.assoc, UniformFilteredCone.coneMap_snd, ← Category.assoc]
  · have hrel : ¬ (ComplexShape.up ℤ).Rel m n := by
      simp only [ComplexShape.up_Rel]
      omega
    rw [Homotopy.zero _ _ _ hrel, Homotopy.zero _ _ _ hrel]
    simp

/-- Transport the fiber of an actual restricted cone inclusion to its stepwise model.
Source: Stacks, Sections 13.9 and 13.13; its component identity is proved below.
(blueprint: lem-trf-uniform-filtered-cone-rotation). -/
def fiberConeStepMap {K L : FilteredObject (CochainComplex C ℤ)}
    (f : K ⟶ L) (p : ℤ) :
    (mappingCone (FilteredObject.restrictionSteps (UniformFilteredCone.filteredCone_inr f) p))
        ⟦(-1 : ℤ)⟧ ⟶
      (mappingCone (mappingCone.inr (FilteredObject.restrictionSteps f p)))⟦(-1 : ℤ)⟧ :=
  (mappingCone.map _ _ (𝟙 _) (UniformFilteredCone.coneStepIso f p).hom (by
    simpa only [Category.id_comp] using UniformFilteredCone.filteredCone_inr_restriction f p))
      ⟦(-1 : ℤ)⟧'

/-- The transported fiber map factors the actual fiber-step inclusion.
Source: Stacks, Sections 13.9 and 13.13; its component identity is proved below.
(blueprint: lem-trf-uniform-filtered-cone-rotation). -/
theorem fiberConeStepMap_fac {K L : FilteredObject (CochainComplex C ℤ)}
    (f : K ⟶ L) (p : ℤ) :
    fiberConeStepMap f p ≫
      (mappingCone.map _ _ (L.filtration.F p).arrow (UniformFilteredCone.coneStep f p)
        (by ext n; simp [UniformFilteredCone.coneStep,
          UniformFilteredCone.filteredCone_inr, mappingCone.map]))⟦(-1 : ℤ)⟧' =
      (UniformFilteredCone.coneStep (UniformFilteredCone.filteredCone_inr f) p)⟦(-1 : ℤ)⟧' := by
  dsimp only [fiberConeStepMap]
  rw [← Functor.map_comp, ← mappingCone.map_comp]
  congr 2
  · exact Category.id_comp _
  · exact Subobject.underlyingIso_hom_comp_eq_mk _

/-- The rotation projection preserves every actual filtration step.
Source: Stacks, Sections 13.9 and 13.13; its component identity is proved below.
(blueprint: lem-trf-uniform-filtered-cone-rotation). -/
def filteredRotateProjection {K L : FilteredObject (CochainComplex C ℤ)}
    (f : K ⟶ L) :
    fiber L (UniformFilteredCone.filteredCone f) (UniformFilteredCone.filteredCone_inr f) ⟶ K :=
  ⟨rotateProjection f.hom, fun p ↦
    ⟨(fiberStepIso (UniformFilteredCone.filteredCone_inr f) p).hom ≫
      fiberConeStepMap f p ≫ rotateProjection (FilteredObject.restrictionSteps f p), by
      rw [Category.assoc, Category.assoc, ← rotateProjection_naturality _ _ _ _
        (UniformFilteredCone.restriction_arrow f p)]
      have he := fiberConeStepMap_fac f p
      have he' := congrArg ((fiberStepIso (UniformFilteredCone.filteredCone_inr f) p).hom ≫ ·) he
      have he'' := congrArg (· ≫ rotateProjection f.hom) he'
      rw [fiberStepIso_fac] at he''
      simpa only [Category.assoc, fiberStepIso_fac,
        UniformFilteredCone.filteredCone_inr, UniformFilteredCone.coneStep] using he'' ⟩⟩

/-- The rotation homotopy preserves every actual filtration step.
Source: Stacks, Sections 13.9 and 13.13; its component identity is proved below.
(blueprint: lem-trf-uniform-filtered-cone-rotation). -/
theorem filteredRotateProjectionHomotopy {K L : FilteredObject (CochainComplex C ℤ)}
    (f : K ⟶ L) : UniformFilteredHomotopy (filteredRotateProjection f ≫ f)
      (filteredFiberProjection (UniformFilteredCone.filteredCone_inr f)) := by
  refine ⟨rotateProjectionHomotopy f.hom, ?_⟩
  intro p n m
  refine ⟨(fiberStepIso (UniformFilteredCone.filteredCone_inr f) p).hom.f n ≫
    (fiberConeStepMap f p).f n ≫
      (rotateProjectionHomotopy (FilteredObject.restrictionSteps f p)).hom n m, ?_⟩
  rw [Category.assoc, Category.assoc, ← rotateProjectionHomotopy_naturality _ _ _ _
    (UniformFilteredCone.restriction_arrow f p) n m]
  have he := congrArg ((fiberStepIso (UniformFilteredCone.filteredCone_inr f) p).hom ≫ ·)
    (fiberConeStepMap_fac f p)
  rw [fiberStepIso_fac] at he
  have hef := congrArg (fun k ↦ k.f n ≫ (rotateProjectionHomotopy f.hom).hom n m) he
  simpa only [HomologicalComplex.comp_f, Category.assoc,
    UniformFilteredCone.filteredCone_inr, UniformFilteredCone.coneStep] using hef

end UniformFilteredBridge
end CategoryTheory
