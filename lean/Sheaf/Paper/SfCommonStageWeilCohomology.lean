/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N5
-/
module

public import Sheaf.Paper.PbcQbarStandardCohomology
public import Sheaf.Paper.WeilIndSheafCategory

/-! # Standard cohomology on the intrinsic common-stage Weil category

Source: Bhatt--Scholze 6.8.11(3), 6.8.14(2), 6.8.15; BBD 1.3
(blueprint: def-weil-derived-cohomology-sheaves).
The recorded ambient and coefficient-pair cohomology remain reexported. Here the same
standard truncation construction is applied to the general intrinsic pair category.
The Weil map is induced by the canonical Frobenius truncation comparison.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.Endofunctor AlgebraicGeometry
namespace WeilConjectures

/-- Uniquely normalized truncation/shift comparisons. Shifting by one carries
truncation at one to truncation at zero, with the same unit and counit.
Source: BBD 1.3.3 (blueprint: def-weil-derived-cohomology-sheaves).
Proof: shift the truncation triangles at one. Their two terms satisfy the required
bounds at zero. Uniqueness of truncation triangles gives the isomorphisms; the
adjunction universal properties give uniqueness among maps satisfying these equations. -/
theorem sfTruncationShift_existsUnique
    {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
    (t : CategoryTheory.Triangulated.TStructure C) (K : C) :
    (∃! e : (t.truncLE 0).obj (K⟦(1 : ℤ)⟧) ≅ ((t.truncLE 1).obj K)⟦(1 : ℤ)⟧,
      e.hom ≫ ((t.truncLEι 1).app K)⟦(1 : ℤ)⟧' =
        (t.truncLEι 0).app (K⟦(1 : ℤ)⟧)) ∧
    (∃! e : (t.truncGE 0).obj (K⟦(1 : ℤ)⟧) ≅ ((t.truncGE 1).obj K)⟦(1 : ℤ)⟧,
      (t.truncGEπ 0).app (K⟦(1 : ℤ)⟧) ≫ e.hom =
        ((t.truncGEπ 1).app K)⟦(1 : ℤ)⟧') := by
  let eK : K⟦(1 : ℤ)⟧ ≅ K⟦(1 : ℤ)⟧ :=
    { hom := -𝟙 _, inv := -𝟙 _
      hom_inv_id := by simp
      inv_hom_id := by simp }
  constructor
  · obtain ⟨e, he⟩ := t.triangle_iso_exists
      (t.triangleLEGE_distinguished 0 1 (by decide) (K⟦(1 : ℤ)⟧))
      (Pretriangulated.Triangle.shift_distinguished _
        (t.triangleLEGE_distinguished 1 2 (by decide) K) 1)
      eK 0 1
      (by change t.IsLE ((t.truncLE 0).obj (K⟦(1 : ℤ)⟧)) 0; infer_instance)
      (by change t.IsGE ((t.truncGE 1).obj (K⟦(1 : ℤ)⟧)) 1; infer_instance)
      (by
        change t.IsLE (((t.truncLE 1).obj K)⟦(1 : ℤ)⟧) 0
        exact t.isLE_shift _ 1 1 0 (by decide))
      (by
        change t.IsGE (((t.truncGE 2).obj K)⟦(1 : ℤ)⟧) 1
        exact t.isGE_shift _ 2 1 1 (by decide))
    let a := ((Pretriangulated.Triangle.π₁).mapIso e)
    have ha : a.hom ≫ ((t.truncLEι 1).app K)⟦(1 : ℤ)⟧' =
        (t.truncLEι 0).app (K⟦(1 : ℤ)⟧) := by
      have h := e.hom.comm₁.symm
      simp only [Pretriangulated.Triangle.shiftFunctor_eq,
        Pretriangulated.Triangle.shiftFunctor, Int.negOnePow_one,
        Functor.comp_obj, Pretriangulated.Triangle.mk_mor₁,
        Triangulated.TStructure.triangleLEGE_obj_mor₁,
        Units.neg_smul, one_smul, Preadditive.comp_neg, he, neg_inj, eK] at h
      change a.hom ≫ ((t.truncLEι 1).app K)⟦(1 : ℤ)⟧' =
        (t.truncLEι 0).app (K⟦(1 : ℤ)⟧) ≫ 𝟙 _ at h
      simpa only [Category.comp_id] using h
    refine ⟨a, ha, ?_⟩
    intro b hb
    apply Iso.ext
    apply (cancel_mono a.inv).1
    apply t.to_truncLE_obj_ext
    simp only [Category.assoc, ← ha, Iso.inv_hom_id_assoc, hb, Iso.hom_inv_id,
      Category.id_comp]
  · obtain ⟨e, he⟩ := t.triangle_iso_exists
      (t.triangleLEGE_distinguished (-1) 0 (by decide) (K⟦(1 : ℤ)⟧))
      (Pretriangulated.Triangle.shift_distinguished _
        (t.triangleLEGE_distinguished 0 1 (by decide) K) 1)
      eK (-1) 0
      (by change t.IsLE ((t.truncLE (-1)).obj (K⟦(1 : ℤ)⟧)) (-1); infer_instance)
      (by change t.IsGE ((t.truncGE 0).obj (K⟦(1 : ℤ)⟧)) 0; infer_instance)
      (by
        change t.IsLE (((t.truncLE 0).obj K)⟦(1 : ℤ)⟧) (-1)
        exact t.isLE_shift _ 0 1 (-1) (by decide))
      (by
        change t.IsGE (((t.truncGE 1).obj K)⟦(1 : ℤ)⟧) 0
        exact t.isGE_shift _ 1 1 0 (by decide))
    let a := ((Pretriangulated.Triangle.π₃).mapIso e)
    have ha : (t.truncGEπ 0).app (K⟦(1 : ℤ)⟧) ≫ a.hom =
        ((t.truncGEπ 1).app K)⟦(1 : ℤ)⟧' := by
      have h := e.hom.comm₂
      simp only [Int.reduceNeg, Pretriangulated.Triangle.shiftFunctor_eq,
        Pretriangulated.Triangle.shiftFunctor,
        Int.negOnePow_one, Functor.comp_obj, Triangulated.TStructure.triangleLEGE_obj_mor₂,
        he, Pretriangulated.Triangle.mk_mor₂, Units.neg_smul, one_smul,
        Preadditive.comp_neg,
        Preadditive.neg_comp, neg_neg, eK] at h
      change (t.truncGEπ 0).app (K⟦(1 : ℤ)⟧) ≫ a.hom =
        𝟙 _ ≫ ((t.truncGEπ 1).app K)⟦(1 : ℤ)⟧' at h
      simpa only [Category.id_comp] using h
    refine ⟨a, ha, ?_⟩
    intro b hb
    apply Iso.ext
    have := t.isGE_shift ((t.truncGE 1).obj K) 1 1 0 (by decide)
    exact t.from_truncGE_obj_ext (hb.trans ha.symm)

/-- The shift comparison H^0(K[1]) = H^1(K), built from the uniquely normalized
truncation comparisons and the prescribed zero shift. This fixes its sign.
Source: BBD 1.3.3 (blueprint: def-weil-derived-cohomology-sheaves). -/
@[irreducible]
def sfCohomologyShift
    {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
    (t : CategoryTheory.Triangulated.TStructure C) (K : C) :
    (constructibleTruncationCohomology t 0).obj (K⟦(1 : ℤ)⟧) ≅
      (constructibleTruncationCohomology t 1).obj K :=
  (shiftFunctorZero C ℤ).app ((t.truncGE 0).obj ((t.truncLE 0).obj (K⟦(1 : ℤ)⟧))) ≪≫
    (t.truncGE 0).mapIso (sfTruncationShift_existsUnique t K).1.exists.choose ≪≫
      (sfTruncationShift_existsUnique t ((t.truncLE 1).obj K)).2.exists.choose

/-- Finite type on a bundled base change is finite type of its second projection.
Source: blueprint geometric-fibre convention
(blueprint: def-weil-derived-cohomology-sheaves). -/
instance sfBaseChangeFinite {B T : Scheme.{u}} (f : T ⟶ B) (Y : Over B)
    [LocallyOfFiniteType Y.hom] :
    LocallyOfFiniteType (((Over.pullback f).obj Y).left ↘ T) :=
  inferInstanceAs (LocallyOfFiniteType (pullback.snd Y.hom f))

/-- Quasi-compactness on a bundled base change is that of its second projection.
Source: blueprint geometric-fibre convention
(blueprint: def-weil-derived-cohomology-sheaves). -/
instance sfBaseChangeQuasiCompact {B T : Scheme.{u}} (f : T ⟶ B) (Y : Over B)
    [QuasiCompact Y.hom] :
    QuasiCompact (((Over.pullback f).obj Y).left ↘ T) :=
  inferInstanceAs (QuasiCompact (pullback.snd Y.hom f))

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  (X₀ : Over (Spec (.of D.k₀)))
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]

/-- Finite type of the actual geometric base change, as the pullback projection.
Source: blueprint geometric-fibre convention
(blueprint: def-weil-derived-cohomology-sheaves). -/
instance sfModelGeometricFinite :
    LocallyOfFiniteType ((D.geometricFiber X₀).left ↘ Spec (.of D.k)) :=
  inferInstanceAs (LocallyOfFiniteType
    (pullback.snd X₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))

/-- Quasi-compactness of the actual geometric base change, as the pullback projection.
Source: blueprint geometric-fibre convention
(blueprint: def-weil-derived-cohomology-sheaves). -/
instance sfModelGeometricQuasiCompact :
    QuasiCompact ((D.geometricFiber X₀).left ↘ Spec (.of D.k)) :=
  inferInstanceAs (QuasiCompact
    (pullback.snd X₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))

/-- Standard geometric cohomology, placed in degree zero, on the actual pair category.
Source: BS 6.8.11(3), 6.8.14(2), 6.8.15
(blueprint: def-weil-derived-cohomology-sheaves). -/
def sfModelCohomology (n : ℤ) :=
  constructibleTruncationCohomology
    (sfCommonStageStandardTStructure l (D.geometricFiber X₀).left Ω D hl) n

/-- Cohomology commutes with actual geometric inverse image, with the normalized
truncation-unit, truncation-counit and shift comparison.
Source: BS 6.8.15, BBD 1.3 (blueprint: def-weil-derived-cohomology-sheaves). -/
@[irreducible]
def sfModelPullCohomology {Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] (f : X₀ ⟶ Y₀) (n : ℤ) :
    sfModelCohomology D l hl Ω Y₀ n ⋙ zlPull D l hl Ω f ≅
      zlPull D l hl Ω f ⋙ sfModelCohomology D l hl Ω X₀ n :=
  cast (congrArg (fun F ↦ sfModelCohomology D l hl Ω Y₀ n ⋙ F ≅
      F ⋙ sfModelCohomology D l hl Ω X₀ n)
    (congrArg₂ (fun hX hY ↦ @commonStageDerivedPullback l _ Ω _ _ _ _ _
      (zlFiberMap D f) hX hY)
      (Subsingleton.elim (constructiblePullbackResidueUnits D l hl
        (D.geometricFiber X₀).left) (sfWeilPrimeInvertible D l hl X₀))
      (Subsingleton.elim (constructiblePullbackResidueUnits D l hl
        (D.geometricFiber Y₀).left) (sfWeilPrimeInvertible D l hl Y₀))))
    (((constructible_pullback_t_exact D l hl Ω (Padic.finiteCoefficientBase l Ω)
      (zlFiberMap D f)).2.some).cohomology n)

/-- The canonical cohomology/Frobenius comparison, characterized by the truncation
unit, counit and shift equations of ConstructiblePullbackComparison.cohomology_formula.
Its data come from the uniquely normalized t-exact comparison, not an arbitrary iso.
Source: BBD 1.3; BS 6.8.15 (blueprint: def-weil-derived-cohomology-sheaves). -/
@[irreducible]
def sfModelFrobeniusCohomology (n : ℤ) :
    sfModelCohomology D l hl Ω X₀ n ⋙ sfCommonStageWeilFrobeniusPullback D l hl X₀ Ω ≅
      sfCommonStageWeilFrobeniusPullback D l hl X₀ Ω ⋙ sfModelCohomology D l hl Ω X₀ n :=
  cast (congrArg (fun F ↦ sfModelCohomology D l hl Ω X₀ n ⋙ F ≅
      F ⋙ sfModelCohomology D l hl Ω X₀ n)
    (congrArg₂ (fun hX hY ↦ @commonStageDerivedPullback l _ Ω _ _ _ _ _
      (D.geometricFrobenius X₀).hom hX hY)
      (Subsingleton.elim (constructiblePullbackResidueUnits D l hl
        (D.geometricFiber X₀).left) (sfWeilPrimeInvertible D l hl X₀))
      (Subsingleton.elim (constructiblePullbackResidueUnits D l hl
        (D.geometricFiber X₀).left) (sfWeilPrimeInvertible D l hl X₀))))
    (((constructible_pullback_t_exact D l hl Ω (Padic.finiteCoefficientBase l Ω)
      (D.geometricFrobenius X₀).hom).2.some).cohomology n)

/-- Cohomology of a fixed Frobenius pair, with the actual induced Weil isomorphism.
Source: blueprint cohomology convention (blueprint: def-weil-derived-cohomology-sheaves). -/
def sfModelWeilCohomologyPair (n : ℤ) :=
  IsoAlgebra.mapOfNatIso (sfModelFrobeniusCohomology D l hl Ω X₀ n)

/-- Standard cohomology of any constructible Weil complex lies in the Weil heart.
Source: BBD 1.3; BS 6.8.11(3), 6.8.15
(blueprint: def-weil-derived-cohomology-sheaves).
Proof: truncating at n from above and below leaves only degree n, and shifting by n
puts that degree at zero. The standard-heart identification in SfConstructibleHeart
makes this exactly sfCommonStageHeartProperty. Frobenius is t-exact, so its normalized
cohomology comparison and the original Weil iso give the indicated invertible Weil map. -/
theorem sfModelWeilCohomology_mem (n : ℤ)
    (K : sfCommonStageWeilComplex D l hl X₀ Ω) :
    sfCommonStageHeartProperty l (D.geometricFiber X₀).left Ω
      (((sfModelWeilCohomologyPair D l hl Ω X₀ n).obj K).carrier) := by
  rw [← (sfCommonStageHeart_properties l (D.geometricFiber X₀).left Ω D hl).1]
  change (sfCommonStageStandardTStructure l (D.geometricFiber X₀).left Ω D hl).heart
    ((constructibleTruncationCohomology
      (sfCommonStageStandardTStructure l (D.geometricFiber X₀).left Ω D hl) n).obj K.carrier)
  let t := sfCommonStageStandardTStructure l (D.geometricFiber X₀).left Ω D hl
  change t.heart (((t.truncGE n).obj ((t.truncLE n).obj K.carrier))⟦n⟧)
  rw [t.mem_heart_iff]
  exact ⟨t.isLE_shift _ n n 0 (add_zero n), t.isGE_shift _ n n 0 (add_zero n)⟩

/-- Standard cohomology with values in the recorded constructible Weil heart.
Source: blueprint cohomology convention (blueprint: def-weil-derived-cohomology-sheaves). -/
def sfModelWeilCohomology (n : ℤ) :
    sfCommonStageWeilComplex D l hl X₀ Ω ⥤ sfCommonStageWeilSheaf D l hl X₀ Ω :=
  ((sfCommonStageHeartProperty l (D.geometricFiber X₀).left Ω).inverseImage
    (sfCommonStageWeilForget D l hl X₀ Ω)).lift
    (sfModelWeilCohomologyPair D l hl Ω X₀ n) (sfModelWeilCohomology_mem D l hl Ω X₀ n)

end WeilConjectures
