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
  sorry

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
  sorry

/-- Standard cohomology with values in the recorded constructible Weil heart.
Source: blueprint cohomology convention (blueprint: def-weil-derived-cohomology-sheaves). -/
def sfModelWeilCohomology (n : ℤ) :
    sfCommonStageWeilComplex D l hl X₀ Ω ⥤ sfCommonStageWeilSheaf D l hl X₀ Ω :=
  ((sfCommonStageHeartProperty l (D.geometricFiber X₀).left Ω).inverseImage
    (sfCommonStageWeilForget D l hl X₀ Ω)).lift
    (sfModelWeilCohomologyPair D l hl Ω X₀ n) (sfModelWeilCohomology_mem D l hl Ω X₀ n)

end WeilConjectures
