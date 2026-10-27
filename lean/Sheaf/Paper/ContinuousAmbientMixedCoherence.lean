/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H8
-/
module

public import Sheaf.Paper.ContinuousRationalRealizationData

/-! # Normalized continuous tensor coherence

Source: Bhatt--Scholze, Proposition 6.8.14(2) and Remark 6.8.15
(blueprint: lem-per-continuous-ambient-mixed-coherence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genInjectivity false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.ContinuousRational
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

variable (F : Type u) [Field F] [Algebra ℚ_[l] F]
  [FiniteDimensional ℚ_[l] F]

/-- The ordinary and derived mixed square, before its raw normalization.
Source: BS Remark 6.8.15; Stacks 0D6D (blueprint: lem-per-continuous-ambient-mixed-coherence). -/
structure AmbientMixed (i : E →ₐ[ℚ_[l]] F) {X Y : Base.{u} l} (g : X.scheme ⟶ Y.scheme)
    (aXE : At l E X) (aYE : At l E Y) (aXF : At l F X) (aYF : At l F Y)
    (agE : Along l E g aXE aYE) (agF : Along l F g aXF aYF)
    (bX : FieldChange l E F i X aXE aXF) (bY : FieldChange l E F i Y aYE aYF) where
  coefficient : (adicTowerInverseImage g).map bY.coefficient ≫ agF.coefficient =
    agE.coefficient ≫ bX.coefficient
  ordinary : pbcExtend bY.coefficient ⋙ modulePull g agF.coefficient ≅
    modulePull g agE.coefficient ⋙ pbcExtend bX.coefficient
  ordinary_sections : ∀ (M : pbcModules Y.scheme (rationalCoefficientSheaf l Y.scheme E))
      (U : Y.scheme.ProEt)
      (a : (rationalCoefficientSheaf l Y.scheme F).obj.obj (op U)) (m : M.val.obj (op U)),
    (ordinary.hom.app M).val.app (op ((proEtaleBaseChange g).obj U))
      (moduleUnit g agF.coefficient ((pbcExtend bY.coefficient).obj M) U
        (pbcTensorSection bY.coefficient M (op U) a m)) =
      pbcTensorSection bX.coefficient ((modulePull g agE.coefficient).obj M)
        (op ((proEtaleBaseChange g).obj U))
        (((proEtaleSheafAdjunction g CommRingCat.{u + 1}).homEquiv _ _
          agF.coefficient).hom.app (op U) a)
        (moduleUnit g agE.coefficient M U m)
  complex : (pbcExtend bY.coefficient).mapHomologicalComplex (.up ℤ) ⋙
      (modulePull g agF.coefficient).mapHomologicalComplex (.up ℤ) ≅
    (modulePull g agE.coefficient).mapHomologicalComplex (.up ℤ) ⋙
      (pbcExtend bX.coefficient).mapHomologicalComplex (.up ℤ)
  complex_components : ∀ P (n : ℤ), (complex.hom.app P).f n = ordinary.hom.app (P.X n)
  ambient : pbcDerivedExtend bY.coefficient ⋙ derivedPull g agF.coefficient ≅
    derivedPull g agE.coefficient ⋙ pbcDerivedExtend bX.coefficient
  ambient_normalization : ∀ P : CochainComplex
      (pbcModules Y.scheme (rationalCoefficientSheaf l Y.scheme E)) ℤ,
    CochainComplex.IsAcyclicTensorKFlat (J := ProEt.topology Y.scheme)
      (R := rationalCoefficientSheaf l Y.scheme E) P →
    (∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := ProEt.topology Y.scheme)
      (R := rationalCoefficientSheaf l Y.scheme E) (P.X n)) →
    (derivedPull g agF.coefficient).map (pbcComplexCounit bY.coefficient P) ≫
        agF.counit.app (((pbcExtend bY.coefficient).mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map (complex.hom.app P) =
      ambient.hom.app (DerivedCategory.Q.obj P) ≫
        (pbcDerivedExtend bX.coefficient).map (agE.counit.app P) ≫
        pbcComplexCounit bX.coefficient
          (((modulePull g agE.coefficient).mapHomologicalComplex (.up ℤ)).obj P)

/-- Coefficient extension and scheme pullback have a normalized balanced comparison.
Source: BS Remark 6.8.15; Stacks 0D6D (blueprint: lem-per-continuous-ambient-mixed-coherence).

Proof: the coefficient square follows by transposing the two maps through the
inverse-image adjunction: both postcompose a continuous function by the field
embedding after precomposition by the scheme map. On ordinary modules flatten
the two tensor factors, sending a scalar times a pulled generator to the product
of the scalar images times that generator. Insertion of one gives the inverse;
balancing and sheafification make these maps well-defined and natural. Apply them
termwise to obtain the complex comparison and its component equation. Resolve a
complex by flat-term K-flat terms. Exact inverse image and scalar extension
preserve this resolving class, so the universal derived counits descend the
termwise comparison. Their specified normalizations give precisely the equation
in AmbientMixed. No completed or rationalized integral object is used here. -/
theorem continuousAmbientMixedCoherence (i : E →ₐ[ℚ_[l]] F)
    {X Y : Base.{u} l} (g : X.scheme ⟶ Y.scheme)
    (aXE : At l E X) (aYE : At l E Y) (aXF : At l F X) (aYF : At l F Y)
    (agE : Along l E g aXE aYE) (agF : Along l F g aXF aYF)
    (bX : FieldChange l E F i X aXE aXF) (bY : FieldChange l E F i Y aYE aYF) :
    Nonempty (AmbientMixed l E F i g aXE aYE aXF aYF agE agF bX bY) := by sorry

end AlgebraicGeometry.Scheme.ContinuousRational
