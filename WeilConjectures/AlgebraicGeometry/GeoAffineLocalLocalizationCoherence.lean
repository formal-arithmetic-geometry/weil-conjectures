/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GeoAffineLocalCompactSupport

/-! Coherence of counit-normalized exceptional localization.
(blueprint: lem-geo-affine-local-localization-coherence). -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory Limits AlgebraicGeometry Scheme
namespace AlgebraicGeometry.ProEtale

/-- The normalized four-Hom comparisons commute with further etale restriction.
Source: the final sentence and four-Hom calculation of blueprint unit
`sk-lem-geo-affine-local`, clause (2).
(blueprint: lem-geo-affine-local-localization-coherence).

Proof: identify the three left functors using their specified ordinary compactification
models. The compact-support compositors satisfy the associativity equation: replace the
three compactifications by the chosen ones, apply the unbounded lower-shriek associativity
square, and cancel the compactification comparison isomorphisms. The etale sum adjunctions
are the transported canonical sum/restriction adjunctions by the normalization fields.
Their composite right mate is therefore the derived upper-star compositor. Descend this
compositor through the fully faithful comparison equivalence to obtain the displayed
upper_star_compositor and its component normalization. Take right mates of the preceding
compact-support associativity square. Right-adjoint uniqueness identifies the change from
cv to its associatively reindexed copy with the specified assocRight. Mate composition
then gives the localization equation. This also includes identity maps, because both
compact-support and upper-star comparison isomorphisms have their canonical unit coherence.
-/
theorem classicalLocalization_comparison_eq
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {V U X S : Scheme.{u}} (v : V ⟶ U) (g : U ⟶ X) (f : X ⟶ S)
    [IsNoetherian V] [IsNoetherian U] [IsNoetherian X] [IsNoetherian S]
    [IsSeparated f] [LocallyOfFiniteType f]
    [Etale v] [IsSeparated v] [QuasiCompact v]
    [Etale g] [IsSeparated g] [QuasiCompact g] [QuasiCompact f]
    (c : Compactification f) (cu : Compactification (g ≫ f))
    (cv : Compactification (v ≫ g ≫ f))
    (cx : Compactification g) (cV : Compactification v)
    (cVU : Compactification (v ≫ g))
    (CX : ClassicalComparisonData X A) (CU : ClassicalComparisonData U A)
    (CV : ClassicalComparisonData V A) (CS : ClassicalComparisonData S A)
    (F : ProEtaleD X A ⥤ ProEtaleD S A)
    (FU : ProEtaleD U A ⥤ ProEtaleD S A)
    (FV : ProEtaleD V A ⥤ ProEtaleD S A)
    (data : ClassicalExceptionalAdjunctionData X S A f c CX CS F)
    (dataU : ClassicalExceptionalAdjunctionData U S A (g ≫ f) cu CU CS FU)
    (dataV : ClassicalExceptionalAdjunctionData V S A (v ≫ g ≫ f) cv CV CS FV)
    (dataVU : ClassicalExceptionalAdjunctionData V S A ((v ≫ g) ≫ f)
      (cv.copy (Category.assoc v g f)) CV CS FV)
    (sumU : ClassicalEtaleSumData U X A g cx CU CX)
    (sumV : ClassicalEtaleSumData V U A v cV CV CU)
    (sumVU : ClassicalEtaleSumData V X A (v ≫ g) cVU CV CX)
    (thetaU : ClassicalCanonicalComposite A g f c cu cx CU CX CS F FU data dataU sumU)
    (thetaV : ClassicalCanonicalComposite A v (g ≫ f) cu cv cV
      CV CU CS FU FV dataU dataV sumV)
    (thetaVU : ClassicalCanonicalComposite A (v ≫ g) f c (cv.copy (Category.assoc v g f))
      cVU CV CX CS F FV data dataVU sumVU)
    (assocLeft : dataV.left = dataVU.left) :
    Functor.isoWhiskerRight thetaU.comparison.comparison sumV.right ≪≫
        (thetaV.comparison.comparison ≪≫
          (dataV.adjunction.ofNatIsoLeft (eqToIso assocLeft)).rightAdjointUniq
            dataVU.adjunction) =
      Functor.associator data.right sumU.right sumV.right ≪≫
        Functor.isoWhiskerLeft data.right
          (classicalUpperStarCompositor A v g cx cV cVU CX CU CV sumU sumV sumVU) ≪≫
        thetaVU.comparison.comparison := by sorry

/-- Package the localization equation with the explicitly constructed upper-star compositor.
Source: clause (2), final compatibility assertion
(blueprint: lem-geo-affine-local-localization-coherence).

Proof: use the fully faithful lift of the canonical derived upper-star compositor, whose
component normalization was proved in the compact-support transport module, and insert
the normalized localization equation. -/
theorem classicalFurtherLocalization_of_normalized_composites
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {V U X S : Scheme.{u}} (v : V ⟶ U) (g : U ⟶ X) (f : X ⟶ S)
    [IsNoetherian V] [IsNoetherian U] [IsNoetherian X] [IsNoetherian S]
    [IsSeparated f] [LocallyOfFiniteType f]
    [Etale v] [IsSeparated v] [QuasiCompact v]
    [Etale g] [IsSeparated g] [QuasiCompact g] [QuasiCompact f]
    (c : Compactification f) (cu : Compactification (g ≫ f))
    (cv : Compactification (v ≫ g ≫ f))
    (cx : Compactification g) (cV : Compactification v)
    (cVU : Compactification (v ≫ g))
    (CX : ClassicalComparisonData X A) (CU : ClassicalComparisonData U A)
    (CV : ClassicalComparisonData V A) (CS : ClassicalComparisonData S A)
    (F : ProEtaleD X A ⥤ ProEtaleD S A)
    (FU : ProEtaleD U A ⥤ ProEtaleD S A)
    (FV : ProEtaleD V A ⥤ ProEtaleD S A)
    (data : ClassicalExceptionalAdjunctionData X S A f c CX CS F)
    (dataU : ClassicalExceptionalAdjunctionData U S A (g ≫ f) cu CU CS FU)
    (dataV : ClassicalExceptionalAdjunctionData V S A (v ≫ g ≫ f) cv CV CS FV)
    (dataVU : ClassicalExceptionalAdjunctionData V S A ((v ≫ g) ≫ f)
      (cv.copy (Category.assoc v g f)) CV CS FV)
    (sumU : ClassicalEtaleSumData U X A g cx CU CX)
    (sumV : ClassicalEtaleSumData V U A v cV CV CU)
    (sumVU : ClassicalEtaleSumData V X A (v ≫ g) cVU CV CX)
    (thetaU : ClassicalCanonicalComposite A g f c cu cx CU CX CS F FU data dataU sumU)
    (thetaV : ClassicalCanonicalComposite A v (g ≫ f) cu cv cV
      CV CU CS FU FV dataU dataV sumV)
    (thetaVU : ClassicalCanonicalComposite A (v ≫ g) f c (cv.copy (Category.assoc v g f))
      cVU CV CX CS F FV data dataVU sumVU)
    (assocLeft : dataV.left = dataVU.left) :
    Nonempty (ClassicalFurtherLocalization A v g data.right dataU.right dataVU.right
      cx cV cVU CX CU CV sumU sumV sumVU thetaU.comparison.comparison
      (thetaV.comparison.comparison ≪≫
        (dataV.adjunction.ofNatIsoLeft (eqToIso assocLeft)).rightAdjointUniq dataVU.adjunction)
      thetaVU.comparison.comparison) := by
  exact ⟨{
    upper_star_compositor :=
      classicalUpperStarCompositor A v g cx cV cVU CX CU CV sumU sumV sumVU
    upper_star_normalization :=
      classicalUpperStarCompositor_normalization A v g cx cV cVU CX CU CV sumU sumV sumVU
    localization_equation := classicalLocalization_comparison_eq A v g f c cu cv cx cV cVU
      CX CU CV CS F FU FV data dataU dataV dataVU sumU sumV sumVU thetaU thetaV thetaVU
      assocLeft }⟩

end AlgebraicGeometry.ProEtale
