/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Lisse.Tower.LisseTowerLocalizedConstantsNormalization
import WeilConjectures.AlgebraicGeometry.Lisse.Tower.LisseTowerConstantCoherence

/-! # Constant model comparisons and the coefficient identity on complexes

Source: Stacks Project, Modules on Sites, Tags 03CY and 03DA; Sites, Tag 0H7J;
Cohomology on Sites, Tag 06YY.

Only the identity semilinear arrow on a represented complex is checked here.
Localization and naturality extend this to arbitrary derived arrows in
`lisseTower_localized_constants_normalization`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local irreducible] HasDerivedCategory.standard pbcDerivedRestrict
  lisseTowerFixedRealization constantAdicQuotientRealization constantAdicFiniteRealization
  constantAdicQuotientRightIso constantAdicFiniteProjection
  lisseTowerConstantInput lisseTowerConstantScalarIso lisseTowerConstantModelIso
  lisseTowerAlgebraRestrictIso

/-- The natural constant comparisons can be constructed with compatible coefficient
identity arrows on cochain complexes.

Source: Stacks Project, Modules on Sites, Tags 03CY and 03DA; Sites, Tag 0H7J;
Cohomology on Sites, Tag 06YY.
(blueprint: lem-weil-pbc-lisse-tower-constant-complex-comparisons).

Proof: first construct ordinary natural comparisons, rather than choosing an
isomorphism independently at each object or coefficient level. The constant-sheaf
adjunction identifies constants followed by comparison and the inverse images along
a and b with constants on Z. Use the constant-section identification
lisseTowerFiniteCoefficientIso and associated-module-sheafification to identify
these with constantAdicQuotientModules X d n followed by the ringed inverse image
along g. The adjunction units specify this comparison on every constant section,
so it is natural in the algebraic module. Apply it termwise to cochain complexes
and localize, using mapDerivedCategoryCompIso and lisseTowerFixedRealizationIso.
This produces the natural isomorphisms model n.

For the displayed equality take the identity from the coefficient restriction of
a module to itself. Before localization both paths send every constant generator
x to x. The section normalization of lisseTowerNormalizedScalarSquare and
constantAdicQuotientComparison identifies these paths, including the inverse-image
coefficient mates. The ordinary restriction compositor is restrictScalarsComp';
the ringed restriction compositor is pbcRestrictComp. Apply the equality in every
degree of K, then apply the localization functor. Its exact-composition comparisons
are precisely those in lisseTowerConstantScalarIso, lisseTowerConstantModelIso and
lisseTowerAlgebraRestrictIso. The resulting equality is the one asserted at Q K.
No roof or arbitrary derived semilinear arrow is part of this assertion. Zero
complexes and empty schemes are included because the construction uses adjunctions
and equality of natural transformations, with no chosen nonzero section. -/
theorem lisseTower_constant_complex_comparisons
    {X Z T S : Scheme.{u}} (g : Z ⟶ X) (a : T ⟶ S) (b : Z ⟶ T)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) :
    ∃ model : ∀ n : ℕ,
      lisseTowerConstantInput g a b d n ≅ constantAdicQuotientRealization g d n,
    ∀ (n : ℕ)
      (K : CochainComplex (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)) ℤ),
      ((lisseTowerConstantScalarIso g a b d n) ≪≫
        lisseTowerConstantModelIso g a b d n (model n)).hom.app (DerivedCategory.Q.obj K) =
      (Functor.isoWhiskerLeft (normalizationModuleRestrict (lisseTowerEtaleQuotient d n))
          (lisseTowerConstantModelIso g a b d (n + 1) (model (n + 1))) ≪≫
        Functor.isoWhiskerRight (lisseTowerAlgebraRestrictIso d n)
          (constantAdicFiniteRealization g d)).hom.app (DerivedCategory.Q.obj K) :=
  ⟨fun n ↦ lisseTowerConstantModel g a b d n,
    fun n K ↦ lisseTowerConstantModel_coherence g a b d n K⟩

end AlgebraicGeometry.Scheme
