/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups NE and Q24
-/
module

public import Sheaf.AlgebraicGeometry.ComparisonPullbackCoherence
public import Sheaf.AlgebraicGeometry.ChosenCartesianSquare
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Sheaf.CategoryTheory.RingedSiteModules
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
/-!
# Coherent comparison of etale and pro-etale inverse images

Source: blueprint, sec-proper-base-change, sk-thm-properbasechange,
node lem-weil-pbc-comparison-pullback; Stacks Project, Tags 098T, 099R, 00WX and 0B65
(blueprint: lem-weil-pbc-comparison-pullback).

The auxiliary interfaces extend the existing Kan-extension constructions to sets as
well as abelian groups and finite fixed-ring modules. Every comparison is the mate
of the canonical base-change isomorphism on restriction functors. No arbitrary
isomorphism is selected.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

variable (D : Type v) [Category.{u + 1} D] [HasColimitsOfSize.{u + 1, u + 1} D]
variable [∀ X : Scheme.{u}, HasWeakSheafify X.smallEtaleTopology D]
variable [∀ X : Scheme.{u}, HasWeakSheafify (Scheme.ProEt.topology X) D]

/-- The constructed etale inverse image for the coefficient category `D`.
For abelian coefficients this is definitionally the existing `upperStar`.
Source: blueprint, lem-weil-pbc-comparison-pullback, proof steps 1--4;
Stacks, Tags 00WX and 0B65 (blueprint: lem-weil-pbc-comparison-pullback). -/
noncomputable abbrev cbcEtaleComparisonPullback {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  Functor.sheafPullbackConstruction.sheafPullback
    (MorphismProperty.Over.pullback @Etale ⊤ f) D
    Y.smallEtaleTopology X.smallEtaleTopology

/-- The canonical inverse-image adjunction, obtained from Kan extension and sheafification.
Source: blueprint, lem-weil-pbc-comparison-pullback, proof steps 1--4;
Stacks, Tags 00WX and 0B65 (blueprint: lem-weil-pbc-comparison-pullback). -/
noncomputable abbrev cbcEtaleComparisonAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y) :
    cbcEtaleComparisonPullback D f ⊣ Etale.lowerStar D f :=
  have : (MorphismProperty.Over.pullback @Etale ⊤ f).IsContinuous
      Y.smallEtaleTopology X.smallEtaleTopology := Etale.isContinuous_overPullback f
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (MorphismProperty.Over.pullback @Etale ⊤ f) D
    Y.smallEtaleTopology X.smallEtaleTopology

/-- The identity comparison, adjoint to the canonical fibre-product identity.
Source: blueprint, lem-weil-pbc-comparison-pullback, proof steps 1--4;
Stacks, Tags 00WX and 0B65 (blueprint: lem-weil-pbc-comparison-pullback). -/
noncomputable def cbcEtaleComparisonId (X : Scheme.{u}) :
    cbcEtaleComparisonPullback D (𝟙 X) ≅ 𝟭 _ :=
  have : (MorphismProperty.Over.pullback @Etale ⊤ (𝟙 X)).IsContinuous
      X.smallEtaleTopology X.smallEtaleTopology := Etale.isContinuous_overPullback (𝟙 X)
  (conjugateIsoEquiv Adjunction.id (cbcEtaleComparisonAdjunction D (𝟙 X))).symm
    (Functor.sheafPushforwardContinuousId'
      (MorphismProperty.Over.pullbackId @Etale ⊤ X) D X.smallEtaleTopology).symm

/-- The composition comparison, adjoint to associativity of chosen fibre products.
Source: blueprint, lem-weil-pbc-comparison-pullback, proof steps 1--4;
Stacks, Tags 00WX and 0B65 (blueprint: lem-weil-pbc-comparison-pullback). -/
noncomputable def cbcEtaleComparisonComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    cbcEtaleComparisonPullback D (f ≫ g) ≅
      cbcEtaleComparisonPullback D g ⋙ cbcEtaleComparisonPullback D f :=
  have : (MorphismProperty.Over.pullback @Etale ⊤ f).IsContinuous
      Y.smallEtaleTopology X.smallEtaleTopology := Etale.isContinuous_overPullback f
  have : (MorphismProperty.Over.pullback @Etale ⊤ g).IsContinuous
      Z.smallEtaleTopology Y.smallEtaleTopology := Etale.isContinuous_overPullback g
  have : (MorphismProperty.Over.pullback @Etale ⊤ (f ≫ g)).IsContinuous
      Z.smallEtaleTopology X.smallEtaleTopology := Etale.isContinuous_overPullback (f ≫ g)
  ((conjugateIsoEquiv (cbcEtaleComparisonAdjunction D (f ≫ g))
    ((cbcEtaleComparisonAdjunction D g).comp (cbcEtaleComparisonAdjunction D f))).symm
      (Functor.sheafPushforwardContinuousComp'
        (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) f g).symm D
        Z.smallEtaleTopology Y.smallEtaleTopology X.smallEtaleTopology).symm).symm

/-- The specified square identification: compose through the equal composite morphisms.
The chosen Cartesian identification supplies the commutativity equation.
Source: blueprint, lem-weil-pbc-comparison-pullback, proof steps 1--4;
Stacks, Tags 00WX and 0B65 (blueprint: lem-weil-pbc-comparison-pullback). -/
noncomputable def cbcEtaleComparisonSquare {X' X Y' Y : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare g' f' f g) :
    cbcEtaleComparisonPullback D g ⋙ cbcEtaleComparisonPullback D f' ≅
      cbcEtaleComparisonPullback D f ⋙ cbcEtaleComparisonPullback D g' :=
  (cbcEtaleComparisonComp D f' g).symm ≪≫
    eqToIso (congrArg (cbcEtaleComparisonPullback D) sq.w.symm) ≪≫
      cbcEtaleComparisonComp D g' f

/-- The constructed proEtale inverse image for the coefficient category `D`.
For abelian coefficients this is definitionally the existing `upperStar`.
Source: blueprint, lem-weil-pbc-comparison-pullback, proof steps 1--4;
Stacks, Tags 00WX and 0B65 (blueprint: lem-weil-pbc-comparison-pullback). -/
noncomputable abbrev cbcProEtaleComparisonPullback {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  Functor.sheafPullbackConstruction.sheafPullback
    (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f) D
    (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)

/-- The canonical inverse-image adjunction, obtained from Kan extension and sheafification.
Source: blueprint, lem-weil-pbc-comparison-pullback, proof steps 1--4;
Stacks, Tags 00WX and 0B65 (blueprint: lem-weil-pbc-comparison-pullback). -/
noncomputable abbrev cbcProEtaleComparisonAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f) D
    (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)

/-- The identity comparison, adjoint to the canonical fibre-product identity.
Source: blueprint, lem-weil-pbc-comparison-pullback, proof steps 1--4;
Stacks, Tags 00WX and 0B65 (blueprint: lem-weil-pbc-comparison-pullback). -/
noncomputable def cbcProEtaleComparisonId (X : Scheme.{u}) :
    cbcProEtaleComparisonPullback D (𝟙 X) ≅ 𝟭 _ :=
  (conjugateIsoEquiv Adjunction.id (cbcProEtaleComparisonAdjunction D (𝟙 X))).symm
    (Functor.sheafPushforwardContinuousId'
      (MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X) D (Scheme.ProEt.topology X)).symm

/-- The composition comparison, adjoint to associativity of chosen fibre products.
Source: blueprint, lem-weil-pbc-comparison-pullback, proof steps 1--4;
Stacks, Tags 00WX and 0B65 (blueprint: lem-weil-pbc-comparison-pullback). -/
noncomputable def cbcProEtaleComparisonComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    cbcProEtaleComparisonPullback D (f ≫ g) ≅
      cbcProEtaleComparisonPullback D g ⋙ cbcProEtaleComparisonPullback D f :=
  ((conjugateIsoEquiv (cbcProEtaleComparisonAdjunction D (f ≫ g))
    ((cbcProEtaleComparisonAdjunction D g).comp (cbcProEtaleComparisonAdjunction D f))).symm
      (Functor.sheafPushforwardContinuousComp'
        (MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) f g).symm D
        (Scheme.ProEt.topology Z) (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).symm).symm

/-- The specified square identification: compose through the equal composite morphisms.
The chosen Cartesian identification supplies the commutativity equation.
Source: blueprint, lem-weil-pbc-comparison-pullback, proof steps 1--4;
Stacks, Tags 00WX and 0B65 (blueprint: lem-weil-pbc-comparison-pullback). -/
noncomputable def cbcProEtaleComparisonSquare {X' X Y' Y : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare g' f' f g) :
    cbcProEtaleComparisonPullback D g ⋙ cbcProEtaleComparisonPullback D f' ≅
      cbcProEtaleComparisonPullback D f ⋙ cbcProEtaleComparisonPullback D g' :=
  (cbcProEtaleComparisonComp D f' g).symm ≪≫
    eqToIso (congrArg (cbcProEtaleComparisonPullback D) sq.w.symm) ≪≫
      cbcProEtaleComparisonComp D g' f

/-- The comparison inverse image, constructed by left Kan extension and sheafification.
It is definitionally `comparisonUpperStar` for abelian coefficients and the left adjoint
of `Scheme.proEtaleSiteComparison` for sets.
Source: blueprint, lem-weil-pbc-comparison-pullback, proof steps 1--4;
Stacks, Tags 00WX and 0B65 (blueprint: lem-weil-pbc-comparison-pullback). -/
noncomputable abbrev cbcComparisonCoefficientPullback (X : Scheme.{u}) :=
  Functor.sheafPullbackConstruction.sheafPullback (Scheme.toProEt X) D
    X.smallEtaleTopology (Scheme.ProEt.topology X)

/-- The canonical comparison adjunction for the common coefficient category.
Source: blueprint, lem-weil-pbc-comparison-pullback, proof steps 1--4;
Stacks, Tags 00WX and 0B65 (blueprint: lem-weil-pbc-comparison-pullback). -/
noncomputable abbrev cbcComparisonCoefficientAdjunction (X : Scheme.{u}) :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (Scheme.toProEt X) D
    X.smallEtaleTopology (Scheme.ProEt.topology X)

/-- The comparison inclusion commutes with the actual chosen base change.
Source: Stacks, Tag 099R; blueprint, proof step 1
(blueprint: lem-weil-pbc-comparison-pullback). -/
noncomputable def cbcComparisonSiteBaseChangeIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Scheme.toProEt Y ⋙ MorphismProperty.Over.pullback @WeaklyEtale ⊤ f ≅
      MorphismProperty.Over.pullback @Etale ⊤ f ⋙ Scheme.toProEt X :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ by ext; simp; rfl)

/-- The canonical right-image comparison, induced by the chosen fibre products.
Its components identify sections over the same base change, including for sets.
Source: Stacks, Tags 099R and 00WX; blueprint, proof step 1
(blueprint: lem-weil-pbc-comparison-pullback). -/
noncomputable def cbcComparisonCoefficientDirectImageIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    lowerStar D f ⋙ comparisonLowerStar D Y ≅
      comparisonLowerStar D X ⋙ Etale.lowerStar D f :=
  have : (MorphismProperty.Over.pullback @Etale ⊤ f).IsContinuous
      Y.smallEtaleTopology X.smallEtaleTopology := Etale.isContinuous_overPullback f
  have := Scheme.ProEt.isContinuous_overPullback f
  have := Scheme.isContinuous_toProEt X
  have := Scheme.isContinuous_toProEt Y
  have := Functor.isContinuous_comp (Scheme.toProEt Y)
    (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f)
    Y.smallEtaleTopology (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)
  have := Functor.isContinuous_comp (MorphismProperty.Over.pullback @Etale ⊤ f)
    (Scheme.toProEt X) Y.smallEtaleTopology X.smallEtaleTopology (Scheme.ProEt.topology X)
  Functor.sheafPushforwardContinuousComp (Scheme.toProEt Y)
      (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f) D Y.smallEtaleTopology
      (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X) ≪≫
    Functor.sheafPushforwardContinuousIso (cbcComparisonSiteBaseChangeIso f) D
      Y.smallEtaleTopology (Scheme.ProEt.topology X) ≪≫
    (Functor.sheafPushforwardContinuousComp (MorphismProperty.Over.pullback @Etale ⊤ f)
      (Scheme.toProEt X) D Y.smallEtaleTopology X.smallEtaleTopology
        (Scheme.ProEt.topology X)).symm

/-- The canonical inverse-image comparison, normalized as the conjugate of
`cbcComparisonCoefficientDirectImageIso`, which evaluates on `W` as the identity on
sections over `W ×[Y] X`. This extends the inverse of
`comparisonUpperStarCompUpperStarIso` to set coefficients.
Source: blueprint, lem-weil-pbc-comparison-pullback, proof steps 1--4;
Stacks, Tags 00WX and 0B65 (blueprint: lem-weil-pbc-comparison-pullback). -/
noncomputable def cbcComparisonCoefficientPullbackIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    cbcEtaleComparisonPullback D f ⋙ cbcComparisonCoefficientPullback D X ≅
      cbcComparisonCoefficientPullback D Y ⋙ cbcProEtaleComparisonPullback D f :=
  ((conjugateIsoEquiv
    ((cbcEtaleComparisonAdjunction D f).comp (cbcComparisonCoefficientAdjunction D X))
    ((cbcComparisonCoefficientAdjunction D Y).comp (cbcProEtaleComparisonAdjunction D f))).symm
      (cbcComparisonCoefficientDirectImageIso D f).symm).symm

/-- The identity, composition and chosen Cartesian-square equations for the
canonical comparison. Equations are componentwise on every sheaf, equivalently
equalities of natural transformations. The square is the specified one, including
its commutativity transport; it is not replaced by an arbitrary isomorphism.
Source: blueprint, lem-weil-pbc-comparison-pullback, proof steps 1--4;
Stacks, Tags 00WX and 0B65 (blueprint: lem-weil-pbc-comparison-pullback). -/
abbrev cbcComparisonPullbackCoherent : Prop :=
  ComparisonPullbackCoherent D

/-- The canonical isomorphism `ν_U^* u⁻¹ ≅ u⁻¹ ν_V^*` is coherent for sets, abelian
sheaves and sheaves of modules over every finite discrete ring.
Source: blueprint, sec-proper-base-change, sk-thm-properbasechange,
lem-weil-pbc-comparison-pullback; Stacks, Tags 098T, 099R and 0B65
(blueprint: lem-weil-pbc-comparison-pullback).

Proof: (1) the etale-to-pro-etale inclusion commutes with base change: both composites
have the same fibre products and arrows. Restriction of sheaves therefore gives
`cbcComparisonCoefficientDirectImageIso`. Scalar actions are the same constant sections,
so this works in fixed-ring modules as well as sets and abelian groups.
(2) Compose the inverse-image and comparison adjunctions (`Adjunction.comp`), and
apply the unit-normalized conjugation bijection (`conjugateIsoEquiv` and
`unit_conjugateEquiv_symm`). This is exactly `cbcComparisonCoefficientPullbackIso`.
(3) For identities the right-image map is the identity after the fibre-product identity.
For composites, both right-image paths restrict along the same associativity map
`(W ×[Z] Y) ×[Y] X ≅ W ×[Z] X`, preserving the two projections. The composite Hom
bijections thus coincide; their injectivity proves the identity and composite equations.
(4) For the chosen Cartesian square, expand each square identification through the
composition comparisons and the supplied commutativity equation. Both paths on sections
identify the iterated products with `W ×[Y] X'` preserving both projections. Thus the
right-image maps agree, and injectivity of the adjunction Hom bijections proves the
specified square equation. These arguments are the node's four proof steps and retain
all identity, arbitrary-composite and chosen-square cases. -/
theorem cbcComparison_pullback_coherent :
    cbcComparisonPullbackCoherent (Type (u + 1)) ∧
      cbcComparisonPullbackCoherent AddCommGrpCat.{u + 1} ∧
      ∀ (Λ : Type (u + 1)) [Ring Λ] [Finite Λ],
        cbcComparisonPullbackCoherent (ModuleCat.{u + 1} Λ) := by
  refine ⟨comparison_pullback_coherent.1, comparison_pullback_coherent.2.1, ?_⟩
  intro Λ _ _
  exact comparison_pullback_coherent.2.2 Λ

end ProEtale
end AlgebraicGeometry
