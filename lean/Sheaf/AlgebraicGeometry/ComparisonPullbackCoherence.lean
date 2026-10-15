/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NE
-/
module

public import Sheaf.AlgebraicGeometry.ChosenCartesianSquare
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStar

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
noncomputable abbrev etaleComparisonPullback {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  Functor.sheafPullbackConstruction.sheafPullback
    (MorphismProperty.Over.pullback @Etale ⊤ f) D
    Y.smallEtaleTopology X.smallEtaleTopology

/-- The canonical inverse-image adjunction, obtained from Kan extension and sheafification.
Source: blueprint, lem-weil-pbc-comparison-pullback, proof steps 1--4;
Stacks, Tags 00WX and 0B65 (blueprint: lem-weil-pbc-comparison-pullback). -/
noncomputable abbrev etaleComparisonAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y) :
    etaleComparisonPullback D f ⊣ Etale.lowerStar D f :=
  have : (MorphismProperty.Over.pullback @Etale ⊤ f).IsContinuous
      Y.smallEtaleTopology X.smallEtaleTopology := Etale.isContinuous_overPullback f
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (MorphismProperty.Over.pullback @Etale ⊤ f) D
    Y.smallEtaleTopology X.smallEtaleTopology

/-- The identity comparison, adjoint to the canonical fibre-product identity.
Source: blueprint, lem-weil-pbc-comparison-pullback, proof steps 1--4;
Stacks, Tags 00WX and 0B65 (blueprint: lem-weil-pbc-comparison-pullback). -/
noncomputable def etaleComparisonId (X : Scheme.{u}) :
    etaleComparisonPullback D (𝟙 X) ≅ 𝟭 _ :=
  have : (MorphismProperty.Over.pullback @Etale ⊤ (𝟙 X)).IsContinuous
      X.smallEtaleTopology X.smallEtaleTopology := Etale.isContinuous_overPullback (𝟙 X)
  (conjugateIsoEquiv Adjunction.id (etaleComparisonAdjunction D (𝟙 X))).symm
    (Functor.sheafPushforwardContinuousId'
      (MorphismProperty.Over.pullbackId @Etale ⊤ X) D X.smallEtaleTopology).symm

/-- The composition comparison, adjoint to associativity of chosen fibre products.
Source: blueprint, lem-weil-pbc-comparison-pullback, proof steps 1--4;
Stacks, Tags 00WX and 0B65 (blueprint: lem-weil-pbc-comparison-pullback). -/
noncomputable def etaleComparisonComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    etaleComparisonPullback D (f ≫ g) ≅
      etaleComparisonPullback D g ⋙ etaleComparisonPullback D f :=
  have : (MorphismProperty.Over.pullback @Etale ⊤ f).IsContinuous
      Y.smallEtaleTopology X.smallEtaleTopology := Etale.isContinuous_overPullback f
  have : (MorphismProperty.Over.pullback @Etale ⊤ g).IsContinuous
      Z.smallEtaleTopology Y.smallEtaleTopology := Etale.isContinuous_overPullback g
  have : (MorphismProperty.Over.pullback @Etale ⊤ (f ≫ g)).IsContinuous
      Z.smallEtaleTopology X.smallEtaleTopology := Etale.isContinuous_overPullback (f ≫ g)
  ((conjugateIsoEquiv (etaleComparisonAdjunction D (f ≫ g))
    ((etaleComparisonAdjunction D g).comp (etaleComparisonAdjunction D f))).symm
      (Functor.sheafPushforwardContinuousComp'
        (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) f g).symm D
        Z.smallEtaleTopology Y.smallEtaleTopology X.smallEtaleTopology).symm).symm

/-- The specified square identification: compose through the equal composite morphisms.
The chosen Cartesian identification supplies the commutativity equation.
Source: blueprint, lem-weil-pbc-comparison-pullback, proof steps 1--4;
Stacks, Tags 00WX and 0B65 (blueprint: lem-weil-pbc-comparison-pullback). -/
noncomputable def etaleComparisonSquare {X' X Y' Y : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare g' f' f g) :
    etaleComparisonPullback D g ⋙ etaleComparisonPullback D f' ≅
      etaleComparisonPullback D f ⋙ etaleComparisonPullback D g' :=
  (etaleComparisonComp D f' g).symm ≪≫
    eqToIso (congrArg (etaleComparisonPullback D) sq.w.symm) ≪≫
      etaleComparisonComp D g' f

/-- The constructed proEtale inverse image for the coefficient category `D`.
For abelian coefficients this is definitionally the existing `upperStar`.
Source: blueprint, lem-weil-pbc-comparison-pullback, proof steps 1--4;
Stacks, Tags 00WX and 0B65 (blueprint: lem-weil-pbc-comparison-pullback). -/
noncomputable abbrev proEtaleComparisonPullback {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  Functor.sheafPullbackConstruction.sheafPullback
    (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f) D
    (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)

/-- The canonical inverse-image adjunction, obtained from Kan extension and sheafification.
Source: blueprint, lem-weil-pbc-comparison-pullback, proof steps 1--4;
Stacks, Tags 00WX and 0B65 (blueprint: lem-weil-pbc-comparison-pullback). -/
noncomputable abbrev proEtaleComparisonAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f) D
    (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)

/-- The identity comparison, adjoint to the canonical fibre-product identity.
Source: blueprint, lem-weil-pbc-comparison-pullback, proof steps 1--4;
Stacks, Tags 00WX and 0B65 (blueprint: lem-weil-pbc-comparison-pullback). -/
noncomputable def proEtaleComparisonId (X : Scheme.{u}) :
    proEtaleComparisonPullback D (𝟙 X) ≅ 𝟭 _ :=
  (conjugateIsoEquiv Adjunction.id (proEtaleComparisonAdjunction D (𝟙 X))).symm
    (Functor.sheafPushforwardContinuousId'
      (MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X) D (Scheme.ProEt.topology X)).symm

/-- The composition comparison, adjoint to associativity of chosen fibre products.
Source: blueprint, lem-weil-pbc-comparison-pullback, proof steps 1--4;
Stacks, Tags 00WX and 0B65 (blueprint: lem-weil-pbc-comparison-pullback). -/
noncomputable def proEtaleComparisonComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    proEtaleComparisonPullback D (f ≫ g) ≅
      proEtaleComparisonPullback D g ⋙ proEtaleComparisonPullback D f :=
  ((conjugateIsoEquiv (proEtaleComparisonAdjunction D (f ≫ g))
    ((proEtaleComparisonAdjunction D g).comp (proEtaleComparisonAdjunction D f))).symm
      (Functor.sheafPushforwardContinuousComp'
        (MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) f g).symm D
        (Scheme.ProEt.topology Z) (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).symm).symm

/-- The specified square identification: compose through the equal composite morphisms.
The chosen Cartesian identification supplies the commutativity equation.
Source: blueprint, lem-weil-pbc-comparison-pullback, proof steps 1--4;
Stacks, Tags 00WX and 0B65 (blueprint: lem-weil-pbc-comparison-pullback). -/
noncomputable def proEtaleComparisonSquare {X' X Y' Y : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare g' f' f g) :
    proEtaleComparisonPullback D g ⋙ proEtaleComparisonPullback D f' ≅
      proEtaleComparisonPullback D f ⋙ proEtaleComparisonPullback D g' :=
  (proEtaleComparisonComp D f' g).symm ≪≫
    eqToIso (congrArg (proEtaleComparisonPullback D) sq.w.symm) ≪≫
      proEtaleComparisonComp D g' f

/-- The comparison inverse image, constructed by left Kan extension and sheafification.
It is definitionally `comparisonUpperStar` for abelian coefficients and the left adjoint
of `Scheme.proEtaleSiteComparison` for sets.
Source: blueprint, lem-weil-pbc-comparison-pullback, proof steps 1--4;
Stacks, Tags 00WX and 0B65 (blueprint: lem-weil-pbc-comparison-pullback). -/
noncomputable abbrev comparisonCoefficientPullback (X : Scheme.{u}) :=
  Functor.sheafPullbackConstruction.sheafPullback (Scheme.toProEt X) D
    X.smallEtaleTopology (Scheme.ProEt.topology X)

/-- The canonical comparison adjunction for the common coefficient category.
Source: blueprint, lem-weil-pbc-comparison-pullback, proof steps 1--4;
Stacks, Tags 00WX and 0B65 (blueprint: lem-weil-pbc-comparison-pullback). -/
noncomputable abbrev comparisonCoefficientAdjunction (X : Scheme.{u}) :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (Scheme.toProEt X) D
    X.smallEtaleTopology (Scheme.ProEt.topology X)

/-- The canonical inverse-image comparison, normalized as the conjugate of
`lowerStarCompComparisonLowerStarIso`, which evaluates on `W` as the identity on
sections over `W ×[Y] X`. This extends the inverse of
`comparisonUpperStarCompUpperStarIso` to set coefficients.
Source: blueprint, lem-weil-pbc-comparison-pullback, proof steps 1--4;
Stacks, Tags 00WX and 0B65 (blueprint: lem-weil-pbc-comparison-pullback). -/
noncomputable def comparisonCoefficientPullbackIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    etaleComparisonPullback D f ⋙ comparisonCoefficientPullback D X ≅
      comparisonCoefficientPullback D Y ⋙ proEtaleComparisonPullback D f :=
  ((conjugateIsoEquiv
    ((etaleComparisonAdjunction D f).comp (comparisonCoefficientAdjunction D X))
    ((comparisonCoefficientAdjunction D Y).comp (proEtaleComparisonAdjunction D f))).symm
      (lowerStarCompComparisonLowerStarIso f D).symm).symm

/-- The identity, composition and chosen Cartesian-square equations for the
canonical comparison. Equations are componentwise on every sheaf, equivalently
equalities of natural transformations. The square is the specified one, including
its commutativity transport; it is not replaced by an arbitrary isomorphism.
Source: blueprint, lem-weil-pbc-comparison-pullback, proof steps 1--4;
Stacks, Tags 00WX and 0B65 (blueprint: lem-weil-pbc-comparison-pullback). -/
def ComparisonPullbackCoherent : Prop :=
  (∀ (X : Scheme.{u}) (F : Sheaf X.smallEtaleTopology D),
    (comparisonCoefficientPullbackIso D (𝟙 X)).hom.app F ≫
        (proEtaleComparisonId D X).hom.app ((comparisonCoefficientPullback D X).obj F) =
      (comparisonCoefficientPullback D X).map ((etaleComparisonId D X).hom.app F)) ∧
  (∀ (X Y Z : Scheme.{u}) (f : X ⟶ Y) (g : Y ⟶ Z)
      (F : Sheaf Z.smallEtaleTopology D),
    (comparisonCoefficientPullback D X).map ((etaleComparisonComp D f g).hom.app F) ≫
        (comparisonCoefficientPullbackIso D f).hom.app ((etaleComparisonPullback D g).obj F) ≫
        (proEtaleComparisonPullback D f).map ((comparisonCoefficientPullbackIso D g).hom.app F) =
      (comparisonCoefficientPullbackIso D (f ≫ g)).hom.app F ≫
        (proEtaleComparisonComp D f g).hom.app ((comparisonCoefficientPullback D Z).obj F)) ∧
  (∀ (X' X Y' Y : Scheme.{u}) (g' : X' ⟶ X) (f' : X' ⟶ Y')
      (f : X ⟶ Y) (g : Y' ⟶ Y) (sq : ChosenCartesianSquare g' f' f g)
      (F : Sheaf Y.smallEtaleTopology D),
    (comparisonCoefficientPullbackIso D f').hom.app ((etaleComparisonPullback D g).obj F) ≫
        (proEtaleComparisonPullback D f').map ((comparisonCoefficientPullbackIso D g).hom.app F) ≫
        (proEtaleComparisonSquare D sq).hom.app ((comparisonCoefficientPullback D Y).obj F) =
      (comparisonCoefficientPullback D X').map ((etaleComparisonSquare D sq).hom.app F) ≫
        (comparisonCoefficientPullbackIso D g').hom.app ((etaleComparisonPullback D f).obj F) ≫
        (proEtaleComparisonPullback D g').map ((comparisonCoefficientPullbackIso D f).hom.app F))

/-- The canonical isomorphism `ν_U^* u⁻¹ ≅ u⁻¹ ν_V^*` is coherent for sets, abelian
sheaves and sheaves of modules over every finite discrete ring.
Source: blueprint, sec-proper-base-change, sk-thm-properbasechange,
lem-weil-pbc-comparison-pullback; Stacks, Tags 098T, 099R and 0B65
(blueprint: lem-weil-pbc-comparison-pullback).

Proof: (1) the etale-to-pro-etale inclusion commutes with base change: both composites
have the same fibre products and arrows. Restriction of sheaves therefore gives
`lowerStarCompComparisonLowerStarIso`. Scalar actions are the same constant sections,
so this works in fixed-ring modules as well as sets and abelian groups.
(2) Compose the inverse-image and comparison adjunctions (`Adjunction.comp`), and
apply the unit-normalized conjugation bijection (`conjugateIsoEquiv` and
`unit_conjugateEquiv_symm`). This is exactly `comparisonCoefficientPullbackIso`.
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
theorem comparison_pullback_coherent :
    ComparisonPullbackCoherent (Type (u + 1)) ∧
      ComparisonPullbackCoherent AddCommGrpCat.{u + 1} ∧
      ∀ (Λ : Type (u + 1)) [Ring Λ] [Finite Λ],
        ComparisonPullbackCoherent (ModuleCat.{u + 1} Λ) := by
  sorry

end ProEtale
end AlgebraicGeometry
