module

public import Sheaf.Paper.SmoothOperationIdentificationSpecification
public import Sheaf.Paper.PurFrameworkPbcCoefficientCategoryComparison
public import Sheaf.Paper.RationalScalarComparisonIdentification
public import Sheaf.Paper.PbcDescentFunctors
import Sheaf.Paper.CommonStageSmoothOperationCore
import Sheaf.Paper.CommonStageSmoothOperationShift
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Whiskering

/-! # Identification of smooth operations on common coefficient stages

Source: smooth-purity transport, Step 2, common-stage morphisms and inverse equations
(blueprint: lem-pur-common-stage-smooth-operation-identification).

The finite PBC operations are the specified localized integral operations transported
through the identity coefficient-presentation equivalences. The conclusion fixes
all comparison components, representative actions, shifts and transformation equations.
-/

@[expose] public noncomputable section
set_option Elab.async false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u v w z
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
  AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.CommonStageSmoothOperationIdentification
set_option allowUnsafeReducibility true
attribute [local irreducible] HasDerivedCategory.standard stageEquivalence
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (D : FiniteFieldDatum.{max u v}) (hl : l ≠ D.p)
  {X Y : Scheme.{max u v}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [sepX : IsSeparated (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [sepY : IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (d : ℕ) [smooth : SmoothOfRelativeDimension d f]
  (S : ConstructibleExceptionalCoefficients.System.{u, v} l Ω D hl (f := f))
  [IsNoetherian X] [IsNoetherian Y]
  [dX : Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
  [dY : Fact (∃ n : ℕ, topologicalKrullDim Y ≤ n)]
  [iX : Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
  [iY : Fact (∀ y : Y, IsUnit (l : Y.presheaf.stalk y))]
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]
  (JX : FdCoefficientComparison l Ω X) (JY : FdCoefficientComparison l Ω Y)

attribute [local irreducible] finiteOperation commonOperation
  conjugate conjugateIso pbcOperation finiteComparison strictComparison objectComparison

include sepX sepY smooth in
/-- The framework operations are the ordinary PBC descents through canonical J.
Source: smooth-purity transport Step 2
(blueprint: lem-pur-common-stage-smooth-operation-identification).

Proof plan:
1. Use lem-pur-framework-pbc-coefficient-category-comparison on X and Y; J and
its inverse scalar comparison j are the normalized chi comparisons.
2. Normalize the actual source object using commonSourceComparison, retaining the
completeness self-extension unitors and both tensor presentation maps. The
exceptional object comparison is the inverse common coefficient comparison of S.
3. Compose the pullback, twist and shift mixed squares, using
lem-pur-framework-pbc-pullback-scalar-bridge, lem-weil-integral-twist-derived-scalar
and lem-weil-point-completed-scalar-shift. The result is the source mixed square.
4. For the exceptional square use lem-pur-etale-coefficient-system-adjoint and
lem-pur-etale-system-scalar-mate-coherence: both sides are the same counit
transpose. Transport along the actual compact-support comparison and chi;
injectivity of the adjunction Hom bijection gives equality of the maps.
5. The ordinary comparisons satisfy the unit, associator and shift equations by
lem-pur-rational-scalar-comparison-identification. Apply prop-weil-pbc-descent-functors.
6. On an arbitrary unequal-field representative conjugate J(u) by j at both ends.
Insert the two mixed squares and naturality of r. Adjacent inverse comparisons
cancel, giving the displayed representative action and the normalized R components.
7. Expand the associator cocycle to check enlargement: tr(mapAt(u)) = mapAt(tr(u)).
Common-stage equality gives representative independence. The same identities for
shifts prove exactness and the specified commutation squares.
8. For a compatible theta use its coefficient square at the source field,
naturality at the common-field arrow, and its coefficient square at the target.
This descends [E,theta], and fully faithful J gives the displayed finite conjugate.
9. Composition and identity at the single stage E preserve every equation.
Apply this to both inverse equations and use faithfulness of J on the common
category. No transition functor is assumed faithful. -/
theorem commonStageSmoothOperationIdentification : Result l Ω D hl f d S JX JY := by
  unfold Result
  obtain ⟨H, G, RH, RG, hH, hG, hRX, hRY, hθ, htransport⟩ :=
    commonStageSmoothOperationCore l Ω D hl f d S JX JY
  obtain ⟨hS, gS, hP, gP, hshift⟩ :=
    commonStageSmoothOperationShift l Ω D hl f d S JX JY H G RH RG
  exact ⟨H, G, RH, RG, hH, hG, hRX, hRY, hθ, htransport,
    hS, gS, hP, gP, hshift⟩

end WeilConjectures.CommonStageSmoothOperationIdentification
