/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O3
-/
module

public import Sheaf.Paper.PbcWeilCoefficientComparison
public import Sheaf.Paper.ConstantCoefficientScalarNormalization

/-! # Canonical constant-object maps as Weil maps

Source: blueprint constant coefficients, order 1869
(blueprint: lem-weil-constant-weil-structure-stage-independence).
The former recorded module was deleted. This interface retains the normalized
constant-object arrow; it does not introduce an unrelated constant-line isomorphism.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genInjectivity false
set_option backward.isDefEq.respectTransparency true
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory.Endofunctor
namespace WeilConjectures
variable (D : FiniteFieldDatum.{u}) (c : D.CoefficientDatum)
  (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]

/-- The canonical scalar arrow is Frobenius-equivariant, with exactly its strict-cone
normalization from the coefficient-object node.
Source: node clause 1 (blueprint: lem-weil-constant-weil-structure-stage-independence).
Proof: compare the two maps before taking the strict derived limit. At every positive
quotient they send the constant unit to the same tensor of units. Both shifted cone
components are zero. Projection uniqueness gives equality of the chain maps. Their
localizations give the Weil square; faithful forgetting proves uniqueness. -/
theorem constantWeilStageScalar_existsUnique
    {E L : Padic.FiniteCoefficientFields c.l c.Qbar} (h : E ≤ L) :
    ∃! a : (constantTwistSfScalar D c X₀ h).obj
          (constantWeilRationalComplex c.l (pbcFiniteField.{u} c.l c.Qbar E)
            D c.different X₀) ≅
        constantWeilRationalComplex c.l (pbcFiniteField.{u} c.l c.Qbar L)
          D c.different X₀,
      HEq a.hom.hom.f
        (constantCoefficientRationalScalarIso c.l
          (pbcFiniteField.{u} c.l c.Qbar E) (pbcFiniteField.{u} c.l c.Qbar L)
          (pbcFiniteFieldInclusion c.l c.Qbar h) (D.geometricFiber X₀).left
          D c.different).hom := by
  sorry

/-- The normalized scalar-extension isomorphism on constant Weil pairs.
Source: node clause 1 (blueprint: lem-weil-constant-weil-structure-stage-independence). -/
def constantWeilStageScalar
    {E L : Padic.FiniteCoefficientFields c.l c.Qbar} (h : E ≤ L) :=
  (constantWeilStageScalar_existsUnique D c X₀ h).exists.choose

/-- The base coefficient field is the least finite subextension.
Source: node clause 2 (blueprint: lem-weil-constant-weil-structure-stage-independence).
Proof: the least field is the bottom intermediate field, which is contained in E. -/
theorem constantWeilBase_le (l : ℕ) [Fact l.Prime]
    (Q : Type u) [Field Q] [Algebra ℚ_[l] Q]
    (E : Padic.FiniteCoefficientFields l Q) : Padic.finiteCoefficientBase l Q ≤ E := by
  sorry

/-- Constant objects at every finite stage give the same common-stage Weil sheaf;
the forgetful normalization is the actual stage-inclusion scalar arrow.
Source: node clause 2 (blueprint: lem-weil-constant-weil-structure-stage-independence).
Proof: include the canonical scalar map from the least Q_l stage to E. The
constant-stage scalar theorem makes it a Weil map. Its inverse and the stage
transition identification give the common-stage isomorphism. Forgetting retains
precisely the same coefficient map. All maps are formed from the specified scalar
alpha, so the statement retains compatibility with forgetting. -/
theorem constantWeilStage_common
    (E : Padic.FiniteCoefficientFields c.l c.Qbar) :
    ∃ e : sfWeilStageObject D c.l c.different X₀ c.Qbar E
        (constantWeilRationalComplex c.l (pbcFiniteField.{u} c.l c.Qbar E)
          D c.different X₀) ≅ constantWeilAlgebraicallyClosedComplex c.l D
            c.different X₀ c.Qbar,
      HEq e.hom
        (((constantTwistSfInclusion D c X₀ E).map
            (constantWeilStageScalar D c X₀
              (constantWeilBase_le c.l c.Qbar E)).inv) ≫
          (constantTwistSfTransition D c X₀
            (constantWeilBase_le c.l c.Qbar E)).hom.app
              (constantWeilRationalComplex c.l
                (pbcFiniteField.{u} c.l c.Qbar (Padic.finiteCoefficientBase c.l c.Qbar))
                D c.different X₀)) := by
  sorry

end WeilConjectures
