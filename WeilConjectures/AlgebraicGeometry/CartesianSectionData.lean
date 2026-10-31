/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FiniteAdjunctionDiagramRealization
public import WeilConjectures.AlgebraicGeometry.SystemInternalHomRepresentability
public import WeilConjectures.AlgebraicGeometry.SystemAdjunctionTransposeCoherence

/-! # Definition interface for cartesian-section adjunctions

Source: the ordinary-system refinement of the middle RHom calculation and final
unit/counit paragraph of `prop-coef-integral-exceptional-adjoint`; current blueprint,
`lem-coef-finite-exceptional.proof`, paragraphs 2--3
(blueprint: def-coef-cartesian-section-data).

This module publicly re-exports the existing definitions, without asserting their
existence theorems: `FiniteAdjunctionDiagram.Enriched`,
`FiniteAdjunctionDiagram.Realization.mappingSource` and `mappingTarget`,
`FiniteAdjunctionDiagram.finiteMappingSource` and `finiteMappingTarget`,
`SystemInternalHom.Representability`, `coefficients`, `Et`,
`SystemInternalHom.ComparisonImage.P`, `R` and `derivedAdjunction`, and
`SemilinearSections.SystemTensorTransposeCoherence`.
The abbreviation below exposes the comparison presentation under this definition
interface. It is definitionally the existing structure, with no new data or choice.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

namespace WeilConjectures.CartesianSectionData

/-- The existing ordinary etale/pro-etale internal-Hom comparison presentation,
re-exported with exactly its original parameters and fields. This defines the type
of comparison data; it makes no assertion that the type is inhabited.
Source: ordinary-system RHom calculation, Zheng Lemma 4.10, Stacks 08J9 and 0D6E
(blueprint: def-coef-cartesian-section-data). -/
abbrev Representability
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {W s : Scheme.{u}} (a : W ⟶ s) :=
  SystemInternalHom.Representability l E a

end WeilConjectures.CartesianSectionData
