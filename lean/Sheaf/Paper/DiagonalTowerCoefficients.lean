/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N8
-/
module

public import Sheaf.Paper.DiagonalCoefficientReference
public import Sheaf.Paper.DiagonalCoefficientQuotients
public import Sheaf.Paper.DiagonalCoefficientFamilyPullback

import Sheaf.AlgebraicGeometry.BoundedContinuityDirectImage
import Sheaf.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage
import Sheaf.Paper.DiagonalTowerLimit
import Sheaf.Paper.DiagonalTowerSystem
import Sheaf.Paper.DiagonalTowerTrace
import Sheaf.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit
import Sheaf.AlgebraicGeometry.ProEtaleCoefficientComparisonsPullback
import Sheaf.AlgebraicGeometry.ProEtaleAbelianClosedSupport
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.AlgebraicGeometry.GeoCartierCycleClass
import Sheaf.AlgebraicGeometry.GeoP1Cohomology
import Sheaf.Paper.CartesianCoefficients
import Sheaf.Paper.CompletedCondensedCoefficients

import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf

/-! # Change of coefficients and base change for the diagonal class

Source: blueprint main-20261015, sk-prop-diagonal-tower-coefficients.
(blueprint: det-prop-diagonal-tower-coefficients).

## Main statements

- `diagonalTower_coefficients`: coefficient extension and every finite reduction.
- `diagonalTower_coefficients_baseChange`: compatibility with geometric base change.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

/-- Extension to every integral finite-extension coefficient, every positive
uniformizer quotient, rational coefficients and the finite-extension-valued
algebraic closure preserves the diagonal class, its traces and both integration
identities.

Source: blueprint main-20261015, sec-six-functors-basics,
sk-prop-diagonal-tower/sk-prop-diagonal-tower-coefficients.md, clauses 1--2
(blueprint: det-prop-diagonal-tower-coefficients).

Proof: A finite free Z_l-basis of O_E identifies scalar extension with a finite
biproduct functor. It is exact, commutes with products and hence with the cone
of 1-shift computing the specified derived inverse limit. Additive derived
direct images preserve that same finite biproduct, so the canonical scalar mate
is invertible on the unit and positive Tate objects. Transport the whole-system
limit class and the three completed unit/Chern traces, including their two
integration equalities. For every pi^(n+1) quotient, choose r with ell^(r+1)
killing it, using ell = unit times pi^e. First reduce the whole coherent class
and trace system modulo ell^(r+1), then extend coefficients to this quotient.
The positive Cartier roof is compatible with this scalar map. The finite trace
is inverse to the unit/Chern biproduct splitting followed by the constant
summand projection; this construction commutes with coefficient extension.
This identifies every uniformizer quotient, without restricting to cofinal
levels. For localization and the filtered system of finite subextensions,
the unit and shifted lines have the common lower bound -2. The projections
q,p1,p2 are qcqs, as verified by the standard two affine charts and affine
overlap of a relative projective line. Bounded continuity of direct image and
exactness of filtered colimits of abelian sheaves identify their canonical
colimit/direct-image maps. Apply these actual functors to the arrows and
composites to obtain the rational and closure stages, preserving both identities.
The endpoint comparisons are fixed by their adjunctions, unit projections and
root projections; they are precisely the comparisons in Family and Reference. -/
theorem diagonalTower_coefficients (l : ℕ) [Fact l.Prime]
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (_hpl : p ≠ l)
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    [IsNoetherian Y] [IsNoetherian (ProjectiveLine Y)] [IsNoetherian (diagonalSurface Y)]
    (hY : IsUnit (l : Γ(Y, ⊤)))
    [DiagonalTraceLocalizations l Y]
    [DiagonalTraceLocalizations l (ProjectiveLine Y)]
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (D : DiagonalDerivedReduction l (diagonalScalarExtension l (diagonalSurface Y)))
    (_hcompletion : DiagonalCompletionSpec l (diagonalSurface Y) D)
    (_hsystem : DiagonalCycleSystemSpec l Y hY D)
    (δ : diagonalCompletedDomain l Y ⟶ diagonalCompletedCodomain l Y)
    (_hδ : DiagonalTrace.IsDiagonalLimit l Y hY D δ) :
    ∃ family : Family l Y, Nonempty (Reference l Y δ family) ∧ FiniteReductions l Y family := by
  sorry

/-- Every separated finite-type base change in the standing setting pulls the
specified diagonal classes and traces to the corresponding primed morphisms at
all coefficient stages, including every positive uniformizer quotient.

Source: blueprint main-20261015, sec-six-functors-basics,
sk-prop-diagonal-tower/sk-prop-diagonal-tower-coefficients.md, clause 3
(blueprint: det-prop-diagonal-tower-coefficients).

Proof: The diagonal has equation a-b on the charts meeting it, and the standard
section has equation t. These equations remain nonzerodivisors over every base
ring, including under nonflat base change. Pull the Cartier two-term roof using
the units map u to g*u and the positive generator t^-1 to (g*t)^-1. These maps
glue and preserve the quotient generator +1. Exact inverse image and the
canonical derived-tensor comparison give a diagram of entire coefficient
systems: the free resolution has transitions ell in degree -1 and identity in
degree zero, so the induced root transitions remain zeta to zeta^ell.
Closed-support base change identifies the supported source by the actual
Beck--Chevalley mate. For the specified source and twist towers, repleteness
kills higher inverse limits and their degree-zero limits are the coefficient
unit and root line; the projection-normalized limit/pullback maps are therefore
isomorphisms. This argument concerns these two systems only. Pulling the
unit/Chern splitting square gives equality of its actual maps. Taking inverses
and the constant summand projection proves the trace square, and pulling the
diagonal roof proves the class square. Finite free extension, localization and
filtered finite-field colimits commute with these constructions by the recorded
coefficient pullback comparisons. The rational comparison is normalized on the
balanced tensor generators, the closure comparison on all finite-field legs,
and each quotient comparison on the same integral-root tensor generators.
Thus the arrows are precisely the canonical mates and root comparisons recorded
in FamilyPullback; both integration identities pull back with their composites. -/
theorem diagonalTower_coefficients_baseChange (l : ℕ) [Fact l.Prime]
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (_hpl : p ≠ l)
    (Y Y' : Scheme.{u}) [Y.Over (Spec (.of k))] [Y'.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y' ↘ Spec (.of k))] [QuasiCompact (Y' ↘ Spec (.of k))]
    [IsSeparated (Y' ↘ Spec (.of k))]
    [IsNoetherian Y] [IsNoetherian (ProjectiveLine Y)] [IsNoetherian (diagonalSurface Y)]
    [IsNoetherian Y'] [IsNoetherian (ProjectiveLine Y')] [IsNoetherian (diagonalSurface Y')]
    (g : Y' ⟶ Y) [g.IsOver (Spec (.of k))]
    [LocallyOfFiniteType g] [QuasiCompact g] [IsSeparated g]
    (hY : IsUnit (l : Γ(Y, ⊤))) (hY' : IsUnit (l : Γ(Y', ⊤)))
    [DiagonalTraceLocalizations l Y]
    [DiagonalTraceLocalizations l (ProjectiveLine Y)]
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    [DiagonalTraceLocalizations l Y']
    [DiagonalTraceLocalizations l (ProjectiveLine Y')]
    [DiagonalTraceLocalizations l (diagonalSurface Y')]
    (D : DiagonalDerivedReduction l (diagonalScalarExtension l (diagonalSurface Y)))
    (_hcompletion : DiagonalCompletionSpec l (diagonalSurface Y) D)
    (_hsystem : DiagonalCycleSystemSpec l Y hY D)
    (D' : DiagonalDerivedReduction l (diagonalScalarExtension l (diagonalSurface Y')))
    (_hcompletion' : DiagonalCompletionSpec l (diagonalSurface Y') D')
    (_hsystem' : DiagonalCycleSystemSpec l Y' hY' D')
    (δ : diagonalCompletedDomain l Y ⟶ diagonalCompletedCodomain l Y)
    (δ' : diagonalCompletedDomain l Y' ⟶ diagonalCompletedCodomain l Y')
    (_hδ : DiagonalTrace.IsDiagonalLimit l Y hY D δ)
    (_hδ' : DiagonalTrace.IsDiagonalLimit l Y' hY' D' δ')
    (family : Family l Y) (family' : Family l Y')
    (_reference : Reference l Y δ family) (_reference' : Reference l Y' δ' family') :
    Nonempty (FamilyPullback l g family family') := by
  sorry

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
