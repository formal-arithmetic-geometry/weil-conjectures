/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficientReference
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficientQuotients
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficientFamilyPullback

import WeilConjectures.AlgebraicGeometry.DiagonalNonTorsionBaseChange
import WeilConjectures.AlgebraicGeometry.DiagonalQuotientBaseChange
import WeilConjectures.AlgebraicGeometry.DiagonalBaseSquares
import WeilConjectures.AlgebraicGeometry.DiagonalCompletedDiagramRealization
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficientFamilyExtension
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficientUniformizerReduction
import WeilConjectures.AlgebraicGeometry.DiagonalUniformizerAnnihilator
import WeilConjectures.AlgebraicGeometry.DiagonalFiniteRootMap

import WeilConjectures.AlgebraicGeometry.DiagonalTowerSystem
import WeilConjectures.AlgebraicGeometry.DiagonalTowerTrace
import WeilConjectures.AlgebraicGeometry.CompletedCondensedCoefficients

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
  obtain ⟨tq, t₁, t₂, hq, h₁, h₂, a₁, a₂, hi₁, hi₂⟩ :=
    diagonalTower_trace l k p _hpl Y hY D _hcompletion _hsystem δ _hδ
  obtain ⟨d, hd⟩ := diagonalCompletedDiagram_realization l Y hY δ
    tq t₁ t₂ hq h₁ h₂ a₁ a₂ hi₁ hi₂
  obtain ⟨family, hfamily⟩ := diagonalCoefficientFamily_extension l Y hY d
  obtain ⟨reference⟩ := hd family hfamily
  refine ⟨family, ⟨reference⟩, ?_⟩
  intro E π hπ n
  have hfinite : Finite (ULift.{u + 1} (completedResidue l E π n)) := by
    let := (completedCondensedIntegral Y l E π hπ).2.1 n
    infer_instance
  have hYpow : IsUnit ((l ^ (n + 1) : ℕ) : Γ(Y, ⊤)) := by
    simpa only [Nat.cast_pow] using hY.pow (n + 1)
  have hWpow := diagonalSurface_power_unit l Y hY n
  have hPpow : IsUnit ((l ^ (n + 1) : ℕ) : Γ(ProjectiveLine Y, ⊤)) := by
    simpa using (hY.map (ProjectiveLine Y ↘ Y).appTop.hom).pow (n + 1)
  obtain ⟨rootsP⟩ := diagonalFiniteRoots_exists (ProjectiveLine Y)
    (l ^ (n + 1)) (pow_pos (Fact.out : l.Prime).pos _) hPpow
  obtain ⟨rootsW⟩ := diagonalFiniteRoots_exists (diagonalSurface Y)
    (l ^ (n + 1)) (pow_pos (Fact.out : l.Prime).pos _) hWpow
  obtain ⟨d, hscalar, hc⟩ :=
    diagonalCoefficient_uniformizerFiniteComparison l Y hY D _hcompletion _hsystem
      δ _hδ family reference E π hπ n hfinite
      (diagonalUniformizer_annihilator l E π hπ n) hYpow hWpow rootsP rootsW
  exact ⟨d, hscalar, hc⟩

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
  obtain ⟨c⟩ := diagonalCoefficient_nonTorsionBaseChange l k p _hpl Y Y' g hY hY'
    D _hcompletion _hsystem D' _hcompletion' _hsystem' δ δ' _hδ _hδ'
    (diagonalBaseSquares g) family family' _reference _reference'
  let := c.invertibleP
  let := c.invertibleP'
  let := c.invertibleW
  let := c.invertibleW'
  exact ⟨{
    rootsP := c.rootsP, rootsW := c.rootsW
    zl := c.zl, integral := c.integral, rational := c.rational, closure := c.closure
    quotients := fun E π hπ n d d' h h' ↦
      diagonalCoefficient_quotientBaseChange l g family family' E (c.integral E)
        π hπ n d d' h h' }⟩

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
