/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A7
-/
module

public import Sheaf.Paper.ConstantExtensionSheetHeartData
import Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage
import Sheaf.Paper.IsomorphismDerivedPullback
import Sheaf.Paper.IsomorphismFieldTransport
import Sheaf.Paper.FiniteClopenDerivedDecomposition
import Sheaf.Paper.IntegralFinitePullbackComposition
import Sheaf.Paper.IntegralPullbackComposition
import Sheaf.Paper.PullbackIdentitiesScalarExtension

/-! # Finite, integral and rational sheet equivalences

Source: Deligne, Weil II, pp. 150--152; Stacks Project, Tags 04TS and 0D6D.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (m : ℕ) (hm : 1 ≤ m)
variable (X₀ : Over (Spec (.of D.k₀)))
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]

variable (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)

/-- Canonical cyclic-sheet pullbacks give compatible coefficient-stage equivalences.
Source: Deligne, Weil II, pp. 150--152; Stacks Project, Tags 04TS and 0D6D
(blueprint: lem-zl-constant-extension-sheet-coefficient-equivalences).

Proof: write each canonical sheet map as its coordinate isomorphism followed by
its clopen inclusion using G.factor. Restriction to the disjoint clopen cover is
an equivalence of module-sheaf categories, with inverse gluing the component
sheaves by zero outside their components. The same inverse acts termwise on
complexes, giving the finite and integral derived decompositions. Termwise
restriction computes cohomology componentwise, so bounded constructibility and
both standard cohomological inequalities hold precisely on every component.
Reindexing along each coordinate isomorphism and its inverse gives exact inverse
functors, and the isomorphism-transport theorem identifies these with the actual
derived pullbacks. The specified composition isomorphisms therefore identify the
composite product equivalence with the actual canonical sheet pullbacks.
Restricting both inverse functors to their degree-zero carriers gives the heart
functor and its factorization equality; an equivalence preserves finite limits
and colimits, and each component is the corresponding exact restriction.
Reduction modulo every coefficient ideal and every quotient map commutes with
restriction and these termwise isomorphism transports, giving the reduction and
quotient comparisons. Rationalization descends the integral equivalence and the
scalar squares. The rational standard classes are isomorphism closures of the
integral ones, so both halves, hearts, and cohomology comparisons descend too.
For scalar extension use the published integral pullback-scalar comparison and
its rational image themselves; their normalization clauses are then reflexive,
including identity extensions. The scalar-compositor law proves compatibility
with the preceding geometric factorization. Empty fibres give zero categories;
for m=1 this is just transport along a scheme isomorphism. -/
theorem constantExtensionSheetCoefficientEquivalences (G : ZlSheetGeometry D m hm X₀) :
    ZlSheetCoefficientClauses D m hm X₀ l hl := by sorry

end WeilConjectures
