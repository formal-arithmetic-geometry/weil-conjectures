## What changed

Proved `WeilConjectures.SixFunctors.integral_models_generators` in
`Sheaf.SixFunctors.IntegralModelsGenerators`, retaining its entire signature and all
original public instance signatures. Added proved private helpers for finite
cone induction, lattice coefficient transport, flat extension by zero, ordinary and
derived scalar comparison, and the specified fixed-scalar finite realization.
Updated the existing generator node's proof and dependencies to match this argument.
No other library module is changed.

Refactored `integralReductionHasEtaleOrigin` by sharing the complex, quotient ring, and
derived reduction, and elaborating derived scalar extension over abstract ring objects.
A compiled universal equality check proves the original and new definitions equal by
`rfl`. The coefficient monoid instance is also computed directly by
`Functor.monObjObj`, with its original value universally equal by `rfl`; all remaining
public definitions are unchanged. In the same profiling process the
old definition took 15.9 seconds and the new one 6.0 seconds. This addresses the actual
60-second timeout of the original full delivery without raising the limit. The change
record is `coord/changes/W4-integral-model-reduction-elaboration.md`.
`tools/downstream.py --uses` and source inspection found only the unchanged
`Sheaf.Paper.IntegralModels` statement as an external direct user; no adaptation is
required because the predicate is definitionally identical.
The coefficient-instance optimization reduced the twenty-helper reduction compilation
from 49.4 to 37.6 seconds, and its consumer check found no external textual references.
Its record is `coord/changes/W4-integral-model-coefficient-monoid.md`; implicit instance
users retain exactly the original value by definitional equality. Both records now list
all 64 downstream modules in the final shared snapshot.

The finite-extension argument follows coefficient-heart generation and the existing
lattice-subquotient filtration; it does not assume a global lattice. The algebraic
closure clause descends to one finite field before transporting the construction.
For reductions, flatness is proved by complementary open/closed restriction, and
scalar extension commutes with extension by zero via support identities. The finite
realization keeps the same underlying sheaf, is exact, and satisfies the existing
finite-ring constructible derived-origin criterion.

A private irreducible predicate shares the locally closed lisse-extension condition
between the lattice argument and the generic generation argument. This avoids kernel
normalization of two fully expanded derived coefficient function types. It has a real
defining formula, and both uses explicitly unfold that formula when proving it. Local
transparency settings and retained let bindings keep the coefficient objects shared.
The complete diagnostic module compiled in 33.5 seconds; the final module, with normal
lint checks enabled, compiled cleanly in 25.8 seconds. Both used the original 60-second
limit, with no file or proof split.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.SixFunctors.integral_models_generators`
(node `det-lem-integral-models-generators`). All three clauses are proved from existing
library declarations. No new public theorem, node, or sorry is added. Zero holes remain
in the delivered module. Existing holes in imported dependencies remain their own items; the established
coefficient-heart generation and finite-descent theorems are reused without alteration.

## No longer needed

Removed these direct proof imports:

- `Sheaf.AlgebraicGeometry.ProEtaleBoundedConstructible`
- `Sheaf.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale`
- `Sheaf.AlgebraicGeometry.ConstructibleProEtaleClassical`
- `Sheaf.AlgebraicGeometry.IntegralConstantCompletion`
- `Sheaf.AlgebraicGeometry.LocallyClosedExtensionCoherence`
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`
- `Sheaf.Paper.CoefficientHeartCommonStratification`
- `Sheaf.Paper.CoefficientHeartFiltration`
- `Sheaf.Paper.IntegralModelsOperations`
- `Sheaf.Paper.PadicIntegersInvertEll`
- `Sheaf.Paper.StratifiedLattice`

The item no longer directly depends on `det-lem-integral-models-operations`,
`det-prop-integral-criterion-constant-coefficients`,
`lem-sfb-locally-free-derived-scalars`,
`lem-sfb-locally-closed-extension-coherence`, or
`det-pe-constructible-comparison-classical`. The first two and the general locally
free derived-scalar lemma are replaced here by a direct flat-single/support argument;
the finite classical comparison is supplied by the already proved finite-ring
constructible derived-origin theorem. Removed the obsolete top-level `tool_uses`
entries for locally closed extension coherence and classical comparison, preserving
all other approval entries in order.

The generic finite-level theorem attached to `def-weil-l-adic-coefficient-extension`
is not used for these specified quotients. Their finiteness is the Mathlib leaf
`lem-weil-valued-dvr-finite-quotients`, applied through the proved
`PadicAlgCl.finite_quotient_maximalIdeal_pow` instance.

The stratified-lattice, common-stratification, filtration, and rationalization theory
is still needed transitively by the lattice-subquotient node; these imports are
removed only from this module. No module is withdrawn, and no source-tree declaration
is removed. The integral-models unit's operations steps remain assigned to its existing
realized nodes; this proof does not replace those unit steps.

## Where the brief, the DAG or earlier work was wrong

The original Lean docstring described an older eight-step proof while the current
node had six steps. Both now describe the actual argument. The lattice theorem uses
universe-polymorphic coefficients with the spectral norm, whereas this item specifies
a small finite intermediate field; the proof supplies the missing ULift and norm
comparison explicitly. The fixed-scalar realization in the statement is respected:
it is compared on underlying sheaves, rather than replaced by an arbitrarily chosen
coefficient equivalence. Residue finiteness uses the source library's proved
maximal-ideal-power quotient instance, avoiding an unnecessary dependence on the
unfinished completed-coefficient limit theorem.

The original reduction predicate repeatedly elaborated the concrete derived scalar
functor. Profiling identified it as a 15.9-second definition; the definitionally equal
local generic construction and shared terms reduce that to 6.0 seconds. Its scalar
maps, positive exponent, isomorphism, constructibility and fixed-scalar etale-origin
clauses all remain exactly the same.

## Second reading by W4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
