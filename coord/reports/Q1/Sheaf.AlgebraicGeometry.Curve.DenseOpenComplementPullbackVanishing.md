## What changed

Wrote a complete proof of
`AlgebraicGeometry.IsCurve.dense_open_complement_pullback_vanishing` in
`Sheaf.AlgebraicGeometry.Curve.DenseOpenComplementPullbackVanishing`, preserving its
signature and both original public imports. Added non-public proof imports of
`WeilConjectures.AlgebraicGeometry.Sites.FiniteSupport`,
`WeilConjectures.SixFunctors.OpenClosed.Vanishing`,
`Sheaf.AlgebraicGeometry.Curve.DenseOpenFiniteComplement`, and
`Sheaf.AlgebraicGeometry.EtaleModulePullbackForgetNaturality`.

The proof uses the already proved finite boundary and finite-support acyclicity results.
It transfers the boundary along the injective open immersion, proves zero restriction
using disjoint ranges in module coefficients, and transports through forgetting and
inverse-image composition. Positive degrees are written as n+1 before applying acyclicity.
Updated the item's DAG proof and dependency list to match this route. No new declarations,
interface changes, new nodes, or new sorries. The item is below the unit's realized steps;
the dense-open reduction of curve assertions stays in place.

## Proved and sorry left

Proved `AlgebraicGeometry.IsCurve.dense_open_complement_pullback_vanishing`
(node `lem-pbc-k2-dense-open-complement-pullback-vanishing`): 1 of 1 original sorries.
No sorry remains in this delivery; no holes were added. The final module compiles cleanly
with the authorized local compiler (exit code 0, 3.2 seconds).
The proof works for the empty scheme, the empty
complement, degree one, nonreduced curves and arbitrary coefficients, including the zero ring.

## No longer needed

Preserved both public imports supporting the unchanged signature and the proof import
`Sheaf.AlgebraicGeometry.EtaleModulePullbackForgetNaturality`. Removed these original
proof imports:

- `Sheaf.Paper.ZeroDimensionalCohomology`
- `WeilConjectures.AlgebraicGeometry.Sites.CohomologyClopen`
- `WeilConjectures.SixFunctors.Finite.BaseChange`
The following original planned dependencies are no longer needed directly by this item:

- `lem-weil-pbc-finite-type-over-noetherian`
- `lem-weil-pbc-noetherian-finitely-many-components`
- `lem-weil-pbc-closed-point-residue-field-base`
- `lem-weil-pbc-closed-immersion-finite`
- `lemma-weil-pbc-finite-exchange`
- `lem-weil-pbc-closed-immersion-base-change`
- `lem-weil-pbc-finite-pushforward-cohomology`
- `lem-weil-pbc-zero-dimensional-cohomology`

In particular, no direct proof import of `WeilConjectures.SixFunctors.Finite.BaseChange`,
`WeilConjectures.AlgebraicGeometry.Sites.CohomologyClopen`, or
`Sheaf.Paper.ZeroDimensionalCohomology` is needed. The finite-support theorem encapsulates
the point-cohomology and finite-edge-map argument; its own transitive dependencies remain.
No global unreachability claim is made: other items can still need these nodes.

## Where the brief, the DAG or earlier work was wrong

No statement error found. The DAG plan is valid but longer than necessary: the existing
proved finite-support theorem removes the explicit pullback complement scheme, the
module direct-image/forget comparison, and the derived cohomology comparison.
`lem-sc-dense-open-finite-complement` is used as a generic geometric tool from another
unit, and `lem-sc-finite-support-acyclic` as a proved generic cohomological tool; this does
not replace a unit's route.

Searches: LeanFinder returned unrelated formally etale algebra lemmas; Loogle did not
know the project-specific finite-support identifier; the launcher grep returned no hits.
Direct rg in the source library located `subsingleton_H_of_isZero_upperStar` and the
open-closed disjoint-range theorem, whose signatures and proofs were read.

The earlier attempts were blocked by the compiled snapshot lacking
`Sheaf/AlgebraicGeometry/Curve/DenseOpenFiniteComplement.olean`. On this retry the
existing dependency is available and the preserved final proof compiles without warnings.
No dependency was duplicated or independently compiled. The existing statement and
docstring remain unchanged. The required `deliver3.py Q1
Sheaf.AlgebraicGeometry.Curve.DenseOpenComplementPullbackVanishing --no-push`
printed `OK (dry run)`: compilation and preflight passed, with only the second
reading reserved for the next worker as instructed. Nothing was pushed.


## Second reading by Q1

1. PASS: Read the full source and sandbox diff. The existing theorem signature is
   byte-for-byte identical (checked separately by comparing text up to `:= by`).
   The declaration docstring and both public imports are unchanged. There are no
   definitions or additional declarations, and no statement change records are needed.
2. PASS: Independently compiled the delivered module using `lcompile.py`, without
   errors or warnings (2.4 seconds). A scratch copy with `#print axioms
   AlgebraicGeometry.IsCurve.dense_open_complement_pullback_vanishing` compiled and
   printed exactly `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx`.
   No sorry or prohibited declaration/attribute occurs in the delivered module.
3. PASS: No split-off statements, new nodes, or added holes. Read the existing
   finite-complement, finite-support acyclicity, disjoint-range vanishing, and
   coefficient-forgetting comparison declarations and their proofs. The finite
   boundary pulls back along an injective open immersion; singleton closedness
   pulls back continuously; residue fields transport across the open-immersion
   isomorphism. Empty schemes, empty complement, q=1, and zero coefficients require
   no extra assumptions. The theorem closes one original hole and adds zero.
4. PASS: The proof reduces directly to existing proved finite-support acyclicity.
   Independent rg searches of curve modules and a launcher Mathlib grep search
   for `subsingleton_H|disjoint_range|finite_complement` found no shorter matching
   theorem. All four non-public imports supply declarations used by this proof;
   the original public imports support the unchanged interface. The report lists
   all eight old proof dependencies absent from the new dependency list and all
   three removed direct imports. These imports can remain reachable transitively,
   so this delivery claims no globally pruned modules. Read `dag/units/sk-thm-p1.json`:
   this item is below its realized steps, and the dense-open curve reduction is
   preserved. No unit record changes.
5. PASS: Compared the node JSON to the repository. Only `proof`, `proof_deps`,
   and `proof_origin` differ. The four recorded dependencies match the actual
   declarations used; `proof_deps` equals the union of the proof steps' `uses`.
   The statement, source, Lean signature record, chapter, and unit are unchanged.

Second reading changed only this report: added independent review and axiom evidence.
No Lean or DAG repair was necessary.
