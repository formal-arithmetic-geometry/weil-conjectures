## What changed

Proved `AlgebraicGeometry.Scheme.constantEtaleSheaf_shortExact` in
`Sheaf.AlgebraicGeometry.ConstantEtaleSheafShortExact`, preserving its signature.
Added the proof-only import
`WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver`.
Its proved instances `CategoryTheory.preservesFiniteLimits_constantSheaf` and
`CategoryTheory.preservesFiniteColimits_constantSheaf` implement the existing DAG
argument: the constant presheaf functor preserves limits and colimits, and
sheafification is left exact and left adjoint. Mathlib's
`CategoryTheory.ShortComplex.ShortExact.map_of_exact` then preserves the given
short exact sequence, including the monomorphism and epimorphism at its ends.
No route, statement, definition, node, or public import changed.

## Proved and sorry left

Proved `AlgebraicGeometry.Scheme.constantEtaleSheaf_shortExact`
(node `lem-constructible-constant-exact`): one of one original sorries removed.
No sorry remains in this module; none was added elsewhere. No new intermediate
statement is required. Local compilation completed without errors or warnings.
The delivery dry run checks the declaration's transitive axioms as well as
compilation on the server.

## No longer needed

None. All existing public imports are retained for the statement's API.
The existing proof dependencies `def-weil-pbc-constant-sheaf`,
`def-weil-pbc-etale-site`, and
`lem-weil-pbc-site-r-module-presheaf-sheafification-exact` still describe the
argument. The last dependency is already a Mathlib leaf; no Sheaf module is
needed for it. No blueprint unit statement or step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The earlier search record reported no constant-sheaf exactness theorem, but the
current source library provides proved finite-limit and finite-colimit
preservation instances in `ConstantSheafOver`. Together with Mathlib's
`ShortExact.map_of_exact`, these close the statement directly by its planned
route. The argument works for all modules and rings; the retained finiteness
hypotheses are unnecessary to the proof, and were not removed. The zero
sequence, nonsplit sequences, noncommutative coefficient rings, and an empty
scheme require no special case because the functorial preservation theorem
holds for every short exact sequence on the site.

## Second reading by E1

1. **Visible changes and statements.** Compared the delivered module with the repository version. The theorem signature and all existing declarations are byte-for-byte unchanged; only a proof-only import and the theorem proof differ. Verdict: pass.
2. **Proof and axioms.** Compiled the module with `lcompile.py`; it has no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern`. A scratch `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`. Verdict: pass.
3. **Statements and split-offs.** No statement was split off and no new node or theorem was added. The existing target statement remains exactly the finite constant-etale short exactness claim, with its original hypotheses and conclusion. Verdict: pass.
4. **Route and pruning.** The proof uses the shortest available route: constant-sheaf preservation of finite limits and colimits followed by `ShortComplex.ShortExact.map_of_exact`. The unit's target statement and intended constant-sheaf exactness route remain represented; no import can be removed without losing the theorem's API. Verdict: pass.
5. **DAG agreement.** Updated `lem-constructible-constant-exact` proof, proof dependencies, and proof origin to record the preservation instances and `map_of_exact` route actually used by Lean. Verdict: pass.

Changed the DAG metadata and added this second-reading record; no Lean statement or definition was changed.
