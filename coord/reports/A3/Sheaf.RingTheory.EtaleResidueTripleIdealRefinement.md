## What changed

Proved `AlgebraicGeometry.Scheme.etaleResidueTriple_ideal_refinement` in
`Sheaf.RingTheory.EtaleResidueTripleIdealRefinement` without changing its signature.
The proof uses Mathlib's local unramified ideal equality and denominator-clearing
criterion, then the existing unit-refinement theorem. The morphism's structure-map
compatibility transports ideal membership, and cancellation of the resulting unit
finishes the proof. Added proof-only imports of
`Mathlib.RingTheory.Unramified.LocalRing` and
`Sheaf.RingTheory.EtaleResidueTripleUnitRefinement`.
Updated the existing node's proof, proof dependencies, and proof origin to match.

## Proved and sorry left

Closed the sole hole:
`AlgebraicGeometry.Scheme.etaleResidueTriple_ideal_refinement`
(node `lem-weil-pbc-etale-triple-ideal-refinement`). No holes remain in the delivered
module; no new holes, definitions, statements, or modules are added.
The proof imports the existing theorem
`AlgebraicGeometry.Scheme.etaleResidueTriple_unit_refinement`
(node `lem-weil-pbc-etale-triple-unit-refinement`), whose repository source still has
`sorry`. This is a proof from an existing stated dependency, not a new decomposition.

## No longer needed

No imports were removed: the original module had only its statement import.
The direct dependency on `lem-weil-pbc-etale-composition-cancellation` is removed
from this node. Its role in the principal-localization construction is delegated
to the existing unit-refinement node, which still needs it; it is not globally
pruned. No module is claimed to leave the target closure.

## Where the brief, the DAG or earlier work was wrong

The mathematical plan is correct. Its second step need not reconstruct the
principal localization: existing unit refinement already supplies a successor
that makes the cleared denominator a unit. The original proof dependencies did
not name that reusable theorem. No statement or definition was changed.

## Second reading by A3

1. Compared both sandbox modules against the repository with `diff -u`. The sole
   existing theorem's signature and its docstring are byte for byte unchanged;
   only its proof and private imports differ. The unit-refinement module is an
   unchanged compilation companion, not an adapted or newly delivered module.
   No definition or target statement changes; no change record is required.
2. Compiled both modules locally through `lcompile.py`, with no errors or warnings.
   The ideal-refinement body has no `sorry` or forbidden declaration or attribute.
   Compiled a scratch copy with `#print axioms` for
   `AlgebraicGeometry.Scheme.etaleResidueTriple_ideal_refinement`: precisely
   `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`. The latter comes
   from the already-stated unit-refinement dependency, whose named hole remains
   open and was not changed. No data definition or arbitrary witness is added.
3. No statements are split off, so there are no new statement searches or nodes
   to validate. Read the existing unit-refinement signature: it applies exactly
   to the denominator `g` outside `q` supplied by Mathlib, and returns the required
   successor morphism and unit property. It is strictly different from ideal
   refinement. For `f = 0` membership remains valid; when `R` is a field and
   `p = 0`, the argument still clears denominators and forces the resulting
   image to vanish. Prime ideals already exclude the zero-ring triple case.
4. Read the proof downward, the triple/category definitions, Mathlib's
   `Algebra.isUnramifiedAt_iff_map_eq` and
   `IsLocalization.algebraMap_mem_map_algebraMap_iff`, and searched the library
   and upstream checkout for refinement alternatives. Etaleness supplies the
   finite-type and unramified instances; `t.over` supplies exactly `LiesOver`.
   `Under.w` gives the needed structure-map identity, so `Ideal.map_map` transports
   membership to the same ideal in the conclusion, and unit cancellation is valid.
   The route already uses the short Mathlib reduction and existing unit refinement.
   Removed the redundant newly added `Mathlib.RingTheory.Localization.Ideal`
   import: it is available through `Unramified.LocalRing`, and the reduced imports
   compile. The original public statement import stays. Checked `sk-thm-p1`'s
   `realized` fields: neither refinement node is a unit-level realization, and
   the local rewrite bypasses no unit step. `No longer needed` identifies the
   entire removed old dependency set (composition-cancellation alone), which
   stays needed by unit refinement; no global pruning is claimed.
5. Compared the node JSON against the repository: only `proof`, `proof_deps`,
   and `proof_origin` change. The first proof step uses the recorded Mathlib
   match of `lem-weil-pbc-etale-prime-generates-maximal`; the second uses
   `lem-weil-pbc-etale-triple-unit-refinement`. Their union is exactly the new
   `proof_deps`. No new nodes or metadata repairs are necessary.

Second reading changed only the redundant proof-only localization-ideal import
and this report. Kept the unchanged unit-refinement compilation companion because
its compiled module is not yet present in this machine's green-build cache;
`deliver3.py` omits unchanged source files from the commit. The final proof
compiles with the reduced imports and the same axiom set.
