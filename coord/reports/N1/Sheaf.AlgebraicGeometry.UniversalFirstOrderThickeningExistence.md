## What changed

Added proof-only imports of `UniversalFirstOrderThickeningAffineLocal` and
`UniversalFirstOrderThickeningAffineGlobalization`. The target theorem now applies the
strictly weaker affine-local construction interface and then the separate globalization
interface. Added both corresponding node records.

## Proved and sorry left

`FormallyUnramified.exists_universalFirstOrderThickening_existence` is proved by extracting
the affine-local data and applying `isUniversalFirstOrderThickening_of_affine_local`.

Sorries remain in `FormallyUnramified.exists_affine_local_universalFirstOrderThickening`
(node `lem-weil-pbc-universal-first-order-thickening-affine-local`) and
`isUniversalFirstOrderThickening_of_affine_local`
(node `lem-weil-pbc-universal-first-order-thickening-globalization`). These are strictly
smaller interfaces: the former tests only affine schemes, while the latter is only the
upgrade from affine tests to arbitrary tests.

## No longer needed

The previous `UniversalFirstOrderThickeningConstruction` module and its redundant
construction node are removed from this delivery. No affine or gluing implementation module
is imported by the target beyond the two stated interfaces.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt wrapped the target existential in a conjunct and therefore merely moved
the same `sorry`. The decomposition here separates the affine construction from the
independent affine-to-global gluing implication.

## Earlier second reading (a previous round; superseded)

A second reading checked that the target signature is unchanged, that the target proof is a
real application/projection, and that each new statement is strictly weaker than the target.
The affine-local statement restricts both test schemes to `IsAffine`; the globalization
statement assumes this restricted property and concludes the full universal predicate.
The unit's construction-then-gluing route is retained at its two interfaces.

## Second reading by N1

1. **Signatures:** Compared the delivered item module with the repository version. The
   existing target declaration has the same signature; only proof-only imports and its proof
   body changed. The two new declarations are recorded verbatim in their node files.
   **Verdict: pass.**
2. **Proof and axioms:** Compiled all three delivered modules with `lcompile.py --all`.
   The target proof has no `sorry`; the two intentionally split interface theorems retain
   named `sorry`s and have source, proof descriptions, and matching nodes. **Verdict: pass.**
3. **Statements:** Checked both split statements against the definition of
   `IsUniversalFirstOrderThickening`: the affine-local theorem adds the affine test
   restriction, while globalization only removes that restriction. Neither restates the
   target, and no existing Mathlib or Sheaf declaration duplicates them. **Verdict: pass.**
4. **Pruning and route:** The proof uses exactly the affine construction interface followed
   by its affine-to-global upgrade, preserving the unit's construction-then-gluing route.
   The removed construction module is not imported by the delivered item. **Verdict: pass.**
5. **DAG agreement:** The target node's proof and dependencies match the two applications in
   Lean, and the two new split nodes carry their declarations, sources, proof steps, and
   `split` status. **Verdict: pass.**

Changed the report only by recording this review; no further Lean changes were needed.

## New nodes

`lem-weil-pbc-universal-first-order-thickening-affine-local`: affine-test construction;
no change record is needed for a new module.

`lem-weil-pbc-universal-first-order-thickening-globalization`: affine-to-global gluing;
no change record is needed for a new module.
