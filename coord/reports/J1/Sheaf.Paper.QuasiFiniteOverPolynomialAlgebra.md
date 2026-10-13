## What changed

Proved `Algebra.exists_quasiFinite_over_polynomial_algebra` in
`lean/Sheaf/Paper/QuasiFiniteOverPolynomialAlgebra.lean`, preserving its full signature,
public imports. The second reader updated its proof docstring to match the implemented
route. Four fully proved private helpers implement the
fibre-spectrum equivalence, principal-neighbourhood dimension choice, polynomial
normalization at a point, and a topological comparison of fibres. All helpers are in
the assigned module; there are no new modules or public declarations.

The proof follows Stacks Tag 00QE: shrink to the local fibre dimension, rescale a
Noether normalization so its coordinates lift, prove quasi-finiteness at the point,
and shrink again. The last shrink uses Mathlib's proved finite-subalgebra form of
Zariski's Main Theorem directly. It needs neither the project openness theorem nor
the four-rings theorem. Updated the existing DAG node's proof and proof dependencies.

Added proof imports of `Mathlib.RingTheory.TensorProduct.MvPolynomial` and
`Mathlib.RingTheory.ZariskisMainTheorem`. Kept the NoetherNormalization proof import.
A scoped `linter.unusedVariables false` before the existing theorem suppresses the
warning about its original existential proof binder `hg`, which must stay unchanged.
This option affects only linting of that declaration.

## Proved and sorry left

Closed the sole original hole:
`Algebra.exists_quasiFinite_over_polynomial_algebra`
(node `lem-weil-pbc-quasi-finite-over-polynomial-algebra`).

Holes added: none. Sorries left in the delivery: none. This is a full proof, not a
decomposition. `#print axioms Algebra.exists_quasiFinite_over_polynomial_algebra`
reports exactly `[propext, Classical.choice, Quot.sound]`. The final single-file
compile is clean and takes approximately 7–10 seconds locally.

Edge cases: `n = 0` uses the empty family of normalization variables and the same
polynomial automorphism proof. The zero fibre cannot occur because the distinguished
prime gives `Nontrivial F`; the zero source ring cannot occur when `q` exists.
No domain assumption on R or S is added. R and S retain independent universes.
No object is defined by choosing data from an unproved existence theorem.

## No longer needed

Removed proof imports:
- `Sheaf.RingTheory.QuasiFiniteFourRings`.
- `Sheaf.RingTheory.QuasiFiniteLocusOpen`.

The assigned node no longer uses:
- `lem-weil-pbc-quasi-finite-four-rings`: finite type of the fibre is Mathlib's
  tensor-product instance; the finite-type witness over the polynomial algebra
  is obtained by restricting scalars.
- `lem-weil-pbc-ring-quasi-finite-locus-open`: replaced by Mathlib's proved
  `Algebra.QuasiFiniteAt.exists_fg_and_exists_notMem_and_awayMap_bijective` and
  permanence of `QuasiFinite` under localization and surjective algebra maps.
- `lem-weil-pbc-finite-type-dim-zero-artinian`: the scheme-level result is unnecessary;
  the finite normalized fibre and the explicit fibre homeomorphism suffice.
- `lem-weil-pbc-finite-dim-algebra-artinian`: no separate call is made; the finite
  algebra's isolated fibre points are supplied by Mathlib's quasi-finite API.

These are local dependency removals; other target branches may still need them.
The second reader also removed redundant proposed proof imports
`Mathlib.RingTheory.Localization.BaseChange` and
`Mathlib.Order.ConditionallyCompleteLattice.Indexed`: their declarations are already
available through the remaining imports, as checked by a clean compile with both
removed. These two imports were absent from the repository baseline.

No public import is removed. No unit realization is bypassed: this assigned node is
below the unit level and is not a node in `sk-thm-p1.realized`.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The DAG's scheme-level zero-dimensional Artinian
argument was longer than needed. A finite normalized fibre already supplies the
isolated-point assertion via Mathlib; comparing its fibre with the original one
can be done using the fibre-spectrum embeddings, without another tensor-associativity
construction. Mathlib's Zariski main theorem also supplies the final shrink directly.

The literature checkout is absent on this machine. The source proof was checked at
https://stacks.math.columbia.edu/tag/00QE. No literature file was written. LeanSearch
returned an internal-server error; the provided msearch wrapper recorded it as
unavailable. LeanFinder, Loogle, and local Mathlib/library searches succeeded.


## Second reading by J1

1. **Interface: PASS.** Read the complete module and its diff against the repository.
   The existing theorem signature is byte-for-byte identical, including the
   existential proof binders, independent universes, and all hypotheses. The four
   original public imports and visibility are unchanged. No existing definition
   was edited; there are no change records or forced adaptations.
2. **Proof: PASS.** Independently compiled the delivered proof locally. A scratch
   copy printed axioms for all four private helpers and the public theorem; each
   uses exactly `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.
   Scanned the entire module for forbidden declarations/options and holes: none.
   All witness choices eliminate proved existential theorems inside proofs; no
   data definition chooses a witness from an unproved existence statement.
3. **Split statements: PASS (none).** No new public or split-off statements, new
   nodes, or holes exist. Read all private helper statements and arguments. The
   embedding helper needs no topology on the codomains; its coverage hypothesis
   makes the restricted embedding surjective. Normalization works for `n = 0`
   and for arbitrary commutative source rings; the fibre point supplies its
   required nontriviality. Independent LeanFinder and Loogle searches with new
   wording and local searches in Mathlib, upstream, and `lean/` found no ready
   theorem replacing this local polynomial construction.
4. **Route and pruning: PASS after repair.** Checked the normalization theorem
   upstream, Mathlib's Zariski main theorem, the project's quasi-finite definition,
   and Stacks Tag 00QE (https://stacks.math.columbia.edu/tag/00QE). The proof shrinks
   the fibre, lifts rescaled normalization coordinates, compares whole fibres via
   embeddings, and shrinks using the proved finite-subalgebra theorem. No shorter
   ready route was found. Checked `dag/units/sk-thm-p1.json`: the item is not a
   realized unit node and no realized statement or step is bypassed. The report's
   four old dependency removals equal the old-minus-new `proof_deps` exactly.
   Removed two redundant proposed proof imports and compiled the result cleanly.
   Remaining proof imports supply normalization, polynomial scalar extension, and
   Zariski main; all remain plain `import`.
5. **DAG agreement: PASS.** Only `proof`, `proof_deps`, and `proof_origin` differ
   in the existing node. Verified `proof_deps` is exactly the union of step uses,
   read the recorded declarations/Mathlib matches, and matched all five steps to
   the Lean argument. Statement, source, unit, chapter, and Lean signature records
   remain unchanged. No new-node obligations arise.

Changes by the second reader: updated the public theorem's stale four-step proof
text and the normalization helper's proof explanation to describe the actual
fibre-homeomorphism and Zariski main argument; removed the redundant BaseChange
and Indexed imports; corrected the report accordingly. No proof term, signature,
definition, visibility, or DAG field was changed by this second reading. Holes
closed remain one; holes added and split off remain zero.
