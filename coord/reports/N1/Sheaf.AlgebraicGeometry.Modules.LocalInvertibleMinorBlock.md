## What changed

The existing theorem `exists_local_invertible_minor_block` keeps its signature and
visibility byte for byte. Its proof now obtains local coordinate decompositions,
a determinant compatibility equality and a unit determinant from
`exists_local_invertible_minor_block_data`, then rewrites that equality and applies
the proved generic theorem `local_invertible_minor_block_isIso`.

The two new modules are `LocalInvertibleMinorBlockData` and
`LocalInvertibleMinorBlockIso`. The parent imports them privately, because only its
proof needs them. Both auxiliary modules publicly import only the upstream module
`WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf` that supplies their types
and `freeMatrix`. The generic inverse proof privately imports
`Mathlib.LinearAlgebra.Matrix.NonsingularInverse`. The parent's existing public
`FreeComplex` import is preserved. No existing definition or statement changes,
and no change record or forced adaptation is needed.

## Proved and sorry left

Original hole closed: `AlgebraicGeometry.Scheme.Modules.exists_local_invertible_minor_block`.
New hole added: `AlgebraicGeometry.Scheme.Modules.exists_local_invertible_minor_block_data`
(node `lem-pc-local-invertible-minor-block-data`). This is the only remaining
`sorry` in the delivery. Its docstring gives the source and the complete coordinate
construction and determinant argument.

New theorem proved without `sorry`:
`AlgebraicGeometry.Scheme.Modules.local_invertible_minor_block_isIso`
(node `lem-pc-local-invertible-minor-block-iso`). It constructs the inverse sheaf
map from the nonsingular inverse matrix, proves matrix injectivity and the
composition identity using existing free-sheaf universal properties, and checks
both inverse equations.

This is a decomposition: one original hole closed and one new hole added, net
zero holes before any independent import-closure effects. The original theorem
still depends on the open geometric construction and is not an axiom-free proof
of the item. The generic invertibility theorem has only `propext`,
`Classical.choice`, and `Quot.sound`; the parent and geometric statement also
have `sorryAx`. These were checked with `#print axioms` in scratch copies.

## No longer needed

No existing import is removed and no whole module is claimed pruned.
All five former direct proof dependencies of the parent are replaced by the two
new nodes:

- `def-weil-pbc-free-module`
- `def-weil-pbc-matrix-determinant`
- `lem-weil-pbc-det-repeated-column-zero`
- `lem-weil-pbc-matrix-adjugate-identity`
- `lem-weil-pbc-open-immersion-module-pullback-restriction`

They remain in the auxiliary nodes' proof routes: the geometric construction uses
the free module, determinant, repeated-column and restriction results; the proved
algebraic bridge uses the free universal property and Mathlib's nonsingular
inverse identities based on the adjugate identity. They are therefore not claimed
unnecessary transitively.

## Where the brief, the DAG or earlier work was wrong

The first worker's `local_invertible_minor_block_isIso` was false: it asserted
invertibility for arbitrary decompositions, without tying their leading block to
the selected minor or restricting the neighbourhood to its nonvanishing locus.
For example, over a field take a=1, m=n=2, phi=diag(1,0), select the (0,0)
minor and use the whole one-point scheme as U. Swap the source coordinates and
keep the target coordinates. The selected determinant is 1 but the leading block
in these arbitrary decompositions is zero, hence not invertible.

The first data statement concluded only `True` after producing arbitrary
isomorphisms, so it could not justify the subsequent invertibility assertion.
The earlier second reading in the supplied report missed this error and is
superseded. Both new statements also lacked complete docstring proofs, and the
parent's node had not been updated to match its proposed Lean reduction.
These faults are repaired; no false assertion is delivered.

## New nodes

`lem-pc-local-invertible-minor-block-data`: the geometric construction of local
coordinate decompositions with an explicit leading-determinant compatibility
and a unit restriction of the selected determinant. It leaves the coordinate
construction open, without asserting a sheaf inverse.

`lem-pc-local-invertible-minor-block-iso`: a proved generic algebraic bridge from
a unit global determinant to an inverse of a square finite free sheaf map. It
has no open immersion, point, minor or local decomposition hypotheses.

Each node records its complete Lean signature, statement dependencies, proof
steps and their dependency union, source, origin and real search results. Searches
used new wording for coordinate permutations and for unit-determinant free-sheaf
maps. LeanSearch returned Internal Server Error; this is recorded as unavailable.
LeanFinder and Loogle found matrix/linear-map results but no theorem of the sheaf
statement; grep and a separate upstream/project source search found no duplicate.

## Second reading by N1

1. Compared every delivered module with the repository using diff. The two
   auxiliary modules and nodes are new. The parent's existing declaration,
   signature, docstring and visibility are unchanged; only private proof imports
   and its proof differ. No definitions change. Verdict: pass after repair.
2. Compiled all three files in import order through lcompile.py, without errors
   or warnings. Searched the delivered files for forbidden declarations and
   proof escapes. The sole `sorry` is the named data theorem; no definition
   contains one. Scratch-copy axiom checks show only the three permitted axioms
   for the generic inverse theorem and additionally `sorryAx` for the parent and
   data statement. Verdict: pass, with one explicitly reported open lemma.
3. Rejected the arbitrary-decomposition invertibility lemma by the concrete
   diag(1,0) counterexample above. The replacement data statement connects the
   actual determinant and carries its unit proof; the inverse theorem is generic
   and now fully proved. Checked a=0 (empty determinant 1, zero free sheaf), full
   selected rank, empty index sets, and impossible oversized injective selections.
   No reducedness or other-fibre rank hypothesis is needed. The surviving hole is
   strictly the local coordinate/determinant part, rather than the parent's sheaf
   isomorphism conclusion. Full docstring argument and duplicate searches checked.
   Verdict: pass after repair.
4. The reduction follows the existing unit's pivot-minor route: choose the unit
   determinant locus, reorder and split the bases, then invert the leading block.
   Mathlib inverse identities close the algebraic step. Proof-only imports are
   private and auxiliary public imports are narrowed to their type dependencies.
   All five old direct parent proof dependencies are accounted for above.
   `dag/units/sk-thm-picard-semicon.json` has empty realization entries; none is
   bypassed or changed. Verdict: pass; no whole-module pruning claimed.
5. Updated the existing parent's proof, proof_deps and proof_origin. Rewrote both
   new nodes with self-contained statements matching their Lean signatures,
   actual proof routes, dependency unions and genuine recorded searches. The
   generic node records its now-complete inverse construction; the data node
   records the remaining geometric argument. Verdict: pass after repair.

Second reading changed the false split into determinant-compatible local data,
proved the generic free-sheaf inverse theorem, completed the docstrings, minimized
the auxiliary imports, repaired all three DAG proof records, and corrected the
report's progress accounting. Dry run and final delivery are performed with
deliver3.py as required.
