## What changed

Restored `lean/Sheaf/AlgebraicGeometry/PicardCoefficientTransposePasting.lean`
from its quarantine archive, byte-for-byte. This repairs the absent module
listed in `coord/rework.tsv`, restoring the explicit coefficient-transpose
construction, its defining equation, the complete categorical pasting proof,
and the public fibre-product pasting theorem. No source-library file changes.

Both existing DAG attachments and their recorded signatures are preserved
verbatim. The proof route remains square vertical coherence, tensor-single
coefficient composition, counit naturality, and equality of fibre-product
lifts by the two projection equations. The unit route is unchanged.

Compilation through `lcompile.py --all` succeeds without errors or warnings
when the current, unchanged tensor-composition dependency is compiled in the
same sandbox. The dependency copy is compilation support only and is identical
to the live source; it creates no delivery diff. A separate importing module
checks all four public declarations and their axioms. Each uses only
`propext`, `Classical.choice`, and `Quot.sound`, including the pasting theorem.

The source and DAG consumer searches identify exactly the two quarantined
parents listed in the change record; their imports, declarations and node
edges are preserved. They need no adaptation because the restored interface
is identical. There are no live importers of the absent module to adapt.

Change record: `coord/changes/F3-picard-coefficient-transpose-restoration.md`.

## Proved and sorry left

This is a zero-hole restoration repair. The archive has zero direct holes;
the restored module has zero direct holes. Holes closed: 0. Holes added: 0.
Split-off theorems: 0. No declaration remains `sorry`.

The following public declarations are restored with complete proofs or
explicit definition data:

- `AlgebraicGeometry.Scheme.coefficientCounitTranspose`.
- `AlgebraicGeometry.Scheme.coefficientCounitTranspose_eq`.
- `AlgebraicGeometry.Scheme.picardCoefficientTranspose`
  (`def-sc-picard-coefficient-transpose`).
- `AlgebraicGeometry.Scheme.picardCoefficientTranspose_pasting`
  (`lem-sc-picard-coefficient-transpose-pasting`).

The three private pasting helpers are also proved. No arbitrary existence
witness, axiom, hollow definition, or new admitted lemma is introduced.
The current tensor-single composition dependency is already proved, so the
restored pasting theorem's axiom audit contains no `sorryAx`.

## No longer needed

None. All archived imports and all existing node dependencies remain needed.
No module, declaration, node attachment or parent edge is pruned or withdrawn.
The temporary API/axiom probe and import-isolation files are not delivered.

A fresh LeanFinder query for counit naturality and derived-square coefficient
pasting returned generic categorical-pullback results, with no exact match.
Loogle confirms `CategoryTheory.NatTrans.naturality`, which is the ingredient
already used by the archived categorical proof. Repository search found the
existing square-pasting and tensor-composition APIs and no duplicate of this
module's two constructions or pasting theorem. Restoring the existing proof
is the shortest route and needs no new statements.

## Where the brief, the DAG or earlier work was wrong

The assignment is rework of an absent, already proved module, not a current
one-hole theorem. The quarantine archive is the source of the restoration;
its absence from `lean/` does not justify withdrawal.

The first compile against the published dependency artifacts reported a
collision between the retired Sheaf base-change declaration and the adopted
source declaration. Import-isolation probes located it in the published
tensor-composition dependency: that module alone imported successfully, but
combining it with the current source mate-evaluation module failed. Compiling
the current tensor-composition source unchanged alongside the item resolves
the collision. No library source or proof route required modification.

The earlier A4 report's remaining tensor-composition hole is historical:
the current H2 restoration supplies a complete proof. No new node or
statement correction is required. Identity maps, zero coefficient modules
and empty schemes remain covered by the same categorical argument, which
never inverts the single-pullback coefficient map.

## Second reading by F3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
