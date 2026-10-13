## What changed
Proved `Algebra.residue_conormal_snake_sequence` with the existing signature and public
imports unchanged. All supporting lemmas are private and proved in the same module.
Added proof imports for surjective-presentation conormal equivalence (which publicly
imports middle Jacobi-Zariski exactness, the module snake lemma and field flatness),
characteristic transfer, the prime-field instance, and prime-field H1 vanishing.

The conormal map alpha is constructed by factoring beta a through the injective lower
conormal arrow c. This proves its commuting square without connecting-map naturality.
The other square is checked on universal differential generators. The kernel and quotient
maps and their four exactness assertions and both endpoints are proved explicitly, with
Mathlib supplying the snake connecting map and its two adjacent exactness assertions.
Field defect equivalences are proved directly from the two middle Jacobi-Zariski
exactness assertions. The existing node's proof and dependencies now describe this route.

## Proved and sorry left
Closed the only original hole: `Algebra.residue_conormal_snake_sequence`
(node `lem-weil-pbc-residue-conormal-snake-sequence`). No holes added or left in the delivery.
The proof uses `Algebra.subsingleton_h1Cotangent_of_charP`. The second reader checked
`#print axioms` for the main theorem and all four private helpers: each depends only
on `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.

## No longer needed
The planned nodes `lem-weil-pbc-jacobi-zariski-connecting-map-naturality`,
`lem-weil-pbc-nl-presentation-h1-functoriality`, and
`lem-weil-pbc-jacobi-zariski-homology-sequence` are not direct proof dependencies.
Their planned modules `Sheaf.RingTheory.JacobiZariskiConnectingMapNaturality` and
`Sheaf.RingTheory.JacobiZariskiHomologySequence` are not imported. The latter is replaced
by the already-proved Mathlib interface recorded in
`lem-weil-pbc-jacobi-zariski-middle-exactness`, avoiding the full left-term/Tor theorem.
No original imports were removed. The temporary explicit proof import
`Mathlib.LinearAlgebra.TensorProduct.RightExactness` was removed after confirming that
field-flatness imports provide the needed results. The second reader also removed
redundant direct proof imports `Mathlib.Algebra.Module.SnakeLemma`,
`Mathlib.RingTheory.Kaehler.JacobiZariski`, and `Mathlib.RingTheory.Flat.Basic`: all are
publicly supplied by the necessary `Mathlib.RingTheory.Extension.ExtendScalars`.
No previously reachable library module is claimed globally pruned by this delivery. No blueprint unit statement or
realized step was bypassed.

## Where the brief, the DAG or earlier work was wrong
The DAG's naturality route is unnecessary for the existential alpha in the stated target.
Factoring through the injective lower conormal arrow is enough and needs no generator
formula for alpha. The full Jacobi-Zariski homology/Tor sequence is also unnecessary:
Mathlib's two middle exactness results suffice. No statement or definition was changed.
The private helpers cover arbitrary field extensions, including purely inseparable
ones; no separability, finiteness, or regularity was introduced.


## Second reading by E4
1. **Interface unchanged: pass.** Compared the only delivered Lean module with the
   repository version by diff and checked the existing theorem signature byte for byte.
   Both original public imports remain unchanged. No existing definition, signature,
   visibility, target statement, or change record is altered.
2. **Proof and axioms: pass.** Compiled the module locally through `lcompile.py`.
   No sorry or forbidden declaration mechanism occurs in it. A scratch copy with
   `#print axioms` on all four private helpers and the main declaration reports only
   `propext`, `Classical.choice`, and `Quot.sound`. The equivalences are constructed
   from injective/bijective maps and their inverse laws, not from arbitrary witnesses
   of an unproved existence assertion.
3. **Split statements: pass, none.** No new sorry theorem, public statement, module,
   or node was split off. Read the private helpers and their proofs: they cover
   identity field maps, rings that are fields (zero conormal spaces), and purely
   inseparable residue extensions without a separability assumption on L/K.
   Searched the upstream/library sources for residue-conormal and snake formulations;
   the available Mathlib ingredients are used directly, with no duplicate public API.
4. **Route and pruning: pass after repair.** Read the top-level reduction, the conormal
   row construction, the generator comparison, the range factorization defining alpha,
   and the explicit kernel/cokernel snake maps. Checked the big diagram in Stacks
   [Tag 07E5](https://stacks.math.columbia.edu/tag/07E5). The module snake API supplies
   exactly the two connecting-map exactness claims; the remaining claims are proved.
   Removed three redundant proof imports publicly supplied by ExtendScalars and tested
   that the remaining field and characteristic imports are needed. All three discarded
   old proof dependencies are listed under No longer needed. None is a realized statement
   or step of `dag/units/sk-thm-p1.json`; the unit route is preserved.
5. **Nodes match: pass.** Only proof, proof_deps and proof_origin differ in the existing
   node. Read the dependency nodes and their Mathlib matches/Lean declarations; the
   proof_deps set is exactly the union of the steps' uses. The node describes range
   factorization of alpha, middle Jacobi-Zariski exactness and the module snake API,
   matching the actual Lean proof. No new-node requirements apply.

Second-reading changes: corrected the helper and main proof docstrings to describe
range factorization rather than connecting-map naturality; removed an unused local
kernel equality and three redundant proof imports; updated the report's import and
axiom claims. No mathematical proof or statement needed repair. Closed one original
hole, added zero holes; no decomposition.
