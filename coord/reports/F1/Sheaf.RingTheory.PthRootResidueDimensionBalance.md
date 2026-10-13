## What changed

Reduced `Algebra.pthRoot_residue_dimension_balance` to two sourced, strictly smaller
obligations in new modules: `Algebra.pthRoot_cotangent_dimension` compares the two
cotangent dimensions and supplies finite residue extension; and
`Algebra.residue_conormal_snake_sequence` supplies the exact sequence for an arbitrary
local homomorphism of local prime-field algebras. The assigned theorem combines them
with existing Cartier equality, rank-nullity, and Mathlib's six-term Euler characteristic.
A proved private helper `Algebra.finite_of_exact` restricts a map to its range to derive
finiteness of the middle term of an exact sequence from finiteness of its neighbors.

The assigned theorem's signature and public imports are unchanged. Its proof imports
are the two new modules, `Sheaf.Paper.CartierEquality`,
`Mathlib.Algebra.Module.LinearMap.Index`, and
`Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra`. Updated the assigned node's
proof, proof_deps and proof_origin, and recorded both new signatures verbatim.
No existing definitions, interfaces, or other held modules changed.

This retry repaired the preserved draft after the missing dependencies became available.
The new statements use Mathlib's canonical residue-field algebra instance. An explicit
RingHom.toAlgebra instance in the old draft conflicted with the separately registered
residue-field module instance when elaborating the snake map. The proof also unfolds
its outer let-bound quotient before introducing the local-ring hypotheses, and unfolds
local aliases before integer dimension arithmetic. All three modules compile without
warnings through the prescribed `lcompile.py --all` command. The final dry run is the
required `deliver3.py F1 Sheaf.RingTheory.PthRootResidueDimensionBalance --no-push`;
the second reader is authorized to perform the final push.

## Proved and sorry left

Closed the original explicit hole in `Algebra.pthRoot_residue_dimension_balance`, node
`lem-weil-pbc-pth-root-residue-dimension-balance`, by a complete compiling combination
of the intermediate results. The assigned module has no remaining sorry.

Added exactly two holes, each the entire proof of a named public theorem in its own module:

- `Algebra.pthRoot_cotangent_dimension`, node
  `lem-weil-pbc-pth-root-cotangent-dimension`.
- `Algebra.residue_conormal_snake_sequence`, node
  `lem-weil-pbc-residue-conormal-snake-sequence`.

This is a decomposition: one upper hole is replaced by two lower obligations, not a
sorry-free proof of the mathematical result. Neither obligation asserts equality of
beta's kernel and cokernel dimensions. No hole occurs in a definition or private helper.

## No longer needed

No original public import was removed; no existing module is claimed pruned.
Removed the preserved draft's redundant proof imports
`Mathlib.RingTheory.Finiteness.Finsupp` and `Mathlib.RingTheory.Polynomial.Basic`.
The direct proof no longer uses `Algebra.pthRoot_residue_differentials`: finiteness
of beta's kernel and cokernel instead follows from the snake sequence and finite
conormal and field-homology terms. Its module remains a public import because it
defines `residueDifferentialComparison` used by the assigned statement.
All original field-construction, regular-local, Jacobi-Zariski and snake-lemma nodes
remain needed inside the two new nodes. Cartier equality remains used directly.
No claim is made that an existing module leaves the targets' import closure.

Second-reading import cleanup removed redundant
`Mathlib.RingTheory.Ideal.Cotangent` imports from both new modules; the declarations
remain available through their other public imports. No existing public import changed.
The following old nodes leave the assigned node's **direct** `proof_deps`:

- `def-weil-pbc-finite-purely-inseparable-extension`.
- `def-weil-pbc-flat-ring-map`.
- `def-weil-pbc-g-ring`.
- `def-weil-pbc-kahler-differentials`.
- `def-weil-pbc-mv-polynomial-ring`.
- `def-weil-regular-scheme`.
- `lem-weil-pbc-field-char-p-h1-cotangent-vanishing`.
- `lem-weil-pbc-finite-dimensional-domain-is-field`.
- `lem-weil-pbc-flat-height-formula`.
- `lem-weil-pbc-jacobi-zariski-connecting-map-naturality`.
- `lem-weil-pbc-jacobi-zariski-homology-sequence`.
- `lem-weil-pbc-jacobi-zariski-surjection-h1`.
- `lem-weil-pbc-nl-presentation-h1-functoriality`.
- `lem-weil-pbc-pth-root-residue-differentials`.
- `lem-weil-pbc-pth-roots-extension-degree`.
- `lem-weil-pbc-purely-inseparable-base-change-local-ring`.
- `lem-weil-pbc-regular-local-cotangent-dimension`.
- `lem-weil-pbc-snake-lemma-modules`.

Except for the unused residue-presentation theorem
`lem-weil-pbc-pth-root-residue-differentials`, these remain in the two smaller
obligations' routes. Definitions still needed by signatures remain available through
public imports. These are direct dependency reductions, not claims of closure pruning.


## Where the brief, the DAG or earlier work was wrong

The previous retries could not import published PthRootAlgebraLocal and
PthRootResidueDifferentials object files. Both are available on this retry; the
publication blocker is resolved. The preserved draft had not been checked as a whole
and contained the instance and binder issues described above, now repaired.

Re-read [Stacks 07E5](https://stacks.math.columbia.edu/tag/07E5), proof of (2) => (4),
particularly the big conormal diagram and its dimension comparison, and
[Stacks 00ON](https://stacks.math.columbia.edu/tag/00ON) for the flat height equality.
The latter supplies the equality needed here rather than the dimension inequality
of 00OM. The reduction preserves the unit sk-thm-p1 and changes only its lower nodes.

The snake-sequence statement was checked on the identity map, field-to-field maps,
and nonregular local rings. Its exactness needs vanishing of prime-field H1 for
fields, but no geometric regularity or finite-dimensional absolute differential modules.
The cotangent comparison includes n=0 and A a field; independence supplies the correct
p-root field degree. No arbitrary data is chosen from an unproved existence theorem.

The preserved search records contain no duplicate of either intermediate statement.
LeanSearch's Internal Server Error is recorded as unavailable, not evidence of absence.
The assigned node's recorded blueprint ancestor is retained, and the new nodes prepend
the assigned node to its via chain and name their source steps.

## New nodes

`lem-weil-pbc-pth-root-cotangent-dimension` records original steps 1-3: the p-root field
identification, finite residue extension, regularity, and equality of cotangent dimensions.
It lives in `Sheaf.RingTheory.PthRootCotangentDimension`.

`lem-weil-pbc-residue-conormal-snake-sequence` records original steps 5-7 through the
exact sequence, leaving all dimension arithmetic in the assigned module. It applies
to arbitrary local maps of local prime-field algebras and is independent of geometric
regularity and coefficient independence. It lives in
`Sheaf.RingTheory.ResidueConormalSnakeSequence`.

Both nodes carry their source, complete natural-language proof, search records,
unchanged unit, and verbatim Lean signature. No change record or forced adaptation is
needed: no existing statement, definition, or visibility changed.

## Second reading by F1

1. Compared the delivered original module with the repository using `diff`, and
   mechanically compared its existing theorem signature byte for byte: unchanged.
   Only proof imports, a proved private helper, the proof, and its descriptive
   docstring changed. There are no existing definition or visibility changes and
   no forced adaptations. All three node Lean signatures match the source text.
2. Compiled all three modules in import order through `lcompile.py --all`, with
   no errors or warnings. The assigned theorem and private helper contain no
   `sorry`; the only two holes are the public theorems listed above. Inspected for
   forbidden declarations and arbitrary witness constructions: none. Explicit
   `#print axioms` probes are recorded below. The upper result is a decomposition,
   closing one explicit hole and adding two, for net minus one before closure pruning.
3. Read both new theorem statements and complete proof docstrings against Stacks
   [07E5](https://stacks.math.columbia.edu/tag/07E5) and the flat dimension formula
   [00ON](https://stacks.math.columbia.edu/tag/00ON). The cotangent statement is just
   the regularity/dimension part, not the beta balance. Tested n=0, A a field,
   and empty independent families. For the general snake statement, tested identity
   maps, field extensions, the dual-number ring mapping to its residue field, and
   a prime field mapping into dual numbers: the conormal rows and endpoint terms
   have the asserted exactness, including without regularity or Noetherianity.
   The existential maps are eliminated solely inside a proof, not used to define
   arbitrary data. Repeated semantic Mathlib searches with embedding-dimension
   and six-term-exact-sequence wording, plus grep on Mathlib and both library
   roots: only separate ingredients, no duplicate assembled statements. Neither
   remaining obligation can be closed by a short existing theorem application.
4. Reviewed the complete reduction: cotangent finiteness, Cartier equality,
   exactness-derived beta finiteness, rank-nullity for alpha, and the six-term
   Euler characteristic justify every dimension cancellation. Proof-only imports
   are plain imports. Removed two redundant imports from the new modules and
   enumerated every removed direct proof dependency above. The unit sk-thm-p1's
   realized statement and steps are unchanged; the reduction stays below them.
5. Compared the original and delivered DAG node: only `proof`, `proof_deps`, and
   `proof_origin` changed. For all three nodes, `proof_deps` equals the union of
   step uses. Checked new-node sources, self-contained statements, creation data,
   search records, blueprint provenance, unit/chapter, and verbatim Lean records.
   Verdict: both smaller obligations are true, sourced, and necessary for this
   reduction; the DAG agrees with the Lean.

Changes made by this reading: removed the two redundant cotangent imports,
corrected the assigned theorem's docstring to describe its actual exactness-based
finiteness argument, completed the direct-dependency inventory, and documented
this independent review. No mathematical statement or proof body was changed.

Axiom probe result: `Algebra.pthRoot_residue_dimension_balance`,
`Algebra.pthRoot_cotangent_dimension`, and
`Algebra.residue_conormal_snake_sequence` use only `propext`, `Classical.choice`,
`Quot.sound`, and `sorryAx` from open obligations. The private
`Algebra.finite_of_exact` helper uses only `propext`, `Classical.choice`, and
`Quot.sound`. The scratch copy was removed after the successful check.
