## What changed

Proved `Algebra.transitivityGamma` in
`lean/Sheaf/RingTheory/TransitivityGamma.lean`, with its statement unchanged.
Added six fully proved private helpers in the same module: finite-stage
injectivity, evaluation compatibility with variable renaming, descent of
membership in the square of the relation ideal, the canonical conormal formula
on pure tensors, finite-support descent of tensors and their representatives,
and the resulting left injectivity. No new public declaration or new module.

At a regular stage the proof combines the existing regular-sequence theorem
with injectivity of tensoring the H1 inclusion over a field. At the limit the
proof actually constructs the finite support of the tensor representative and
of the ideal-square witness, then uses the existing complete-intersection
subalgebra theorem on their union. The image of its embedding is a subalgebra;
its presentation is the quotient map followed by range restriction. Thus no
object is defined by selecting an arbitrary witness from an unproved theorem.
Existential elimination occurs only inside proofs of propositions.

The five exactness/surjectivity clauses use Mathlib's existing canonical maps
and exactness lemmas. Retained the existing public Jacobi–Zariski sequence import to preserve the
module interface. The proof uses its underlying Mathlib declarations directly.
The second reading removed the redundant proposed proof imports of
`Mathlib.Algebra.Algebra.Subalgebra.Tower` and
`Mathlib.Algebra.MvPolynomial.Variables`; their declarations are already available.
Kept the two existing proof imports
for complete-intersection subalgebras and regular-sequence injectivity.
Updated the item's DAG proof, proof dependencies, and proof origin.

Sources checked: [07E2](https://stacks.math.columbia.edu/tag/07E2),
[07D5](https://stacks.math.columbia.edu/tag/07D5),
[07BQ](https://stacks.math.columbia.edu/tag/07BQ), and
[07BV](https://stacks.math.columbia.edu/tag/07BV).
The finite-support proofs implement the canonical-presentation argument in
07BQ rather than introducing any unproved continuity theorem.

## Proved and sorry left

Closed the one original hole: `Algebra.transitivityGamma`
(node `lem-weil-pbc-transitivity-gamma`). All six private helpers are proved.
There are zero `sorry`s left in the delivered module, zero holes added,
and zero intermediate statements split off.

The proof uses the existing stated dependencies
`Algebra.jacobiZariski_left_injective_of_regularSequence`
(node `lem-weil-pbc-jacobi-zariski-regular-sequence-left-injective`) and
`FieldTheory.exists_completeIntersection_subalgebra`
(node `lem-weil-pbc-field-extension-complete-intersection-subalgebras`).
Their pre-existing holes are unchanged; closing this module is a proof from
those statements, not a claim that the entire target import closure is closed.

The single-file compiler accepts the proof. The final delivery dry run checks
the compiled module, declarations, imports, and preflight; its result is the
worker's READY status. No library-wide build was run.

## No longer needed

The proof does not call `Algebra.jacobiZariski_homology_sequence` or its Tor
comparison. Removed `lem-weil-pbc-jacobi-zariski-homology-sequence` from this
node's `proof_deps`; its underlying Mathlib exactness declarations suffice.
The public import `Sheaf.RingTheory.JacobiZariskiHomologySequence` is retained
because removing it changes the module interface (the initial dry run caught
this). It is also an indirect import of the regular-stage dependency, so this
delivery does not claim that the module leaves the targets' import closure.
No existing import was removed. The second reading removed the two redundant
new Mathlib imports listed above, after compiling a scratch copy without both.
Removed `def-weil-pbc-tor-modules` from this node's proof dependencies.
Neither positive Tor vanishing nor the two-term-kernel base-change equivalence
is needed: flat tensoring of the H1 inclusion suffices. No separate imports
of Tor, vector-space freeness, or presentation functoriality were added;
the necessary freeness and functoriality declarations are available through
Mathlib and the existing dependencies. Every other original proof dependency
is retained for the finite-stage or finite-support argument. No globally
unreachable module is claimed without the maintainer's closure computation.

## Where the brief, the DAG or earlier work was wrong

The DAG's Tor comparison is mathematically valid but unnecessary for this
proof. It also described exactness at H1(M/K) as requiring that comparison;
Mathlib already proves it under flatness of M/L. The actual unresolved work
was the finite-stage injectivity and the passage from finite stages to M;
both are now connected by complete Lean proofs.

The node's unit is `sk-thm-p1`. This node is not among that unit's `realized`
statement or proof-step nodes. The change only shortens this node's internal
route and retains the complete-intersection and regular-sequence ingredients;
no prescribed unit step is bypassed. No statement or definition was changed,
and no adaptation of another module is required.

The local `literature/stacks-project/` source files named by the DAG are absent
on this machine. The corresponding official Stacks pages were read directly.

The first dry run refused a public-import removal; restored that import and
scoped the tensor notation to individual private helpers before rerunning.

## Second reading by G2

1. **Interface — PASS.** Compared the only delivered Lean module with the
   repository version using `diff`, and checked the existing
   `Algebra.transitivityGamma` signature byte for byte. Its signature, universes,
   visibility, and all original imports are unchanged. There are no existing
   definitions to alter and no change records or forced adaptations. The only
   added declarations are six private, fully proved helpers.
2. **Proof — PASS.** Independently compiled the module with `lcompile.py`:
   no errors or warnings. Scanned for holes and forbidden declarations or
   attributes: none. A scratch copy printed axioms for all seven declarations.
   The evaluation, relation-square descent, pure-tensor conormal formula, and
   tensor finite-support helpers use only `propext`, `Classical.choice`, and
   `Quot.sound`. The regular-stage helper, final injectivity helper, and public
   theorem additionally use `sorryAx` through the two existing dependencies
   identified under `Proved and sorry left`. No hole is added. Existential
   witnesses are eliminated only in proofs of propositions; in particular the
   image subalgebra and its quotient presentation do not introduce a public
   data definition selected from unproved mere existence.
3. **Split statements — PASS (none).** No new sorry statement or node was split
   off. Read all six helper statements and their proofs. Checked the zero tensor,
   empty support, sums, empty regular list, and identity-tower cases: the arguments
   require no nonempty support, positive presentation size, separability, or
   finite extension hypothesis. Relation factors descend by injective evaluation;
   equality of lifted representatives follows from injective renaming. The union
   of tensor support and relation-witness support is essential and is included.
4. **Route and pruning — PASS after import cleanup.** Independently searched
   LeanFinder for “base extension injective first cotangent homology field
   extension filtered union complete intersection”, and searched the project,
   upstream RingTheory sources, and Mathlib Jacobi–Zariski source. No theorem
   gives a shorter general left-injectivity proof; the hits concern cotangent
   spaces, inclusions, localization, or formally smooth presentations. The five
   remaining clauses already use Mathlib directly. Scratch compilation without
   each added Mathlib import, then without both together, succeeded. Removed
   both redundant new imports. Preserved the original public import needed by
   the interface. Checked every old proof dependency against the new list:
   the unused Jacobi–Zariski project theorem and Tor definition are both recorded
   under `No longer needed`. No globally pruned module is claimed. Inspected
   `dag/units/sk-thm-p1.json`: neither this item nor the discarded dependencies
   realizes a prescribed unit statement or step. The unit route is unchanged.
5. **DAG — PASS.** The sole node changes only `proof`, `proof_deps`, and
   `proof_origin`; its statement and Lean record are unchanged. Its five proof
   steps match the compiled argument, and `proof_deps` is exactly the union of
   their `uses`. The retained complete-intersection and regular-sequence nodes
   supply the two actual project theorem applications. Independently read the
   official [07E2](https://stacks.math.columbia.edu/tag/07E2) and
   [07BV](https://stacks.math.columbia.edu/tag/07BV) pages: they support the tower
   statement and the complete-intersection finite-subset route, respectively.

Changed in this reading: removed the two redundant new Mathlib imports and
updated this report. No proof body, declaration signature, definition, or node
was changed by the second reader. One original hole closed, zero holes added,
zero split-off statements; the upstream dependencies remain open.
