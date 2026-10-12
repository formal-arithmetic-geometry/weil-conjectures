## What changed

Replaced the sole hole in `Sheaf.FieldTheory.BrauerScalarDefectFaithfulForward`
with a compiling reduction through concrete positive matrix amplifications,
algebra-isomorphism transport, and uniqueness for one fixed algebra. The existing
public signature and public import are unchanged. Added proof-only imports of
`Mathlib.Algebra.Central.Matrix`, `Mathlib.RingTheory.SimpleRing.Matrix`,
`Sheaf.FieldTheory.BrauerScalarDefectAmplification`, and
`Sheaf.FieldTheory.BrauerScalarDefectUnique`.

The new amplification module proves
`Field.hasBrauerScalarDefect_of_matrix_algEquiv` fully. Its private constructions
commute scalar extension with matrices using `TensorProduct.piRight`, flatten nested
matrices using `Matrix.compAlgEquiv` and `finProdFinEquiv`, and amplify invertible
matrices using `Units.map` of the diagonal and flattening ring homomorphisms.
The proof verifies local constancy, the descent identity, the scalar identity, and
compatibility with Galois action. It reuses the original homogeneous cocycle and
its homology-image equation; it chooses no algebra or cocycle from mere existence.
`#print axioms Field.hasBrauerScalarDefect_of_matrix_algEquiv` reports exactly
`propext`, `Classical.choice`, and `Quot.sound`.

The main module's proved private `Field.scalarDefect_transport` composes a splitting
with the inverse algebra isomorphism extended by `Algebra.TensorProduct.congr`.
All other witnesses are reused, and its descent identity is proved by evaluating
the old identity on the inverse image. The main theorem constructs the two CSA
matrix records from actual matrix carriers, amplifies each realization, transports
the first across the given matrix isomorphism, and applies fixed-algebra uniqueness.
Updated the original node's proof, proof dependencies, and proof origin accordingly.
No existing definition, statement, visibility, or target signature changed.

Validation: all three modules compile in import order without warnings using
`lcompile.py --all`. The amplification axiom check is clean. Both new statements
were checked against the scalar-defect construction of Stacks Section 03R1
(following Lemma 03R6 and preceding Theorem 03R7), with continuous coboundaries
as in Section 0DVG. The unit `sk-thm-br` states the proper-case route via Brauer injection and
Tsen. Its `realized.statement` and sole `realized.steps` entry are empty in this
checkout; this delivery leaves them unchanged and works below the unit level.

## Proved and sorry left

Closed the original hole in
`Field.brauerScalarDefect_eq_of_brauerEquivalent`
(node `lem-sc-brauer-scalar-defect-faithful-forward`). Its proof is complete from the
new lemmas. This is a decomposition, not an unconditional proof: it still depends
transitively on the remaining fixed-algebra uniqueness hole.

Added and fully proved
`Field.hasBrauerScalarDefect_of_matrix_algEquiv`
(node `lem-sc-brauer-scalar-defect-amplification`). All private helper theorems in
that module are proved: `tensorMatrixLinear_tmul`, `flatten_map`, `amplify_map`,
and `amplify_scalar`. Its private definitions have fully constructed data and
fully proved algebra laws. Also proved the main module's private
`Field.scalarDefect_transport`.

The only sorry left anywhere in this delivery is
`Field.brauerScalarDefect_unique`
(node `lem-sc-brauer-scalar-defect-unique`, new module
`Sheaf.FieldTheory.BrauerScalarDefectUnique`). Its whole proof is `:= by sorry`.
Its statement concerns two splittings/lifts of a single fixed algebra, with no
Brauer-equivalence or matrix-amplification input. Its docstring and node describe
the positive-size identification, Skolem-Noether change of splitting, locally
constant scalar one-cochain, and homogeneous continuous coboundary calculation.
This is the remaining part of the argument, while amplification and isomorphism
transport have real Lean proofs. Holes closed: 1. Holes added: 1. Net holes: 0.

Edge cases: amplification requires `n != 0` and the realization already supplies
`d != 0`, so the new size `n*d` is positive. The n=1 case is ordinary transport,
and d=1 reduces to scalar units. No characteristic restriction is used. The
uniqueness argument needs a diagonal entry, available from the existing positive
size; it imposes no extra normalized-lift or normalized-cocycle hypothesis. A change
of lifts by a locally constant scalar one-cochain gives exactly a coboundary,
including at the identity element.

## No longer needed

No original import, DAG dependency, or module was pruned: the original module
imports only the scalar-defect definition, which its statement still needs.
Removed the redundant experimental imports `Mathlib.RingTheory.TensorProduct.Maps`
from the main and amplification modules and `Mathlib.Data.Matrix.Composition`
from the amplification module after recompiling without them. Also removed an unused
`open scoped TensorProduct` from the main module; its proof uses no tensor notation. The necessary
constructions are already exposed by the retained imports. The tensor-with-opposite
comparison suggested in the original docstring is unnecessary for this route;
no such dependency node or module was originally imported, so this is not claimed
as a pruned module.

## Where the brief, the DAG or earlier work was wrong

The original node supplied only the scalar-defect definition as its proof dependency.
It did not supply usable comparison lemmas for changing splittings or taking
matrix amplifications. The revised route implements amplification and isomorphism
transport and isolates only the still-unproved uniqueness calculation.

`blueprint_refs.py ancestor lem-sc-brauer-scalar-defect-faithful-forward` reports
no ancestor because the original chain records module names in `created.item`.
The parent faithfulness and comparison nodes explicitly identify the ancestor as
`lem-sc-brauer-zero`; the new nodes use that recorded ancestor and give their via
chain. Existing ancestry fields were not changed, since they are outside the
stage-3 owned fields.

Searches ran through `msearch.py`: LeanFinder and Loogle found Brauer equivalence
and its elementary relation lemmas, but no scalar-defect class comparison; grep
found only Brauer definitions in Mathlib, and repository searches found only this
family and its downstream consumers. LeanSearch returned an Internal Server Error,
recorded as unavailable, not as a negative search result. Blueprint searches found
no scalar-defect node matching the two new statements.

A shared /tmp inode limit prevented one shell here-document before any file was
changed. Subsequent temporary files use the sandbox scratchpad via TMPDIR.

## New nodes

`lem-sc-brauer-scalar-defect-amplification`, module
`Sheaf.FieldTheory.BrauerScalarDefectAmplification`, states that a central simple
algebra isomorphic to a positive matrix amplification realizes the same class.
It is fully proved from explicit tensor/matrix constructions and Mathlib lemmas.

`lem-sc-brauer-scalar-defect-unique`, module
`Sheaf.FieldTheory.BrauerScalarDefectUnique`, states uniqueness of the class for
one fixed central simple algebra. This is the sole newly added hole. Its complete
proof in words explains both change of splitting and the continuous coboundary.

Both nodes inherit chapter `sec-curve-estimates` and unit `sk-thm-br`, cite the
scalar-defect definition, record the searches actually run, and identify their
source and blueprint place. There are no change records or forced adaptations,
because no existing interface changed.


## Second reading by H3

1. **Interfaces: PASS.** Compared the delivered main module with the repository
   using `diff -u` and checked the complete existing theorem signature as an exact
   text string: it is byte-for-byte identical. Its existing docstring and public
   import are unchanged. The other two Lean modules are new; no existing definition,
   target, or other module is altered, and no change record is required.
2. **Proof and axioms: PASS as a decomposition.** Independently compiled all three
   modules in dependency order with `lcompile.py --all`, with no errors or warnings.
   Read every construction and helper: tensor/matrix multiplication is proved by
   tensor induction, flattening is an explicit equivalence, and amplified units use
   actual ring homomorphisms. No data is taken from an unproved existence statement.
   The only textual `sorry` is the whole proof of the public named uniqueness
   theorem. There are no forbidden declarations or attributes. A scratch module
   printing axioms confirms amplification uses only `propext`, `Classical.choice`,
   `Quot.sound`; the main theorem and uniqueness additionally use `sorryAx`, as
   expected from the explicitly reported uniqueness hole.
3. **New statements: PASS.** Amplification has an actual proof and uses precisely
   the positive-size hypothesis. Fixed-algebra uniqueness removes the matrix
   comparison part of the original item, and is strictly a part of its argument,
   rather than its renaming. Checked the degree-one case, amplification by one,
   absence of zero-size realizations, arbitrary characteristic, and non-normalized
   lifts. Verified the change-of-splitting formula
   `d(g) = P⁻¹ * b(g) * g(P)` and the scalar coboundary formula in the docstring;
   the positive size permits scalar extraction and the finite set of entries of
   `P` has an open common stabilizer. The docstring gives the full remaining
   mathematical proof, including continuity and passage to homogeneous cochains.
   Read Stacks Sections [03R1](https://stacks.math.columbia.edu/tag/03R1) and
   [0DVG](https://stacks.math.columbia.edu/tag/0DVG). Independent searches used
   `msearch.py` LeanFinder for projective descent lifts and cohomologous factor sets,
   Loogle for `IsLocallyConstant, Units`, and grep for
   `SkolemNoether|factorSet|cohomolog|inner_aut`, together with repository `rg` on
   scalar-defect users and conjugacy. No existing theorem closes this continuous
   degree-two comparison; Hilbert 90 hits concern degree one. The repository's
   pointwise conjugacy/lift results do not supply the coboundary calculation.
   Closing this remaining theorem is not a small repair.
4. **Route and pruning: PASS.** The original proof dependency was only the
   scalar-defect definition, which is still required; there is no old dependency
   to prune. Additional main-module imports are proof-only; the new modules expose
   only the scalar-defect definition needed by their signatures. Tensor-product Pi
   supports the explicit construction, and matrix centrality/simplicity support
   the concrete CSA records. Checked `dag/units/sk-thm-br.json`: its unit statement
   and injection/Tsen step are unchanged, and its realization entries are empty.
   The reduction is below that unit and bypasses no recorded realization.
5. **DAG: PASS.** The sole existing node differs only in `proof`, `proof_deps`,
   and `proof_origin`. These follow the implemented amplification, isomorphism
   transport, and fixed-algebra uniqueness. Both new nodes have their exact Lean
   signatures, source, natural-language proof steps, dependency union, searches,
   creation record, blueprint ancestry, chapter, unit, and Lean record. The single
   newly holed declaration has its own matching node and module.

Second reading changed the report's inaccurate assertion about unit realizations
and added this independent review and axiom evidence. No Lean proof or node needed
repair. This remains one original hole closed and one strictly simpler hole added,
net zero holes; no unconditional proof of the original item is claimed.
